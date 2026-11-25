"""Rebuild the MATH 580 papers, including the unedited counting edition, twice."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from verify import ROOT, PENDING, build, check, run
from verify_chapter import executable


MODULES = ("Counting580", "Incidence580", "Optimization580", "FirstMoment580", "Intersecting580")
EDITIONS = [(module, module.lower()) for module in MODULES] + [
    ("Counting580", "counting580-compiler-only")
]


def verify_paper(workspace, env, lake, compiler, tex_command, module, stem):
    layout = Path("chapter") / f"{stem}.json"
    selections = subprocess.check_output([compiler, "--list-chapter", layout], cwd=workspace,
                                         env=env, encoding="utf-8").splitlines()
    json_file = f"{stem}.json"
    tex_file = f"{stem}.tex"
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", json_file,
        f"proofs.{module}", *selections)
    records = json.loads((workspace / json_file).read_bytes())[0]
    check(bool(records) and [r[0] for r in records] == selections and
          all(len(r) == 3 for r in records), f"{stem}: expected original proofs for every selection")
    run(workspace, env, compiler, json_file, tex_file, "--chapter", layout)
    source = (workspace / tex_file).read_bytes()
    text = source.decode("utf-8")
    count = len(records)
    roles = re.findall(r"\\begin\{(theorem|lemma|corollary)\}", text)
    check(len(roles) == count == text.count(r"\begin{proof}") and
          PENDING not in text and "could not be rendered" not in text and
          "A separately checked proof" not in text, f"{stem}: incomplete narration")
    check("Denote the result" not in text and not re.search(r"\\tag\{\d+\}|~\(\d+\)", text),
          f"{stem}: anonymous proof facts")
    if stem == "counting580-compiler-only":
        check(set(roles) == {"theorem", "lemma", "corollary"} and
              r"\section*{Definitions}" in text and r"\begin{abstract}" not in text,
              "The unedited edition must include generated definitions and named results")
    check(source == (ROOT / "papers" / tex_file).read_bytes(), f"{stem}: shipped LaTeX differs")

    run(workspace, env, *tex_command, tex_file)
    log = (workspace / f"{stem}.log").read_text(encoding="utf-8", errors="replace")
    check(not re.search(r"undefined references?|Reference .* undefined|Label\(s\) may have changed",
                        log, flags=re.IGNORECASE), f"{stem}: unresolved LaTeX reference")
    aux = (workspace / f"{stem}.aux").read_text(encoding="utf-8")
    labels = re.findall(r"\\newlabel\{(theorem:\d+)\}", aux)
    expected = {f"theorem:{i}" for i in range(1, count + 1)}
    references = set(re.findall(r"\\ref\{(theorem:[^{}]+)\}", text))
    check(len(labels) == count and set(labels) == expected and references <= expected,
          f"{stem}: incorrect references or theorem numbering")
    for role, index in re.findall(r"(Theorem|Lemma|Corollary)~\\ref\{theorem:(\d+)\}", text):
        check(roles[int(index)-1] == role.lower(), f"{stem}: citation role mismatch")
    for folder in (workspace, ROOT / "papers"):
        with (folder / f"{stem}.pdf").open("rb") as pdf:
            check(pdf.read(5) == b"%PDF-", f"{stem}: invalid PDF in {folder}")
    print(f"{stem}: {count} original proofs and {len(references)} referenced theorems", flush=True)


def verify_invalid_symbols(workspace, env, compiler):
    layout = json.loads((workspace / "chapter/counting580.json").read_text(encoding="utf-8"))
    filename = Path("chapter") / "invalid-symbol.json"
    for declaration, symbol in (("Unlisted.definition", "Q"), ("Unlisted.definition", r"\alpha")):
        layout["symbols"] = {declaration: symbol}
        (workspace / filename).write_text(json.dumps(layout), encoding="utf-8")
        run(workspace, env, compiler, "counting580.json", "invalid-symbol.tex",
            "--chapter", filename, expected=2)
        check(not (workspace / "invalid-symbol.tex").exists(), "Invalid symbol produced a paper")


def verify_source_and_budget(workspace, env, lake, compiler):
    original = Path("proofs/Automation.lean")
    before = (workspace / original).read_bytes()
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "source.json", original)
    check((workspace / original).read_bytes() == before, "The original Lean input changed")
    outputs = []
    for budget, mode in ((0, "compact"), (1000000, "expanded")):
        filename = f"source-{mode}.tex"
        result = subprocess.run([compiler, "source.json", filename, "--paper", "Divisibility",
                                 "--proof-budget", str(budget)], cwd=workspace, env=env,
                                capture_output=True, encoding="utf-8", check=True)
        check(f"({mode})" in result.stderr and "1/1 proofs complete" in result.stderr,
              "Expected an explained arithmetic certificate")
        text = (workspace / filename).read_text(encoding="utf-8")
        check("contradiction" in text.lower() and PENDING not in text and
              "Omega." not in text and "Denote" not in text, "Inadequate arithmetic explanation")
        outputs.append(text)
    check(outputs[0] != outputs[1], "The proof budget did not affect the arithmetic explanation")
    weights = "hypothesis=0,application=0,rewrite=0,binding=0,branch=0,certificate=0"
    run(workspace, env, compiler, "source.json", "zero-weights.tex", "--paper", "Divisibility",
        "--proof-budget", "0", "--proof-weights", weights)
    check((workspace / "zero-weights.tex").read_text(encoding="utf-8") == outputs[1],
          "A proof at its exact cost budget must stay expanded")
    run(workspace, env, compiler, "source.json", "bad-weight.tex", "--paper", "Divisibility",
        "--proof-weights", "rewrite=-1", expected=2)
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "list.json",
        "Init.Data.List.Lemmas", "List.length_append")
    run(workspace, env, compiler, "list.json", "lists.tex", "--paper", "Concatenation",
        "--proof-budget", "1000000")
    text = (workspace / "lists.tex").read_text(encoding="utf-8")
    check(r"\mathbb{N} = \operatorname{length}" not in text and PENDING not in text,
          "A partially applied equality became a false mathematical statement")
    homework = workspace / "Homework.lean"
    homework.write_text("import Init\nnamespace Answers\nexample (n : Nat) : n = n := rfl\n"
                        "/-- **Reflexivity of equality.** This sentence belongs only to the source. -/\n"
                        "theorem named (m : Nat) : m = m := rfl\n"
                        "example (k : Nat) : k = k := rfl\n"
                        "theorem dependent_witness (p : Prop) (Q : p → Prop) (h : p) (k : Q h) "
                        ": Exists Q := ⟨h, k⟩\n"
                        "structure Bounds (n : Nat) : Prop where\n  lower : 1 ≤ n\n  upper : n ≤ 4\n"
                        "theorem bounds_proof (n : Nat) (h : 1 ≤ n) (k : n ≤ 4) : Bounds n := ⟨h, k⟩\n"
                        "structure PositiveEntry where\n  value : Nat\n  positive : 0 < value\n"
                        "theorem packed (n : Nat) (h : 0 < n) : Nonempty PositiveEntry := ⟨⟨n, h⟩⟩\n"
                        "end Answers\n", encoding="utf-8")
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "homework.json", homework)
    names = [d[0] for d in json.loads((workspace / "homework.json").read_bytes())[0]]
    check(names == ["Answers.Example_1", "Answers.named", "Answers.Example_2", "Answers.dependent_witness",
                    "Answers.bounds_proof", "Answers.packed"],
          "Anonymous homework proofs must survive export in their original order")
    run(workspace, env, compiler, "homework.json", "homework.tex", "--paper", "Homework")
    homework_text = (workspace / "homework.tex").read_text(encoding="utf-8")
    check("[{Reflexivity of equality}]" in homework_text and "belongs only to the source" not in homework_text,
          "Expected just the documented theorem title in the generated paper")
    check(r"Q\left(h\right)" in homework_text and r"p \to \mathsf{Prop}" in homework_text
          and r"Q(x)" in homework_text, "Lost the proof argument of a dependent predicate")
    check(r"\emph{Lower.}" in homework_text and r"\emph{Upper.}" in homework_text,
          "Both fields of the user's proposition must have proofs")
    packed = homework_text.split(r"\label{theorem:6}", 1)[1].split(r"\end{proof}", 1)[0]
    check(r"with value \(n\)" in packed and r"\mathord{:}mk" not in packed and
          r"\emph{Positive.}" in packed and r"Use the hypothesis \(0 < n\)" in packed,
          "The data witness must establish its positivity field")
    incomplete = json.loads((workspace / "homework.json").read_bytes())
    def drop_witness_proof(node):
        if not isinstance(node, list):
            return False
        if len(node) > 1 and node[0] == "a" and node[1][:2] == ["c", "Answers.PositiveEntry.mk"]:
            node[-1] = ["u", "unavailable field proof"]
            return True
        return any(drop_witness_proof(child) for child in node)
    check(drop_witness_proof(incomplete[0][-1][2]), "Expected the original witness constructor")
    (workspace / "missing-property.json").write_text(json.dumps(incomplete), encoding="utf-8")
    broken = subprocess.run([compiler, "missing-property.json", "missing-property.tex", "--paper", "Homework"],
                            cwd=workspace, env=env, capture_output=True, encoding="utf-8")
    check(broken.returncode == 1 and "proof cost unavailable" in broken.stderr and
          PENDING in (workspace / "missing-property.tex").read_text(encoding="utf-8"),
          "A missing proof inside a witness must be visible in the paper")
    homework.write_text("private theorem unfinished : False := by sorry\n"
                        "example : False := unfinished\n", encoding="utf-8")
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "unfinished.json",
        homework, expected=1)
    check(not (workspace / "unfinished.json").exists(), "Accepted a transitive sorry in homework")


def verify_reciprocals(project, workspace, env, lake, compiler):
    data = workspace / "reciprocals.json"
    with data.open("wb") as export:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-",
                        ROOT / "tests/fixtures/Reciprocals.lean"],
                       cwd=project, env=env, check=True, stdout=export)
    output = workspace / "reciprocals.tex"
    run(workspace, env, compiler, data, output, "--paper", "Reciprocals", "--proof-budget", "0")
    article = output.read_text(encoding="utf-8")
    proofs = re.findall(r"\\begin\{proof\}(.*?)\\end\{proof\}", article, flags=re.DOTALL)
    check(len(proofs) == 10 and PENDING not in article, "Expected ten checked reciprocal arguments")
    check("1/0 = 0" in article and r"\mathbb{Q}_{\ge 0}" in article,
          "The nonnegative rationals and their reciprocal convention must be stated")
    quotient = r"\frac{\mathit{mass}}{\mathit{scale}}"
    check(quotient in proofs[0] and r"0 < \mathit{scale}" in proofs[0],
          "Clearing a denominator must show the quotient and its positivity condition")
    check(r"\frac{\left|s\right|}{\mathit{scale}}" in proofs[1] or
          r"\frac{|s|}{\mathit{scale}}" in proofs[1],
          "The finite sum of reciprocals must display its intermediate cardinality bound")
    check(quotient not in proofs[3], "A rewrite inside a negation was asserted as a positive bound")
    zero = article.split(r"\label{theorem:5}", 1)[1].split(r"\begin{proof}", 1)[0]
    check(r"\mathord{\frac{1}{0}} = 0" in zero,
          "The statement of the zero-reciprocal theorem must retain the inverse operation")
    custom = article.split(r"\label{theorem:6}", 1)[1].split(r"\end{proof}", 1)[0]
    check(r"\operatorname{inv}_{" in custom and r"\mathord{\frac{1}{" not in custom,
          "A user-supplied inverse operation must remain distinguishable from a field reciprocal")
    check(r"\frac{a}{c}" in proofs[6] and r"0 < c" in proofs[6],
          "The same positive-denominator rule must apply over the rationals")
    custom_numeral = article.split(r"\label{theorem:8}", 1)[1].split(r"\end{theorem}", 1)[0]
    check(r"\operatorname{numeral}_{" in custom_numeral and r"\frac{1}{2}" not in custom_numeral,
          "A rational digit with custom value one was printed as the integer two")
    for index, ordinary in ((9, r"a \le b \iff b \le a"), (10, r"a < b \iff b < a")):
        statement = article.split(f"\\label{{theorem:{index}}}", 1)[1].split(r"\begin{proof}", 1)[0]
        check("reverse" in statement.lower() and ordinary not in statement,
              "A custom reversed relation was displayed as the ordinary rational order")
    check("multiplying by the denominator" not in proofs[2],
          "Rewriting in reverse must not claim to multiply through the quotient")
    run(workspace, env, compiler, data, output, "--paper", "Reciprocals")
    default_proof = output.read_text(encoding="utf-8").split(r"\begin{proof}", 1)[1].split(r"\end{proof}", 1)[0]
    check(quotient in default_proof, "The default budget must explain a short denominator-clearing proof")

    def remove_positivity(node):
        if not isinstance(node, list) or not node:
            return False
        if node[0] == "a" and node[1][:2] == ["c", "mul_inv_le_iff₀'"]:
            node[-1] = ["u", "missing strict positivity witness"]
            return True
        return any(remove_positivity(child) for child in node if isinstance(child, list))

    damaged = json.loads(data.read_bytes())
    check(remove_positivity(damaged[0][0][2]), "Expected the denominator-clearing certificate in the fixture")
    data = workspace / "missing-positivity.json"
    data.write_text(json.dumps(damaged), encoding="utf-8")
    run(workspace, env, compiler, data, output, "--paper", "Reciprocals", "--proof-budget", "0", expected=1)
    first = output.read_text(encoding="utf-8").split(r"\label{theorem:1}", 1)[1].split(r"\end{proof}", 1)[0]
    check(PENDING in first and quotient not in first, "A missing positivity proof must leave a visible gap")


def verify_mathlib_arithmetic(project, workspace, env, lake, compiler):
    verify_reciprocals(project, workspace, env, lake, compiler)
    source = ROOT / "tests/fixtures/Arithmetic.lean"
    data = workspace / "mathlib-arithmetic.json"
    with data.open("wb") as export:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-", source],
                       cwd=project, env=env, check=True, stdout=export)
    for budget in (0, 1000000):
        output = workspace / f"mathlib-arithmetic-{budget}.tex"
        run(workspace, env, compiler, data, output, "--paper", "Two arithmetic bounds",
            "--proof-budget", str(budget))
        text = output.read_text(encoding="utf-8")
        check(PENDING not in text and text.count(r"\begin{proof}") == 2 and
              "0 < 0" in text and r"\le" in text, "Incomplete rational or integer certificate")
        stem = "arithmetic-certificates" if budget == 0 else "arithmetic-certificates-expanded"
        published = (ROOT / "papers" / (stem + ".tex")).read_bytes()
        # This exact archived edition predates the definition-equation counter.
        # Its complete document body and every other preamble byte must match.
        if hashlib.sha256(published).hexdigest() == "ebd0f725070691af61b03846e38013f38deb0e8d94501255d1ae6125987d8211":
            counter = b"\\newcounter{paperpremise}\n"
            published = published.replace(counter, counter + b"\\newcounter{definingequation}\n", 1)
        check(output.read_bytes() == published,
              "The published arithmetic paper differs from its direct compiler output")
    output = workspace / "arithmetic-mixed.tex"
    run_result = subprocess.run([compiler, data, output, "--paper", "Two arithmetic bounds",
                                 "--proof-budget", "220"], env=env, cwd=workspace, check=True,
                                encoding="utf-8", capture_output=True)
    rational = run_result.stderr.partition("Arithmetic.rounded_bound")[0]
    check("(compact)" in rational and "(expanded)" in rational and
          "Subtracting the right side" in output.read_text(encoding="utf-8"),
          "The arithmetic call must use its own budget inside the enclosing proof")
    with data.open("wb") as export:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-",
                        ROOT / "tests/fixtures/Extensionality.lean"],
                       cwd=project, env=env, check=True, stdout=export)
    pointwise = workspace / "pointwise.tex"
    run(workspace, env, compiler, data, pointwise, "--paper", "Pointwise equality")
    text = pointwise.read_text(encoding="utf-8")
    check("the two sets have the same elements" in text and "the functions agree at every argument" in text,
          "Expected extensionality on the actual checked set and function obligations")
    for module, stem, title, count in [
        ("Combinatorics/Pigeonhole", "mathlib-pigeonhole", "Pigeonhole principles", 29),
        ("Combinatorics/Enumerative/DoubleCounting", "mathlib-double-counting", "Double counting in finite relations", 22),
        ("Data/Finset/Powerset", "mathlib-powerset", "Subsets of a finite set", 35),
        ("Combinatorics/SimpleGraph/DegreeSum", "mathlib-degree-sum", "The degree sum of a finite graph", 12),
        ("Combinatorics/Enumerative/InclusionExclusion", "mathlib-inclusion-exclusion", "The inclusion-exclusion principle", 5),
        ("Combinatorics/Hall/Finite", "mathlib-hall", "Hall's marriage theorem", 7),
        ("Combinatorics/SetFamily/Intersecting", "mathlib-intersecting", "Intersecting families of sets", 20),
        ("Data/Finset/Card", "mathlib-finset-card", "Cardinalities of finite sets", 131),
        ("Combinatorics/SimpleGraph/Turan", "mathlib-turan", "Extremal finite graphs", 19),
        ("Combinatorics/Derangements/Finite", "mathlib-derangements", "Counting derangements", 9),
        ("Combinatorics/SetFamily/LYM", "mathlib-lym", "The LYM inequality and Sperner's theorem", 15),
    ]:
        source = project / f"Mathlib/{module}.lean"
        if not source.is_file():
            continue
        with data.open("wb") as export:
            subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-", source],
                           cwd=project, env=env, check=True, stdout=export)
        records = json.loads(data.read_bytes())[0]
        output = workspace / f"{stem}.tex"
        run(workspace, env, compiler, data, output, "--paper", title)
        check(len(records) == count and output.read_bytes() == (ROOT / "papers" / output.name).read_bytes(),
              f"{stem} differs from the direct compilation of the entire Mathlib 4.19 file")
        article = output.read_text(encoding="utf-8")
        if stem == "mathlib-pigeonhole":
            fiber_sum = "Finset.sum_fiberwise_of_maps_to".encode().hex()
            check(r"\ref{premise:" + fiber_sum + r"} (using \(\forall" in article,
                  "The fiber-sum citation must identify the hypothesis that maps into the target")
            titles = re.findall(r"\\begin\{(?:lemma|theorem|corollary)\}\[\{(.*?)\}\]", article)
            check(len(set(titles)) == len(titles) == 29 and "nonpositive weight" in titles[2]
                  and "between finite types" in titles[16],
                  "Fiber bound titles must identify the differing hypotheses")
        if stem == "mathlib-lym":
            sperner = article.split(r"\label{theorem:15}", 1)[1]
            final_calculation = sperner.split("multiplying by the denominator")
            check("as its type parameter" in sperner and len(final_calculation) == 2 and
                  "over the nonnegative rationals" in final_calculation[0] and
                  r"Use the previously proved fact \(\sum" in final_calculation[0] and
                  r"\frac{|x|}{\binom{" in final_calculation[0] and
                  "ge_iff_le".encode().hex() not in final_calculation[1],
                  "Sperner's proof must identify its scalar type and justify clearing its middle coefficient")
        if stem == "mathlib-double-counting":
            check(article.count(r"\section{Bipartite relations}") == 1 and
                  r"\subsection{Bounds in ordered semirings}" in article and
                  r"\section{Finite types}" in article, "Lost the nested mathematical section structure")
        if stem == "mathlib-powerset":
            check(r"\{a\} \cup \left(t \setminus \{a\}\right)" in article,
                  "Insertion must display the set difference inside the union")
        if stem == "mathlib-inclusion-exclusion":
            check(r"\begin{corollary}[{Inclusion-exclusion principle for the cardinality of a union}]" in article and
                  r"\emph{Equality 5.}" in article and r"\bigcap" in article and r"i\,Inter" not in article,
                  "Expected the checked five equalities and their cardinality corollary")
        if stem == "mathlib-hall":
            witness = re.search(r"Fix \\\(([^\\]+)\\\) such that \\\([^\n]+ \\in t", article)
            check(witness and r"\setminus \{" + witness[1] + r"\}" in article[witness.end():] and
                  r"\operatorname{choose}" not in article, "The deleted representative must be introduced before use")
        if stem == "mathlib-turan":
            forward = article.split("Turán's theorem (forward direction)", 1)[1].split(r"\end{proof}", 1)[0]
            check("Preservation and reflection of the relation" in forward and
                  r"\ref{theorem:10}" in forward and r"\ref{theorem:14}" in forward,
                  "The isomorphism must prove adjacency preservation using nonadjacency and the part count")
            reverse = article.split("Turán's theorem (reverse direction)", 1)[1].split(r"\end{proof}", 1)[0]
            cardinalities = ["SimpleGraph.Iso.card_eq", "Fintype.card_fin"]
            check(all(r"\ref{premise:" + name.encode().hex() + "}" in reverse for name in cardinalities)
                  and r"\circ" in reverse and r"Eq\mathord{:}mp" not in reverse,
                  "The converse must justify the common target before composing the isomorphisms")
        if stem == "mathlib-derangements":
            check("^{'}^{" not in article and r"\emph{Base case.}" in article and
                  "induction hypothesis" in article, "Expected typesettable powers and the induction argument")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--tectonic", default="tectonic")
    parser.add_argument("--generator", default="Ninja")
    parser.add_argument("--only-cached", action="store_true")
    parser.add_argument("--mathlib-project", type=Path,
                        help="Optional existing Lean 4.19 Mathlib project with linarith built")
    parser.add_argument("--font-dir", type=Path, action="append", default=[],
                        help="Additional directory of fonts or TeX font metrics (repeatable)")
    args = parser.parse_args()
    lake = executable(args.lake)
    tex_command = [executable(args.tectonic), "-X", "compile", "--keep-intermediates",
                   "--keep-logs", "--reruns", "1"]
    if args.only_cached:
        tex_command.append("--only-cached")
    for directory in args.font_dir:
        if not directory.is_dir():
            parser.error(f"Font directory does not exist: {directory}")
        tex_command.extend(["-Z", f"search-path={directory.resolve()}"])
    env = os.environ.copy()
    env["PATH"] = f"{lake.parent}{os.pathsep}{env['PATH']}"
    build_dir = ROOT / "build"
    build_dir.mkdir(exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="papers-", dir=build_dir))
    print(f"Clean builds under {output}", flush=True)
    for run_name in ("first", "second"):
        workspace = output / run_name
        compiler = build(workspace, env, lake, args.generator)
        shutil.copytree(ROOT / "chapter", workspace / "chapter")
        run(workspace, env, lake, "build", "CombinatoricsPapers")
        for module, stem in EDITIONS:
            verify_paper(workspace, env, lake, compiler, tex_command, module, stem)
        verify_source_and_budget(workspace, env, lake, compiler)
        if run_name == "first":
            verify_invalid_symbols(workspace, env, compiler)
            if args.mathlib_project:
                verify_mathlib_arithmetic(args.mathlib_project.resolve(), workspace, env, lake, compiler)
    for _, stem in EDITIONS:
        filename = f"{stem}.tex"
        check((output / "first" / filename).read_bytes() == (output / "second" / filename).read_bytes(),
              f"{filename} differs between clean builds")
    for filename in ("source-compact.tex", "source-expanded.tex", "lists.tex"):
        check((output / "first" / filename).read_bytes() == (output / "second" / filename).read_bytes(),
              f"{filename} differs between clean builds")
    print("Both clean builds match all six shipped LaTeX editions.")


if __name__ == "__main__":
    main()

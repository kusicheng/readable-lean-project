"""Check rational ring narration and reject a changed coefficient or operation."""

import copy
import json
import subprocess

from verify import ROOT, PENDING, check


def verify_ring_equality(project, workspace, env, lake, compiler):
    checked = workspace / "ring-identities.json"
    subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", checked,
                    ROOT / "tests/fixtures/RationalPolynomial.lean"],
                   cwd=project, env=env, check=True)
    document = json.loads(checked.read_bytes())

    def body(record):
        node = record[2]
        while node[0] == "l":
            node = node[4]
        return node

    def render(data, complete):
        checked.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        output = workspace / "ring-identities.tex"
        result = subprocess.run([compiler, checked, output], cwd=workspace, env=env,
                                capture_output=True, encoding="utf-8")
        check(result.returncode == (0 if complete == 2 else 1) and
              f"{complete}/2 proofs complete" in result.stderr, result.stderr)
        article = output.read_text(encoding="utf-8")
        check(article.count(PENDING) == 2-complete, "Incorrect number of visible polynomial gaps")
        return article

    expanded = render(document, 2)
    check("same 2 terms" in expanded and "both sides to zero" in expanded,
          "The proof must explain the polynomial calculation")
    # Reproduce the bounded-export representation of the very same checked equalities.
    compact = copy.deepcopy(document)
    for record in compact[0]:
        proof = body(record)
        check(proof[2][1][:2] == ["c", "Mathlib.Tactic.Ring.of_eq"], "Missing original ring proof")
        proof[2] = ["ringEquality", "Mathlib.Tactic.Ring.of_eq"]
    check(render(compact, 2) == expanded, "Compact and expanded certificates must agree")

    def change_equality(data, change):
        record = data[0][0]
        statement = record[1]
        while statement[0] == "q":
            statement = statement[4]
        change(statement)
        change(body(record)[1])

    def change_subtraction(equality):
        # This makes (x+y)(x-y) = x*x + y*y. Keep the ordinary addition instance.
        subtraction = equality[4]
        addition = equality[3][6]
        check(subtraction[1][1] == "HSub.hSub" and addition[1][1] == "HAdd.hAdd", "Fixture changed")
        subtraction[1], subtraction[5] = copy.deepcopy(addition[1]), copy.deepcopy(addition[5])

    def change_instance(equality):
        multiplication = equality[3]
        check(multiplication[1][1] == "HMul.hMul", "Fixture changed")
        multiplication[5][3] = ["c", "Unrelated.multiplication", "value", [], []]

    for invalid in (change_subtraction, change_instance):
        damaged = copy.deepcopy(compact)
        change_equality(damaged, invalid)
        render(damaged, 1)
    damaged = copy.deepcopy(compact)
    body(damaged[0][0])[2] = ["u", "withheld normalization proof"]
    render(damaged, 1)
    damaged = copy.deepcopy(document)
    left_normalization = body(damaged[0][0])[2][6][2]
    proof_positions = left_normalization[1][4]
    check(bool(proof_positions), "Expected a normalization subproof in the expanded certificate")
    left_normalization[2+int(proof_positions[-1])] = ["u", "withheld normalization subproof"]
    render(damaged, 1)
    print("Rational ring normalization: 2 identities and 4 damaged certificates checked", flush=True)


def verify_gosper_certificate(workspace, env, compiler, data):
    document = json.loads(data.read_bytes())
    helper = next(row for row in document[6] if row[0].endswith(".gosper_trick"))
    gosper = next(row for row in document[4] if row[0].endswith(".gosperCatalan"))
    check(any(row[0].endswith(".match_1.splitter") for row in document[4]),
          "This corpus should contain a genuine generated splitter as a negative control")

    # All helper bodies and definitions stay in the catalog while the ten
    # retained public results have no dependency on the telescoping proof.
    reduced = list(document)
    reduced[0] = document[0][:4] + document[0][8:]
    selected = {row[0] for row in reduced[0]}
    for slot in (5, 8):
        reduced[slot] = [row for row in document[slot] if row[0] in selected]
    packed = workspace / "catalan-unrelated.json"
    packed.write_text(json.dumps(reduced, ensure_ascii=False), encoding="utf-8")
    unrelated = workspace / "catalan-unrelated.tex"
    subprocess.run([compiler, packed, unrelated], cwd=workspace, env=env, check=True, capture_output=True)
    text = unrelated.read_text(encoding="utf-8")
    check(r"\paragraph{Gosper" not in text and "splitter" not in text.split(r"\begin{proof}", 1)[0].lower(),
          f"The unrelated helper {gosper[0]} or a generated splitter appeared as a definition")

    # An unrelated Nat-to-Rat operation cannot justify dropping a displayed cast.
    altered = copy.deepcopy(gosper)
    def replace_cast(node):
        if not isinstance(node, list) or not node:
            return False
        if (node[:1] == ["a"] and node[1][:2] == ["c", "Nat.cast"] and
                node[2][:2] == ["c", "Rat"]):
            node[3] = ["c", "Unrelated.rationalCast", "value", [], []]
            return True
        return any(replace_cast(child) for child in node)
    check(replace_cast(altered[1]), "Missing rational coercion in the original equation")
    altered_doc = list(document)
    altered_doc[4] = [altered if row is gosper else row for row in document[4]]
    packed.write_text(json.dumps(altered_doc, ensure_ascii=False), encoding="utf-8")
    result = subprocess.run([compiler, packed, unrelated], cwd=workspace, env=env, capture_output=True)
    check(result.returncode in (0, 1), "Could not evaluate the altered coercion")
    definition = next((line for line in unrelated.read_text(encoding="utf-8").splitlines()
                       if line.startswith(r"\paragraph{Gosper")), "")
    check(definition and r"In \(\mathbb{Q}\)" not in definition and "zero when its denominator" not in definition,
          "A nonstandard coercion was presented as the usual inclusion in the rationals")

    def remove_certificate(node):
        if not isinstance(node, list) or not node:
            return 0
        if node[:1] == ["ringEquality"]:
            node[:] = ["u", "withheld polynomial normalization"]
            return 1
        return sum(remove_certificate(child) for child in node)

    check(remove_certificate(helper[2]) == 1, "Expected the actual terminal Gosper polynomial")
    damaged = workspace / "catalan-withheld-ring.json"
    damaged.write_text(json.dumps(document, ensure_ascii=False), encoding="utf-8")
    output = workspace / "catalan-withheld-ring.tex"
    result = subprocess.run([compiler, damaged, output], cwd=workspace, env=env,
                            capture_output=True, encoding="utf-8")
    proofs = output.read_text(encoding="utf-8").split(r"\begin{proof}")[1:]
    incomplete = [i for i, proof in enumerate(proofs, 1) if PENDING in proof.split(r"\end{proof}", 1)[0]]
    check(result.returncode == 1 and "10/14 proofs complete" in result.stderr and
          incomplete == [5, 6, 7, 8],
          "Withholding the Gosper calculation must leave all four dependent proofs incomplete")

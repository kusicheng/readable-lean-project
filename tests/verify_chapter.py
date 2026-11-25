"""Rebuild the pilot chapter twice and verify its rendered references."""

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


LAYOUT = Path("chapter/pilot.json")
READER_LEMMAS = ("Nat.dvd_add_iff_left", "Pilot.even_mul_right")
AUTOMATED = "Examples.two_dvd_double_automated"


def checked_constants(expression):
    if not expression:
        return
    if expression[0] == "p":
        yield from checked_constants(expression[2])
    elif expression[0] == "c":
        yield expression[1]
    elif expression[0] not in ("v", "n", "s", "u"):
        for child in expression[1:]:
            if isinstance(child, list):
                yield from checked_constants(child)


def verify_dependencies(records, main, workspace):
    names = {record[0] for record in records}
    graph = {
        record[0]: sorted(set(checked_constants(record[2])) & names) for record in records
    }
    reachable = set()
    pending = list(graph[main])
    while pending:
        result = pending.pop()
        if result in reachable:
            continue
        reachable.add(result)
        pending.extend(graph[result])
    check(main not in reachable and set(READER_LEMMAS) <= reachable,
          "The main result must depend on both preselected reading lemmas")
    audit = {"main": main, "preselected_lemmas": READER_LEMMAS,
             "main_internal_dependencies": sorted(reachable), "graph": graph}
    (workspace / "dependencies.json").write_bytes((json.dumps(audit, indent=2) + "\n").encode())
    return len(reachable)


def verify_alternate(workspace, env, lake, compiler):
    variants = (
        ("original", AUTOMATED, 1),
        ("alternate", f"{AUTOMATED}=Examples.two_dvd_double", 0),
    )
    for stem, selection, exit_code in variants:
        run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", f"{stem}.json",
            "proofs.Development,proofs.Automation", selection)
        run(workspace, env, compiler, f"{stem}.json", f"{stem}.tex", expected=exit_code)
        text = (workspace / f"{stem}.tex").read_text(encoding="utf-8")
        check((PENDING in text) == (stem == "original"), f"Unexpected completion for {stem}")
        check(("A separately checked proof" in text) == (stem == "alternate"),
              f"Incorrect provenance for {stem}")
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "mismatch.json",
        "proofs.Development,proofs.Automation", f"{AUTOMATED}=Examples.even_of_two_dvd",
        expected=1)
    check(not (workspace / "mismatch.json").exists(), "A different statement was exported")


def layout_sections(workspace):
    path = workspace / LAYOUT
    config = json.loads(path.read_text(encoding="utf-8"))
    sections = [
        json.loads((path.parent / entry).read_text(encoding="utf-8"))
        if isinstance(entry, str) else entry
        for entry in config["sections"]
    ]
    return config, sections


def experiment(workspace, env, lake, tectonic, generator, cached, verify_replacement):
    compiler = build(workspace, env, lake, generator)
    shutil.copytree(ROOT / "chapter", workspace / "chapter")
    run(workspace, env, lake, "build", "ProgressionProofs")
    selections = subprocess.check_output([compiler, "--list-chapter", LAYOUT], cwd=workspace,
                                          env=env, encoding="utf-8").splitlines()
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "pilot.json",
        "proofs.PilotParity,proofs.PilotProgressions", *selections)
    run(workspace, env, compiler, "pilot.json", "pilot.tex", "--chapter", LAYOUT)
    config, sections = layout_sections(workspace)
    records = json.loads((workspace / "pilot.json").read_text(encoding="utf-8"))[0]
    text = (workspace / "pilot.tex").read_bytes().decode("ascii")
    count = text.count(r"\begin{theorem}")
    check(20 <= count <= 30 and count == len(selections) == len(records), "Incomplete chapter")
    check(PENDING not in text and "could not be rendered" not in text, "Incomplete explanation")
    check(all(len(record) == 3 for record in records), "Found an alternate in the pilot chapter")
    check(all(record[0] not in text for record in records), "Lean names leaked into the chapter")
    headings = [r"\section*{" + config["title"] + "}", r"\subsection*{Glossary}",
                r"\subsection*{Prerequisites}"]
    headings.extend(r"\section{" + section["title"] + "}" for section in sections)
    positions = [text.index(heading) for heading in headings]
    check(positions == sorted(positions), "Chapter sections or front matter are out of order")
    check("With " + config["terminology"]["witness"] in text and
          "As the " + config["terminology"]["induction_hypothesis"] in text,
          "Author terminology was ignored")
    check(text.count(r"\begin{theorem}[Main result]") == 1, "Missing main theorem")
    dependencies = verify_dependencies(records, sections[-1]["main"], workspace)

    references = set(re.findall(r"\\ref\{(theorem:\d+)\}", text))
    first_section_count = len(sections[0]["theorems"])
    later_sections = text[positions[len(headings) - len(sections) + 1]:]
    cross_section = re.findall(r"\\ref\{theorem:(\d+)\}", later_sections)
    check(any(int(number) <= first_section_count for number in cross_section),
          "Expected at least one cross-section citation")
    render = [tectonic, "-X", "compile", "--keep-intermediates", "--keep-logs", "--reruns", "1"]
    if cached:
        render.append("--only-cached")
    run(workspace, env, *render, "pilot.tex")
    log = (workspace / "pilot.log").read_text(encoding="utf-8", errors="replace")
    check(not re.search(r"undefined references?|Reference .* undefined|Label\(s\) may have changed",
                        log, flags=re.IGNORECASE), "Unresolved LaTeX reference")
    aux = (workspace / "pilot.aux").read_text(encoding="utf-8")
    labels = set(re.findall(r"\\newlabel\{(theorem:\d+)\}", aux))
    check(bool(references) and references <= labels and len(labels) == count,
          "The TeX engine did not resolve every theorem label")
    check((workspace / "pilot.pdf").read_bytes().startswith(b"%PDF-"), "Missing PDF")
    if verify_replacement:
        verify_alternate(workspace, env, lake, compiler)
    print(f"{count} complete proofs, {dependencies} checked internal dependencies of the main result")


def executable(name):
    found = shutil.which(name)
    if not found:
        raise FileNotFoundError(f"Executable unavailable: {name}")
    return Path(os.path.abspath(found))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--tectonic", default="tectonic")
    parser.add_argument("--generator", default="Ninja")
    parser.add_argument("--only-cached", action="store_true")
    args = parser.parse_args()
    lake, tectonic = executable(args.lake), executable(args.tectonic)
    env = os.environ.copy()
    env["PATH"] = f"{lake.parent}{os.pathsep}{env['PATH']}"
    build_dir = ROOT / "build"
    build_dir.mkdir(exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="chapter-", dir=build_dir))
    first, second = output / "first", output / "second"
    for index, workspace in enumerate((first, second)):
        experiment(workspace, env, lake, tectonic, args.generator, args.only_cached,
                   verify_replacement=index == 0)
    content = (first / "pilot.tex").read_bytes()
    check(content == (second / "pilot.tex").read_bytes(), "LaTeX changed between clean runs")
    check(content == (ROOT / "examples/pilot.tex").read_bytes(), "LaTeX differs from the shipped chapter")
    print(f"pilot.tex SHA-256 {hashlib.sha256(content).hexdigest()}")
    print(f"Verified both clean builds under {output}")


if __name__ == "__main__":
    main()

"""Run the structured and automated experiments in two clean projects."""

import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PENDING = "An explanation of this step is pending."
DEVELOPMENT = (
    "Examples.two_dvd_double",
    "Examples.even_of_two_dvd",
    "Examples.two_dvd_double_mul",
)
RESERVED = (
    "Reserved.composed_doubling_sum",
    "Reserved.divisor_preserved_by_multiplication",
)
AUTOMATION = "Examples.two_dvd_double_automated"


def run(workspace, env, *command, expected=0):
    result = subprocess.run(command, cwd=workspace, env=env, check=False)
    if result.returncode != expected:
        raise RuntimeError(
            f"Expected exit {expected}, got {result.returncode} from {command!r}"
        )


def build(workspace, env, lake, generator):
    workspace.mkdir()
    for filename in ("CMakeLists.txt", "Adapter.lean", "lakefile.toml", "lean-toolchain"):
        shutil.copyfile(ROOT / filename, workspace / filename)
    for directory in ("src", "proofs"):
        shutil.copytree(ROOT / directory, workspace / directory)
    run(workspace, env, lake, "build", "DevelopmentProofs", "ReservedProofs", "AutomatedProofs")
    run(workspace, env, "cmake", "-S", ".", "-B", "cpp", "-G", generator)
    run(workspace, env, "cmake", "--build", "cpp", "--config", "Release")
    name = "lean-to-latex.exe" if os.name == "nt" else "lean-to-latex"
    return next((workspace / "cpp").rglob(name))


def check(condition, description):
    if not condition:
        raise RuntimeError(description)


def experiment(workspace, env, lake, generator, policy_checks):
    executable = build(workspace, env, lake, generator)
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "structured.json",
        "proofs.Development,proofs.Reserved", *DEVELOPMENT, *RESERVED)
    run(workspace, env, executable, "structured.json", "structured.tex")
    run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", "automation.json",
        "proofs.Automation", AUTOMATION)
    run(workspace, env, executable, "automation.json", "automation.tex", expected=1)

    structured = (workspace / "structured.tex").read_bytes().decode("ascii")
    automation = (workspace / "automation.tex").read_bytes().decode("ascii")
    check(structured.count(r"\begin{theorem}") == 5 and PENDING not in structured,
          "Expected all three development and both reserved proofs to be complete")
    check(automation.count(r"\begin{theorem}") == 1 and automation.count(PENDING) == 1,
          "Expected a single standalone automated proof with a pending step")
    for text in (structured, automation):
        check(all(name not in text for name in (*DEVELOPMENT, *RESERVED, AUTOMATION))
              and "Decidable.byContradiction" not in text, "Lean syntax leaked into LaTeX")
    check(structured.index(r"\subsection*{Prerequisites}") <
          structured.index(r"\begin{theorem}"), "Prerequisites must precede the proofs")

    induction = structured.split(r"\label{theorem:3}", 1)[1].split(r"\end{proof}", 1)[0]
    check(induction.index("Base case.") < induction.index("Inductive step.") <
          induction.index("As the induction hypothesis") < induction.index(r"\end{description}"),
          "The induction hypothesis must stay in the successor case")
    if policy_checks:
        for threshold in (0, 1000):
            run(workspace, env, executable, "structured.json", f"threshold-{threshold}.tex",
                "--threshold", str(threshold))
        low = (workspace / "threshold-0.tex").read_text(encoding="ascii")
        high = (workspace / "threshold-1000.tex").read_text(encoding="ascii")
        earlier_references = [line for line in structured.splitlines() if r"\ref{theorem:" in line]
        check(bool(earlier_references) and all(line in low and line in high
              for line in earlier_references), "The threshold changed an earlier-theorem citation")
        check(low.count(r"\begin{equation}") > structured.count(r"\begin{equation}") > 0
              and r"\begin{equation}" not in high,
              "The threshold failed to change display for uncited expressions")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable or path")
    parser.add_argument("--generator", default="Ninja", help="CMake generator")
    args = parser.parse_args()
    lake = shutil.which(args.lake)
    if lake is None:
        parser.error("Lake is unavailable. Install Lean 4.19.0 or pass --lake.")
    lake = Path(os.path.abspath(lake))
    env = os.environ.copy()
    env["PATH"] = f"{lake.parent}{os.pathsep}{env['PATH']}"

    build_dir = ROOT / "build"
    build_dir.mkdir(exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="experiment-", dir=build_dir))
    first, second = output / "first", output / "second"
    experiment(first, env, lake, args.generator, policy_checks=True)
    experiment(second, env, lake, args.generator, policy_checks=False)
    for filename in ("structured.tex", "automation.tex"):
        content = (first / filename).read_bytes()
        check(content == (second / filename).read_bytes(), f"{filename} differed between clean runs")
        check(content == (ROOT / "examples" / filename).read_bytes(),
              f"{filename} differed from the shipped example")
        print(f"{filename} SHA-256 {hashlib.sha256(content).hexdigest()}")
    print(f"Verified both clean runs in {output}")


if __name__ == "__main__":
    main()

"""Check induction recovered from Lean's predecessor table."""

import copy
import json
import subprocess

from verify import PENDING, ROOT, check


def application(expression, name):
    if isinstance(expression, list):
        if expression[:1] == ["a"] and expression[1][:2] == ["c", name]:
            return expression
        for child in expression:
            result = application(child, name)
            if result is not None:
                return result
    return None


def verify_nat_below(project, workspace, env, lake, compiler):
    source = ROOT / "tests/fixtures/NaturalRecursion.lean"
    with (workspace / "natural-recursion.json").open("wb") as checked:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-", source],
                       cwd=project, env=env, check=True, stdout=checked)
    document = json.loads((workspace / "natural-recursion.json").read_bytes())
    matcher = document[2][0]
    check(matcher[5] == ["natCases", "Nat.zero", "Nat.succ"], "Missing ordered natural-number cases")

    def render(data, budget, completed):
        path = workspace / "recursion-control.json"
        output = workspace / "recursion-control.tex"
        path.write_text(json.dumps(data), encoding="utf-8")
        result = subprocess.run([compiler, path, output, "--paper", "Addition", "--proof-budget", str(budget)],
                                cwd=workspace, env=env, capture_output=True, encoding="utf-8")
        check(result.returncode == (0 if completed == 2 else 1), result.stderr)
        check(f"{completed}/2 proofs complete" in result.stderr, result.stderr)
        article = output.read_text(encoding="utf-8")
        check(article.count(PENDING) == 2 - completed, "Incorrect number of visible induction gaps")
        return article

    def case(document):
        return application(document[0][1][2], matcher[0])

    tail = copy.deepcopy(document)
    recursive_call = application(case(tail)[5], "congrArg")
    check(recursive_call[-1][:3] == ["proj", "PProd", "0"], "Missing predecessor projection")
    recursive_call[-1][2] = "1"

    swapped_arguments = copy.deepcopy(document)
    base = application(case(swapped_arguments)[4], "Nat.add_comm")
    base[2], base[3] = base[3], base[2]

    missing_branch = copy.deepcopy(document)
    case(missing_branch)[5][4][4] = ["u", "missing successor proof"]

    missing_conversion = copy.deepcopy(document)
    case(missing_conversion)[4][4].pop()

    reversed_constructors = copy.deepcopy(document)
    reversed_constructors[2][0][5][1:] = ["Nat.succ", "Nat.zero"]

    for budget in (0, 1000000):
        article = render(document, budget, 2)
        for phrase in ("Base case.", "Successor step.", "Assume as induction hypothesis"):
            check(article.count(phrase) == 2, f"Both proofs must show {phrase}")
        for damaged in (tail, swapped_arguments, missing_branch, missing_conversion):
            render(damaged, budget, 1)
        render(reversed_constructors, budget, 0)

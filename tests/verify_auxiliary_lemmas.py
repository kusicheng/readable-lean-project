"""Verify the scope, dependencies and detail budget of proof-local auxiliary lemmas."""

import copy
import json
import subprocess

from verify import PENDING, ROOT, check, run


def helper_calls(node, name):
    if not isinstance(node, list) or not node:
        return
    if node[0] == "p":
        yield from helper_calls(node[2], name)
    elif node[0] == "a" and node[1][:2] == ["c", name]:
        yield node
    else:
        for child in node:
            yield from helper_calls(child, name)


def verify_auxiliary_lemmas(workspace, env, lake, compiler):
    data = workspace / "auxiliary.json"
    run(workspace, env, lake, "env", "lean", "--run", ROOT / "Adapter.lean",
        data, ROOT / "tests/fixtures/AuxiliaryLemmas.lean")
    document = json.loads(data.read_bytes())
    name = next(row[0] for row in document[6] if row[0].endswith(".liftEquality"))
    compact = workspace / "auxiliary-compact.tex"
    full = workspace / "auxiliary-expanded.tex"
    run(workspace, env, compiler, data, compact, "--proof-budget", "0")
    run(workspace, env, compiler, data, full, "--proof-budget", "1000000")
    article = compact.read_text(encoding="utf-8")
    anchor = r"\paperlineanchor{aux:1:1}\textbf{Auxiliary lemma~1.1.}"
    link = r"\paperlink{aux:1:1}{Auxiliary lemma~1.1}"
    check(article.count(anchor) == 1 and article.count(link) == 2 and
          article.index(anchor) < article.index("Proof of the main assertion.") < article.index(link),
          "A repeated helper must be proved once before its two linked uses")
    check(r"(using \(a = b\))" in article and r"(using \(c = d\))" in article and
          article.count("Applying the same function") == 7 and
          full.read_text(encoding="utf-8").count("Applying the same function") == 14,
          "Both specializations must retain the actual hypothesis and full detail must expand both")
    for failure in ("helper", "unrelated conclusion", "missing argument", "other hypothesis",
                    "other object", "other specialization"):
        damaged = copy.deepcopy(document)
        first, second = helper_calls(damaged[0][0][2], name)
        if failure == "helper":
            next(row for row in damaged[6] if row[0] == name)[2] = ["u", "absent proof"]
        elif failure == "unrelated conclusion":
            body = next(row for row in damaged[6] if row[0] == name)[2]
            while body[0] == "l":
                body = body[4]
            body[:] = ["p", ["c", "True", "prop", [], []], ["c", "True.intro", "proof", [], []]]
        elif failure == "missing argument":
            second[-1] = ["u", "absent proof"]
        elif failure == "other hypothesis":
            second[-1] = first[-1]
        elif failure == "other object":
            second[2] = first[2]
        else:
            function = second[4]
            check(function[0] == "l", "The regression needs a lambda-valued specialization")
            function[4] = ["a", ["c", "Nat.succ", "value", ["0"], []], function[4]]
        data.write_text(json.dumps(damaged), encoding="utf-8")
        attempt = subprocess.run([compiler, data, compact, "--proof-budget", "0"], env=env,
                                 cwd=workspace, capture_output=True)
        text = compact.read_text(encoding="utf-8")
        check(attempt.returncode == 1 and PENDING in text and link not in text,
              f"The damaged {failure} must leave an explicit gap")

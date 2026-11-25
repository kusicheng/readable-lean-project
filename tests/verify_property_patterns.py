"""Check proof-structure matches against the constructor's ordered fields."""

import copy
import json
import shutil
import subprocess

from verify import PENDING, ROOT, check, run


def verify_property_patterns(workspace, env, lake, compiler):
    def export(stem):
        source = f"{stem}.lean"
        shutil.copyfile(ROOT / "tests" / "fixtures" / source, workspace / source)
        run(workspace, env, lake, "env", "lean", "--run", "Adapter.lean", f"{stem}.json", source)
        return json.loads((workspace / f"{stem}.json").read_bytes())

    output = workspace / "property-patterns.tex"

    def render(document, budget, expected):
        data = workspace / "property-patterns-test.json"
        data.write_text(json.dumps(document), encoding="utf-8")
        result = subprocess.run([compiler, data, output, "--paper", "Bounds", "--proof-budget", str(budget)],
                                cwd=workspace, env=env, capture_output=True, encoding="utf-8")
        check(result.returncode == expected, result.stderr)
        return output.read_text(encoding="utf-8"), result.stderr

    document = export("PropertyPatterns")
    matcher = document[2][0]
    check(matcher[5:] == ["PropertyPatterns.Bounds.mk"], "Missing checked constructor for bounds")
    certificate = copy.deepcopy(document)
    branch = certificate[0][0][2]
    while branch[0] == "l":
        branch = branch[4]
    call = branch[2]
    check(call[1][1] == matcher[0], "Bounds example no longer uses a matcher")
    call[-2] = ["u", "missing instance of the bounds property"]
    legacy = copy.deepcopy(document)
    legacy[2][0].pop()
    different_family = copy.deepcopy(document)
    different_family[2][0][5] = "Twin.mk"

    order = export("PropertyMatcherOrder")
    records = {r[0].split(".")[-1]: r for r in order[2]}
    check(records["positional"][5:] == ["Twin.mk"] and len(records["reversed"]) == 5,
          "Arity or proof irrelevance hid a reversal of two fields of the same type")
    different_family[9].extend(order[9])
    for budget in (0, 1000000):
        text, audit = render(document, budget, 0)
        check(r"gives \(a \le x\) and \(x \le b\)." in text and r"\(a \le b\)" in text
              and PENDING not in text and "1/1 proofs complete" in audit, "Missing bounds or conclusion")
        for invalid in (certificate, legacy, different_family):
            text, audit = render(invalid, budget, 1)
            check(PENDING in text and "0/1 proofs complete" in audit, "Unsupported matcher closed a proof")
        text, audit = render(order, budget, 1)
        check(PENDING in text and "1/2 proofs complete" in audit, "Reversed fields passed positional matching")

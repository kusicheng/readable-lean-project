"""Check which fields and equality evidence survive proof compression."""

import copy
import json
import subprocess

from verify import PENDING, ROOT, check


def application(term, name):
    if not isinstance(term, list) or not term:
        return None
    if term[0] == "a" and term[1][:2] == ["c", name]:
        return term
    for child in term:
        found = application(child, name)
        if found is not None:
            return found
    return None


def verify_record_ext(project, workspace, env, lake, compiler):
    data = workspace / "record-equality.json"
    output = workspace / "record-equality.tex"
    with data.open("wb") as export:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-",
                        ROOT / "tests/fixtures/RecordEquality.lean"], cwd=project, env=env,
                       stdout=export, check=True)
    original = json.loads(data.read_bytes())

    def render(document, expected, budget):
        data.write_text(json.dumps(document), encoding="utf-8")
        result = subprocess.run([compiler, data, output, "--paper", "Equality of records",
                                 "--proof-budget", str(budget)], cwd=workspace, env=env,
                                capture_output=True, encoding="utf-8")
        check(result.returncode == expected, result.stderr)
        return output.read_text(encoding="utf-8"), result.stderr

    for budget in (0, 1000000):
        article, audit = render(original, 0, budget)
        check("15/15 proofs complete" in audit and PENDING not in article, audit)
        check("left and right subtrees" in article and article.count("Apply the induction hypothesis to") >= 2,
              "The tree and well-founded proofs should identify their two recursive cases")
        comparisons = [line for line in article.splitlines() if line.startswith("Compare the two records")]
        check(len(comparisons) == 4 and
              any(all(field in line for field in ("left", "right", "proof irrelevance")) for line in comparisons) and
              any("row" in line and "column" in line and "proof irrelevance" not in line for line in comparisons) and
              any("condition" in line and "proof irrelevance" in line for line in comparisons),
              "Record equality must identify every data field, including proposition-valued fields")

    for control in ("missing right", "swapped tail", "missing reflexivity", "wrong constructor", "wrong projection"):
        damaged = copy.deepcopy(original)
        family = "Score" if control in ("missing reflexivity", "wrong constructor") else "OrderedPair"
        name = f"RecordEquality.{family}.ext"
        proof = next(row[2] for row in damaged[0] if row[0] == name)
        if control == "wrong constructor":
            matcher = next(row for row in damaged[2] if row[0] == name + ".match_1")
            matcher[5] = "RecordEquality.OrderedPair.mk"
        elif control in ("missing right", "swapped tail"):
            transfer = application(proof, "Eq.ndrec")
            check(transfer is not None, "The ordered pair must transport its coordinates")
            transfer[-1] = ["u", "missing right coordinate"] if control == "missing right" else transfer[-2]
        else:
            elimination = application(proof, "Eq.casesOn")
            check(elimination is not None, "The projected equality must be eliminated")
            if control == "missing reflexivity":
                elimination[8] = ["u", "missing reflexivity"]
            else:
                elimination[5] = elimination[3]
        article, audit = render(damaged, 1, 0)
        check(PENDING in article and "12/15 proofs complete" in audit,
              f"The unsupported equality and its two uses must stay visible for {control}")

    for control in ("wrong subtree", "missing decrease", "wrong decrease", "wrong motive", "missing order"):
        damaged = copy.deepcopy(original)
        if control == "wrong subtree":
            proof = next(row[2] for row in damaged[0] if row[0].endswith(".double_reflection"))
            def swap_right_use(n):
                if not isinstance(n, list) or not n:
                    return False
                if n[:3] == ["proj", "PProd", "0"] and n[3][:3] == ["proj", "PProd", "1"]:
                    n[3][2] = "0"
                    return True
                return any(swap_right_use(k) for k in n)
            check(swap_right_use(proof), "Tree case should use its right subtree")
        else:
            proof = next(row[2] for row in damaged[0] if row[0].endswith(".via_smaller"))
            fix = application(proof, "WellFounded.fix")
            step = fix[6][4][4][2]
            if control == "wrong motive":
                fix[3] = fix[4]
            elif control == "missing order":
                fix[5] = ["u", "missing order"]
            else:
                left = step[-2][2]
                right = step[-1][2]
                check(left[0] == right[0] == "a" and left[1][:2] == right[1][:2],
                      "The two smaller cases must invoke the same recursive hypothesis")
                right[-1] = left[-1] if control == "wrong decrease" else ["u", "missing decrease"]
        article, audit = render(damaged, 1, 0)
        check(PENDING in article and "14/15 proofs complete" in audit, f"Undetected {control}")

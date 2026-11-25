"""Exercise equality of records whose fields determine the common index."""

import copy
import json
import subprocess

from verify import PENDING, ROOT, check
from verify_record_ext import application


def final_constructor(expression, constructor):
    if not isinstance(expression, list) or not expression:
        return None
    if expression[0] == "p":
        body = expression[2]
        if (body[:1] == ["a"] and body[1][:2] == ["c", "Eq.refl"] and
                body[3][:1] == ["a"] and body[3][1][:2] == ["c", constructor]):
            return expression
        return final_constructor(body, constructor)
    for child in expression:
        found = final_constructor(child, constructor)
        if found is not None:
            return found
    return None


def verify_indexed_record_controls(data, workspace, env, compiler, family, remaining, total):
    document = json.loads(data.read_bytes())
    for control in ("outer index", "wrong index proof", "missing transport", "inner index",
                    "missing field proof", "wrong field proof", "annotation proof"):
        damaged = copy.deepcopy(document)
        proof = next(row[2] for row in damaged[0] if row[0] == family + ".ext")
        first = application(proof, "Eq.casesOn")
        transfer = application(first[7], "Eq.ndrec")
        last = final_constructor(proof, family + ".mk")
        check(last is not None, "The last reflexivity step should contain the constructed record")
        record = last[2][3]
        if control == "outer index":
            first[5] = ["n", "99"]
        elif control == "wrong index proof":
            first[6] = transfer[-2]
        elif control == "missing transport":
            application(transfer[5], "Eq.ndrec")[7] = ["u", "missing proof transport"]
        elif control == "inner index":
            record[2] = ["n", "99"]
        elif control == "missing field proof":
            record[4] = ["u", "missing field proof"]
        elif control == "wrong field proof":
            record[5] = record[4]
        else:
            last[1][3][5] = ["u", "missing field proof in annotation"]
        source = workspace / "damaged-indexed-record.json"
        source.write_text(json.dumps(damaged), encoding="utf-8")
        output = source.with_suffix(".tex")
        result = subprocess.run([compiler, source, output], cwd=workspace, env=env,
                                capture_output=True, encoding="utf-8")
        article = output.read_text(encoding="utf-8")
        check(result.returncode == 1 and f"{remaining}/{total} proofs complete" in result.stderr
              and article.count(PENDING) == total - remaining and "rewrite their common index" not in article,
              f"The damaged {family} proof must remain incomplete for {control}")


def verify_indexed_record_fixture(project, workspace, env, lake, compiler):
    data = workspace / "digit-rows.json"
    with data.open("wb") as export:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-",
                        ROOT / "tests/fixtures/IndexedRecordTrial.lean"], cwd=project,
                       env=env, check=True, stdout=export)
    for budget in (0, 1000000):
        output = workspace / "digit-rows.tex"
        result = subprocess.run([compiler, data, output, "--proof-budget", str(budget)],
                                cwd=workspace, env=env, capture_output=True, encoding="utf-8")
        article = output.read_text(encoding="utf-8")
        explanation = next((s for s in article.splitlines() if "rewrite their common index" in s), "")
        check(result.returncode == 0 and "3/3 proofs complete" in result.stderr and PENDING not in article
              and all(word in explanation for word in ("length", "digits", "width", "proof irrelevance")),
              "Record equality must identify the length of the list as the common width")
    verify_indexed_record_controls(data, workspace, env, compiler, "IndexedRecordTrial.DigitRow", 0, 3)

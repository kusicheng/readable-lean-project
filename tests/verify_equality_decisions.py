"""Check the evidence for describing a record's equality decision in a paper."""

import copy
import json
import subprocess

from verify import ROOT, check


def verify_equality_decisions(project, workspace, env, lake, compiler):
    source = ROOT / "tests/fixtures/EqualityDecisions.lean"
    data = workspace / "equality-decisions.json"
    with data.open("wb") as checked:
        subprocess.run([lake, "env", "lean", "--run", ROOT / "Adapter.lean", "-", source],
                       cwd=project, env=env, stdout=checked, check=True)
    document = json.loads(data.read_bytes())
    definitions = {row[0]: row for row in document[4]}
    packet = "EqualityDecisions.instDecidableEqPacket"
    bundle = "EqualityDecisions.instDecidableEqBundle"
    for name, field in ((packet, "payload"), (bundle, "contents")):
        row = definitions[name]
        check(len(row) == 4 and row[3][0] == "record-equality-test" and row[3][4] == field,
              f"Missing checked comparison of {field} for {name}")
    for name in ("EqualityDecisions.alternate", "EqualityDecisions.instDecidableEqCoordinates"):
        check(all(extra[0] != "record-equality-test" for extra in definitions[name][3:]),
              f"The single-field comparison must be checked against the implementation of {name}")

    gap = "Some defining equations could not be rendered."
    def render(input_file):
        output = input_file.with_suffix(".tex")
        result = subprocess.run([compiler, input_file, output, "--paper", "Testing record equality"],
                                cwd=workspace, env=env, capture_output=True, encoding="utf-8")
        check(result.returncode in (0, 1) and "4/4 proofs complete" in result.stderr, result.stderr)
        article = output.read_text(encoding="utf-8")
        check(result.returncode == int(gap in article), "Incorrect status for incomplete record definitions")
        return article

    def summary(article, title, field):
        heading = rf"\paragraph{{Equality test ({title}).}}"
        paragraph = article.partition(heading)[2].split("\n\n", 1)[0]
        return (rf"Compare the values of the \emph{{{field}}} field. "
                "Two records are equal exactly when these values agree.") in paragraph

    article = render(data)
    check(summary(article, "Packet", "payload") and summary(article, "Bundle", "contents"),
          "The paper must explain both the closed and parameterized record tests")
    check(article.count("Two records are equal exactly when these values agree.") == 2,
          "An unrelated decision received the single-field explanation")

    controls = [(4, "nonempty"), (1, definitions[bundle][3][1]), (6, definitions[bundle][3][6])]
    for index, substitution in controls:
        damaged = copy.deepcopy(document)
        next(row for row in damaged[4] if row[0] == packet)[3][index] = substitution
        path = workspace / f"equality-decision-control-{index}.json"
        path.write_text(json.dumps(damaged), encoding="utf-8")
        changed = render(path)
        check(not summary(changed, "Packet", "payload") and summary(changed, "Bundle", "contents")
              and changed.count(gap) == article.count(gap) + 1,
              f"Invalid field or equation in certificate slot {index} hid the missing definition")

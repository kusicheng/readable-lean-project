"""Check PDF citation targets and the spacing of the reported Hamiltonian proofs."""

import argparse
from collections import Counter
from contextlib import closing
import ctypes as ct
from pathlib import Path
import re

import pypdfium2 as pdf
import pypdfium2.raw as raw


ROOT = Path(__file__).resolve().parents[1]
CITATION = re.compile(r"\b(Auxiliary\s+lemma|Prerequisite|Lemma|Theorem|Corollary|Definition|defining\s+equation)\s+([PD]?\d+(?:\.\d+)?)\b", re.I)
TARGET = re.compile(r"(?m)^(?:(Auxiliary lemma|Theorem|Lemma|Corollary) (\d+(?:\.\d+)?)(?:\s*\(|\.)|(P\d+)\.)")
WORD_PAIR = re.compile(r"\b([A-Za-z]{2,}[,.;]?)(?= +([A-Za-z]{2,})\b)")


def indexed_text(text_page):
    # Keep one character per PDFium index so that matches map to printed glyphs.
    return "".join(chr(raw.FPDFText_GetUnicode(text_page, n)) for n in range(text_page.count_chars()))


def validate_hamiltonian_spacing(path):
    """Measure visible gaps in the proof body, allowing room for ordinary justification."""
    widest = dict.fromkeys(("Theorem 1", "Lemma 4"))
    result, in_proof = None, False
    with closing(pdf.PdfDocument(path)) as document:
        for index in range(len(document)):
            with closing(document[index]) as page, closing(page.get_textpage()) as text_page:
                for line in re.finditer(r"[^\r\n]+", indexed_text(text_page)):
                    heading = TARGET.match(line[0])
                    if heading and heading[1] and raw.FPDFText_GetFontWeight(text_page, line.start()) >= 500:
                        # A citation wrapped to column one can also begin with "Lemma 4".
                        result, in_proof = f"{heading[1]} {heading[2]}", False
                    if result not in widest:
                        continue
                    if line[0].startswith("Proof."):
                        in_proof = True
                    if not in_proof:
                        continue
                    for pair in WORD_PAIR.finditer(line[0]):
                        # A prose word on either side rules out gaps between aligned formulas.
                        words = {word.casefold().rstrip(",.;") for word in pair.groups()}
                        if words.isdisjoint({"by", "the", "we"}):
                            continue
                        left = line.start() + pair.end(1) - 1
                        right = line.start() + pair.start(2)
                        gap = text_page.get_charbox(right)[0] - text_page.get_charbox(left)[2]
                        em = raw.FPDFText_GetFontSize(text_page, left)
                        if em <= 0:
                            raise ValueError(f"Missing font size in the proof of {result}")
                        sample = (gap / em, gap, " ".join(pair.groups()), index + 1)
                        if widest[result] is None or sample[0] > widest[result][0]:
                            widest[result] = sample
    problems = []
    for label, sample in widest.items():
        if sample is None:
            problems.append(f"No measurable prose in the proof of {label}")
        elif sample[0] > 1.5:
            ratio, gap, words, page = sample
            problems.append(f"{label}, page {page}: {words!r} has a {gap:.1f} pt gap "
                            f"({ratio:.2f} em, limit 1.5 em)")
    if problems:
        raise ValueError("\n".join(problems))
    return widest


def link_target(document, link):
    dest = raw.FPDFLink_GetDest(document, link)
    if not dest:
        action = raw.FPDFLink_GetAction(link)
        if action:
            dest = raw.FPDFAction_GetDest(document, action)
    if not dest:
        raise ValueError("Citation has no internal PDF destination")
    page = raw.FPDFDest_GetDestPageIndex(document, dest)
    has_x, has_y, has_zoom = ct.c_int(), ct.c_int(), ct.c_int()
    x, y, zoom = ct.c_float(), ct.c_float(), ct.c_float()
    located = raw.FPDFDest_GetLocationInPage(dest, ct.byref(has_x), ct.byref(has_y), ct.byref(has_zoom),
                                            ct.byref(x), ct.byref(y), ct.byref(zoom))
    if page < 0 or not located or not has_y.value:
        raise ValueError("Citation needs a destination at a specific position in the paper")
    return page, y.value


def validate(path, require_mixed=True):
    targets = {}
    visits = []
    counts = Counter()
    document = pdf.PdfDocument(path)
    try:
        for page_index, page in enumerate(document):
            text_page = page.get_textpage()
            try:
                text = indexed_text(text_page)
                headings = set()
                for target in TARGET.finditer(text):
                    key = (target[1], target[2]) if target[1] else ("Prerequisite", target[3])
                    # A reference such as "Lemma 6 (using ...)" can wrap to
                    # column one. The actual result precedes every reference.
                    if key in targets:
                        continue
                    targets[key] = (page_index, text_page.get_charbox(target.start())[3])
                    headings.add(target.start())
                for number in re.finditer(r"\((D\d+)\)", text):
                    targets[("Definition", number[1])] = (page_index, text_page.get_charbox(number.start())[3])

                for citation in CITATION.finditer(text):
                    if citation.start() in headings:
                        continue
                    name, number = citation.groups()
                    key = ("Definition" if name.lower().startswith("defin") else " ".join(name.split()).capitalize(), number)
                    counts[key[0]] += 1
                    where = f"{citation[0]!r} on page {page_index + 1}"
                    destinations = set()
                    annotations = set()
                    for i in range(citation.start(), citation.end()):
                        if text[i].isspace():
                            continue
                        left, bottom, right, top = text_page.get_charbox(i)
                        link = raw.FPDFLink_GetLinkAtPoint(page, (left + right) / 2, (bottom + top) / 2)
                        if not link:
                            raise ValueError(f"{where} is not clickable at {text[i]!r} (character {i - citation.start() + 1})")
                        destinations.add(link_target(document, link))
                        annotations.add(ct.cast(link, ct.c_void_p).value)
                    if len(destinations) != 1:
                        raise ValueError(f"The words and number of {where} point to different destinations")
                    # A rectangle covering the entire line would pass the character checks
                    # while also making ordinary words redirect the reader.
                    for pattern, offset, fragment in ((r"([A-Za-z]{2,})[ ,;:]*$", 0, text[:citation.start()]),
                                                      (r"^[ ,;:]*([A-Za-z]{2,})", citation.end(), text[citation.end():])):
                        neighbor = re.search(pattern, fragment)
                        if neighbor:
                            i = offset + (neighbor.start(1) + neighbor.end(1)) // 2
                            left, bottom, right, top = text_page.get_charbox(i)
                            link = raw.FPDFLink_GetLinkAtPoint(page, (left + right) / 2, (bottom + top) / 2)
                            if link and ct.cast(link, ct.c_void_p).value in annotations:
                                raise ValueError(f"The clickable area of {where} includes the neighboring word {neighbor[1]!r}")
                    visits.append((key, where, destinations.pop()))
            finally:
                text_page.close()
                page.close()
    finally:
        document.close()
    if require_mixed and (not counts["Prerequisite"] or not any(counts[k] for k in ("Lemma", "Theorem", "Corollary"))):
        raise ValueError("The paper must exercise both prerequisite and numbered-result citations")
    for key, where, (actual_page, anchor_y) in visits:
        if key not in targets:
            raise ValueError(f"Could not locate the printed target of {where}")
        expected_page, heading_y = targets[key]
        # PDF coordinates increase upward. Allow one line of padding above
        # the label and rounding error below it. An anchor on the baseline
        # clips the first line when a viewer places it at the viewport top.
        if actual_page != expected_page or not -1.5 <= anchor_y - heading_y <= 16:
            raise ValueError(f"{where} leads to page {actual_page + 1} at {anchor_y:.1f} pt. "
                             f"Its label is on page {expected_page + 1} at {heading_y:.1f} pt.")
        for other, (other_page, other_y) in targets.items():
            if other[0] == key[0] and other_page == actual_page and abs(anchor_y - other_y) + 1 < abs(anchor_y - heading_y):
                raise ValueError(f"{where} lands closer to {' '.join(other)} than to its own label")
    return counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("papers", nargs="*", type=Path, help="PDFs with prerequisite and result citations",
                        default=[ROOT / "papers" / f"mathlib-{name}.pdf" for name in
                                 ("hamiltonian", "double-counting", "derangements", "powerset")])
    for paper in parser.parse_args().papers:
        if "hamiltonian" in paper.stem.casefold():
            for label, (ratio, gap, words, page) in validate_hamiltonian_spacing(paper).items():
                print(f"{paper.name}: {label}, page {page}, widest measured prose gap "
                      f"{gap:.1f} pt ({ratio:.2f} em) between {words!r}")
        checked = validate(paper)
        print(f"{paper.name}: {sum(checked.values())} complete citation links verified ({dict(sorted(checked.items()))})")

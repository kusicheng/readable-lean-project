"""Check clickable citations in typeset papers. Run with Python and pypdfium2."""

import argparse
from collections import Counter
import ctypes as ct
from pathlib import Path
import re

import pypdfium2 as pdf
import pypdfium2.raw as raw


ROOT = Path(__file__).resolve().parents[1]
CITATION = re.compile(r"\b(Prerequisite|Lemma|Theorem|Corollary|Definition|defining\s+equation)\s+([PD]?\d+)\b", re.I)
TARGET = re.compile(r"(?m)^(?:(Theorem|Lemma|Corollary) (\d+)(?:\s*\(|\.)|(P\d+)\.)")


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


def validate(path):
    targets = {}
    visits = []
    counts = Counter()
    document = pdf.PdfDocument(path)
    try:
        for page_index, page in enumerate(document):
            text_page = page.get_textpage()
            try:
                # Use one character per PDFium index so that matching text can also be hit-tested.
                text = "".join(chr(raw.FPDFText_GetUnicode(text_page, n)) for n in range(text_page.count_chars()))
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
                    key = ("Definition" if name.lower().startswith("defin") else name.capitalize(), number)
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
    if not counts["Prerequisite"] or not any(counts[k] for k in ("Lemma", "Theorem", "Corollary")):
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
                                 ("hamiltonian-linked", "double-counting", "derangements", "powerset")])
    for paper in parser.parse_args().papers:
        checked = validate(paper)
        print(f"{paper.name}: {sum(checked.values())} complete citation links verified ({dict(sorted(checked.items()))})")

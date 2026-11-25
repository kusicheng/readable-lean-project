"""Refresh the generated portions of CHANGELOG.md and CONTRIBUTORS.md from Git."""

import argparse
from collections import defaultdict
from html import escape
from pathlib import Path
import re
import subprocess


START = "<!-- BEGIN generated project history -->"
END = "<!-- END generated project history -->"
REFRESH_TRAILER = "Project-History-Refresh: generated"


def git(*args):
    result = subprocess.check_output(["git", *args], encoding="utf-8", errors="replace")
    return result.splitlines()


def display(value):
    # Subjects, tags and even author display names may contain an address or markup.
    value = re.sub(r"[^\s<>@]+@[^\s<>@]+", "[email withheld]", value)
    return re.sub(r"([\\`*_\[\]~])", r"\\\1", escape(value, quote=False))


def changelog():
    lines = ["### Tags", ""]
    tags = git("tag", "--merged", "HEAD", "--sort=-version:refname")
    for tag in tags:
        commit, = git("rev-parse", "--short", "--verify", f"refs/tags/{tag}^{{commit}}")
        lines.append(f"- {display(tag)} (`{commit}`)")
    if not tags:
        lines.append("This history has no Git tags yet.")

    lines.extend(["", "### Commits", ""])
    # Changes to the two indexes alone must not add another entry about the refresh.
    records = git("log", "--format=%h%x09%cs%x09%s", "HEAD", "--", ".",
                  ":(exclude)CHANGELOG.md", ":(exclude)CONTRIBUTORS.md")
    for record in records:
        commit, date, subject = record.split("\t", 2)
        lines.append(f"- {date} — {display(subject)} (`{commit}`)")
    if not records:
        lines.append("This history contains only the project history files.")
    return "\n".join(lines)


def contributors():
    # Git applies .mailmap to both authors and identity-valued Co-authored-by trailers.
    # shortlog -n puts the most frequently recorded name for each address first.
    records = git("shortlog", "-nse", "--group=author", "--group=trailer:co-authored-by",
                  "--invert-grep", f"--grep=^{REFRESH_TRAILER}$", "HEAD")
    names_by_address = defaultdict(list)
    for record in records:
        _, identity = record.split("\t", 1)
        match = re.fullmatch(r"(.*?)\s*<([^<>]+)>", identity)
        if not match:
            continue
        name, address = match.groups()
        if name:
            names_by_address[address.casefold()].append(display(name))
    lines = []
    for names in names_by_address.values():
        primary, *aliases = dict.fromkeys(names)
        line = f"- {primary}"
        if aliases:
            line += f" (also credited as {', '.join(aliases)})"
        lines.append(line)
    return "\n".join(sorted(lines, key=str.casefold)) or "No named Git contributors have been recorded."


def updated(path, content):
    original = path.read_bytes()
    text = original.decode("utf-8")
    if text.count(START) != 1 or text.count(END) != 1 or text.index(END) < text.index(START):
        raise ValueError(f"{path} needs one ordered pair of project history markers")
    prefix, tail = text.split(START)
    _, suffix = tail.split(END)
    newline = "\r\n" if "\r\n" in text else "\n"
    generated = ("\n\n" + content + "\n\n").replace("\n", newline)
    return original, (prefix + START + generated + END + suffix).encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report stale files without writing")
    args = parser.parse_args()
    if git("rev-parse", "--is-shallow-repository") == ["true"]:
        parser.exit(1, "A full Git history is needed. Fetch the remaining commits and tags first.\n")
    changes = {}
    for filename, content in [("CHANGELOG.md", changelog()), ("CONTRIBUTORS.md", contributors())]:
        path = Path(filename)
        old, new = updated(path, content)
        if old != new:
            changes[path] = new
    for path, content in changes.items():
        if args.check:
            print(f"Out of date: {path}")
        else:
            path.write_bytes(content)
            print(f"Updated {path}")
    return int(args.check and bool(changes))


if __name__ == "__main__":
    raise SystemExit(main())

"""List the numbered statements of a thesis edition with the numbers LaTeX prints.

Usage: python inventory.py <chapters dir> [kinds]

Numbering follows the preamble: one counter shared by all theorem-like environments,
reset at each section and printed as chapter.section.n.  Chapters are read in file-name
order.  Output: one tab-separated line per statement (number, kind, optional title,
label, first words).
"""
import re
import sys
from pathlib import Path

KINDS = ["definition", "proposition", "lemma", "corollary", "theorem", "claim",
         "observation", "problem", "example"]
TOKEN = re.compile(r"\\(chapter|section)\*?\{|\\begin\{(" + "|".join(KINDS) + r")\}(\[[^\]]*\])?")


def main() -> None:
    root = Path(sys.argv[1])
    wanted = set(sys.argv[2].split(",")) if len(sys.argv) > 2 else set(KINDS)
    ch = sec = n = 0
    for path in sorted(root.glob("ch*.tex")):
        text = path.read_text(encoding="utf-8")
        for m in TOKEN.finditer(text):
            if m.group(1) == "chapter":
                ch, sec, n = ch + 1, 0, 0
            elif m.group(1) == "section":
                sec, n = sec + 1, 0
            else:
                n += 1
                kind = m.group(2)
                if kind not in wanted:
                    continue
                body = text[m.end():m.end() + 400]
                label = re.search(r"\\label\{([^}]*)\}", body[:120])
                words = re.sub(r"\\label\{[^}]*\}|\s+", " ", body).strip()[:110]
                print(f"{ch}.{sec}.{n}\t{kind}\t{(m.group(3) or '').strip('[]')}\t"
                      f"{label.group(1) if label else ''}\t{words}")


if __name__ == "__main__":
    main()

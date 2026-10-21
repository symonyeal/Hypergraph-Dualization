"""Write the automorphism-tree figures as `forest` code, checked against FK-A.

Usage (from the repository root): python thesis/tools/autotree.py <autotrees.json> <output dir>

A tree with an ``instance`` takes its shape from FK-A (variant ``modified``, split rule
``degree_sum``, the configuration that produced the 2024 figures) on that instance.
``root_order: RL`` renumbers it with the root's R subtree first, as six of the printed
figures do. Every printed split vertex is then compared with the computed one, and a
mismatch stops the build: a figure cannot drift from the algorithm it depicts.
A tree without an instance (Asym-1, Asym-2) is drawn from its transcribed children.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from fka.algorithm import fk_a  # noqa: E402
from fka.instances import load  # noqa: E402


def printed_shape(instance: str, root_order: str) -> tuple[dict[int, list[int]], dict[int, str]]:
    """Children lists and split labels of the FK-A tree under the printed numbering."""
    inst = load(instance)
    tree = fk_a(inst.cnf, inst.dnf, variant="modified", split_rule="degree_sum")
    kids = {n.node_id: list(n.children) for n in tree}
    split = {n.node_id: n.split_var_label() for n in tree}
    root = tree.root_id
    if root_order == "RL":
        kids[root] = list(reversed(kids[root]))
    renumber: dict[int, int] = {}
    stack = [root]
    while stack:
        u = stack.pop()
        renumber[u] = len(renumber) + 1
        stack.extend(reversed(kids[u]))
    children = {renumber[u]: [renumber[c] for c in cs] for u, cs in kids.items() if cs}
    labels = {renumber[u]: s for u, s in split.items()}
    return children, labels


def split_tex(s: str) -> str:
    if not s:
        return ""
    if s.startswith("$"):
        return s
    return f"$v_{{{s[1:]}}}$"


def node_tex(num: int, row: list) -> str:
    split, aut, hyp, graph = row
    aut_tex = "" if aut is None or aut == "" else f"${aut}$"
    if aut is None:  # 7-ver node 21 prints its group in the split field and omits the rest
        return f"\\textbf{{Node: {num}}}\\\\Split vert.: {split_tex(split)}\\\\Hyp.:\\\\Graph:"
    return f"\\anode{{{num}}}{{{split_tex(split)}}}{{{aut_tex}}}{{{hyp}}}{{{graph}}}"


def forest(children: dict[int, list[int]], rows: dict[str, list], num: int, depth: int) -> str:
    pad = "  " * depth
    body = f"{pad}[{{{node_tex(num, rows[str(num)])}}}"
    kids = children.get(num, [])
    if not kids:
        return body + "]"
    inner = "\n".join(forest(children, rows, k, depth + 1) for k in kids)
    return f"{body}\n{inner}\n{pad}]"


def main() -> None:
    spec, out = Path(sys.argv[1]), Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    trees = json.loads(spec.read_text(encoding="utf-8"))
    for name, t in trees.items():
        if name.startswith("_"):
            continue
        rows = t["nodes"]
        if "instance" in t:
            children, computed = printed_shape(t["instance"], t["root_order"])
            if len(computed) != len(rows):
                raise SystemExit(f"{name}: figure has {len(rows)} nodes, FK-A gives {len(computed)}")
            for num, label in computed.items():
                printed = rows[str(num)][0]
                if printed.startswith("$"):
                    continue
                if printed != label:
                    raise SystemExit(f"{name} node {num}: printed split {printed!r}, FK-A {label!r}")
        else:
            children = {int(k): v for k, v in t["children"].items()}
        style = "autotree, for tree={font=\\small}" if t.get("large") else "autotree"
        code = f"\\begin{{forest}}\n{style}\n{forest(children, rows, 1, 0)}\n\\end{{forest}}\n"
        (out / f"at-{name}.tex").write_text(code, encoding="utf-8")
        print(f"at-{name}.tex: {len(rows)} nodes")


if __name__ == "__main__":
    main()

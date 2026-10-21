"""Write the revised edition's figure data from the 2024 data and the corrections.

Usage (from the repository root): python thesis/tools/revise_figures.py

hypergraphs.json: the Section 3.2 drawings whose edge sets were wrong are replaced by the
Lean-verified sets (`lean/HypergraphDualization/Section32.lean`). autotrees.json: the group and
graph labels corrected in thesis/CLAIMS.md. Then every `X-tr` drawing is checked to be the
transversal of `X`. thesis/tools/check_tree_labels.py checks the tree labels.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from fka.hypergraph import Hypergraph  # noqa: E402
from fka.transversal import transversal  # noqa: E402

OLD = ROOT / "thesis" / "2024" / "figures"
NEW = ROOT / "thesis" / "revised" / "figures"

SQUARE = {"v1": [0, 2], "v2": [2, 2], "v3": [2, 0], "v4": [0, 0]}
COLOURS = ["red", "blue", "green", "pink", "orange", "yellow"]


def drawing(edges, pos=SQUARE):
    return {"pos": pos, "edges": [[COLOURS[i], e] for i, e in enumerate(edges)]}


HYPERGRAPHS = {
    "d31-tr": {"pos": {"v1": [0, 2], "v3": [0, 0], "v2": [2, 0]},
               "edges": [["blue", ["v1", "v3", "v2"]]]},
    "p4": drawing([["v1", "v2"], ["v2", "v3"], ["v3", "v4"]]),
    "p4-tr": drawing([["v1", "v3"], ["v2", "v3"], ["v2", "v4"]]),
    "k4minus-tr": drawing([["v1", "v2", "v3"], ["v1", "v2", "v4"], ["v3", "v4"]]),
    "k2dd": drawing([["v1"], ["v2"], ["v3", "v4"]]),
    "k2dd-tr": drawing([["v1", "v2", "v3"], ["v1", "v2", "v4"]]),
    "c4": drawing([["v1", "v2"], ["v2", "v3"], ["v3", "v4"], ["v1", "v4"]]),
    "c4-tr": drawing([["v1", "v3"], ["v2", "v4"]]),
    "k4-tr": drawing([["v1", "v2", "v3"], ["v1", "v2", "v4"], ["v1", "v3", "v4"],
                      ["v2", "v3", "v4"]]),
}

# (figure, node, field index, old value, new value); field 1 is the group, 3 the graph label.
TREE_LABELS = [
    ("6d", "9", 1, "C_3", "S_3"),
    ("7ver", "3", 1, "C_3", "S_3"),
    ("7ver", "7", 1, "C_3", "S_3"),
    ("8ver", "4", 1, "D_4", "C_2"),
    ("f2g2", "10", 3, "$C_4$ graph, Chordal Bipartite", "$C_4+K_1$ graph, Chordal Bipartite"),
    ("f2g2", "19", 3, "$C_4$ graph", "$C_4+K_1$ graph"),
]


def edge_sets(d):
    return {frozenset(int(v.strip("v!")) for v in e) for _, e in d["edges"]}


def main() -> None:
    hg = json.loads((OLD / "hypergraphs.json").read_text(encoding="utf-8"))
    hg["_note"] = ("Revised edition: the Section 3.2 drawings use the Lean-verified edge sets; "
                   "see thesis/CLAIMS.md. thesis/tools/revise_figures.py writes this file.")
    for name, d in HYPERGRAPHS.items():
        hg[name] = d
    bad = 0
    for name in hg:
        if name.endswith("-tr"):
            base = edge_sets(hg[name[:-3]])
            n = max(max(e) for e in base)
            want = transversal(Hypergraph.from_sets(n, [sorted(e) for e in base],
                                                    one_indexed=True))
            got = {frozenset(e) for e in want.to_sets(one_indexed=True)}
            if got != edge_sets(hg[name]):
                bad += 1
                print(f"{name} is not the transversal of {name[:-3]}")
    (NEW / "hypergraphs.json").write_text(json.dumps(hg, indent=1, ensure_ascii=False),
                                          encoding="utf-8")

    at = json.loads((OLD / "autotrees.json").read_text(encoding="utf-8"))
    for fig, node, field, old, new in TREE_LABELS:
        row = at[fig]["nodes"][node]
        if row[field] != old:
            sys.exit(f"{fig} node {node}: expected {old!r}, found {row[field]!r}")
        row[field] = new
    at["_note"] = at["_note"] + " Revised edition: group labels of 6-D node 9, 7-Ver nodes 3 and 7, 8-Ver node 4 and two graph labels of f2/g2 corrected (thesis/CLAIMS.md)."
    (NEW / "autotrees.json").write_text(json.dumps(at, indent=1, ensure_ascii=False),
                                        encoding="utf-8")
    if bad:
        sys.exit(f"{bad} transversal drawings are wrong")
    print("figure data written; every transversal drawing checked")


if __name__ == "__main__":
    main()

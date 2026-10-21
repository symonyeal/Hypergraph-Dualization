"""Check every printed property label of the automorphism-tree figures.

Usage (from the repository root): python thesis/tools/check_tree_labels.py [2024|revised]

Properties are recomputed on the vertices actually present (isolated vertices dropped), for
both hypergraphs of the node.  A printed label is supported when it holds for C or for D;
the script lists every label that holds for neither, and every group label whose order
differs from the computed |Aut(C)| on the present vertices.
"""
import json
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[2]
edition = sys.argv[1] if len(sys.argv) > 1 else "revised"
sys.path.insert(0, str(root / "src"))
from fka.graphs import primal_graph  # noqa: E402
from fka.hypergraph import Hypergraph  # noqa: E402
from fka.properties import analyse  # noqa: E402

HYP = {"roh": "read_once", "read-once": "read_once", "read-once hypergraph": "read_once",
       "$\\alpha$-acyclic": "alpha_acyclic", "conformal": "conformal",
       "not conformal": "not_conformal", "non-conformal": "not_conformal"}
GRAPH = {"bipartite": "bipartite", "split": "split", "chordal": "chordal", "cograph": "cograph",
         "perfect": "perfect", "chordal bipartite": "chordal_bipartite",
         "$c_4$ graph": "c4", "$c_4$": "c4", "$c_4+k_1$ graph": "c4k1"}
ORDER = {"C_1": 1, "C_2": 2, "C_3": 3, "\\{\\}": None, "\\text{Trivial}": 1, "D_4": 8, "D_8": 8,
         "S_4": 24, "C_2\\times C_2": 4, "C_2\\times D_4": 16, "C_2\\times S_4": 48,
         "PSL(3,2)": 168, "S_3": 6, "S_4\\text{ (Non-terminal)}": 24,
         "(((C_2\\times C_2\\times C_2\\times C_2):C_2):C_2):C_2": 128}


def props(edges, n):
    H = Hypergraph.from_sets(n, edges, one_indexed=True)
    if not H.edges or H.edges == [0]:
        return None
    Hc = H.compact()[0]
    p = analyse(Hc)
    g = primal_graph(Hc)
    gc = p.graph_classes
    is_c4 = g.n == 4 and all(a.bit_count() == 2 for a in g.adj)
    is_c4k1 = g.n == 5 and sorted(a.bit_count() for a in g.adj) == [0, 2, 2, 2, 2]
    return {"read_once": p.read_once, "alpha_acyclic": p.alpha_acyclic, "conformal": p.conformal,
            "not_conformal": not p.conformal, "bipartite": gc.bipartite, "split": gc.split,
            "chordal": gc.chordal, "cograph": gc.cograph, "perfect": gc.perfect,
            "chordal_bipartite": gc.chordal_bipartite, "c4": is_c4, "c4k1": is_c4k1}


trees = json.loads((root / f"thesis/{edition}/figures/autotrees.json").read_text(encoding="utf-8"))
bad = 0
for name, t in trees.items():
    if name.startswith("_") or "instance" not in t:
        continue
    res = json.loads((root / f"results/{t['instance']}.fk-a.modified.json").read_text())
    nodes = {x["node_id"]: x for x in res["nodes"]}
    kids = {i: list(x["children"]) for i, x in nodes.items()}
    rid = res["root_id"]
    if t["root_order"] == "RL":
        kids[rid] = list(reversed(kids[rid]))
    order, stack = [], [rid]
    while stack:
        u = stack.pop()
        order.append(u)
        stack.extend(reversed(kids[u]))
    for num, nid in enumerate(order, 1):
        split, grp, hyp, graph = t["nodes"][str(num)]
        x = nodes[nid]
        n = x["n"]
        pc, pd = props(x["cnf"], n), props(x["dnf"], n)
        aut = (x["analysis"].get("aut_C") or {}).get("order")
        want = ORDER.get(grp, "?")
        if grp and want != "?" and want is not None and want != aut:
            bad += 1
            print(f"{name} node {num}: group {grp} (order {want}) but |Aut(C)| = {aut}")
        for kind, text, table in (("hyp", hyp, HYP), ("graph", graph, GRAPH)):
            for lab in [s.strip() for s in text.split(",") if s.strip()]:
                if lab.lower() == "conformal (transversal not)":
                    if not (pc and pd and pc["conformal"] and not pd["conformal"]):
                        bad += 1
                        print(f"{name} node {num}: {lab!r} does not hold")
                    continue
                key = table.get(lab.lower())
                if key is None:
                    print(f"{name} node {num}: unrecognised {kind} label {lab!r}")
                    continue
                ok = any(p and p[key] for p in (pc, pd))
                if not ok:
                    bad += 1
                    print(f"{name} node {num}: {kind} label {lab!r} holds for neither side "
                          f"(C={x['cnf']}, D={x['dnf']})")
print(f"{bad} unsupported labels")
sys.exit(1 if bad else 0)

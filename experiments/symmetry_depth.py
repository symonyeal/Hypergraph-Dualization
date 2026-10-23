"""Count ordered-pair isomorphism classes by FK-A depth.

Legend: C,D are the reduced hypergraphs; j is depth; k is the depth cap;
G is a three-colour incidence graph; R stores one graph per isomorphism class.
Vertex labels are discarded, side colours are preserved, and isolated ground
vertices are retained. Counts use exact graph isomorphism, without hashing.
Run: python experiments/symmetry_depth.py [--write]
"""
from itertools import combinations
from pathlib import Path
import sys

import networkx as nx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from fka.algorithm import fk_a  # noqa: E402
from fka.hypergraph import Hypergraph  # noqa: E402
from fka.instances import load  # noqa: E402


def complete(n, r):
    return Hypergraph.from_sets(n, combinations(range(n), r))


def graph(C, D):
    G = nx.Graph()
    G.add_nodes_from((("v", x), {"c": 0}) for x in range(C.n))
    for c, H in enumerate((C, D), 1):
        for e in H:
            G.add_node((c, e), c=c)
            G.add_edges_from(((c, e), ("v", x)) for x in range(C.n) if e >> x & 1)
    return G


def classes(P):
    R = []
    match = nx.algorithms.isomorphism.categorical_node_match("c", None)
    for C, D in P:
        G = graph(C, D)
        if not any(nx.is_isomorphic(G, H, node_match=match) for H in R):
            R.append(G)
    return len(R)


def profile(C, D, k, rule="degree_sum", variant="modified"):
    T = fk_a(C, D, split_rule=rule, variant=variant)
    assert T.dual
    P = [[(v.cnf, v.dnf) for v in T.nodes.values() if v.depth == j]
         for j in range(k + 1)]
    return [classes(p) for p in P], classes([q for p in P for q in p])


def main():
    cases = [("complete(10,3)", complete(10, 3), complete(10, 8), 2)]
    for name, k in (("fano", 2), ("w11", 4)):
        I = load(name)
        cases.append((name, I.cnf, I.dnf, k))
    out = ["# Ordered isomorphism classes by FK-A depth", "",
           "Regenerate with `python experiments/symmetry_depth.py --write`.", "",
           "Exact three-colour incidence-graph isomorphism; both side colours and all",
           "ambient vertices are retained. Each row comes from the actual FK-A tree.", "",
           "| pair | rule | variant | classes by depth | classes through cap |",
           "| --- | --- | --- | --- | ---: |"]
    for name, C, D, k in cases:
        for rule in ("degree_sum", "leftmost", "guarded"):
            for variant in ("modified", "faithful"):
                a, b = profile(C, D, k, rule, variant)
                row = f"| {name} | {rule} | {variant} | {a} | {b} |"
                print(row, flush=True)
                out.append(row)
    if "--write" in sys.argv:
        (ROOT / "results" / "symmetry-depth.md").write_text("\n".join(out) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

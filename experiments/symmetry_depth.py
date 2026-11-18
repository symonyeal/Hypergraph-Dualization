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

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from iso_classes import classes as count_classes  # noqa: E402
from fka.algorithm import fk_a  # noqa: E402
from fka.hypergraph import Hypergraph  # noqa: E402
from fka.instances import load  # noqa: E402


def complete(n, r):
    return Hypergraph.from_sets(n, combinations(range(n), r))


def classes(P):
    by_ground = {}
    for C, D in P:
        by_ground.setdefault(C.n, set()).add((C.edges, D.edges))
    return sum(count_classes(n, pairs) for n, pairs in by_ground.items())


def profile(C, D, k, rule="degree_sum", variant="modified"):
    T = fk_a(C, D, split_rule=rule, variant=variant)
    assert T.dual
    P = [[] for _ in range(k + 1)]
    for node in T.nodes.values():
        if node.depth <= k:
            P[node.depth].append((node.cnf, node.dnf))
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

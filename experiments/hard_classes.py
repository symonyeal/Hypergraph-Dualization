"""Chapter 4's hard classes: the frequency threshold, and symmetry through the
whole recursion.

    python experiments/hard_classes.py   ->  results/hard-classes.{json,md}

Two measurements over one instance set:

1. Placement.  ``c = eps * log2 N`` against FK96's window ``[1, 2]``
   (:mod:`fka.bound`), beside FK-A and FK-B tree sizes.  ``exp`` is
   ``log(FK-A nodes)/log N``, the empirical degree of the tree in the instance
   size -- what a superpolynomial lower bound is a claim about.

2. Symmetry at every node. Count read-once nodes and primitive nodes outside
   that class. A capped enumeration can certify primitivity if the generated
   subgroup is already primitive. Other capped cases are undetermined.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from fka.algorithm import eps_exact, fk_a
from fka.hypergraph import Hypergraph, verts
from fka.instances import gk, list_ids, load, matching, threshold, tk
from fka.memo import dag_size
from fka.properties import is_read_once
from fka.selfdual import is_primitive, is_transitive, pair_automorphisms
from fka.bound import shortest_edge_ratio, threshold_ratio
from fka.transversal import transversal
from fkb.algorithm import fk_b

RESULTS = Path(__file__).resolve().parents[1] / "results"
#: Automorphisms enumerated per node before unproved primitivity is undetermined.
CAP = 120
#: Above this many hyperedges the incidence graph is too big to enumerate in
#: reasonable time, so the node is recorded as undetermined rather than guessed.
MAX_EDGES = 100


def classify(cnf: Hypergraph, dnf: Hypergraph):
    """(primitive outside read-once or None if undetermined, read-once) on the support."""
    keep = verts(cnf.support() | dnf.support())
    if len(keep) < 2:
        return False, True
    C, _ = cnf.restricted_to(keep)
    D, _ = dnf.restricted_to(keep)
    if is_read_once(C):
        return False, True
    if len(C) + len(D) > MAX_EDGES:
        return None, False
    perms, capped = pair_automorphisms(C, D, cap=CAP)
    primitive = is_transitive(perms, len(keep)) and is_primitive(perms, len(keep))
    return (None if capped and not primitive else primitive), False


def walk(tree, cache):
    by_depth = {}
    for node in tree.nodes.values():
        key = (node.cnf.edges, node.dnf.edges)
        if key not in cache:
            cache[key] = classify(node.cnf, node.dnf)
        prim, ro = cache[key]
        rec = by_depth.setdefault(
            node.depth,
            {"nodes": 0, "primitive": 0, "read_once": 0, "undetermined": 0})
        rec["nodes"] += 1
        rec["primitive"] += int(prim is True)
        rec["read_once"] += int(ro)
        rec["undetermined"] += int(prim is None)
    return by_depth


def cases():
    for i in list_ids():
        inst = load(i)
        yield i, inst.cnf, inst.dnf, "library"
    C = gk(3)
    yield "gk-f3", C, transversal(C), "read-once"
    for k in (1, 2):
        C = tk(k)
        yield f"tk-s{k}", C, transversal(C), "read-once"
    C = matching(12)
    yield "matching-12", C, transversal(C), "output"
    C = threshold(10)
    yield "threshold-10", C, transversal(C), "shape"


def main():
    rows = []
    for name, cnf, dnf, cls in cases():
        t0 = time.time()
        ta, tb = fk_a(cnf, dnf, variant="modified"), fk_b(cnf, dnf, variant="faithful")
        assert ta.dual and tb.dual, name
        cache = {}
        da, db = walk(ta, cache), walk(tb, cache)
        prim = [d for d, r in list(da.items()) + list(db.items()) if r["primitive"]]
        N = len(cnf) + len(dnf)
        top = ta.root
        root = cache[(top.cnf.edges, top.dnf.edges)]
        rows.append({
            "instance": name, "class": cls, "n_vertices": max(cnf.n, dnf.n), "N": N,
            "eps": str(eps_exact(cnf, dnf)), "c": round(threshold_ratio(cnf, dnf), 4),
            "s_over_log2N": round(shortest_edge_ratio(cnf, dnf), 4),
            "fka_nodes": len(ta), "fka_depth": ta.depth,
            "fkb_nodes": len(tb), "fkb_depth": tb.depth,
            "ratio": round(len(ta) / len(tb), 3),
            "exponent": round(math.log(len(ta)) / math.log(N), 3),
            "fka_repeat_rate": round((len(ta) - dag_size(ta)) / len(ta), 4),
            "distinct_pairs": len(cache),
            "root_primitive": root[0], "root_read_once": root[1],
            "last_primitive_depth": max(prim) if prim else -1,
            "primitive_nodes_fka": sum(r["primitive"] for r in da.values()),
            "primitive_nodes_fkb": sum(r["primitive"] for r in db.values()),
            "read_once_nodes_fka": sum(r["read_once"] for r in da.values()),
            "undetermined_nodes": (sum(r["undetermined"] for r in da.values())
                                   + sum(r["undetermined"] for r in db.values())),
            "fka_by_depth": {str(d): da[d] for d in sorted(da)},
            "fkb_by_depth": {str(d): db[d] for d in sorted(db)},
            "seconds": round(time.time() - t0, 1),
        })
        print(f"  {name:<16} c={rows[-1]['c']:>6.2f} FK-A={len(ta):>7} "
              f"FK-B={len(tb):>6} {rows[-1]['ratio']:>7.2f}x  "
              f"prim<=d{rows[-1]['last_primitive_depth']:<3} "
              f"[{rows[-1]['seconds']:.0f}s]", flush=True)

    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "hard-classes.json").write_text(
        json.dumps(rows, indent=2) + "\n", encoding="utf-8")

    lines = [
        "# Hard classes: placement and symmetry depth",
        "",
        "Regenerate with `python experiments/hard_classes.py`.",
        "",
        "`c = eps * log2 N` (FK96 window is `[1, 2]`); `exp = log(FK-A nodes)/log N`;",
        "`prim depth` is the deepest level with a confirmed primitive node outside",
        "the read-once class. `undet` counts nodes where the cap prevents a verdict.",
        "",
        "| instance | class | \\|V\\| | N | eps | c | s/log2N | FK-A | FK-B | A/B | exp | repeat | prim depth | RO root | undet |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :-: | ---: |",
    ]
    for r in rows:
        lines.append(
            f"| `{r['instance']}` | {r['class']} | {r['n_vertices']} | {r['N']} | "
            f"{r['eps']} | {r['c']:.2f} | {r['s_over_log2N']:.2f} | {r['fka_nodes']} | "
            f"{r['fkb_nodes']} | {r['ratio']:.2f}x | {r['exponent']:.2f} | "
            f"{r['fka_repeat_rate']:.1%} | {r['last_primitive_depth']} | "
            f"{'yes' if r['root_read_once'] else 'no'} | "
            f"{r['undetermined_nodes']} |")
    (RESULTS / "hard-classes.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"\nwrote {RESULTS/'hard-classes.json'} and {RESULTS/'hard-classes.md'}")


if __name__ == "__main__":
    main()

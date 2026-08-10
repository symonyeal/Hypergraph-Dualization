"""Tree against DAG: how much of FK-A's tree is re-derived subproblems.

    python experiments/dag_size.py          ->  results/dag-size.{json,md}
    python experiments/dag_size.py --deep   ->  the same, plus the length-3
                                                words (minutes, not seconds)

Three measurements over one instance set.

1. ``tau`` (:func:`fka.algorithm.fk_a`) beside ``delta``
   (:func:`fka.memo.fk_a_memo`) and FK-B's ``beta``, per instance. ``tau/delta``
   is the redundancy the tree carries; ``delta/beta`` says how much of it FK-B
   captures.

2. The exact laws along ``matching(v)`` and ``threshold(v)``, where both
   quantities are closed forms.

3. ``delta`` alone on the alternating-tree words, out to sizes whose tree cannot
   be enumerated. This is the point of having ``delta``: ``--deep`` reaches
   ``N = 16512``, where ``tau`` is not a computable observable.

`docs/tree-vs-dag.md` is what the numbers are read to mean.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

from fka.algorithm import fk_a
from fka.bound import threshold_ratio
from fka.instances import (gk, list_ids, load, matching, template_word,
                           threshold, tk)
from fka.memo import dag_size, fk_a_memo
from fka.transversal import transversal
from fkb.algorithm import fk_b

RESULTS = Path(__file__).resolve().parents[1] / "results"
#: The length-3 words cost minutes each; the library and the short words do not.
DEEP = "--deep" in sys.argv

sys.setrecursionlimit(100000)


def swap(w: str) -> str:
    return w.translate(str.maketrans("XY", "YX"))


def library():
    """Instances small enough to unfold, so ``tau`` and ``beta`` are observable."""
    for i in list_ids():
        inst = load(i)
        yield i, "library", inst.cnf, inst.dnf
    for k in (2, 3):
        yield f"gk-f{k}", "alternating", gk(k), transversal(gk(k))
    for k in (1, 2):
        yield f"tk-s{k}", "alternating", tk(k), transversal(tk(k))
    for v in (8, 10, 12, 14):
        yield f"matching-{v}", "output", matching(v), transversal(matching(v))
    for v in (8, 10, 12):
        yield f"threshold-{v}", "shape", threshold(v), transversal(threshold(v))


def deep():
    """``delta`` only: the words whose tree is out of reach."""
    words = ["XY", "YX"] + (["XXY", "XYX", "XYY", "XXX", "YYY"] if DEEP else [])
    for w in words:
        yield f"word-{w.lower()}", template_word(w), template_word(swap(w))


rows, laws, deep_rows = [], [], []

for name, cls, C, D in library():
    t0 = time.time()
    ta = fk_a(C, D, variant="modified")
    tb = fk_b(C, D, variant="faithful")
    run = fk_a_memo(C, D)
    assert run.dual == ta.dual, name
    assert run.nodes == dag_size(ta), name
    N, tau, beta, delta = len(C) + len(D), len(ta), len(tb), run.nodes
    rows.append({
        "instance": name, "class": cls, "n": C.n, "N": N,
        "c": round(threshold_ratio(C, D), 4),
        "tau": tau, "beta": beta, "delta": delta,
        "tau_over_delta": round(tau / delta, 2),
        "delta_over_beta": round(delta / beta, 3),
        "delta_over_N": round(delta / N, 4),
        "tau_exp": round(math.log(tau) / math.log(N), 3),
        "delta_exp": round(math.log(delta) / math.log(N), 3),
        "depth_tau": ta.depth, "depth_delta": run.depth,
        "seconds": round(time.time() - t0, 1),
    })
    print(f"{name:14} N={N:6d} tau={tau:7d} beta={beta:6d} delta={delta:5d} "
          f"tau/delta={tau/delta:7.1f} delta/N={delta/N:6.3f}", flush=True)

print()
for fam, build, lo, hi in (("matching", matching, 8, 20),
                           ("threshold", threshold, 8, 20)):
    for v in range(lo, hi + 1, 2):
        C = build(v)
        D = transversal(C)
        ta = fk_a(C, D, variant="modified")
        run = fk_a_memo(C, D)
        laws.append({"family": fam, "v": v, "N": len(C) + len(D),
                     "tau": len(ta), "delta": run.nodes})
        print(f"{fam}({v:2d}) N={len(C)+len(D):6d} tau={len(ta):7d} "
              f"delta={run.nodes:4d}", flush=True)

print()
for name, C, D in deep():
    t0 = time.time()
    run = fk_a_memo(C, D)
    N = len(C) + len(D)
    deep_rows.append({"instance": name, "n": C.n, "N": N, "delta": run.nodes,
                      "depth": run.depth, "dual": run.dual,
                      "delta_over_N": round(run.nodes / N, 4),
                      "delta_exp": round(math.log(run.nodes) / math.log(N), 3),
                      "seconds": round(time.time() - t0, 1)})
    print(f"{name:12} N={N:6d} delta={run.nodes:5d} "
          f"delta/N={run.nodes/N:6.3f}", flush=True)

RESULTS.mkdir(exist_ok=True)
(RESULTS / "dag-size.json").write_text(
    json.dumps({"instances": rows, "laws": laws, "deep": deep_rows,
                "deep_complete": DEEP}, indent=1) + "\n", encoding="utf-8")

L = ["# Tree against DAG",
     "",
     "Regenerate with `python experiments/dag_size.py` "
     "(`--deep` for the length-3 words).",
     "",
     "`tau` = FK-A recursion-tree nodes; `delta` = distinct subproblems among "
     "them, the size of the DAG and the node count of `fka.memo.fk_a_memo`; "
     "`beta` = FK-B nodes. `c = eps * log2 N` places the pair against the FK96 "
     "window, as in `hard-classes.md`.",
     "",
     "| instance | class | N | c | tau | beta | delta | tau/delta | delta/beta "
     "| delta/N | tau exp | delta exp |",
     "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | "
     "---: | ---: |"]
for r in rows:
    L.append(f"| `{r['instance']}` | {r['class']} | {r['N']} | {r['c']:.2f} | "
             f"{r['tau']} | {r['beta']} | {r['delta']} | "
             f"{r['tau_over_delta']:.1f}x | {r['delta_over_beta']:.2f} | "
             f"{r['delta_over_N']:.3f} | {r['tau_exp']:.2f} | "
             f"{r['delta_exp']:.2f} |")

L += ["", "## Closed forms", "",
      "Both families admit an exact law, checked in `tests/test_memo.py`:",
      "",
      "    matching(v):   tau = 2^(v/2+1) - 3      delta = v",
      "    threshold(v):  tau = v - 1              delta = v - 1",
      "",
      "| family | v | N | tau | delta |", "| --- | ---: | ---: | ---: | ---: |"]
for r in laws:
    L.append(f"| `{r['family']}` | {r['v']} | {r['N']} | {r['tau']} | "
             f"{r['delta']} |")

L += ["", "## Past the tree", "",
      "`delta` on the alternating-tree words, including sizes where `tau` "
      "cannot be enumerated." + ("" if DEEP else
      " Run with `--deep` for the length-3 rows."),
      "", "| instance | n | N | delta | delta/N | delta exp | depth |",
      "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
for r in deep_rows:
    L.append(f"| `{r['instance']}` | {r['n']} | {r['N']} | {r['delta']} | "
             f"{r['delta_over_N']:.3f} | {r['delta_exp']:.2f} | {r['depth']} |")

(RESULTS / "dag-size.md").write_text("\n".join(L) + "\n", encoding="utf-8")
print("\nwrote results/dag-size.{json,md}")

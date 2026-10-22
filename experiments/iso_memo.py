"""FK-A's subproblems up to isomorphism on read-once pairs (research prompt, Track S).

Usage (from the repository root): python experiments/iso_memo.py [kmax_gk] [kmax_tk]

Legend
  g        hash-consed formula id of experiments/readonce_sim.py; DNF g = C, DNF g^d = Tr C
  shp(g)   AHU shape id, (op, sorted child shape ids) with variable labels forgotten; two read-once
           formulas have the same shape iff they are equal up to relabelling, so iff the pairs
           (C, Tr C) are isomorphic
  delta    distinct subproblems of label-exact memoised FK-A (= readonce_sim.run()[1])
  d_shp    isomorphism classes among those delta subproblems
  d_iso    subproblems expanded by iso-memoised FK-A: a node whose shape was already seen is not
           expanded, so d_iso <= d_shp <= delta

The split rule breaks ties by least index, so it is not relabelling-equivariant and isomorphic
nodes can have different subtrees; d_iso depends on the traversal order (depth-first, left
child last pushed). `delta` is capped (CAP); GK f4 under degree_sum exceeds it (67,247,387 by
experiments/readonce_dag) and is printed as '>CAP'. GK f4 iso takes about 80 s.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
import readonce_sim as rs  # noqa: E402

sys.setrecursionlimit(1 << 20)
CAP = 500_000
SHP, SID = {}, {}


def shp(g):
    if g not in SHP:
        key = ('v',) if rs.OP[g] == 'v' else (rs.OP[g], tuple(sorted(shp(k) for k in rs.KIDS[g])))
        SHP[g] = SID.setdefault(key, len(SID))
    return SHP[g]


def leaf(g):
    c, d = rs.T[g], rs.TD[g]
    return c * d <= 1 or c == 1 or d == 1


def kids(g, rule):
    x = rs.split_var(g, rule)
    return rs.restrict(g, x, 0), rs.dual(rs.restrict(g, x, 1))


def exact(f, rule):
    """(delta, d_shp), or (None, None) past CAP."""
    seen, st = set(), [f]
    while st:
        g = st.pop()
        if g in seen:
            continue
        seen.add(g)
        if len(seen) > CAP:
            return None, None
        if not leaf(g):
            st.extend(kids(g, rule))
    return len(seen), len({shp(g) for g in seen})


def iso(f, rule):
    """d_iso: nodes expanded when the memo is keyed by shape."""
    seen, st = set(), [f]
    while st:
        g = st.pop()
        s = shp(g)
        if s in seen:
            continue
        seen.add(s)
        if not leaf(g):
            st.extend(kids(g, rule))
    return len(seen)


if __name__ == "__main__":
    kg = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    kt = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    cases = [(f"gk-f{k}", rs.gk(k), 2 ** (2 * k - 1)) for k in range(1, kg + 1)]
    cases += [(f"tk-s{k}", rs.tk(k), 4 ** k) for k in range(1, kt + 1)]
    print(f"{'pair':8s} {'rule':10s} {'n':>5s} {'N':>8s} {'delta':>10s} {'d_shp':>8s} {'d_iso':>8s}")
    for name, f, n in cases:
        for rule in ("degree_sum", "guarded", "leftmost"):
            dl, ds = exact(f, rule)
            di = iso(f, rule)
            dl, ds = (str(dl), str(ds)) if dl else (f">{CAP}", "-")
            print(f"{name:8s} {rule:10s} {n:5d} {rs.T[f] + rs.TD[f]:8d} {dl:>10s} {ds:>8s} {di:8d}",
                  flush=True)

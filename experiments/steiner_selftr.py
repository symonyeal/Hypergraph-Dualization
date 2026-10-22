"""Which Steiner systems can be self-transversal? (research track A, items A4 and A5)

Usage (from the repository root): python experiments/steiner_selftr.py

1. A4: checks d(r^2 - t) >= r(r - 1) on every self-transversal hypergraph at hand, and
   that equality holds exactly when distinct edges meet in one point.
2. A5: for a Steiner system S(t,k,v) the number of blocks disjoint from a fixed block is
   n0(t,k,v) = sum_{i<t} (-1)^i C(k,i) (lambda_i - 1), lambda_i = C(v-i,t-i)/C(k-i,t-i)
   (inclusion-exclusion; lambda_i is the number of blocks through an i-set). Only n0 = 0
   allows an intersecting, hence a self-transversal, system. Lists every admissible
   (t,k,v) with 2 <= t < k < v <= VMAX and n0 = 0, and checks n0 against brute force on
   the systems constructed here.
3. Tests the intersecting candidates that can be built here for 2-colourability by a full
   scan of 2^v colourings (vectorised): PG(2,2), PG(2,3), PG(2,4), S(4,5,11), S(4,7,23).
With --lean, writes lean/HypergraphDualization/SteinerData.lean: the blocks of PG(2,4) and
S(4,7,23) and the colour classes found.
Deterministic.
"""
import sys
from itertools import combinations
from math import comb
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from fka.hypergraph import Hypergraph, verts  # noqa: E402
from fka.instances import load  # noqa: E402
from fka.transversal import transversal  # noqa: E402

VMAX = 100


def lam(t, k, v, i):
    num, den = comb(v - i, t - i), comb(k - i, t - i)
    return num // den if num % den == 0 else None


def n0(t, k, v):
    lams = [lam(t, k, v, i) for i in range(t)]
    if any(x is None for x in lams):
        return None  # not admissible
    return sum((-1) ** i * comb(k, i) * (lams[i] - 1) for i in range(t))


def blocks_of(edges, n):
    return [frozenset(verts(e)) for e in edges]


def check_a4(name, H: Hypergraph):
    bl = blocks_of(H.edges, H.n)
    r = {len(b) for b in bl}
    d = {sum(1 for b in bl if v in b) for v in range(H.n)}
    t = H.n
    if len(r) != 1 or len(d) != 1:
        print(f"  {name}: not uniform/regular (sizes {r}, degrees {d}); skipped")
        return
    (r,), (d,) = r, d
    lhs, rhs = d * (r * r - t), r * (r - 1)
    linear = all(len(a & b) == 1 for a, b in combinations(bl, 2))
    print(f"  {name}: t={t} r={r} d={d} b={len(bl)}  d(r^2-t)={lhs} >= r(r-1)={rhs}: {lhs >= rhs};"
          f" equality {lhs == rhs}, pairwise meet 1: {linear}, consistent: {(lhs == rhs) == linear}")


def maj(m):
    """All (m+1)/2-subsets of m points: the majority function, S(k,k,2k-1)."""
    k = (m + 1) // 2
    return Hypergraph.from_sets(m, [list(c) for c in combinations(range(m), k)])


def two_colourable(bl, v):
    """Return a set A (bitmask) with no block inside A and none inside its complement, or None."""
    masks = np.array([sum(1 << x for x in b) for b in bl], dtype=np.int64)
    full = (1 << v) - 1
    chunk = 1 << 20
    for lo in range(0, 1 << v, chunk):
        A = np.arange(lo, min(lo + chunk, 1 << v), dtype=np.int64)
        C = full ^ A
        bad = np.zeros(A.shape, dtype=bool)
        for m in masks:
            bad |= (A & m) == m
            bad |= (C & m) == m
        ok = np.nonzero(~bad)[0]
        if ok.size:
            return int(A[ok[0]])
    return None


def golay_s4723():
    """Weight-7 words of the cyclic [23,12,7] binary Golay code, g = x^11+x^10+x^6+x^5+x^4+x^2+1."""
    g = sum(1 << e for e in (11, 10, 6, 5, 4, 2, 0))
    words = set()
    for msg in range(1 << 12):
        w = 0
        for i in range(12):
            if msg >> i & 1:
                w ^= g << i
        if w.bit_count() == 7:
            words.add(w)
    return [frozenset(i for i in range(23) if w >> i & 1) for w in sorted(words)]


def pg2(q):
    """PG(2,q) for prime q from the field, or q = 4 from GF(4)."""
    if q == 4:
        mul = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
        add = lambda a, b: a ^ b  # noqa: E731
    else:
        mul = [[(a * b) % q for b in range(q)] for a in range(q)]
        add = lambda a, b: (a + b) % q  # noqa: E731
    pts = []
    for x in range(q):
        for y in range(q):
            pts.append((x, y, 1))
    for x in range(q):
        pts.append((x, 1, 0))
    pts.append((1, 0, 0))
    idx = {p: i for i, p in enumerate(pts)}
    lines = set()
    for a in pts:  # line a.x = 0
        on = []
        for p in pts:
            s = 0
            for u, w in zip(a, p):
                s = add(s, mul[u][w])
            if s == 0:
                on.append(idx[p])
        lines.add(frozenset(on))
    return sorted(lines, key=sorted)


def steiner_t(bl):
    k = len(next(iter(bl)))
    pts = sorted(set().union(*bl))
    for t in range(k, 0, -1):
        cnt = {}
        for b in bl:
            for s in combinations(sorted(b), t):
                cnt[s] = cnt.get(s, 0) + 1
        if len(cnt) == comb(len(pts), t) and set(cnt.values()) == {1}:
            return t
    return None


print("A4: d(r^2 - t) >= r(r - 1) on self-transversal uniform regular hypergraphs")
for iid in ("k3", "fano", "w11"):
    H = load(iid).cnf
    assert transversal(H).edges == H.edges
    check_a4(iid, H)
for m in (5, 7, 9):
    H = maj(m)
    assert transversal(H).edges == H.edges
    check_a4(f"maj{m}", H)

print(f"\nA5: admissible S(t,k,v), 2 <= t < k < v <= {VMAX}, with n0 = 0 (no two disjoint blocks)")
zero = []
for v in range(3, VMAX + 1):
    for k in range(3, v):
        for t in range(2, k):
            x = n0(t, k, v)
            if x is None:
                continue
            if x < 0:
                print(f"  S({t},{k},{v}): n0 = {x} < 0 -- cannot exist")
            if x == 0:
                zero.append((t, k, v))
for t, k, v in zero:
    plane = t == 2 and v == (k - 1) ** 2 + (k - 1) + 1
    print(f"  S({t},{k},{v})" + (f"  = projective plane of order {k - 1}" if plane else ""))

print("\nn0 against brute force, and 2-colourability")
systems = {
    "S(2,3,7)=PG(2,2)": pg2(2),
    "S(2,4,13)=PG(2,3)": pg2(3),
    "S(2,5,21)=PG(2,4)": pg2(4),
    "S(4,5,11)": blocks_of(load("w11").cnf.edges, 11),
    "S(4,7,23)": golay_s4723(),
}
colour = {}
for name, bl in systems.items():
    v = len(set().union(*bl))
    k = len(bl[0])
    t = steiner_t(bl)
    b0 = bl[0]
    disjoint = sum(1 for b in bl if not (b & b0))
    print(f"  {name}: v={v} k={k} b={len(bl)} Steiner t={t}  disjoint from a block: {disjoint},"
          f" n0 formula: {n0(t, k, v)}")
    if disjoint == 0:
        A = two_colourable(bl, v)
        if A is None:
            print("    not 2-colourable: SELF-TRANSVERSAL")
        else:
            colour[name] = sorted(i for i in range(v) if A >> i & 1)
            print(f"    2-colourable, colour class {colour[name]}")

if "--lean" in sys.argv:
    def fs(b):
        return "{" + ", ".join(map(str, sorted(b))) + "}"

    out = [
        "/-",
        "Generated by experiments/steiner_selftr.py --lean. Do not edit.",
        "",
        "`pg24L`: the 21 lines of `PG(2,4)` over `GF(4)`. `s4723L`: the 253 weight-7 words of the",
        "cyclic binary Golay code of length 23, the blocks of `S(4,7,23)`. `*Colour`: a colour class",
        "of a 2-colouring found by a full scan.",
        "-/",
        "import Mathlib.Data.Fintype.Fin",
        "",
        "namespace HD.Steiner",
        "",
    ]
    for name, key, v in (("pg24", "S(2,5,21)=PG(2,4)", 21), ("s4723", "S(4,7,23)", 23)):
        bl = sorted(sorted(b) for b in systems[key])
        out.append(f"def {name}L : List (Finset (Fin {v})) := [" + ", ".join(fs(b) for b in bl) + "]")
        out.append("")
        out.append(f"def {name}Colour : Finset (Fin {v}) := {fs(colour[key])}")
        out.append("")
    out.append("end HD.Steiner")
    path = ROOT / "lean" / "HypergraphDualization" / "SteinerData.lean"
    path.write_text("\n".join(out) + "\n", encoding="utf-8", newline="\n")
    print("wrote", path)

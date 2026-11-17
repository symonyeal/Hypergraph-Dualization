"""Decision-tree size of the alternating trees GK f_k and TK S_k (docs/complex-evaluation.md).

Legend
  v       : number of variables (GK f_k: 2^(2k-1), OR root; TK S_k: 4^k, AND root)
  u       : P_F(w, ..., w), the multilinear extension at w = (1 + i sqrt3)/2, exact in Q(i sqrt3)
  L1, L0  : 1- and 0-leaves of the depth-first decision tree (all orders agree by symmetry)
  DT(F)   : least number of leaves of a decision tree computing F

rates K      : log2|u|/v, log2(|u| + |1 - u|)/v and log2(L1 + L0)/v for k <= K, exactly.
least K      : DT of GK f_1..f_K and TK S_1..S_{K-1} by DP over isomorphism classes of
               restricted read-once formulas (K <= 3: about five seconds).
random S T   : T random read-once formulas (<= 14 leaves, seed S): DT against the best
               depth-first tree (Pareto sets of (L1, L0) over child orders).
balanced A B : the same on every balanced alternating formula (each gate's children
               isomorphic) with arities 2, 3, at most 5 levels and 36 leaves, for the cost
               A L1 + B L0 (default 1 1, the number of leaves; about a minute per pair).
lp           : GK f_2 by truth tables: DT, and the subcube-partition LP bound (needs scipy).
Usage: python experiments/alternating_dt.py rates 6 | least 3 | random 1 400 | balanced 1 5 | lp
"""
import random
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from math import log2, prod


class Q:
    """a + b i sqrt3 with rational a, b."""

    def __init__(self, a, b):
        self.a, self.b = Fraction(a), Fraction(b)

    def __sub__(self, o):
        return Q(self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        return Q(self.a * o.a - 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    def lg(self):
        """log2 |self|, from the exact norm a^2 + 3 b^2."""
        m = self.a * self.a + 3 * self.b * self.b
        return (log2(m.numerator) - log2(m.denominator)) / 2


ONE, W = Q(1, 0), Q(Fraction(1, 2), Fraction(1, 2))


def alternating(top_or, depth):
    """(u, L1 + L0) of the binary alternating tree of the given depth and root."""
    u, L1, L0 = W, 1, 1
    for d in range(depth):
        if (depth - d) % 2 == (1 if top_or else 0):
            u, L1, L0 = ONE - (ONE - u) * (ONE - u), L1 + L0 * L1, L0 * L0
        else:
            u, L1, L0 = u * u, L1 * L1, L0 + L1 * L0
    return u, L1 + L0


def rates(K):
    for name, top_or, depths in (("GK f_k", True, [2 * k - 1 for k in range(1, K + 1)]),
                                 ("TK S_k", False, [2 * k for k in range(1, K + 1)])):
        for depth in depths:
            u, L = alternating(top_or, depth)
            v, s, s1 = 2 ** depth, u.lg(), (ONE - u).lg()
            both = max(s, s1) + log2(1 + 2 ** -abs(s - s1))
            print(f"{name} v={v:5d}  log2|u|/v={s / v:.9f}  log2(|u|+|1-u|)/v={both / v:.9f}  "
                  f"log2 L_df/v={log2(L) / v:.6f}")


def mk(op, kids):
    """Gate op over kids, simplified: constants are True/False, same-type gates flattened."""
    unit, zero = op == "&", op == "|"
    flat = []
    for k in kids:
        if k is unit:
            continue
        if k is zero:
            return zero
        flat += k[1] if isinstance(k, tuple) and k[0] == op else [k]
    if not flat:
        return unit
    return flat[0] if len(flat) == 1 else (op, tuple(sorted(flat, key=repr)))


def restrict(f, path, val):
    if not path:
        return val
    op, kids = f
    return mk(op, [restrict(k, path[1:], val) if j == path[0] else k for j, k in enumerate(kids)])


def leaf_paths(f, path=()):
    """One path per isomorphism class of leaf position."""
    if f == "x":
        yield path
        return
    seen = set()
    for i, k in enumerate(f[1]):
        if k not in seen:
            seen.add(k)
            yield from leaf_paths(k, path + (i,))


@lru_cache(maxsize=None)
def DT(f, a=1, b=1):
    """Least a L1 + b L0 over decision trees for f; a = b = 1 counts leaves."""
    if f is True or f is False:
        return a if f else b
    return min(DT(restrict(f, p, False), a, b) + DT(restrict(f, p, True), a, b) for p in leaf_paths(f))


def tree(top_or, depth):
    f = "x"
    for d in range(depth):
        op = "|" if (depth - d) % 2 == (1 if top_or else 0) else "&"
        f = mk(op, [f, f])
    return f


def least(K):
    for k in range(1, K + 1):
        print(f"GK f_{k}: DT = {DT(tree(True, 2 * k - 1))}, depth-first = {alternating(True, 2 * k - 1)[1]}")
    for k in range(1, K):
        print(f"TK S_{k}: DT = {DT(tree(False, 2 * k))}, depth-first = {alternating(False, 2 * k)[1]}")


def pareto(pts):
    out = []
    for p in sorted(set(pts)):
        if not out or p[1] < out[-1][1]:
            out.append(p)
    return out


def depth_first(f):
    """Pareto set of (L1, L0) over depth-first trees; OR is AND on (L0, L1)."""
    if f == "x":
        return [(1, 1)]
    op, kids = f
    fr = [depth_first(k) for k in kids]
    if op == "|":
        fr = [[(b, a) for a, b in F] for F in fr]
    best = []
    for order in set(permutations(range(len(kids)))):
        cur = [(1, 0)]
        for i in reversed(order):
            cur = pareto([(a1 * c1, a0 + a1 * c0) for a1, a0 in fr[i] for c1, c0 in cur])
        best += cur
    best = pareto(best)
    return [(b, a) for a, b in best] if op == "|" else best


def random_formula(rng, n, op):
    if n == 1:
        return "x"
    k = rng.choice([2, 2, 3]) if n >= 3 else 2
    cuts = sorted(rng.sample(range(1, n), k - 1))
    other = "&" if op == "|" else "|"
    return mk(op, [random_formula(rng, b - a, other) for a, b in zip([0] + cuts, cuts + [n])])


def random_test(seed, T):
    rng, worse = random.Random(seed), []
    for _ in range(T):
        f = random_formula(rng, rng.randint(2, 14), rng.choice("&|"))
        exact, df = DT(f), min(a + b for a, b in depth_first(f))
        if exact != df:
            worse.append(df / exact)
    print(f"{T} random read-once formulas: depth-first larger than DT on {len(worse)}, "
          f"largest ratio {max(worse, default=1):.3f}")


def balanced(a, b):
    same = total = 0
    for levels in range(1, 6):
        for ar in product((2, 3), repeat=levels):
            if prod(ar) > 36:
                continue
            for first in "&|":
                f = "x"
                for i, m in enumerate(ar):
                    f = mk("&|"[(i + (first == "|")) % 2], [f] * m)
                total += 1
                same += DT(f, a, b) == min(a * l1 + b * l0 for l1, l0 in depth_first(f))
    print(f"balanced alternating formulas, leaf weights ({a}, {b}): {total}; depth-first optimal on {same}")


def lp():
    import numpy as np
    from scipy.optimize import linprog

    n = 8
    f = [((x & 1 or x >> 1 & 1) and (x >> 2 & 1 or x >> 3 & 1)) or
         ((x >> 4 & 1 or x >> 5 & 1) and (x >> 6 & 1 or x >> 7 & 1)) for x in range(1 << n)]
    cubes = []
    for fix in product((-1, 0, 1), repeat=n):
        c = [x for x in range(1 << n) if all(b < 0 or (x >> i & 1) == b for i, b in enumerate(fix))]
        cubes.append((fix, c))

    @lru_cache(maxsize=None)
    def tt_dt(fix):
        c = next(c for g, c in cubes if g == fix)
        if len({f[x] for x in c}) == 1:
            return 1
        return min(tt_dt(fix[:i] + (0,) + fix[i + 1:]) + tt_dt(fix[:i] + (1,) + fix[i + 1:])
                   for i, b in enumerate(fix) if b < 0)

    rows = []
    for _, c in cubes:
        if len({f[x] for x in c}) == 1:
            r = np.zeros(1 << n)
            r[c] = 1
            rows.append(r)
    res = linprog(-np.ones(1 << n), A_ub=np.array(rows), b_ub=np.ones(len(rows)), bounds=(None, None))
    print(f"GK f_2: DT by truth tables = {tt_dt(tuple([-1] * n))}; partition LP bound = {-res.fun:.4f}")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    mode = sys.argv[1] if len(sys.argv) > 1 else "rates"
    if mode == "rates":
        rates(int(sys.argv[2]) if len(sys.argv) > 2 else 6)
    elif mode == "least":
        least(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
    elif mode == "random":
        random_test(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == "balanced":
        balanced(*(map(int, sys.argv[2:4]) if len(sys.argv) > 3 else (1, 1)))
    else:
        lp()

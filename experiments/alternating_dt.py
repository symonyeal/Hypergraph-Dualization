"""Decision-tree size of the alternating trees GK f_k and TK S_k (docs/complex-evaluation.md).

Legend
  v       : number of variables (GK f_k: 2^(2k-1), OR root; TK S_k: 4^k, AND root)
  u       : P_F(w, ..., w), the multilinear extension at w = (1 + i sqrt3)/2, exact in Q(i sqrt3)
  L1, L0  : 1- and 0-leaves of a decision tree
  V(F;a,b): least a L1 + b L0 over decision trees for F, a, b > 0; V(F;1,1) = DT(F), the least size
  H(F)    : vertices of the lower-left convex hull of the achievable (L1, L0), L1 ascending;
            V(F;a,b) = min over H(F), so H(F) = H(G) iff V agrees for all weights.
            H(1) = {(1,0)}, H(0) = {(0,1)}, H(F) = hull of U_x H(F|x=0) + H(F|x=1) (Minkowski sum)
  D(F)    : the same over depth-first trees. AND(K) = hull of U_k D(k) o D(AND(K - k)),
            p o q = (p1 q1, p0 + p1 q0) (k first, the rest at its 1-leaves); OR by De Morgan.
  top(F)  : depth-first at the root gate only, every child's tree optimal (D with H for the kids).

rates K   : log2|u|/v, log2(|u| + |1 - u|)/v and log2(L1 + L0)/v for k <= K, exactly.
least K   : H and D of GK f_1..f_K and TK S_1..S_{K-1}, by DP over isomorphism classes of
            restricted read-once formulas (K <= 3: about ten seconds).
classes K : every restriction class of GK f_K reached by the DP: on how many is H != D.
random S T: T random read-once formulas (<= 14 leaves, seed S): DT against the best depth-first tree.
balanced  : every balanced alternating formula (each gate's children isomorphic) with arities 2, 3,
            at most 5 levels and 36 leaves: H = D, and H a single point (about a minute).
gates L R : AND(g, h) for OR-rooted balanced g, h with <= L leaves each: H = top for all pairs?
            Then, for g, h with <= R leaves, restrictions a of g, b of h: where H(AND(a, b)) differs
            from the hull of the two orders of a and b (a, b as units), and from top (an AND-rooted
            child flattened into the gate), with the least ratios (18 12: about a minute).
theta     : rate bounds of Lemma 16 (one-gate loss theta) and the theta that passes 0.4143394.
rank K    : least rank (k <= 3) and the depth-first tree's rank of GK f_k, k <= K.
Usage: python experiments/alternating_dt.py rates 6 | least 3 | classes 3 | random 1 400 | balanced
       | gates 18 12 | theta | rank 9
"""
import random
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import product
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
    """(u, L1, L0) of the binary alternating tree of the given depth and root; (L1, L0) depth-first."""
    u, L1, L0 = W, 1, 1
    for d in range(depth):
        if (depth - d) % 2 == (1 if top_or else 0):
            u, L1, L0 = ONE - (ONE - u) * (ONE - u), L1 + L0 * L1, L0 * L0
        else:
            u, L1, L0 = u * u, L1 * L1, L0 + L1 * L0
    return u, L1, L0


def rates(K):
    for name, top_or, depths in (("GK f_k", True, [2 * k - 1 for k in range(1, K + 1)]),
                                 ("TK S_k", False, [2 * k for k in range(1, K + 1)])):
        for depth in depths:
            u, L1, L0 = alternating(top_or, depth)
            v, s, s1 = 2 ** depth, u.lg(), (ONE - u).lg()
            both = max(s, s1) + log2(1 + 2 ** -abs(s - s1))
            print(f"{name} v={v:5d}  log2|u|/v={s / v:.9f}  log2(|u|+|1-u|)/v={both / v:.9f}  "
                  f"log2 L_df/v={log2(L1 + L0) / v:.6f}")


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


def restrictions(f):
    """Every non-constant restriction class of f, f included."""
    seen, todo = {f}, [f]
    while todo:
        g = todo.pop()
        for p in leaf_paths(g):
            for e in (False, True):
                r = restrict(g, p, e)
                if r is not True and r is not False and r not in seen:
                    seen.add(r)
                    todo.append(r)
    return seen


def lhull(pts):
    """Vertices of the lower-left convex hull, L1 ascending, L0 strictly descending."""
    S = []
    for p in sorted(set(pts)):
        while len(S) >= 2 and ((S[-1][0] - S[-2][0]) * (p[1] - S[-2][1])
                               - (S[-1][1] - S[-2][1]) * (p[0] - S[-2][0])) <= 0:
            S.pop()
        S.append(p)
    k = min(range(len(S)), key=lambda i: (S[i][1], S[i][0]))
    return tuple(S[:k + 1])


def msum(P, R):
    """Minkowski sum of two lower-left chains: merge the edges by slope."""
    i = j = 0
    out = [(P[0][0] + R[0][0], P[0][1] + R[0][1])]
    while i < len(P) - 1 or j < len(R) - 1:
        if j == len(R) - 1 or (i < len(P) - 1 and
                               (P[i + 1][1] - P[i][1]) * (R[j + 1][0] - R[j][0])
                               <= (R[j + 1][1] - R[j][1]) * (P[i + 1][0] - P[i][0])):
            i += 1
        else:
            j += 1
        out.append((P[i][0] + R[j][0], P[i][1] + R[j][1]))
    return out


def compose(P, R):
    """Hull of p o q: a tree for p's formula with a tree for q's at each of its 1-leaves."""
    return lhull([(p1 * q1, p0 + p1 * q0) for p1, p0 in P for q1, q0 in R])


@lru_cache(maxsize=None)
def H(f):
    if f is True or f is False:
        return ((1, 0),) if f else ((0, 1),)
    pts = []
    for p in leaf_paths(f):
        pts += msum(H(restrict(f, p, False)), H(restrict(f, p, True)))
    return lhull(pts)


def V(f, a, b):
    return min(a * p1 + b * p0 for p1, p0 in H(f))


def neg(f):
    """De Morgan dual with complemented leaves; its hulls are those of f with L1, L0 swapped."""
    if f is True or f is False:
        return not f
    return f if f == "x" else mk("|" if f[0] == "&" else "&", [neg(k) for k in f[1]])


def swap(P):
    return tuple((p0, p1) for p1, p0 in reversed(P))


@lru_cache(maxsize=None)
def chain(kids, inner):
    """Hull of trees for AND(kids) that finish one child before starting the next, each child's
    tree from inner (H or D); kids sorted, H(neg k) and D(neg k) are swaps of H(k), D(k)."""
    if len(kids) == 1:
        return inner(kids[0])
    pts = []
    for i, k in enumerate(kids):
        if i == 0 or kids[i - 1] != k:
            pts += compose(inner(k), chain(kids[:i] + kids[i + 1:], inner))
    return lhull(pts)


def gate(f, inner):
    if f[0] == "&":
        return chain(f[1], inner)
    return swap(chain(tuple(sorted((neg(k) for k in f[1]), key=repr)), inner))


@lru_cache(maxsize=None)
def D(f):
    return ((1, 1),) if f == "x" else gate(f, D)


def top(f):
    return gate(f, H)


def tree(top_or, depth):
    f = "x"
    for d in range(depth):
        op = "|" if (depth - d) % 2 == (1 if top_or else 0) else "&"
        f = mk(op, [f, f])
    return f


def least(K):
    for name, f in [(f"GK f_{k}", tree(True, 2 * k - 1)) for k in range(1, K + 1)] + \
                   [(f"TK S_{k}", tree(False, 2 * k)) for k in range(1, K)]:
        print(f"{name}: H = {H(f)}, depth-first D = {D(f)}, DT = {V(f, 1, 1)}")


def classes(K):
    f = tree(True, 2 * K - 1)
    R = restrictions(f)
    bad = sorted((g for g in R if H(g) != D(g)), key=lambda g: (V(g, 1, 1), repr(g)))
    print(f"GK f_{K}: H = D at the root: {H(f) == D(f)}; restriction classes {len(R)}, H != D on {len(bad)}")
    if bad:
        g = bad[0]
        print(f"  least: {g}  H = {H(g)}, D = {D(g)}")


def random_test(seed, T):
    rng, worse = random.Random(seed), []
    for _ in range(T):
        f = random_formula(rng, rng.randint(2, 14), rng.choice("&|"))
        exact, df = V(f, 1, 1), min(a + b for a, b in D(f))
        if exact != df:
            worse.append(df / exact)
    print(f"{T} random read-once formulas: depth-first larger than DT on {len(worse)}, "
          f"largest ratio {max(worse, default=1):.3f}")


def random_formula(rng, n, op):
    if n == 1:
        return "x"
    k = rng.choice([2, 2, 3]) if n >= 3 else 2
    cuts = sorted(rng.sample(range(1, n), k - 1))
    other = "&" if op == "|" else "|"
    return mk(op, [random_formula(rng, b - a, other) for a, b in zip([0] + cuts, cuts + [n])])


def balanced_formulas(lmax):
    """Balanced alternating formulas, arities 2 and 3, <= 5 levels; first is the bottom gate."""
    for levels in range(1, 6):
        for ar in product((2, 3), repeat=levels):
            if prod(ar) > lmax:
                continue
            for first in "&|":
                f = "x"
                for i, m in enumerate(ar):
                    f = mk("&|"[(i + (first == "|")) % 2], [f] * m)
                yield f


def balanced():
    fs = list(balanced_formulas(36))
    same = sum(H(f) == D(f) for f in fs)
    single = sum(len(H(f)) == 1 for f in fs)
    print(f"balanced alternating formulas: {len(fs)}; H = D (all weights) on {same}; H one point on {single}")


def least_ratio(A, B):
    """min over a, b > 0 of min_A / min_B, attained on an axis or at an edge normal of A or B."""
    dirs = [(1, 0), (0, 1)] + [(P[i][1] - P[i + 1][1], P[i + 1][0] - P[i][0])
                               for P in (A, B) for i in range(len(P) - 1)]
    val = lambda P, a, b: min(a * p1 + b * p0 for p1, p0 in P)
    return min(Fraction(val(A, a, b), val(B, a, b)) for a, b in dirs)


def gates(L, R):
    fs = [f for f in balanced_formulas(L) if f[0] == "|"]
    pairs = [(g, h) for i, g in enumerate(fs) for h in fs[i:]]
    fresh = sum(H(mk("&", [g, h])) == top(mk("&", [g, h])) for g, h in pairs)
    print(f"{len(fs)} OR-rooted balanced formulas, {len(pairs)} pairs: AND(g, h) depth-first at the gate on {fresh}")
    pairs = [(g, h) for g, h in pairs if max(repr(g).count("x"), repr(h).count("x")) <= R]
    for kind in ("one fresh", "both restricted"):
        n, stats = 0, {"gate": [0, Fraction(2), None], "flattened": [0, Fraction(2), None]}
        for g, h in pairs:
            for a in restrictions(g):
                for b in restrictions(h):
                    if (a == g) + (b == h) != (1 if kind == "one fresh" else 0):
                        continue
                    n += 1
                    f = mk("&", [a, b])
                    base = {"gate": lhull(compose(H(a), H(b)) + compose(H(b), H(a))), "flattened": top(f)}
                    for name, B in base.items():
                        if H(f) != B:
                            s = stats[name]
                            s[0] += 1
                            r = least_ratio(H(f), B)
                            if r < s[1]:
                                s[1], s[2] = r, (a, b)
        print(f"  {kind}: {n} restricted pairs")
        for name, (bad, r, w) in stats.items():
            print(f"    not depth-first, {name} (a, b {'as units' if name == 'gate' else 'flattened into the gate'}): "
                  f"{bad}, least ratio {r if bad else 1} = {float(r) if bad else 1:.4f} at {w}")


def theta():
    """Lemma 16: GK f_K with f_3 blocks, loss theta per gate."""
    _, L1, L0 = alternating(True, 5)
    z3 = 2 * log2(L1) + log2(L0)
    bar = 0.4143394
    print(f"f_3: (L1, L0) = ({L1}, {L0}); depth-first rate log2(L1 + L0)/32 = {log2(L1 + L0) / 32:.6f}")
    print(f"(a) V form:  gamma >= {z3 / 96:.7f} - log2(1/theta)/32; passes {bar} for theta > {2 ** (-32 * (z3 / 96 - bar)):.4f}")
    print(f"(b) scalar:  gamma >= z3/96 - log2(1/theta)/48, z3/96 = {z3 / 96:.7f}; "
          f"passes {bar} for theta > {2 ** (-48 * (z3 / 96 - bar)):.4f}")


def c(r, s):
    """Rank of a node whose subtrees have ranks r and s."""
    return max(r, s) if r != s else r + 1


@lru_cache(maxsize=None)
def rank(f):
    """Least rank of a decision tree for f; size >= 2^rank."""
    if f is True or f is False:
        return 0
    return min(c(rank(restrict(f, p, False)), rank(restrict(f, p, True))) for p in leaf_paths(f))


@lru_cache(maxsize=None)
def rank_df(depth, al, be):
    """Rank of the depth-first tree of the binary alternating tree (OR root iff depth odd)
    with 1-leaves of rank al and 0-leaves of rank be: AND g-first R_g(R_h(al, be), be), OR dual."""
    if depth == 0:
        return c(al, be)
    if depth % 2 == 0:
        return rank_df(depth - 1, rank_df(depth - 1, al, be), be)
    return rank_df(depth - 1, al, rank_df(depth - 1, al, be))


def ranks(K):
    for k in range(1, K + 1):
        v, f = 2 ** (2 * k - 1), tree(True, 2 * k - 1)
        exact = rank(f) if k <= 3 else "-"
        print(f"GK f_{k}: v = {v}, least rank {exact}, depth-first tree rank {rank_df(2 * k - 1, 0, 0)}, "
              f"(v + 1)/3 = {(v + 1) // 3}")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    mode, args = (sys.argv[1] if len(sys.argv) > 1 else "rates"), [int(a) for a in sys.argv[2:]]
    if mode == "rates":
        rates(*(args or [6]))
    elif mode == "least":
        least(*(args or [3]))
    elif mode == "classes":
        classes(*(args or [3]))
    elif mode == "random":
        random_test(*args)
    elif mode == "balanced":
        balanced()
    elif mode == "gates":
        gates(*(args or [18, 12]))
    elif mode == "theta":
        theta()
    elif mode == "rank":
        ranks(*(args or [9]))
    else:
        raise SystemExit(f"unknown mode {mode!r}")

"""FK-A on read-once pairs, simulated on formulas (research track C, items C2 and C3).

Usage (from the repository root): python experiments/readonce_sim.py [kmax]
                                  python experiments/readonce_sim.py --sexpr gk|tk k
The second form prints the formula for experiments/readonce_dag, which measures GK_4 (kmax = 4
here needs more than 14 GB).

A node of modified FK-A on a dual pair (C, Tr C) is determined by the monotone function g whose
DNF is C. For a read-once g every quantity FK-A uses is read off its formula:
  |C| = #terms(g), |Tr C| = #terms(g^d), deg_C x = #terms of g containing x;
  left child  (C - x, Tr(C - x))  has function g|x=0;
  right child (Tr Q, Q), Q = C/x,  has function (g|x=1)^d (the dual: the sides swap).
A node is a leaf when |C||D| <= 1 or |C| = 1 or |D| = 1; otherwise it splits on the vertex of
largest deg_C + deg_D, lowest index on ties. tau counts the tree, delta the distinct functions
(= distinct reduced pairs).

Formulas are hash-consed: a node is an integer id with (op, sorted child ids), so equal
functions get equal ids, and a restriction rebuilds only the path from the root to the leaf.
Degrees come from one top-down pass: at an AND node a child's multiplier is multiplied by the
term counts of its siblings. Validated against fka.algorithm.fk_a and fka.memo.fk_a_memo on
GK_1..3, TK_1..2 and 200 random formulas (seeded).
"""
import random
import sys
from math import prod
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from fka.algorithm import fk_a  # noqa: E402
from fka.hypergraph import Hypergraph  # noqa: E402
from fka.memo import fk_a_memo  # noqa: E402

sys.setrecursionlimit(100000)

OP, KIDS, MASK, T, TD = [], [], [], [], []     # node table: op ('v', '|', '&'), children, var mask, #terms of g, of g^d
ID = {}                                        # (op, kids) or ('v', x) -> id
DUAL = {}


def intern(key, op, kids, mask, t, td):
    if key not in ID:
        ID[key] = len(OP)
        OP.append(op), KIDS.append(kids), MASK.append(mask), T.append(t), TD.append(td)
    return ID[key]


def var(x):
    return intern(('v', x), 'v', (), 1 << x, 1, 1)


ZERO = intern(('|', ()), '|', (), 0, 0, 1)     # empty OR: no terms; its dual has the empty term
ONE = intern(('&', ()), '&', (), 0, 1, 0)


def mk(op, kids):
    """Canonical n-ary node: absorb constants, flatten, sort."""
    unit, zero = (ONE, ZERO) if op == '&' else (ZERO, ONE)
    out = []
    for k in kids:
        if k == zero:
            return zero
        if k != unit:
            out.extend(KIDS[k] if OP[k] == op else (k,))
    if len(out) == 1:
        return out[0]
    out = tuple(sorted(out))
    ts, tds = [T[k] for k in out], [TD[k] for k in out]
    t, td = (sum(ts), prod(tds)) if op == '|' else (prod(ts), sum(tds))
    return intern((op, out), op, out, sum(MASK[k] for k in out), t, td)


def dual(f):
    if f not in DUAL:
        DUAL[f] = f if OP[f] == 'v' else mk('&' if OP[f] == '|' else '|', [dual(k) for k in KIDS[f]])
    return DUAL[f]


def restrict(f, x, b):
    """g|x=b: rebuilds the path to x only."""
    if not MASK[f] >> x & 1:
        return f
    if OP[f] == 'v':
        return ONE if b else ZERO
    return mk(OP[f], [restrict(k, x, b) if MASK[k] >> x & 1 else k for k in KIDS[f]])


def degrees(f, dualised, m=1, out=None):
    """deg x = #terms containing x, for every variable of g (or of g^d)."""
    out = {} if out is None else out
    op = OP[f]
    if op == 'v':
        out[MASK[f].bit_length() - 1] = m
        return out
    is_and = (op == '&') != dualised
    ts = [TD[k] if dualised else T[k] for k in KIDS[f]]
    for i, k in enumerate(KIDS[f]):
        degrees(k, dualised, m * prod(ts[:i] + ts[i + 1:]) if is_and else m, out)
    return out


def run(f):
    """(tau, delta) of modified FK-A on the pair (DNF f, DNF f^d)."""
    tau = {}

    def node(g):
        if g not in tau:
            c, d = T[g], TD[g]
            if c * d <= 1 or c == 1 or d == 1:
                tau[g] = 1
            else:
                dg, dd = degrees(g, False), degrees(g, True)
                x = min(dg, key=lambda v: (-(dg[v] + dd[v]), v))
                tau[g] = 1 + node(restrict(g, x, 0)) + node(dual(restrict(g, x, 1)))
        return tau[g]

    return node(f), len(tau)


def dnf(f):
    """DNF edges (bitmasks) of a formula."""
    if OP[f] == 'v':
        return {MASK[f]}
    parts = [dnf(k) for k in KIDS[f]]
    if OP[f] == '|':
        return set().union(*parts)
    out = {0}
    for P in parts:
        out = {a | b for a in out for b in P}
    return out


def gk(k, base=0):
    """GK_1 = x0 | x1, GK_{k+1} = (f & f) | (f & f) on disjoint copies."""
    if k == 1:
        return mk('|', [var(base), var(base + 1)])
    m = 2 ** (2 * k - 3)
    a, b, c, d = (gk(k - 1, base + i * m) for i in range(4))
    return mk('|', [mk('&', [a, b]), mk('&', [c, d])])


def tk(k, base=0):
    """TK_0 = x0, TK_{k+1} = (f | f) & (f | f)."""
    if k == 0:
        return var(base)
    m = 4 ** (k - 1)
    a, b, c, d = (tk(k - 1, base + i * m) for i in range(4))
    return mk('&', [mk('|', [a, b]), mk('|', [c, d])])


def random_formula(leaves, rng):
    if len(leaves) == 1:
        return var(leaves[0])
    k = rng.randrange(1, len(leaves))
    return mk(rng.choice('|&'), [random_formula(leaves[:k], rng), random_formula(leaves[k:], rng)])


def sexpr(f):
    """The formula as an s-expression `(| (& 0 1) 2)`, the input of readonce_dag."""
    if OP[f] == 'v':
        return str(MASK[f].bit_length() - 1)
    return "(" + OP[f] + " " + " ".join(sexpr(k) for k in KIDS[f]) + ")"


def check(f, n):
    """Compare the simulation with the hypergraph implementations."""
    C = Hypergraph.from_bitsets(n, sorted(dnf(f)))
    D = Hypergraph.from_bitsets(n, sorted(dnf(dual(f))))
    return run(f) == (len(fk_a(C, D).nodes), fk_a_memo(C, D).nodes)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--sexpr"]:
        print(sexpr({"gk": gk, "tk": tk}[sys.argv[2]](int(sys.argv[3]))))
        sys.exit()
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    ok = all(check(gk(k), 2 ** (2 * k - 1)) for k in (1, 2, 3))
    ok &= all(check(tk(k), 4 ** k) for k in (1, 2))
    rng = random.Random(0)
    worst = (0, None)
    for _ in range(200):
        n = rng.randint(2, 12)
        leaves = list(range(n))
        rng.shuffle(leaves)
        f = random_formula(leaves, rng)
        ok &= check(f, n)
        delta = run(f)[1]
        worst = max(worst, (delta / (T[f] + TD[f]), (n, T[f] + TD[f], delta)))
    print("simulation agrees with fk_a and fk_a_memo:", ok)
    print("random formulas: max delta/N = %.3f at (n, N, delta) = %s" % worst)
    print("\n family     n   connectives           N                tau      delta")
    for name, f, n in [(f"gk-f{k}", gk(k), 2 ** (2 * k - 1)) for k in range(1, kmax + 1)] + \
            [(f"tk-s{k}", tk(k), 4 ** k) for k in range(1, kmax)]:
        tau, delta = run(f)
        print(f" {name:7s} {n:5d} {n - 1:11d} {T[f] + TD[f]:11d} {tau:18d} {delta:10d}", flush=True)

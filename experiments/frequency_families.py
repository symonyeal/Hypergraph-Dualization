"""Conjecture 6 of docs/frequency-constant.md on two families of dual pairs.

A dual pair enters only through (A, B, s, t):
    A, B : numbers of terms and clauses (minterms and maxterms)
    s, t : 1/eps_C and 1/eps_D, reciprocal largest term and clause frequencies
    defect = log2 A + log2 B + 3 - 3 min(s, t); Conjecture 6 said defect >= 0.
    Proposition 7 refutes it on 36 variables.

Substitution T[G_0, ..., G_{m-1}] on disjoint supports (research Theorem 5.1) gives
    A = sum_{e in T} prod_{i in e} A_i,   B = sum_{e in Tr T} prod_{i in e} B_i,
    eps_C = max_i eps_C(G_i) * sum_{e in T, e ni i} prod_{j in e} A_j / A,
and the dual formula for eps_D, so the four numbers of a nested substitution follow
from its pieces. OR and AND are the templates {{0},{1}} and {{0,1}}.

closure N  : every read-once formula with at most N leaves (exact); also the least
             slack of the two-parameter form Q, failed route 4 of the note.
compose K S: K random nested substitutions of prime templates (P4, K3, Fano, the Witt
             design w11, threshold 2-of-4) and AND/OR, seed S, in log space.
Usage: python experiments/frequency_families.py closure 13
       python experiments/frequency_families.py compose 20000 1
"""
import random
import sys
from fractions import Fraction
from itertools import combinations
from math import log2
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from fka.hypergraph import Hypergraph  # noqa: E402
from fka.instances import witt_11  # noqa: E402
from fka.selfdual import fano  # noqa: E402
from fka.transversal import transversal  # noqa: E402


def gate(g, h, op):
    (Ag, Bg, sg, tg), (Ah, Bh, sh, th) = g, h
    if op == "|":
        A = Ag + Ah
        return A, Bg * Bh, min(sg * Fraction(A, Ag), sh * Fraction(A, Ah)), min(tg, th)
    B = Bg + Bh
    return Ag * Ah, B, min(sg, sh), min(tg * Fraction(B, Bg), th * Fraction(B, Bh))


def closure(N):
    """{leaves: {(A, B, s, t): formula}} over all read-once formulas with that many leaves."""
    layers = {1: {(1, 1, Fraction(1), Fraction(1)): "x"}}
    for n in range(2, N + 1):
        layers[n] = {}
        for i in range(1, n // 2 + 1):
            for g, fg in layers[i].items():
                for h, fh in layers[n - i].items():
                    for op in "|&":
                        layers[n].setdefault(gate(g, h, op), f"({fg}{op}{fh})")
    return layers


def Q(a, b, s, t):
    """Two-parameter guess: (s/t) a + b >= 3s - 3 + log2(t/s) for s <= t, and its mirror."""
    if s > t:
        a, b, s, t = b, a, t, s
    return (s / t) * a + b - (3 * s - 3 + log2(t / s))


def templates():
    """name -> (m, T, Tr T) as bitmasks; each Tr T computed, never typed."""
    raw = {
        "or2": Hypergraph.from_sets(2, [(0,), (1,)]),
        "and2": Hypergraph.from_sets(2, [(0, 1)]),
        "or3": Hypergraph.from_sets(3, [(0,), (1,), (2,)]),
        "and3": Hypergraph.from_sets(3, [(0, 1, 2)]),
        "P4": Hypergraph.from_sets(4, [(0, 1), (1, 2), (2, 3)]),
        "K3": Hypergraph.from_sets(3, combinations(range(3), 2)),
        "fano": fano(),
        "w11": witt_11(),
        "th2of4": Hypergraph.from_sets(4, combinations(range(4), 2)),
    }
    return {name: (T.n, T.edges, transversal(T).edges) for name, T in raw.items()}


def substitute(tmpl, kids):
    """(logA, logB, epsC, epsD) of T[kids] from the kids' tuples, in log space."""
    m, T, Td = tmpl

    def side(edges, logs, eps):
        w = [sum(logs[i] for i in range(m) if e >> i & 1) for e in edges]
        top = max(w)
        tot = top + log2(sum(2 ** (x - top) for x in w))
        share = [sum(2 ** (w[k] - tot) for k, e in enumerate(edges) if e >> i & 1) for i in range(m)]
        return tot, max(eps[i] * share[i] for i in range(m))

    a, ec = side(T, [k[0] for k in kids], [k[2] for k in kids])
    b, ed = side(Td, [k[1] for k in kids], [k[3] for k in kids])
    return a, b, ec, ed


def random_pair(rng, T, depth):
    """A nested substitution of the given depth; with probability 0.7 all points of a
    template receive one shared child (the tensor structure, which drives eps down)."""
    if depth == 0 or rng.random() < 0.05:
        return (0.0, 0.0, 1.0, 1.0)
    name = rng.choice(list(T))
    m = T[name][0]
    kids = [random_pair(rng, T, depth - 1)] * m if rng.random() < 0.7 else [random_pair(rng, T, depth - 1) for _ in range(m)]
    return substitute(T[name], kids)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "closure"
    if mode == "closure":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
        rows = [(n, k, form) for n, layer in closure(N).items() for k, form in layer.items()]
        defect = min((log2(A) + log2(B) + 3 - 3 * float(min(s, t)), n, form) for n, (A, B, s, t), form in rows)
        q = min((Q(log2(A), log2(B), float(s), float(t)), n, form) for n, (A, B, s, t), form in rows)
        rmax = max(float(min(s, t)) for _, (_, _, s, t), _ in rows)
        print(f"read-once tuples with <= {N} leaves: {len(rows)}; largest 1/eps: {rmax:.4f}")
        print(f"least defect {defect[0]:.6f} at {defect[1]} leaves: {defect[2]}")
        print(f"least Q slack {q[0]:.6f} at {q[1]} leaves: {q[2]}")
    elif mode == "compose":
        K, seed = int(sys.argv[2]), int(sys.argv[3])
        T, rng = templates(), random.Random(seed)
        least, rmax, below = (9e9, None), 0.0, 0
        for _ in range(K):
            a, b, ec, ed = random_pair(rng, T, rng.choice([5, 6, 7, 8]))
            r = 1 / max(ec, ed)
            d = a + b + 3 - 3 * r
            rmax = max(rmax, r)
            below += d < -1e-9
            if r > 3 and d / r < least[0]:
                least = (d / r, (round(a, 2), round(b, 2), round(r, 2)))
        print(f"{K} nested substitutions, seed {seed}: largest 1/eps {rmax:.1f}; pairs with defect < 0: {below}")
        print(f"least defect*eps over 1/eps > 3: {least[0]:.4f} at (log2 A, log2 B, 1/eps) = {least[1]}")
    else:
        raise SystemExit(f"unknown mode {mode!r}")

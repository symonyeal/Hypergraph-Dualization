"""Read-once dual pairs against the product bound |C||D| >= 8^{1/eps - 1}.
See docs/frequency-constant.md, Proposition 7 and Theorem 8.

check      : the counterexample T6 = AND2(OR3(AND3(OR2))) on 36 variables, built as an
             explicit hypergraph; Tr computed by fka.transversal, duality confirmed by
             FK-A, |C|, |D| and every frequency recounted (about two minutes).
templates M R : symmetric templates, gates AND_m / OR_m alternating, m <= M, rank <= R.
             Bottom-up, AND_m: (a, b) -> (m a, b + log2 m), OR_m: (a + log2 m, m b),
             a, b = log2 |C|, log2 |D|; terms and clauses have r = prod of the AND and
             of the OR arities. Iterating a template gives eps log2(|C||D|) ->
             (a + b)/(r - 1) and eps log2 max(|C|, |D|) -> max(a, b)/(r - 1).
split      : Theorem 8's split inequality (b) for Psi on a log grid in (0.001, 1000)^3.
closure N  : Theorem 8 on every read-once formula with at most N leaves.
Usage: python experiments/frequency_readonce.py check | templates 6 400 | split | closure 13
"""
import sys
from fractions import Fraction
from itertools import product
from math import log, log2
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "experiments"))

from fka.algorithm import is_dual
from fka.hypergraph import Hypergraph
from fka.transversal import transversal
from frequency_families import closure as layers

c = 2 / log(2)


def G(s, t):
    """Theorem 8's bound on log2|C|/t + log2|D|/s for s, t >= 1."""
    m, M = min(s, t), max(s, t)
    return c * (1 - 1 / m) + log2(M / m) / m


def check():
    var = {key: n for n, key in enumerate(product(range(2), range(3), range(3), range(2)))}
    terms = [{var[(0, j0, i, l[i])] for i in range(3)} | {var[(1, j1, i, l[3 + i])] for i in range(3)}
             for j0, j1 in product(range(3), repeat=2) for l in product(range(2), repeat=6)]
    C = Hypergraph.from_sets(36, terms)
    D = transversal(C)
    A, B = len(C), len(D)
    freqs = {Fraction(C.degree(v), A) for v in range(36)} | {Fraction(D.degree(v), B) for v in range(36)}
    eps = max(freqs)
    print(f"|C|={A} |D|={B} frequencies={sorted(freqs)} edge sizes={sorted(set(C.edge_sizes()) | set(D.edge_sizes()))}")
    print(f"|C||D|={A * B} < 8^(1/eps-1)={8 ** int(1 / eps - 1)}: {A * B < 8 ** int(1 / eps - 1)}; "
          f"defect={log2(A * B) + 3 - 3 / eps:.6f}; FK-A dual: {is_dual(D, C)}")


def templates(M, R):
    best = {}

    def grow(seq, a, b, p, q, last):
        if p == q > 1:
            for key, v in (("product", (a + b) / (p - 1)), ("max", max(a, b) / (p - 1))):
                if v < best.get(key, (9e9,))[0]:
                    best[key] = (v, p, seq)
        for m in range(2, M + 1):
            if last != "&" and p * m <= R:
                grow(seq + f" &{m}", m * a, b + log2(m), p * m, q, "&")
            if last != "|" and q * m <= R:
                grow(seq + f" |{m}", a + log2(m), m * b, p, q * m, "|")

    grow("", 0.0, 0.0, 1, 1, "")
    for key, (v, r, seq) in best.items():
        print(f"least {key} rate {v:.6f} at r={r}, bottom-up:{seq}")


def split():
    def Psi(x, y):
        X, Y = np.maximum(x, 1.0), np.maximum(y, 1.0)
        m, M = np.minimum(X, Y), np.maximum(X, Y)
        return X * Y * (c * (1 - 1 / m) + np.log2(M / m) / m)

    g = np.exp(np.linspace(np.log(1e-3), np.log(1e3), 300))
    x1, x2, y = np.meshgrid(g, g, g, indexing="ij")
    x = x1 + x2
    gap = Psi(x, y) - Psi(x1, y) - Psi(x2, y) - x1 * np.log2(x / x1) - x2 * np.log2(x / x2)
    rel = gap / np.maximum(1.0, Psi(x, y))
    print(f"split inequality (b): largest relative violation {rel.max():.2e} over {rel.size} points")


def closure(N):
    worst = min((log2(A) / float(t) + log2(B) / float(s) - G(float(s), float(t)), form)
                for layer in layers(N).values() for (A, B, s, t), form in layer.items())
    print(f"read-once formulas with <= {N} leaves: least slack of Theorem 8 {worst[0]:.6f} at {worst[1]}")


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    if mode == "check":
        check()
    elif mode == "templates":
        templates(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == "split":
        split()
    elif mode == "closure":
        closure(int(sys.argv[2]))
    else:
        raise SystemExit(f"unknown mode {mode!r}")

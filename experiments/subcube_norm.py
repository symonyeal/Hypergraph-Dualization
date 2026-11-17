"""Subcube norm of the alternating trees GK f_k and TK S_k (docs/complex-evaluation.md §4).

Legend
  Q        : subcube of {0,1}^v, a partial assignment
  mu       : integer measure on a block's cube with mu(cube) = 1 and |mu(Q)| <= 1 for every Q
  N1, N0   : least sum |y_Q| over representations 1_{F=1} (resp. 1_{F=0}) = sum_Q y_Q 1_Q
  u_k      : rho^{(x)}(f_k = 1) for the product of f_2 measures rho; u_2 = 10, u_{k+1} = u_k^2 (2 - u_k^2)

check     : checks nu (OR), nu x nu and sigma (S_1), rho (f_2) on every subcube in exact integers;
            prints log2|u_k|/v and log2 of the upper bound on N1 (>= N0), over v, for k <= 8.
lp GATES  : partition LP and N1, N0 reduced by symmetry; GATES from the leaves up:
            "|&|" is GK f_2 (a second), "|&|&" is TK S_2 (about three minutes).
Usage: python experiments/subcube_norm.py check | lp "|&|"
"""
import sys
from math import log2

import numpy as np

NU = [-1, 1, 1, 0]                                                # OR(x0, x1): nu(OR = 1) = 2
SIGMA = [-1, 1, 1, 0, 1, 0, -1, 0, 1, -1, -1, 0, 0, 0, 0, 1]      # S_1: sigma(S_1 = 1) = -2


def masses(mu, n):
    """mu(Q) for all 3^n subcubes (index 2 on an axis: coordinate free)."""
    g = np.array(mu, dtype=np.int64).reshape((2,) * n)
    for ax in range(n):
        g = np.concatenate([g, g.sum(axis=ax, keepdims=True)], axis=ax)
    return g


def lg(x):
    """log2 of a positive integer of any size."""
    b = max(x.bit_length() - 60, 0)
    return b + log2(x >> b)


def check():
    OR = lambda x: int(x & 3 > 0)
    S1 = lambda x: OR(x) & OR(x >> 2)
    f2 = lambda x: S1(x) | S1(x >> 4)
    mu4 = [NU[x & 3] * NU[x >> 2] for x in range(16)]
    rho = [mu4[x & 15] * SIGMA[x >> 4] for x in range(256)]
    for name, mu, n, F in (("nu, OR", NU, 2, OR), ("nu x nu, S_1", mu4, 4, S1),
                           ("sigma, S_1", SIGMA, 4, S1), ("rho, f_2", rho, 8, f2)):
        g = masses(mu, n)
        print(f"{name}: total {sum(mu)}, mu(F=1) = {sum(m for x, m in enumerate(mu) if F(x))}, "
              f"max |mu(Q)| over {g.size} subcubes = {np.abs(g).max()}")
    u, N1, N0 = 10, 10, 9
    for k in range(3, 9):
        v = 2 ** (2 * k - 1)
        u = u * u * (2 - u * u)
        a1, a0 = N1 * N1, min(1 + N1 * N1, N0 + N1 * N0)        # AND(f_{k-1}, f_{k-1})
        N1, N0 = min(1 + a0 * a0, a1 + a0 * a1), a0 * a0         # OR of two such
        print(f"f_{k}: v={v:5d}  log2|u|/v = {lg(abs(u)) / v:.10f}  log2(|u| + |1-u|)/v = "
              f"{lg(abs(u) + abs(1 - u)) / v:.10f}  log2 N1/v <= {lg(N1) / v:.10f}")


def build(gates):
    """Point types (value, orbit size) and incidence n[Q, P] of the balanced binary tree."""
    val, size = np.array([0, 1]), np.array([1, 1])
    n = np.array([[1, 0], [0, 1], [1, 1]])            # subcube types: 0, 1, free
    for op in gates:
        P, S = len(val), len(n)
        iu = np.triu_indices(P)
        val = (np.minimum if op == "&" else np.maximum)(val[iu[0]], val[iu[1]])
        size = np.where(iu[0] == iu[1], 1, 2) * size[iu[0]] * size[iu[1]]
        rows = []
        for a in range(S):
            M = np.einsum("i,bj->bij", n[a], n[a:])   # n[a, i] n[b, j] for b >= a
            T = M + M.transpose(0, 2, 1)
            T[:, np.arange(P), np.arange(P)] = M[:, np.arange(P), np.arange(P)]
            rows.append(T[:, iu[0], iu[1]])
        n = np.vstack(rows)
    return val, size, n


def lp(gates):
    from scipy.optimize import linprog

    val, size, n = build(gates)
    has1, has0 = (n * val > 0).any(1), (n * (1 - val) > 0).any(1)
    mono = ~(has1 & has0)
    free = (None, None)
    part = -linprog(-size, A_ub=n[mono], b_ub=np.ones(mono.sum()), bounds=free).fun
    A, b = np.vstack([n, -n]), np.ones(2 * len(n))
    N1 = -linprog(-size * val, A_ub=A, b_ub=b, bounds=free).fun
    N0 = -linprog(-size * (1 - val), A_ub=A, b_ub=b, bounds=free).fun
    print(f"{gates}: {int(size.sum()).bit_length() - 1} variables, {len(val)} point types, "
          f"{len(n)} subcube types ({mono.sum()} monochromatic)\n"
          f"  partition LP = {part:.4f}  N1 = {N1:.4f}  N0 = {N0:.4f}")


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "lp":
        lp(sys.argv[2])
    else:
        check()

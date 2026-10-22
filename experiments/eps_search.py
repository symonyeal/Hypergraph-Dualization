"""Is eps(n) < p/q?  (research track B, Observation 5.2.3)

Usage (from the repository root): python experiments/eps_search.py [n p q] [--cnf FILE]

eps(G, H) = max_v max(deg_G v / |G|, deg_H v / |H|) for a transversal pair H = Tr(G) with
both sides nonempty and no empty edge; eps(n) is its minimum over pairs on n points.

Model (0/1 program on the truth table of a monotone f : {0,1}^n -> {0,1}, 2^n variables):
  f(x) <= f(x + i)                                       monotone
  f(0) = 0, f(1...1) = 1                                 G, H nonempty, no empty edge
  m(x) <-> f(x) and not f(x - i) for all i in x          x is an edge of G (a minterm)
  h(x) <-> not f(~x) and f(~x + i) for all i in x         x is an edge of H = Tr(G)
  q deg_G(v) <= p |G| - 1, q deg_H(v) <= p |H| - 1       every frequency below p/q
  deg_G(0) >= deg_G(1) >= ... >= deg_G(n-1)              symmetry breaking (relabel by S_n)
Feasible: a pair with eps < p/q, checked against the transversal oracle. Infeasible: no pair
on n points has eps < p/q (by CP-SAT; not a Lean certificate).
Without arguments, runs the table n = 3..8 at the thesis' bounds. The verdicts are
deterministic; with 8 workers a feasible witness can differ between runs.
"""
import sys
from fractions import Fraction
from pathlib import Path

from ortools.sat.python import cp_model

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from fka.hypergraph import Hypergraph  # noqa: E402
from fka.transversal import transversal  # noqa: E402


def eps(G, H, n):
    """G, H as lists of bitmasks."""
    return max(Fraction(sum(e >> v & 1 for e in F), len(F)) for F in (G, H) for v in range(n))


def model(n, p, q):
    N, M = 1 << n, cp_model.CpModel()
    f = [M.new_bool_var(f"f{x}") for x in range(N)]
    m = [M.new_bool_var(f"m{x}") for x in range(N)]
    h = [M.new_bool_var(f"h{x}") for x in range(N)]
    for x in range(N):
        for i in range(n):
            if not x >> i & 1:
                M.add_implication(f[x], f[x | 1 << i])
    M.add(f[0] == 0)
    M.add(f[N - 1] == 1)
    for x in range(N):
        I = [i for i in range(n) if x >> i & 1]
        lit_m = [f[x]] + [f[x ^ 1 << i].Not() for i in I]          # minterm of f
        lit_h = [f[~x & N - 1].Not()] + [f[~x & N - 1 | 1 << i] for i in I]   # minterm of f^d
        for y, L in ((m[x], lit_m), (h[x], lit_h)):
            M.add_bool_and(L).only_enforce_if(y)
            M.add_bool_or([l.Not() for l in L]).only_enforce_if(y.Not())
    for F in (m, h):
        size = sum(F)
        for v in range(n):
            M.add(q * sum(F[x] for x in range(N) if x >> v & 1) <= p * size - 1)
    deg = [sum(m[x] for x in range(N) if x >> v & 1) for v in range(n)]
    for v in range(n - 1):
        M.add(deg[v] >= deg[v + 1])
    return M, f, m


def solve(n, p, q):
    M, _, m = model(n, p, q)
    S = cp_model.CpSolver()
    S.parameters.num_workers, S.parameters.random_seed = 8, 0
    st = S.solve(M)
    if st == cp_model.INFEASIBLE:
        return "infeasible", None, S.wall_time
    if st not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        return S.status_name(st), None, S.wall_time
    G = [x for x in range(1 << n) if S.value(m[x])]
    H = list(transversal(Hypergraph.from_bitsets(n, G)))
    return "feasible", (G, H, eps(G, H, n)), S.wall_time


if __name__ == "__main__":
    cases = [tuple(map(int, sys.argv[1:4]))] if len(sys.argv) >= 4 else \
        [(3, 2, 3), (4, 1, 2), (5, 1, 2), (6, 1, 2), (7, 1, 2), (7, 3, 7), (8, 2, 5)]
    for n, p, q in cases:
        status, w, t = solve(n, p, q)
        print(f"n = {n}, eps < {p}/{q}: {status}  ({t:.1f} s)")
        if w:
            G, H, e = w
            print(f"  |G| = {len(G)}, |Tr G| = {len(H)}, eps = {e}")
            print("  G =", [[i for i in range(n) if g >> i & 1] for g in G])

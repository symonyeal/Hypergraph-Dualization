"""experiments/readonce_dag's class counts against iso_memo.py and an orbit oracle.

Skipped when the Rust binary is not built (`cargo build --release` in experiments/readonce_dag).

Legend
  S, t     live set and orientation of an FK-A node: g = h or h^d, h = f pruned to S
  canon    lexicographically least image of S's marks under the automorphisms of a complete
           binary tree: the sorted concatenation of the children's canons
"""

import subprocess
import sys
from itertools import permutations
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
import iso_memo as im  # noqa: E402

rs = im.rs
EXE = ROOT / "experiments" / "readonce_dag" / "target" / "release" / "readonce_dag"
EXE = EXE.with_suffix(".exe") if EXE.with_suffix(".exe").exists() else EXE
pytestmark = pytest.mark.skipif(not EXE.exists(), reason="readonce_dag not built")
FLAG = {"degree_sum": [], "leftmost": ["--leftmost"], "guarded": ["--guarded"]}
CASES = [(rs.gk, 1), (rs.gk, 2), (rs.gk, 3), (rs.tk, 1), (rs.tk, 2), (rs.tk, 3)]


def rust(f, *args):
    out = subprocess.run([str(EXE), *args], input=rs.sexpr(f), capture_output=True, text=True,
                         check=True).stdout
    return [list(map(int, ln.split()[1:] if ln.startswith("blocks") else ln.split()))
            for ln in out.splitlines()]


def reached(f, rule):
    seen, st = set(), [f]
    while st:
        g = st.pop()
        if g not in seen:
            seen.add(g)
            if not im.leaf(g):
                st.extend(im.kids(g, rule))
    return seen


def top_op(f, S):
    """The operator at the top of f pruned to S (unary gates collapsed)."""
    while rs.OP[f] != 'v':
        live = [k for k in rs.KIDS[f] if rs.MASK[k] & S]
        if len(live) > 1:
            return rs.OP[f]
        f = live[0]
    return 'v'


def canon(f, S):
    if rs.OP[f] == 'v':
        return "1" if rs.MASK[f] & S else "0"
    return "".join(sorted(canon(k, S) for k in rs.KIDS[f]))


def node(f, g):
    """(S, t) of the reached formula g, or the constant."""
    S = rs.MASK[g]
    if S == 0:
        return ("const", g)
    return (S, rs.OP[g] != top_op(f, S) and bin(S).count("1") > 1)


@pytest.mark.parametrize("rule", list(FLAG))
@pytest.mark.parametrize("family,k", CASES)
def test_counts_match_iso_memo(rule, family, k):
    f = family(k)
    delta, d_shp = im.exact(f, rule)
    (_, _, rd, rshp, raut, rtau), _ = rust(f, "--classes", *FLAG[rule])
    assert rust(f, "--delta-only", *FLAG[rule])[0][2] == rd == delta
    assert rust(f, *FLAG[rule])[0][3] == rtau == rs.run(f, rule)[0]
    assert rshp == d_shp
    assert rust(f, "--iso", *FLAG[rule])[0][2] == im.iso(f, rule)
    R = {node(f, g) for g in reached(f, rule)}
    assert len(R) == delta
    orbits = {nd if nd[0] == "const" else (canon(f, nd[0]), nd[1]) for nd in R}
    assert raut == len(orbits)
    assert rshp <= raut <= rd


def test_orbits_by_group_enumeration():
    """TK S2: Aut of the DNF hypergraph is the tree's 2^15 automorphisms; orbits counted by
    applying every element to every reached node."""
    f, n = rs.tk(2), 16
    gens = []

    def swaps(g):
        if rs.OP[g] == 'v':
            return
        a, b = rs.KIDS[g]
        la = [x for x in range(n) if rs.MASK[a] >> x & 1]
        lb = [x for x in range(n) if rs.MASK[b] >> x & 1]
        p = list(range(n))
        for x, y in zip(la, lb):
            p[x], p[y] = y, x
        gens.append(tuple(p))
        swaps(a)
        swaps(b)

    swaps(f)
    G = {tuple(range(n))}
    frontier = list(G)
    while frontier:
        new = []
        for p in frontier:
            for q in gens:
                r = tuple(q[p[i]] for i in range(n))
                if r not in G:
                    G.add(r)
                    new.append(r)
        frontier = new
    assert len(G) == 2 ** 15

    def img(p, S):
        return sum(1 << p[x] for x in range(n) if S >> x & 1)

    edges = rs.dnf(f)
    assert all({img(p, e) for e in edges} == edges for p in G)
    R = {node(f, g) for g in reached(f, "degree_sum")}
    orbits = {nd if nd[0] == "const" else min((img(p, nd[0]), nd[1]) for p in G) for nd in R}
    (_, _, _, _, raut, _), _ = rust(f, "--classes")
    assert raut == len(orbits)


def test_gk2_automorphisms_are_the_tree_swaps():
    f, n = rs.gk(2), 8
    edges = rs.dnf(f)
    auts = sum(1 for p in permutations(range(n))
               if {sum(1 << p[x] for x in range(n) if e >> x & 1) for e in edges} == edges)
    assert auts == 2 ** 7

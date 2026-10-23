"""Joint projections and guarded diagnostics against the formula engine.

Legend: f,g formula nodes; R reached formulas; S support; a,c top blocks;
xs block labels; A,C projected supports; P joint pairs; T standalone targets;
q JSON record; lv counts by live-support size; dc,dd degrees of the two sides.
"""
import json
import subprocess
from collections import defaultdict
from pathlib import Path

import pytest

from test_readonce_dag import EXE, FLAG, im, reached, rs

pytestmark = pytest.mark.skipif(not EXE.exists(), reason="readonce_dag not built")


def probe(f, *args):
    p = subprocess.run([str(EXE), *args], input=rs.sexpr(f), text=True,
                       capture_output=True, check=True, timeout=30)
    return [json.loads(ln) for ln in p.stdout.splitlines()]


def norm(S, xs):
    return sum(1 << i for i, x in enumerate(xs) if S >> x & 1)


@pytest.mark.parametrize("family,k", [(rs.gk, 2), (rs.gk, 3), (rs.tk, 2), (rs.tk, 3)])
@pytest.mark.parametrize("rule", list(FLAG))
def test_joint_against_formula_states(family, k, rule):
    f = family(k)
    a, c = [rs.KIDS[h][0] for h in rs.KIDS[f]]
    xs = [[x for x in range(rs.MASK[f].bit_length()) if rs.MASK[h] >> x & 1]
          for h in (a, c)]
    R = reached(f, rule)
    P = {(norm(rs.MASK[g], xs[0]), norm(rs.MASK[g], xs[1])) for g in R if rs.MASK[g]}
    T = {norm(rs.MASK[g], xs[0]) for g in reached(a, rule) if rs.MASK[g]}
    A, C = {a for a, c in P}, {c for a, c in P}
    q = probe(f, "--joint", *FLAG[rule])
    j = next(r for r in q if r["kind"] == "joint")
    assert T and P
    assert j == dict(kind="joint", targets=len(T), a_states=len(A), c_states=len(C),
                     pairs=len(P), a_hits=len(T & A), c_hits=len(T & C),
                     pair_hits=len(P & {(a, c) for a in T for c in T}),
                     pair_missing=sum((a, c) not in P for a in T for c in T))
    assert q[-1]["delta"] == len(R)
    if j["pair_missing"]:
        w = next(r for r in q if r["kind"] == "missing")
        a, c = [sum(1 << x for x in w[s]) for s in ("a", "c")]
        assert a in T and c in T and (a, c) not in P
    eq = defaultdict(lambda: dict(targets=0, pairs=0, hits=0))
    for a in T:
        e = eq[a.bit_count()]
        e["targets"] += 1
        for c in T:
            if c.bit_count() == a.bit_count():
                e["pairs"] += 1
                e["hits"] += (a, c) in P
    got = {r["size"]: {k: r[k] for k in ("targets", "pairs", "hits")}
           for r in q if r["kind"] == "equal_size"}
    assert got == dict(eq)
    w = [r for r in q if r["kind"] == "equal_size_missing"]
    assert bool(w) == any(e["hits"] < e["pairs"] for e in eq.values())
    if w:
        a, c = [sum(1 << x for x in w[0][s]) for s in ("a", "c")]
        assert a in T and c in T and a.bit_count() == c.bit_count() and (a, c) not in P


@pytest.mark.parametrize("family,k", [(rs.gk, 3), (rs.gk, 4), (rs.tk, 3), (rs.tk, 4)])
def test_guard_trace_against_formula_degrees(family, k):
    f = family(k)
    R = reached(f, "guarded")
    lv = defaultdict(lambda: dict(nodes=0, splits=0, leftmost_ineligible=0,
                                  fallbacks=0, diff_degree_sum=0))
    for g in R:
        if not rs.MASK[g]:
            continue
        q = lv[rs.MASK[g].bit_count()]
        q["nodes"] += 1
        if im.leaf(g):
            continue
        dc, dd = rs.degrees(g, False), rs.degrees(g, True)
        s = (rs.T[g] + rs.TD[g]).bit_length() - 1
        eligible = [x for x in dc if rs.T[g] <= s * dc[x] or rs.TD[g] <= s * dd[x]]
        q["splits"] += 1
        q["leftmost_ineligible"] += min(dc) not in eligible
        q["fallbacks"] += not eligible
        q["diff_degree_sum"] += rs.split_var(g, "guarded") != rs.split_var(g, "degree_sum")
    out = probe(f, "--guard-trace", "--guarded")
    got = {q["level"]: {k: v for k, v in q.items() if k not in ("kind", "level")}
           for q in out if q["kind"] == "level"}
    assert got == dict(lv)
    assert out[-1]["delta"] == len(R)
    assert sum(q["splits"] for q in got.values()) > 0
    assert sum(q["fallbacks"] for q in got.values()) == 0


def test_joint_rejects_false_product():
    q = next(q for q in probe(rs.gk(3), "--joint", "--leftmost") if q["kind"] == "joint")
    assert q["pair_missing"] > 0


def test_joint_crosses_mask_word():
    # TK S3 shifted across a 64-bit boundary exercises normalized block coordinates.
    q = probe(rs.tk(3, 61), "--joint")
    r = probe(rs.tk(3), "--joint")
    assert q == r


def test_gk5_first_departure_certificate():
    r = json.loads((Path(__file__).resolve().parents[1] /
                    "results/block-probes/gk5-guard.json").read_text(encoding="utf-8"))
    q = next(q for q in r["records"] if q["kind"] == "first_departure")
    assert q["support"] == list(range(18, 512))
    S = sum(1 << x for x in q["support"])

    def prune(g):
        if rs.OP[g] == 'v':
            return g
        return rs.mk(rs.OP[g], [prune(h) for h in rs.KIDS[g] if rs.MASK[h] & S])

    g = prune(rs.gk(5))
    dc, dd = rs.degrees(g, False), rs.degrees(g, True)
    s = (rs.T[g] + rs.TD[g]).bit_length() - 1
    eligible = sorted(x for x in dc if rs.T[g] <= s * dc[x] or rs.TD[g] <= s * dd[x])
    assert (q["level"], q["leftmost"], q["chosen"], q["degree_sum"]) == (494, 18, 20, 256)
    assert min(dc) == 18 and min(eligible) == 20
    assert rs.split_var(g, "degree_sum") == 256

"""Check the paired-leaf reduction against the independent hypergraph engine."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
sys.path.insert(0, str(ROOT / "src"))

import cherry_probe as cp
from fka.hypergraph import Hypergraph
from fka.memo import fk_a_memo


@pytest.mark.parametrize("k", [1, 2, 3])
def test_macro_reach_against_hypergraphs(k):
    f = cp.fm.gk(k)
    c = Hypergraph.from_bitsets(cp.fm.MASK[f].bit_count(), sorted(cp.fm.dnf(f)))
    d = Hypergraph.from_bitsets(c.n, sorted(cp.fm.dnf(cp.fm.dual(f))))
    complete, transient = cp.macro(f, 50000)
    assert complete.isdisjoint(transient)
    assert complete | transient == cp.reach(f, 50000)
    assert len(complete) + len(transient) == fk_a_memo(c, d).nodes


def test_weight_intervals_against_all_crossings():
    """A line can win only at a crossing or in a consecutive open interval."""
    for g in cp.reach(cp.fm.gk(3), 50000):
        if cp.fm.MASK[g].bit_count() <= 1:
            continue
        c, d = cp.fm.degrees(g, False), cp.fm.degrees(g, True)
        crossings = {Fraction(c[y] - c[x], d[x] - d[y])
                     for x in c for y in c if d[x] != d[y]}
        endpoints = [Fraction(0)] + sorted(z for z in crossings if z > 0)
        weights = endpoints[1:] + [(a + b) / 2 for a, b in zip(endpoints, endpoints[1:])]
        weights.append(endpoints[-1] + 1)
        actual = {min(c, key=lambda x: (-c[x] - w * d[x], x)) for w in weights}
        assert set(cp.candidates(g)) == actual


def test_local_hull_must_continue_past_singleton_edges():
    f = cp.fm.gk(1)
    assert cp.im.leaf(f)
    assert len(cp.reach(f, 20)) == 1
    relaxed = cp.hull(f, False, 100, 10)
    assert relaxed["complete"] and relaxed["supports"] == 3
    global_child = cp.im.kids(cp.fm.gk(2), "degree_sum")[0]
    assert cp.fm.MASK[global_child] & 3 == 2


def test_partial_hull_is_marked_incomplete():
    out = cp.hull(cp.fm.gk(3), False, 2, 10)
    assert out["ordered_states"] == 2
    assert not out["complete"] and out["pending"] > 0

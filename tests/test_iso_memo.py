"""Track S counts against the hypergraph engine and coloured incidence graphs."""

import random
import sys
from itertools import combinations_with_replacement
from pathlib import Path

import networkx as nx
import pytest

from fka.hypergraph import Hypergraph
from fka.memo import fk_a_memo

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
import iso_memo as im  # noqa: E402

rs = im.rs


@pytest.mark.parametrize("rule", ["degree_sum", "leftmost", "guarded"])
@pytest.mark.parametrize("family,k,n", [
    (rs.gk, 1, 2), (rs.gk, 2, 8), (rs.gk, 3, 32),
    (rs.tk, 1, 4), (rs.tk, 2, 16),
])
def test_exact_count_matches_hypergraph_engine(rule, family, k, n):
    f = family(k)
    C = Hypergraph.from_bitsets(n, rs.dnf(f))
    D = Hypergraph.from_bitsets(n, rs.dnf(rs.dual(f)))
    run = fk_a_memo(C, D, split_rule=rule)
    delta, classes = im.exact(f, rule)
    assert run.dual
    assert delta == run.nodes
    assert 1 <= im.iso(f, rule) <= classes <= delta


def test_shape_matches_pair_isomorphism():
    """An independent graph oracle checks both collisions and missed equivalences.

    All pairs use five ground vertices, retaining isolated vertices. Edge colours
    distinguish the two sides, so exchanging C and D is not an isomorphism.
    """
    rng = random.Random(0)
    fs = [rs.ZERO, rs.ONE, rs.var(0), rs.var(4), rs.gk(1), rs.tk(1)]
    for _ in range(24):
        leaves = rng.sample(range(5), rng.randint(2, 5))
        fs.append(rs.random_formula(leaves, rng))

    graphs = []
    for f in fs:
        G = nx.Graph()
        G.add_nodes_from((("v", v), {"colour": "v"}) for v in range(5))
        for side, g in [("C", f), ("D", rs.dual(f))]:
            for e in rs.dnf(g):
                G.add_node((side, e), colour=side)
                G.add_edges_from(((side, e), ("v", v)) for v in range(5) if e >> v & 1)
        graphs.append(G)

    match = nx.algorithms.isomorphism.categorical_node_match("colour", None)
    for i, j in combinations_with_replacement(range(len(fs)), 2):
        assert (im.shp(fs[i]) == im.shp(fs[j])) == nx.is_isomorphic(
            graphs[i], graphs[j], node_match=match
        ), (rs.sexpr(fs[i]), rs.sexpr(fs[j]))


def test_iso_cache_can_skip_reached_classes():
    """Label tie-breaking prevents identifying the cache count with the quotient."""
    f = rs.gk(3)
    assert im.exact(f, "degree_sum") == (369, 160)
    assert im.iso(f, "degree_sum") == 155


def test_cap_does_not_report_partial_counts(monkeypatch):
    monkeypatch.setattr(im, "CAP", 1)
    assert im.exact(rs.gk(2), "degree_sum") == (None, None)

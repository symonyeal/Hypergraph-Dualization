"""Symmetry depth: actual trees, independent isomorphism, and restriction witnesses.

Legend: C,D are input sides; A,B are deleted/contracted bitmasks; b swaps
the source sides; T is the FK-A tree; j is depth; p is a tree node.
"""
import sys
from pathlib import Path

import pytest

from fka.algorithm import fk_a
from fka.hypergraph import Hypergraph
from fka.instances import load
from fka.irredundant import irredundant

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
import symmetry_depth as sd  # noqa: E402


def case(name):
    if name == "complete":
        return sd.complete(10, 3), sd.complete(10, 8), 2, [1, 2, 4], 7
    I = load(name)
    k, a, z = (2, [1, 1, 2], 4) if name == "fano" else (4, [1, 1, 2, 3, 4], 11)
    return I.cnf, I.dnf, k, a, z


@pytest.mark.parametrize("name", ["complete", "fano", "w11"])
@pytest.mark.parametrize("rule", ["degree_sum", "leftmost", "guarded"])
@pytest.mark.parametrize("variant", ["faithful", "modified"])
def test_class_counts(name, rule, variant):
    C, D, k, a, z = case(name)
    assert sd.profile(C, D, k, rule, variant) == (a, z)


def cut(C, A, B):
    return irredundant(Hypergraph.from_bitsets(C.n, (e & ~B for e in C if not e & A))).reduced


@pytest.mark.parametrize("name", ["complete", "fano", "w11"])
@pytest.mark.parametrize("rule", ["degree_sum", "leftmost", "guarded"])
def test_normal_form_at_every_node(name, rule):
    C, D, *_ = case(name)
    T = fk_a(C, D, split_rule=rule)
    assert T.dual and T.nodes
    st = [(T.root_id, C, D, 0, 0)]
    seen = set()
    while st:
        i, E, F, A, B = st.pop()
        p = T.nodes[i]
        seen.add(i)
        assert A & B == 0
        assert (A | B).bit_count() == p.depth
        assert p.depth == 0 or A != 0
        assert (cut(E, A, B), cut(F, B, A)) == (p.cnf, p.dnf)
        if p.children:
            x = 1 << p.split_var
            assert not x & (A | B)
            assert len(p.children) == 2
            st.append((p.children[0], E, F, A | x, B))
            st.append((p.children[1], F, E, B | x, A))
    assert seen == set(T.nodes)


def test_oracle_preserves_orientation_and_ignores_labels():
    C, D = sd.complete(10, 3), sd.complete(10, 8)
    assert sd.classes([(C, D), (D, C)]) == 2
    E = Hypergraph.from_sets(4, [(0, 1), (1, 2)])
    F = Hypergraph.from_sets(4, [(1,), (0, 2)])
    E1 = Hypergraph.from_sets(4, [(3, 2), (2, 1)])
    F1 = Hypergraph.from_sets(4, [(2,), (3, 1)])
    assert sd.classes([(E, F), (E1, F1)]) == 1


def test_original_assignment_count_does_not_determine_orientation():
    C, D, *_ = case("complete")
    T = fk_a(C, D)
    P = {p.path: p for p in T.nodes.values()}
    # LR fixes original bits 01; RR fixes 10. Both contract one original
    # variable, but the first has swapped sides and the second has not.
    assert {e.bit_count() for e in P[("L", "R")].cnf} == {7}
    assert {e.bit_count() for e in P[("R", "R")].cnf} == {2}

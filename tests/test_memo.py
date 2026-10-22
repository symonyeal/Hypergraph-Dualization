"""The subproblem DAG: agreement, the closed forms, and the separation.

`docs/tree-vs-dag.md` is the reading; these are the claims it rests on.
"""

from __future__ import annotations

import sys

import pytest

from fka.algorithm import fk_a
from fka.instances import (gk, list_ids, load, matching, template_word,
                           threshold, tk)
from fka.hypergraph import Hypergraph
from fka.memo import dag_size, fk_a_memo
from fka.transversal import is_dual_oracle, transversal

sys.setrecursionlimit(100000)

LIBRARY = list_ids()


@pytest.mark.parametrize("instance_id", LIBRARY)
def test_memo_agrees_with_tree_and_oracle(instance_id):
    """Same verdict as FK-A and as Berge, and ``delta`` is the tree's DAG.

    Memoising may not change what is decided: the verdict at a node is a
    function of its irredundant pair alone.
    """
    inst = load(instance_id)
    tree = fk_a(inst.cnf, inst.dnf, variant="modified")
    run = fk_a_memo(inst.cnf, inst.dnf)
    assert run.dual == tree.dual == is_dual_oracle(inst.cnf, inst.dnf)
    assert run.nodes == dag_size(tree)
    assert run.nodes <= len(tree)


@pytest.mark.slow
@pytest.mark.parametrize("variant", ["faithful", "modified"])
@pytest.mark.parametrize("split_rule", ["degree_sum", "frequency"])
def test_memo_agrees_under_every_configuration(variant, split_rule):
    """The identity is not an artifact of one base case or one pivot rule."""
    for instance_id in LIBRARY:
        inst = load(instance_id)
        tree = fk_a(inst.cnf, inst.dnf, variant=variant, split_rule=split_rule)
        run = fk_a_memo(inst.cnf, inst.dnf, variant=variant,
                        split_rule=split_rule)
        assert run.dual == tree.dual, instance_id
        assert run.nodes == dag_size(tree), instance_id


@pytest.mark.parametrize("v", [8, 10, 12, 14, 16, 18, 20])
def test_matching_closed_forms(v):
    """``tau = 2^(v/2+1) - 3`` against ``delta = v``.

    The tree is exponential in ``v`` and the DAG is linear, so the separation
    is unbounded on a family `docs/fk-a-vs-fk-b.md` §6 called output-bound.
    Deciding duality here never needs the exponential ``Tr``.
    """
    C = matching(v)
    D = transversal(C)
    assert len(D) == 2 ** (v // 2)
    assert len(fk_a(C, D, variant="modified")) == 2 ** (v // 2 + 1) - 3
    assert fk_a_memo(C, D).nodes == v


@pytest.mark.parametrize("v", [8, 10, 12, 14, 16, 18, 20])
def test_threshold_has_no_redundancy(v):
    """``tau = delta = v - 1``: the one family whose tree repeats nothing.

    It is also the one instance class where FK-B loses, which is the same fact
    -- there is no redundancy for either mechanism to remove.
    """
    C = threshold(v)
    D = transversal(C)
    assert len(fk_a(C, D, variant="modified")) == v - 1
    assert fk_a_memo(C, D).nodes == v - 1


def test_alternating_trees_separate():
    """The published hard families are hard for the tree, not for the DAG."""
    C = gk(3)
    D = transversal(C)
    tree = fk_a(C, D, variant="modified")
    run = fk_a_memo(C, D)
    assert len(tree) == 103377
    assert run.nodes == 369
    assert len(tree) / run.nodes > 250

    S = tk(2)
    assert len(fk_a(S, transversal(S), variant="modified")) == 481
    assert fk_a_memo(S, transversal(S)).nodes == 34


def test_word_dag_is_reachable_where_the_tree_is_not():
    """``delta`` is observable on a word whose tree is not enumerable.

    ``word-xxy`` is 64 variables and ``N = 3072``; the shorter ``word-xy`` at
    ``N = 48`` already unfolds to 577 nodes.
    """
    C, D = template_word("XXY"), template_word("YYX")
    run = fk_a_memo(C, D)
    assert run.dual is True
    assert run.nodes == 2973
    assert run.nodes < len(C) + len(D)


@pytest.mark.slow
def test_delta_stays_linear_on_random_dual_pairs(rng):
    """``delta <= 2N`` on small random dual pairs (n <= 11).

    Not a law: it fails on the read-once pair ``ro12`` on 12 points
    (``test_ro12_exceeds_2N``) and on ``gk-f4``.
    """
    from conftest import random_sperner

    measured = 0
    while measured < 60:
        n = rng.randint(6, 11)
        H = random_sperner(n, rng.randint(3, 12), rng)
        if not len(H):
            continue
        D = transversal(H)
        if not len(D) or len(D) > 200:
            continue
        run = fk_a_memo(D, H)
        assert run.dual is True
        assert run.nodes <= 2 * (len(D) + len(H))
        measured += 1


def test_ro12_exceeds_2N():
    """The read-once pair of ``Blowup.ro12_delta``: ``tau = 59``, ``delta = 43 > 2N = 42``.

    ``g(0,6,4,8,2,9) | g(1,7,5,11,10,3)``, ``g = (a | b) & (c | (d & (e | f)))``.
    """
    C = Hypergraph.from_sets(12, [{0, 2, 8}, {0, 4}, {0, 8, 9}, {1, 3, 11}, {1, 5}, {1, 10, 11},
                                   {2, 6, 8}, {3, 7, 11}, {4, 6}, {5, 7}, {6, 8, 9}, {7, 10, 11}])
    D = transversal(C)
    run = fk_a_memo(C, D)
    assert run.dual is True
    assert len(fk_a(C, D, variant="modified")) == 59
    assert (len(C), len(D), run.nodes) == (12, 9, 43)

"""FK-A's subproblem DAG: the same recursion, memoised on ``(n, C, D)``.

The thesis measures FK-A by its recursion tree -- "the performance of FK-A is
determined by the number of subproblems it generates, and this is reflected in
the number of nodes of the recursion tree" (p.12). The two clauses are not the
same quantity. Write

    tau(C, D)   nodes of the recursion tree, :func:`fka.algorithm.fk_a`
    delta(C, D) *distinct* subproblems among them -- the tree's DAG

A node's verdict is a function of its irredundant pair alone, and the
short-circuit is deterministic (the right child is entered iff the left returned
dual), so unfolding the DAG gives back exactly the tree and ``delta <= tau``.
:func:`fk_a_memo` runs the identical recursion -- same Step 1 reduction, same
conditions, same trivial cases, same split rule -- with a transposition table,
so it visits each distinct subproblem once and its node count *is* ``delta``.

Two reasons this is the module and not a flag on :func:`fka.algorithm.fk_a`.
The tree is the published object and its node counts are fixed by
``tests/test_thesis_reproduction.py``; and ``delta`` is reachable on instances
whose tree is not, which is the entire point -- ``word-xxx`` has
``delta = 4139`` at ``N = 16512``, where ``tau`` cannot be enumerated at all.

:mod:`fka.analysis` already memoises this same key when *annotating* a finished
tree. What is new here is memoising the recursion that builds it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .algorithm import _trivial_case, check_conditions, choose_split_var
from .hypergraph import Hypergraph, phi_x_0, phi_x_1
from .irredundant import irredundant
from .tree import Tree

__all__ = ["MemoRun", "dag_size", "fk_a_memo"]


def _key(C: Hypergraph, D: Hypergraph) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    """The subproblem's identity. Matches :func:`fka.analysis.annotate`'s key.

    ``n`` is carried because ``phi_x_0`` drops variables, so two nodes can share
    an edge tuple over different ground sets.
    """
    return (C.n, C.edges, D.edges)


@dataclass(frozen=True, slots=True)
class MemoRun:
    """What the memoised recursion saw. ``nodes`` is ``delta``."""

    dual: bool
    nodes: int
    depth: int

    def to_json(self) -> dict[str, Any]:
        return {"dual": self.dual, "nodes": self.nodes, "depth": self.depth}


def dag_size(tree: Tree) -> int:
    """``delta`` read off a completed tree, for cross-checking :func:`fk_a_memo`."""
    return len({_key(node.cnf, node.dnf) for node in tree})


def fk_a_memo(
    cnf: Hypergraph,
    dnf: Hypergraph,
    *,
    variant: str = "modified",
    split_rule: str = "degree_sum",
) -> MemoRun:
    """Decide ``cnf = Tr(dnf)``, counting distinct subproblems rather than nodes.

    Returns the same verdict as :func:`fka.algorithm.fk_a` under the same
    ``variant`` and ``split_rule``; ``tests/test_memo.py`` asserts that against
    the tree and against the Berge oracle over the whole library.
    """
    if cnf.n != dnf.n:
        raise ValueError(
            f"C is on {cnf.n} variables but D is on {dnf.n}; "
            "both sides must share a ground set"
        )

    memo: dict[tuple, bool | None] = {}
    deepest = 0

    def recurse(cnf_in: Hypergraph, dnf_in: Hypergraph, depth: int) -> bool:
        nonlocal deepest
        C = irredundant(cnf_in).reduced
        D = irredundant(dnf_in).reduced
        key = _key(C, D)
        if key in memo:
            hit = memo[key]
            # Each level eliminates a variable, so the subproblem relation is
            # acyclic and an in-progress key cannot be re-entered. Asserted
            # rather than assumed: a cycle would silently return this sentinel.
            assert hit is not None, "cycle in the FK-A subproblem relation"
            return hit
        memo[key] = None
        deepest = max(deepest, depth)

        failed = check_conditions(C, D)
        if failed is not None:
            memo[key] = failed.dual
            return failed.dual

        trivial = _trivial_case(C, D, variant)
        if trivial is not None:
            memo[key] = trivial.dual
            return trivial.dual

        x = choose_split_var(C, D, split_rule)
        if x is None:
            raise AssertionError(
                f"no variable of positive degree in {C.label()} / {D.label()}"
            )
        C_x_0, C_x_1 = phi_x_0(C, x), phi_x_1(C, x)
        D_x_0, D_x_1 = phi_x_0(D, x), phi_x_1(D, x)

        out = recurse(C_x_1, D_x_0.vee(D_x_1), depth + 1) and recurse(
            D_x_1, C_x_0.vee(C_x_1), depth + 1
        )
        memo[key] = out
        return out

    dual = recurse(cnf, dnf, 0)
    return MemoRun(dual=dual, nodes=len(memo), depth=deepest)

"""Sperner reduction shared by both algorithms and Berge's transversal construction."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .hypergraph import Hypergraph, popcount

__all__ = ["Reduction", "minimal_elements", "irredundant"]


@dataclass(frozen=True, slots=True)
class Reduction:
    """The reduced hypergraph and the supersets removed in original term order."""

    reduced: Hypergraph
    removed: tuple[int, ...]


def minimal_elements(sets: Iterable[int]) -> tuple[int, ...]:
    """Keep the inclusion-minimal bitsets, in ascending numeric order."""
    kept: list[int] = []
    for s in sorted(set(sets), key=lambda t: (popcount(t), t)):
        if not any((k & s) == k for k in kept):
            kept.append(s)
    return tuple(sorted(kept))


def irredundant(MBF: Hypergraph) -> Reduction:
    """Reduce canonical MBF to its minimal terms, reporting removed supersets."""
    kept = minimal_elements(MBF.edges)
    live = set(kept)
    return Reduction(Hypergraph(MBF.n, kept), tuple(t for t in MBF.edges if t not in live))

"""The atom lift, as executable claims.

The classification of MBF(5) is checked three independent ways: the orbit sizes
must sum to `d(5)`, Cauchy-Frobenius must return the same class count, and both
must agree with the published A003182. The lift is also run at `n = 1, 2, 3`,
where the answer can be computed *directly* from :func:`fka.dedekind.atoms` one
level up -- so the machinery is validated on levels it does not need before it
is trusted on the level it does.

The budget assertions are the research contract: nothing here may construct
MBF(5).
"""

from __future__ import annotations

from itertools import permutations

import pytest

from fka.dedekind import (A003182, DEDEKIND, MAX_LATTICE, act, atoms,
                          canonical, cofactor_profile,
                          free_distributive_lattice, iter_class_reps, lift,
                          orbit_count_burnside, subset_action, upset_from_mbf)


# ----------------------------------------------------------------------
# the lattice
# ----------------------------------------------------------------------
@pytest.mark.parametrize("n", [0, 1, 2, 3, 4])
def test_lattice_size_is_the_dedekind_number(n):
    assert len(free_distributive_lattice(n)) == DEDEKIND[n]


def test_lattice_elements_are_upsets():
    n = 4
    for upset in free_distributive_lattice(n):
        for S in range(1 << n):
            if not (upset >> S & 1):
                continue
            for T in range(1 << n):
                if (S & ~T) == 0:  # S subseteq T
                    assert upset >> T & 1, f"{upset} is not upward closed"


def test_building_the_level_above_is_refused():
    """`FDL(5)` is exactly the enumeration this module exists to avoid."""
    with pytest.raises(ValueError, match="above the ceiling"):
        free_distributive_lattice(5)
    assert DEDEKIND[5] > MAX_LATTICE


# ----------------------------------------------------------------------
# the atoms
# ----------------------------------------------------------------------
@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_atom_classes_match_A003182(n):
    assert len(atoms(n)) == A003182[n]


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_atom_class_sizes_partition_the_lattice(n):
    level = atoms(n)
    assert sum(a.size for a in level) == DEDEKIND[n]
    covered = set()
    for a in level:
        assert not (covered & a.orbit), "atom classes overlap"
        covered |= a.orbit
    assert covered == set(free_distributive_lattice(n))


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_orbit_stabiliser_on_the_atoms(n):
    from math import factorial

    for a in atoms(n):
        assert a.size * len(a.stabiliser) == factorial(n)


def test_upset_and_term_set_round_trip():
    for a in atoms(4):
        assert upset_from_mbf(a.mbf) == a.rep
        assert a.mbf.is_sperner()


def test_the_two_degenerate_atoms_are_present():
    """`{}` and `{{}}` are MBFs and each is its own class."""
    reps = {a.mbf.label() for a in atoms(4)}
    assert "{}" in reps and "{{}}" in reps


# ----------------------------------------------------------------------
# the lift, validated where it can be checked directly
# ----------------------------------------------------------------------
@pytest.mark.parametrize("n", [1, 2, 3])
def test_lift_agrees_with_directly_computed_atoms(n):
    """At these levels the answer is computable both ways, and must agree."""
    lifted = lift(n)
    direct = atoms(n + 1)
    assert lifted.total == DEDEKIND[n + 1]
    assert len(lifted.classes) == len(direct) == A003182[n + 1]
    assert sorted(lifted.class_size(c) for c in range(len(lifted.classes))) == sorted(
        a.size for a in direct
    )


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_orbit_sizes_sum_to_the_next_dedekind_number(n):
    assert lift(n).total == DEDEKIND[n + 1]


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_class_count_matches_A003182(n):
    assert len(lift(n).classes) == A003182[n + 1]


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_cauchy_frobenius_agrees_with_the_lift(n):
    count, _ = orbit_count_burnside(n)
    assert count == len(lift(n).classes) == A003182[n + 1]


def test_the_published_numbers_for_five_variables():
    lifted = lift(4)
    assert len(atoms(4)) == 30
    assert len(lifted.pairs) == 620
    assert lifted.total == 7581
    assert len(lifted.classes) == 210


def test_class_sizes_divide_the_group_order():
    lifted = lift(4)
    sizes = [lifted.class_size(c) for c in range(len(lifted.classes))]
    assert sum(sizes) == 7581
    assert all(120 % s == 0 for s in sizes)


def test_classes_partition_the_orbits():
    lifted = lift(4)
    flat = [k for members in lifted.classes for k in members]
    assert sorted(flat) == list(range(len(lifted.pairs)))


def test_representatives_are_distinct_sperner_functions():
    lifted = lift(4)
    reps = [lifted.mbf(k) for _, k in iter_class_reps(lifted)]
    assert len(reps) == 210
    assert all(r.n == 5 and r.is_sperner() for r in reps)
    assert len({upset_from_mbf(r) for r in reps}) == 210


def test_shannon_halves_recover_the_representative():
    """`f0` and `f1` really are the cofactors of the function they index."""
    lifted = lift(4)
    for _, k in iter_class_reps(lifted):
        f0, f1 = lifted.pairs[k]
        MBF = lifted.mbf(k)
        upset = upset_from_mbf(MBF)
        assert upset & 0xFFFF == f0
        assert upset >> 16 == f1
        assert f0 & ~f1 == 0, "the Shannon pair must be comparable"


# ----------------------------------------------------------------------
# the fusion trap
# ----------------------------------------------------------------------
def test_fusing_on_one_representative_per_orbit_undercounts():
    """`tau` does not normalise `S_4`, so one representative is not enough.

    The wrong version is kept here, as the thing the right one is compared
    against: it returns 216 rather than 210.
    """
    n = 4
    lifted = lift(n)
    tau = subset_action((0, 1, 2, 4, 3))
    half = 1 << n
    low_mask = (1 << half) - 1
    index = {pair: k for k, pair in enumerate(lifted.pairs)}

    parent = list(range(len(lifted.pairs)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for k, (f, g) in enumerate(lifted.pairs):
        image = act(tau, f | (g << half), n + 1)
        j = index[canonical((image & low_mask, image >> half), n)]
        a, b = find(k), find(j)
        if a != b:
            parent[max(a, b)] = min(a, b)

    undercounted = len({find(k) for k in range(len(lifted.pairs))})
    assert undercounted == 216
    assert len(lifted.classes) == 210


def test_canonical_form_is_constant_on_orbits():
    n = 4
    group = [subset_action(p) for p in permutations(range(n))]
    for pair in lift(n).pairs[:40]:
        f, g = pair
        for sub in group:
            assert canonical((act(sub, f, n), act(sub, g, n)), n) == pair


# ----------------------------------------------------------------------
# the atom-built invariant
# ----------------------------------------------------------------------
@pytest.mark.parametrize("n", [2, 3, 4])
def test_cofactor_profile_separates_every_class(n):
    """Verified at n+1 = 3, 4, 5. Not claimed beyond them."""
    lifted = lift(n)
    seen = {}
    for c, k in iter_class_reps(lifted):
        f0, f1 = lifted.pairs[k]
        profile = cofactor_profile(f0 | (f1 << (1 << n)), n + 1)
        assert profile not in seen, f"classes {seen.get(profile)} and {c} collide"
        seen[profile] = c
    assert len(seen) == A003182[n + 1]


def test_cofactor_profile_is_invariant_under_relabelling():
    lifted = lift(4)
    group = list(permutations(range(5)))
    for _, k in list(iter_class_reps(lifted))[:25]:
        f0, f1 = lifted.pairs[k]
        upset = f0 | (f1 << 16)
        base = cofactor_profile(upset, 5)
        for p in group[::17]:
            moved = act(subset_action(p), upset, 5)
            assert cofactor_profile(moved, 5) == base


# ----------------------------------------------------------------------
# the research contract: no enumeration of the level above
# ----------------------------------------------------------------------
def test_the_lift_stays_under_budget():
    """It may not touch as many atom pairs as there are functions above."""
    lifted = lift(4)
    assert lifted.examined == 1568
    assert lifted.examined < DEDEKIND[5]
    assert lifted.examined < DEDEKIND[4] ** 2


def test_the_lift_never_builds_the_level_above(monkeypatch):
    """The lattice constructor is the only way in, and the lift never asks for 5."""
    import fka.dedekind as dedekind

    real = dedekind.free_distributive_lattice
    asked: list[int] = []

    def spy(n: int):
        asked.append(n)
        return real(n)

    monkeypatch.setattr(dedekind, "free_distributive_lattice", spy)
    dedekind.atoms.cache_clear()
    try:
        dedekind.lift(4)
    finally:
        dedekind.atoms.cache_clear()

    assert asked, "the spy never fired, so the test proves nothing"
    assert max(asked) == 4, f"the lift asked for FDL({max(asked)})"

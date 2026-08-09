"""Classify MBF(n+1) by the MBF(n) atoms, without enumerating MBF(n+1).

`d(n)`, the n-th Dedekind number, counts the MBFs on `n` variables -- the
antichains, the Sperner hypergraphs, the irredundant normal forms. It counts
them **labelled**: `d(4) = 168` and `d(5) = 7581` are counts of functions, not
of functions up to renaming the variables. Quotienting by `S_n` is a separate
and much smaller count, OEIS A003182: 30 at `n = 4` and 210 at `n = 5`.

This module computes the second from the first level up, and the whole point is
that it never builds the 7581. Two facts do the work.

**Shannon.** Splitting on the last variable, `f = f0 v (x_{n+1} ^ f1)` with
`f0 = f|x=0` and `f1 = f|x=1`, is a bijection

    MBF(n+1)  <->  { (f0, f1) in MBF(n)^2 : f0 <= f1 }

because monotonicity of `f` is exactly monotonicity of both halves plus
`f0 <= f1`. So a function on `n+1` variables *is* a comparable pair of atoms,
and `d(n+1)` is the number of comparable pairs in the free distributive lattice
`FDL(n)`. Jaekel's `d(9)` computation is this same decomposition, iterated.

**Orbit-stabiliser.** `S_n`, the stabiliser of `x_{n+1}` in `S_{n+1}`, acts on
those pairs coordinatewise. Its orbits are therefore indexed not by pairs but by

    (atom class A,  orbit of Stab(a) on the principal filter up(a))

for one representative `a` of each `A`. At `n = 4` that is 30 filters totalling
1568 memberships, against 7581 objects -- and it yields all 620 `S_4`-orbits.

**Fusion.** `S_5 = <S_4, tau>` for `tau = (4 5)`, so the `S_5`-orbits are the
connected components of the graph whose nodes are the 620 `S_4`-orbits and whose
edges are `tau`. `tau` does *not* normalise `S_4`, so `tau(S_4.x)` meets several
`S_4`-orbits and every coset representative has to be tried; the edges out of an
orbit are `tau*p` over `p in S_4`. Each image is identified by canonical form
(:func:`canonical`), never by a lookup table over the level above, which is what
keeps peak memory at `O(#orbits)`.

Nothing here is a search: every count is closed-form or orbit-local.
:func:`orbit_count_burnside` recomputes the answer by Cauchy-Frobenius over the
seven cycle types of `S_5` as an independent check.

See `docs/dedekind-atoms.md` for the derivation and for what the vendored
`Dedekind/` snapshot can and cannot supply.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations
from typing import Iterator, Optional, Sequence

from .hypergraph import Hypergraph

__all__ = [
    "Atom",
    "Lift",
    "free_distributive_lattice",
    "mbf_from_upset",
    "upset_from_mbf",
    "subset_action",
    "act",
    "atoms",
    "canonical",
    "lift",
    "orbit_count_burnside",
    "cofactor_profile",
    "iter_class_reps",
    "A003182",
    "DEDEKIND",
]

#: `d(n)`, the n-th Dedekind number: labelled MBFs on n variables.
#: OEIS A000372. Beyond `n = 5` these are quoted, not computed here.
DEDEKIND = {0: 2, 1: 3, 2: 6, 3: 20, 4: 168, 5: 7581, 6: 7828354}

#: MBFs on n variables **up to** `S_n`, OEIS A003182. The published values this
#: module's orbit counts are checked against.
A003182 = {0: 2, 1: 3, 2: 5, 3: 10, 4: 30, 5: 210, 6: 16353}

#: Refuse to build a lattice bigger than this. `FDL(5)` has 7581 elements and
#: building it is exactly the enumeration this module exists to avoid; the
#: ceiling makes that a clear error rather than a silent regression.
MAX_LATTICE = 1000


# ----------------------------------------------------------------------
# the free distributive lattice, as up-sets
# ----------------------------------------------------------------------
@lru_cache(maxsize=None)
def free_distributive_lattice(n: int) -> tuple[int, ...]:
    """`FDL(n)`: every MBF on `n` variables, as an up-set of `B_n`.

    An MBF is stored as the bitmask over the `2^n` subsets whose bit `S` is set
    iff `S` satisfies the function. Subsets index bits, so bit `S` and term `S`
    are the same integer and `f <= g` is `f & ~g == 0`.

    Built by the Shannon recursion itself -- `FDL(n)` is the comparable pairs of
    `FDL(n-1)` -- so the constructor and the classification agree by
    construction rather than by assertion.
    """
    if n < 0:
        raise ValueError(f"variable count must be non-negative, got {n}")
    if n == 0:
        return (0b0, 0b1)
    smaller = free_distributive_lattice(n - 1)
    half = 1 << (n - 1)
    out = tuple(
        f0 | (f1 << half) for f0 in smaller for f1 in smaller if f0 & ~f1 == 0
    )
    if len(out) > MAX_LATTICE:
        raise ValueError(
            f"FDL({n}) has {len(out)} elements, above the ceiling of "
            f"{MAX_LATTICE}. Enumerating it is the brute force this module "
            f"avoids; classify level {n} from the level-{n - 1} atoms instead."
        )
    return out


def mbf_from_upset(upset: int, n: int) -> Hypergraph:
    """The term set of an up-set: its minimal subsets, as a :class:`Hypergraph`."""
    members = [S for S in range(1 << n) if upset >> S & 1]
    minimal = [
        S for S in members if not any(T != S and (T & ~S) == 0 for T in members)
    ]
    return Hypergraph.from_bitsets(n, minimal)


def upset_from_mbf(MBF: Hypergraph) -> int:
    """The up-set of a term set: every subset containing some term."""
    upset = 0
    for S in range(1 << MBF.n):
        if any((t & ~S) == 0 for t in MBF.edges):
            upset |= 1 << S
    return upset


# ----------------------------------------------------------------------
# the S_n action
# ----------------------------------------------------------------------
def subset_action(p: Sequence[int]) -> tuple[int, ...]:
    """The permutation of `2^[n]` induced by the variable permutation `p`."""
    n = len(p)
    out = []
    for S in range(1 << n):
        T = 0
        for i in range(n):
            if S >> i & 1:
                T |= 1 << p[i]
        out.append(T)
    return tuple(out)


def act(action: Sequence[int], upset: int, n: int) -> int:
    """Push an up-set through an induced subset permutation."""
    out = 0
    for S in range(1 << n):
        if upset >> S & 1:
            out |= 1 << action[S]
    return out


@lru_cache(maxsize=None)
def _symmetric(n: int) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    """`S_n` as `(permutation, induced subset permutation)` pairs."""
    return tuple((p, subset_action(p)) for p in permutations(range(n)))


# ----------------------------------------------------------------------
# level n: the atoms
# ----------------------------------------------------------------------
@dataclass(frozen=True, slots=True)
class Atom:
    """One `S_n`-class of MBFs on `n` variables.

    ``rep`` is the canonical (numerically least) up-set in the class.
    ``stabiliser`` is ``Stab_{S_n}(rep)``, which is what indexes the classes one
    level up; ``size`` is the class cardinality, and the sizes sum to `d(n)`.
    """

    index: int
    rep: int
    n: int
    orbit: frozenset[int]
    stabiliser: tuple[tuple[int, ...], ...]

    @property
    def size(self) -> int:
        return len(self.orbit)

    @property
    def mbf(self) -> Hypergraph:
        return mbf_from_upset(self.rep, self.n)

    def label(self) -> str:
        return self.mbf.label()


@lru_cache(maxsize=None)
def atoms(n: int) -> tuple[Atom, ...]:
    """The `S_n`-classes of MBFs on `n` variables, canonical representative first.

    At `n = 4` this is the 30 classes that the rest of the module uses as atoms.
    """
    lattice = free_distributive_lattice(n)
    group = _symmetric(n)
    seen: set[int] = set()
    found: list[Atom] = []
    for upset in lattice:
        if upset in seen:
            continue
        orbit = {act(sub, upset, n) for _, sub in group}
        seen |= orbit
        rep = min(orbit)
        stab = tuple(p for p, sub in group if act(sub, rep, n) == rep)
        found.append(Atom(len(found), rep, n, frozenset(orbit), stab))
    return tuple(found)


# ----------------------------------------------------------------------
# level n+1: comparable pairs of atoms
# ----------------------------------------------------------------------
def canonical(pair: tuple[int, int], n: int) -> tuple[int, int]:
    """The numerically least image of a comparable pair under `S_n`.

    Identifies an `S_n`-orbit on `MBF(n+1)` in `|S_n|` steps, so the fusion
    never needs a table over the level above.
    """
    f, g = pair
    best = None
    for _, sub in _symmetric(n):
        candidate = (act(sub, f, n), act(sub, g, n))
        if best is None or candidate < best:
            best = candidate
    return best  # type: ignore[return-value]


@dataclass(frozen=True, slots=True)
class Lift:
    """`MBF(n+1)` classified from the `MBF(n)` atoms.

    ``pairs`` are the `S_n`-orbit representatives as comparable atom pairs
    ``(f0, f1)``; ``sizes[k]`` is the size of orbit `k` and the sizes sum to
    `d(n+1)`; ``classes`` groups those orbits into the `S_{n+1}`-classes.
    ``examined`` is how many atom-pair memberships the construction touched --
    the honest cost, to be compared against `d(n+1)`.
    """

    n: int
    pairs: tuple[tuple[int, int], ...]
    sizes: tuple[int, ...]
    atom_of: tuple[tuple[int, int], ...]
    classes: tuple[tuple[int, ...], ...]
    examined: int

    @property
    def total(self) -> int:
        """`d(n+1)`, summed over the orbits rather than enumerated."""
        return sum(self.sizes)

    def mbf(self, k: int) -> Hypergraph:
        """Orbit `k`'s representative, as an MBF on `n+1` variables."""
        f, g = self.pairs[k]
        return mbf_from_upset(f | (g << (1 << self.n)), self.n + 1)

    def class_size(self, c: int) -> int:
        return sum(self.sizes[k] for k in self.classes[c])


def lift(n: int) -> Lift:
    """Classify `MBF(n+1)` from the `MBF(n)` atoms.

    Two stages. The `S_n`-orbits come from orbit-stabiliser: for each atom class
    with representative `a`, the orbits of `Stab(a)` on the filter
    `up(a) = {g : a <= g}`. The `S_{n+1}`-classes come from fusing those under
    `tau = (n, n+1)`, whose images are identified by :func:`canonical`.
    """
    lattice = free_distributive_lattice(n)
    group = _symmetric(n)
    classes = atoms(n)

    pairs: list[tuple[int, int]] = []
    sizes: list[int] = []
    atom_of: list[tuple[int, int]] = []
    index: dict[tuple[int, int], int] = {}
    examined = 0

    # -- stage 1: S_n-orbits, one principal filter per atom class --------
    for atom in classes:
        a = atom.rep
        filt = [g for g in lattice if a & ~g == 0]
        examined += len(filt)
        stab_actions = [subset_action(p) for p in atom.stabiliser]
        done: set[int] = set()
        for g in filt:
            if g in done:
                continue
            suborbit = {act(sub, g, n) for sub in stab_actions}
            done |= suborbit
            # |S_n.(a,g)| = |A| * |Stab(a).g| by orbit-stabiliser, since the
            # stabiliser of the pair is the stabiliser of g inside Stab(a).
            rep = canonical((a, g), n)
            index[rep] = len(pairs)
            pairs.append(rep)
            sizes.append(atom.size * len(suborbit))
            atom_of.append((atom.index, _class_of(g, classes, n)))

    # -- stage 2: fuse under tau = (n, n+1) ------------------------------
    tau = tuple(list(range(n - 1)) + [n, n - 1]) if n >= 1 else (0,)
    tau_action = subset_action(tau)
    half = 1 << n
    parent = list(range(len(pairs)))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        x, y = find(x), find(y)
        if x != y:
            parent[max(x, y)] = min(x, y)

    low_mask = (1 << half) - 1
    for k, (f, g) in enumerate(pairs):
        for _, sub in group:
            moved = act(sub, f, n) | (act(sub, g, n) << half)
            image = act(tau_action, moved, n + 1)
            union(k, index[canonical((image & low_mask, image >> half), n)])

    buckets: dict[int, list[int]] = {}
    for k in range(len(pairs)):
        buckets.setdefault(find(k), []).append(k)

    return Lift(
        n=n,
        pairs=tuple(pairs),
        sizes=tuple(sizes),
        atom_of=tuple(atom_of),
        classes=tuple(tuple(v) for _, v in sorted(buckets.items())),
        examined=examined,
    )


def _class_of(upset: int, classes: Sequence[Atom], n: int) -> int:
    for atom in classes:
        if upset in atom.orbit:
            return atom.index
    raise ValueError(f"up-set {upset} is not an MBF on {n} variables")


# ----------------------------------------------------------------------
# the independent check: Cauchy-Frobenius over S_{n+1}
# ----------------------------------------------------------------------
def _cycle_type(p: Sequence[int]) -> tuple[int, ...]:
    seen: set[int] = set()
    parts = []
    for i in range(len(p)):
        if i in seen:
            continue
        length, j = 0, i
        while j not in seen:
            seen.add(j)
            j = p[j]
            length += 1
        parts.append(length)
    return tuple(sorted(parts, reverse=True))


def _class_size(cycle_type: Sequence[int], degree: int) -> int:
    """`|S_d|` divided by the centraliser order of a permutation of this type."""
    from collections import Counter
    from math import factorial

    counts = Counter(cycle_type)
    centraliser = 1
    for length, multiplicity in counts.items():
        centraliser *= (length**multiplicity) * factorial(multiplicity)
    return factorial(degree) // centraliser


def _invariant_comparable_pairs(p: Sequence[int], n: int) -> tuple[int, int]:
    """Comparable pairs among the `p`-invariant elements of `FDL(n)`.

    For `sigma` fixing `x_{n+1}` this is `|Fix(sigma)|` on `MBF(n+1)` exactly,
    because `sigma` acts on the Shannon pair coordinatewise.
    """
    sub = subset_action(tuple(p))
    invariant = [U for U in free_distributive_lattice(n) if act(sub, U, n) == U]
    pairs = sum(1 for f in invariant for g in invariant if f & ~g == 0)
    return pairs, len(invariant)


def _quotient_upsets(p: Sequence[int]) -> tuple[int, int]:
    """Up-sets of `B_d / <p>`, i.e. `|Fix(p)|` on `MBF(d)`, for `d = len(p)`.

    A `p`-invariant up-set is a union of `p`-orbits on `2^[d]` that is closed
    upwards, so it is an up-set of the quotient poset. Used only for the cycle
    types with no fixed point, which have no level-`n` reading.
    """
    d = len(p)
    sub = subset_action(tuple(p))
    orbit_id: dict[int, int] = {}
    orbits: list[list[int]] = []
    for S in range(1 << d):
        if S in orbit_id:
            continue
        cycle, T = [], S
        while True:
            cycle.append(T)
            orbit_id[T] = len(orbits)
            T = sub[T]
            if T == S:
                break
        orbits.append(cycle)

    m = len(orbits)
    if m > 24:
        raise ValueError(f"quotient poset has {m} classes; too many to scan")
    above = [0] * m
    for i, cycle in enumerate(orbits):
        for a in cycle:
            for b in range(1 << d):
                if a & ~b == 0:
                    above[i] |= 1 << orbit_id[b]

    count = 0
    for mask in range(1 << m):
        ok = True
        for i in range(m):
            if (mask >> i & 1) and (mask & above[i]) != above[i]:
                ok = False
                break
        if ok:
            count += 1
    return count, m


def orbit_count_burnside(n: int) -> tuple[int, list[tuple]]:
    """`|MBF(n+1) / S_{n+1}|` by Cauchy-Frobenius, and the per-class table.

    Independent of :func:`lift`: it sums fixed points rather than building
    orbits. The five cycle types of `S_5` with a fixed point are conjugate into
    `S_4` and so are answered by level-4 atom data alone; only `(3,2)` and `(5)`
    need the quotient poset of `B_5`.
    """
    degree = n + 1
    rows: list[tuple] = []
    total = 0
    by_type: dict[tuple[int, ...], Sequence[int]] = {}
    for p in permutations(range(degree)):
        by_type.setdefault(_cycle_type(p), p)

    for cycle_type, p in sorted(by_type.items(), reverse=True):
        size = _class_size(cycle_type, degree)
        if 1 in cycle_type:
            # sigma fixes a variable: restrict to S_n and read off the pairs.
            restricted = _restrict_fixing_last(p)
            fixed, invariant = _invariant_comparable_pairs(restricted, n)
            source = f"comparable pairs among {invariant} invariant atoms"
        else:
            fixed, m = _quotient_upsets(p)
            invariant = None
            source = f"up-sets of the {m}-class quotient of B_{degree}"
        rows.append((cycle_type, size, fixed, invariant, source))
        total += size * fixed

    from math import factorial

    if total % factorial(degree):
        raise AssertionError(
            f"Cauchy-Frobenius sum {total} is not divisible by {degree}!"
        )
    return total // factorial(degree), rows


def _restrict_fixing_last(p: Sequence[int]) -> tuple[int, ...]:
    """Rewrite a permutation with a fixed point as one of `S_{d-1}`."""
    d = len(p)
    fixed = next(i for i in range(d) if p[i] == i)
    keep = [i for i in range(d) if i != fixed]
    position = {v: i for i, v in enumerate(keep)}
    return tuple(position[p[v]] for v in keep)


# ----------------------------------------------------------------------
# the atom-built invariant
# ----------------------------------------------------------------------
def cofactor_profile(upset: int, n: int, classes: Optional[Sequence[Atom]] = None) -> tuple:
    """The multiset over the `n` variables of `(class of f|x=0, class of f|x=1)`.

    Every entry is an atom class one level down, and the multiset is unordered,
    so the profile is constant on `S_n`-classes by construction. Whether it
    *separates* them is a fact about `n`, not a theorem -- at `n = 5` it does,
    which `experiments/dedekind_atoms.py` reports and the tests pin.
    """
    if classes is None:
        classes = atoms(n - 1)
    lookup = {U: atom.index for atom in classes for U in atom.orbit}
    profile = []
    for i in range(n):
        low = high = 0
        for S in range(1 << n):
            if not (upset >> S & 1):
                continue
            reduced = (S & ((1 << i) - 1)) | ((S >> (i + 1)) << i)
            if S >> i & 1:
                high |= 1 << reduced
            else:
                low |= 1 << reduced
        profile.append((lookup[low], lookup[high]))
    return tuple(sorted(profile))


def iter_class_reps(lifted: Lift) -> Iterator[tuple[int, int]]:
    """One `(class index, orbit index)` per `S_{n+1}`-class, in order."""
    for c, members in enumerate(lifted.classes):
        yield c, members[0]

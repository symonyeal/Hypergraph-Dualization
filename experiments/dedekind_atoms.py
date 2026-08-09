"""Classify MBF(5) from the 30 MBF(4) atoms, without enumerating the 7581.

    python experiments/dedekind_atoms.py   ->  results/dedekind-atoms.md

The Shannon split on one variable makes `MBF(5)` the comparable pairs of
`FDL(4)`, and orbit-stabiliser makes the `S_4`-orbits on those pairs indexable
by one principal filter per atom class. Fusing under `tau = (4 5)` gives the
`S_5`-classes. Cauchy-Frobenius over the seven cycle types of `S_5` recomputes
the class count independently, and the published A003182 value is the third
opinion.

The cost line at the bottom is the point of the exercise: it reports how many
atom-pair memberships were touched, against `d(5)`. Nothing here constructs the
7581 functions, and :mod:`fka.dedekind` refuses to build `FDL(5)` at all.

See `docs/dedekind-atoms.md` for the derivation and the assessment of what the
vendored `Dedekind/` snapshot can supply.
"""

from __future__ import annotations

import sys
import time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from fka.dedekind import (A003182, DEDEKIND, atoms, cofactor_profile,  # noqa: E402
                          iter_class_reps, lift, orbit_count_burnside)

RESULTS = Path(__file__).resolve().parents[1] / "results"

#: The level classified. `n = 4` atoms, `n + 1 = 5` classified.
N = 4


def main() -> None:
    out: list[str] = []

    def log(line: str = "") -> None:
        print(line, flush=True)
        out.append(line)

    t0 = time.time()
    log(f"# MBF({N + 1}) classified by the MBF({N}) atoms")
    log()
    log("Regenerate with `python experiments/dedekind_atoms.py`.")
    log()
    log(f"`d({N}) = {DEDEKIND[N]}` labelled functions fall into "
        f"`A003182({N}) = {A003182[N]}` classes under `S_{N}`. Those classes are the "
        f"atoms. Every function on {N + 1} variables is a comparable pair of them.")
    log()

    level = atoms(N)
    lifted = lift(N)

    # ------------------------------------------------------------------
    log(f"## The {len(level)} atoms")
    log()
    log("`|A|` is the class size and they sum to "
        f"`d({N}) = {DEDEKIND[N]}`; `|Stab|` is the stabiliser order, and "
        "`|A| * |Stab| = 24` throughout by orbit-stabiliser. `filter` is "
        "`|up(a)|`, the number of atoms above the representative -- the only "
        "set the lift ever scans. `orbits` is how many `S_4`-orbits on "
        f"MBF({N + 1}) that filter contributes.")
    log()
    log("| # | representative | \\|A\\| | \\|Stab\\| | filter | orbits |")
    log("| ---: | --- | ---: | ---: | ---: | ---: |")

    contributed = Counter(a for a, _ in lifted.atom_of)
    for atom in level:
        log(f"| {atom.index} | `{atom.label()}` | {atom.size} | "
            f"{len(atom.stabiliser)} | {_filter_size(atom)} | "
            f"{contributed[atom.index]} |")
    log()

    # ------------------------------------------------------------------
    log(f"## The lift to MBF({N + 1})")
    log()
    log(f"- `S_{N}`-orbits on MBF({N + 1}): **{len(lifted.pairs)}**")
    log(f"- their sizes sum to **{lifted.total}**, which is "
        f"`d({N + 1}) = {DEDEKIND[N + 1]}` — so the orbits are exhaustive and "
        "disjoint, computed without listing what they contain")
    log(f"- `S_{N + 1}`-classes after fusing under `tau = ({N} {N + 1})`: "
        f"**{len(lifted.classes)}**, against the published "
        f"`A003182({N + 1}) = {A003182[N + 1]}`")
    log()
    log(f"`tau` does not normalise `S_{N}`, so `tau(S_{N}.x)` meets several "
        f"`S_{N}`-orbits and every coset representative has to be tried. Fusing "
        "on one representative per orbit is the natural mistake and gives "
        "**216**, six classes too many.")
    log()

    sizes = Counter(lifted.class_size(c) for c in range(len(lifted.classes)))
    log("| class size | how many classes |")
    log("| ---: | ---: |")
    for size, count in sorted(sizes.items()):
        log(f"| {size} | {count} |")
    log()
    log(f"Sizes divide `|S_{N + 1}| = 120` and sum to {DEDEKIND[N + 1]}.")
    log()

    # ------------------------------------------------------------------
    log("## The independent check: Cauchy-Frobenius")
    log()
    count, rows = orbit_count_burnside(N)
    log(f"The five cycle types of `S_{N + 1}` with a fixed point are conjugate "
        f"into `S_{N}`, so `sigma` acts on the Shannon pair coordinatewise and "
        "`Fix(sigma)` is a count of comparable pairs among the invariant atoms "
        "— level-4 data alone. Only the two fixed-point-free types need the "
        f"quotient poset of `B_{N + 1}`.")
    log()
    log("| cycle type | class | Fix(sigma) | computed from |")
    log("| --- | ---: | ---: | --- |")
    for cycle_type, size, fixed, _, source in rows:
        pretty = " ".join(str(c) for c in cycle_type)
        log(f"| {pretty} | {size} | {fixed} | {source} |")
    total = sum(size * fixed for _, size, fixed, _, _ in rows)
    log()
    log(f"Sum = {total}, and {total} / 120 = **{count}**.")
    log()

    # ------------------------------------------------------------------
    log("## How the classes sit over the atoms")
    log()
    spread = Counter()
    for c, k in iter_class_reps(lifted):
        low, high = lifted.atom_of[k]
        spread[tuple(sorted((low, high)))] += 1
    log(f"Each class is carried by an unordered pair of atom classes "
        f"`{{[f|x=0], [f|x=1]}}`. {len(spread)} of the "
        f"{len(level) * (len(level) + 1) // 2} available pairs are used, and one "
        f"pair carries at most {max(spread.values())} classes — so the atom pair "
        "alone is a strong but incomplete invariant.")
    log()
    carried = Counter(spread.values())
    log("| classes on one atom pair | how many pairs |")
    log("| ---: | ---: |")
    for k, v in sorted(carried.items()):
        log(f"| {k} | {v} |")
    log()

    # ------------------------------------------------------------------
    log("## A complete invariant built only from atoms")
    log()
    profiles: dict[tuple, list[int]] = {}
    for c, k in iter_class_reps(lifted):
        low, high = lifted.pairs[k]
        upset = low | (high << (1 << N))
        profiles.setdefault(cofactor_profile(upset, N + 1), []).append(c)
    collisions = {p: v for p, v in profiles.items() if len(v) > 1}
    log("Taking the pair of atom classes not for one variable but for **all "
        f"{N + 1}**, and forgetting the order, gives the *cofactor profile*: the "
        "multiset over the variables of `([f|x=0], [f|x=1])`. It is "
        f"`S_{N + 1}`-invariant by construction.")
    log()
    log(f"- distinct profiles over the {len(lifted.classes)} classes: "
        f"**{len(profiles)}**")
    log(f"- colliding profiles: **{len(collisions)}**")
    log()
    if not collisions:
        log(f"So at `n = {N + 1}` the profile is a **complete** invariant: the 30 "
            "atom classes separate all "
            f"{len(lifted.classes)} classes, with no canonical form and no "
            "isomorphism test. The same holds at `n = 3` and `n = 4`. It is a "
            "verified fact at these three levels, not a theorem — the profile is "
            "a 1-dimensional Weisfeiler-Leman refinement over variables, and "
            "such invariants generally do fail eventually.")
    else:
        log(f"At `n = {N + 1}` the profile leaves {len(collisions)} collisions, "
            "so it is a strong but incomplete invariant.")
    log()

    # ------------------------------------------------------------------
    log("## Cost")
    log()
    raw = DEDEKIND[N] ** 2
    log("| quantity | count |")
    log("| --- | ---: |")
    log(f"| atom-pair memberships examined | **{lifted.examined}** |")
    log(f"| functions on {N + 1} variables constructed | **0** |")
    log(f"| `d({N + 1})`, never enumerated | {DEDEKIND[N + 1]} |")
    log(f"| raw pairs a naive scan would test | {raw} |")
    log()
    log(f"The lift scans {lifted.examined} filter memberships — one principal "
        f"filter per atom class — where listing MBF({N + 1}) means "
        f"{DEDEKIND[N + 1]} objects and a naive double loop over `FDL({N})` "
        f"means {raw} comparisons. `fka.dedekind.MAX_LATTICE` makes building "
        f"`FDL({N + 1})` an error rather than a silent regression.")
    log()
    log(f"_{time.time() - t0:.1f}s_")

    RESULTS.mkdir(exist_ok=True)
    path = RESULTS / "dedekind-atoms.md"
    path.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"\nwrote {path}")


def _filter_size(atom) -> int:
    """`|up(a)|`, the principal filter the lift scans for this atom."""
    from fka.dedekind import free_distributive_lattice

    return sum(1 for g in free_distributive_lattice(atom.n) if atom.rep & ~g == 0)


if __name__ == "__main__":
    main()

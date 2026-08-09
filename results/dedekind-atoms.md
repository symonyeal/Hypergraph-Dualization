# MBF(5) classified by the MBF(4) atoms

Regenerate with `python experiments/dedekind_atoms.py`.

`d(4) = 168` labelled functions fall into `A003182(4) = 30` classes under `S_4`. Those classes are the atoms. Every function on 5 variables is a comparable pair of them.

## The 30 atoms

`|A|` is the class size and they sum to `d(4) = 168`; `|Stab|` is the stabiliser order, and `|A| * |Stab| = 24` throughout by orbit-stabiliser. `filter` is `|up(a)|`, the number of atoms above the representative -- the only set the lift ever scans. `orbits` is how many `S_4`-orbits on MBF(5) that filter contributes.

| # | representative | \|A\| | \|Stab\| | filter | orbits |
| ---: | --- | ---: | ---: | ---: | ---: |
| 0 | `{}` | 1 | 24 | 168 | 30 |
| 1 | `{{1,2,3,4}}` | 1 | 24 | 167 | 29 |
| 2 | `{{1,2,3}}` | 4 | 6 | 148 | 48 |
| 3 | `{{1,2,3},{1,2,4}}` | 6 | 4 | 134 | 59 |
| 4 | `{{1,2}}` | 6 | 4 | 84 | 37 |
| 5 | `{{1,2,3},{1,2,4},{1,3,4}}` | 4 | 6 | 123 | 43 |
| 6 | `{{1,2},{1,3,4}}` | 12 | 2 | 78 | 52 |
| 7 | `{{1,2},{1,3}}` | 12 | 2 | 53 | 39 |
| 8 | `{{1,2},{1,3},{1,4}}` | 4 | 6 | 39 | 19 |
| 9 | `{{1}}` | 4 | 6 | 20 | 10 |
| 10 | `{{1,2,3},{1,2,4},{1,3,4},{2,3,4}}` | 1 | 24 | 114 | 20 |
| 11 | `{{1,2},{1,3,4},{2,3,4}}` | 6 | 4 | 73 | 32 |
| 12 | `{{1,2},{1,3},{2,3,4}}` | 12 | 2 | 50 | 36 |
| 13 | `{{1,2},{1,3},{1,4},{2,3,4}}` | 4 | 6 | 37 | 17 |
| 14 | `{{1},{2,3,4}}` | 4 | 6 | 19 | 9 |
| 15 | `{{1,2},{1,3},{2,3}}` | 4 | 6 | 36 | 15 |
| 16 | `{{1,4},{2,3}}` | 3 | 8 | 48 | 15 |
| 17 | `{{1,2},{1,4},{2,3}}` | 12 | 2 | 35 | 22 |
| 18 | `{{1,2},{1,3},{1,4},{2,3}}` | 12 | 2 | 27 | 19 |
| 19 | `{{1},{2,3}}` | 12 | 2 | 14 | 10 |
| 20 | `{{1,3},{1,4},{2,3},{2,4}}` | 3 | 8 | 26 | 11 |
| 21 | `{{1,2},{1,3},{1,4},{2,3},{2,4}}` | 6 | 4 | 21 | 13 |
| 22 | `{{1},{2,3},{2,4}}` | 12 | 2 | 11 | 9 |
| 23 | `{{1},{2}}` | 6 | 4 | 6 | 5 |
| 24 | `{{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}}` | 1 | 24 | 17 | 6 |
| 25 | `{{1},{2,3},{2,4},{3,4}}` | 4 | 6 | 9 | 5 |
| 26 | `{{1},{2},{3,4}}` | 6 | 4 | 5 | 4 |
| 27 | `{{1},{2},{3}}` | 4 | 6 | 3 | 3 |
| 28 | `{{1},{2},{3},{4}}` | 1 | 24 | 2 | 2 |
| 29 | `{{}}` | 1 | 24 | 1 | 1 |

## The lift to MBF(5)

- `S_4`-orbits on MBF(5): **620**
- their sizes sum to **7581**, which is `d(5) = 7581` — so the orbits are exhaustive and disjoint, computed without listing what they contain
- `S_5`-classes after fusing under `tau = (4 5)`: **210**, against the published `A003182(5) = 210`

`tau` does not normalise `S_4`, so `tau(S_4.x)` meets several `S_4`-orbits and every coset representative has to be tried. Fusing on one representative per orbit is the natural mistake and gives **216**, six classes too many.

| class size | how many classes |
| ---: | ---: |
| 1 | 7 |
| 5 | 14 |
| 10 | 28 |
| 12 | 2 |
| 15 | 14 |
| 20 | 21 |
| 30 | 43 |
| 60 | 74 |
| 120 | 7 |

Sizes divide `|S_5| = 120` and sum to 7581.

## The independent check: Cauchy-Frobenius

The five cycle types of `S_5` with a fixed point are conjugate into `S_4`, so `sigma` acts on the Shannon pair coordinatewise and `Fix(sigma)` is a count of comparable pairs among the invariant atoms — level-4 data alone. Only the two fixed-point-free types need the quotient poset of `B_5`.

| cycle type | class | Fix(sigma) | computed from |
| --- | ---: | ---: | --- |
| 5 | 24 | 11 | up-sets of the 8-class quotient of B_5 |
| 4 1 | 30 | 35 | comparable pairs among 8 invariant atoms |
| 3 2 | 20 | 35 | up-sets of the 12-class quotient of B_5 |
| 3 1 1 | 20 | 105 | comparable pairs among 15 invariant atoms |
| 2 2 1 | 15 | 309 | comparable pairs among 28 invariant atoms |
| 2 1 1 1 | 10 | 887 | comparable pairs among 50 invariant atoms |
| 1 1 1 1 1 | 1 | 7581 | comparable pairs among 168 invariant atoms |

Sum = 25200, and 25200 / 120 = **210**.

## How the classes sit over the atoms

Each class is carried by an unordered pair of atom classes `{[f|x=0], [f|x=1]}`. 161 of the 465 available pairs are used, and one pair carries at most 4 classes — so the atom pair alone is a strong but incomplete invariant.

| classes on one atom pair | how many pairs |
| ---: | ---: |
| 1 | 127 |
| 2 | 21 |
| 3 | 11 |
| 4 | 2 |

## A complete invariant built only from atoms

Taking the pair of atom classes not for one variable but for **all 5**, and forgetting the order, gives the *cofactor profile*: the multiset over the variables of `([f|x=0], [f|x=1])`. It is `S_5`-invariant by construction.

- distinct profiles over the 210 classes: **210**
- colliding profiles: **0**

So at `n = 5` the profile is a **complete** invariant: the 30 atom classes separate all 210 classes, with no canonical form and no isomorphism test. The same holds at `n = 3` and `n = 4`. It is a verified fact at these three levels, not a theorem — the profile is a 1-dimensional Weisfeiler-Leman refinement over variables, and such invariants generally do fail eventually.

## Cost

| quantity | count |
| --- | ---: |
| atom-pair memberships examined | **1568** |
| functions on 5 variables constructed | **0** |
| `d(5)`, never enumerated | 7581 |
| raw pairs a naive scan would test | 28224 |

The lift scans 1568 filter memberships — one principal filter per atom class — where listing MBF(5) means 7581 objects and a naive double loop over `FDL(4)` means 28224 comparisons. `fka.dedekind.MAX_LATTICE` makes building `FDL(5)` an error rather than a silent regression.

_0.8s_

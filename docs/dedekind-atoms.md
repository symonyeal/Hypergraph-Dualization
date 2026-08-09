# Classifying MBF(5) from the MBF(4) atoms

An assessment of whether the vendored `Dedekind/` snapshot can carry the
classification of five-variable Sperner hypergraphs from the four-variable ones,
and a derivation of the classification that does. Every number below is
regenerable:

```text
python experiments/dedekind_atoms.py   -> results/dedekind-atoms.md
pytest tests/test_dedekind_atoms.py
```

## 0. A distinction the question turns on

The premise as posed was that *the Dedekind numbers are the total number of
possible Sperner hypergraphs on `n` variables given their automorphism
structure*. The first half is right and the second half is the opposite of
right, and separating them is what makes the rest tractable.

`d(n)` counts MBFs on `n` **labelled** variables. It does not quotient by
anything. `{{1,2}}` and `{{3,4}}` are two of the 168 at `n = 4`, though a
relabelling carries one to the other. Counting up to `S_n` — which is what
"given their automorphism structure" describes — is a different and much smaller
sequence, OEIS A003182:

| n | `d(n)` = A000372 | up to `S_n` = A003182 |
| ---: | ---: | ---: |
| 3 | 20 | 10 |
| 4 | **168** | **30** |
| 5 | **7,581** | **210** |
| 6 | 7,828,354 | 16,353 |

The two strands are therefore:

1. **the labelled count**, `d(n)`, which is the size of the space FK-A and FK-B
   search and the reason `Dedekind/` is vendored here at all; and
2. **the orbit count**, A003182, which is the number of genuinely distinct
   research objects, and the thing an atom-based classification produces.

The gap between them is the whole opportunity. There are 7581 functions on five
variables but only **210 things to understand**, and the instruction not to
brute-force the 7581 is not merely a performance preference: enumerating them
would produce a list in which 97% of the entries are relabellings of another
entry. The orbit count is not an optimisation of the labelled count. It is the
answer to a different and better question.

## 1. The assessment: what `Dedekind/` can and cannot supply

The vendored snapshot is Jäkel's `d(9)` computation. Its `data/` directory holds
three tables, and they are more relevant than they look. Reading the third
column of each `intervals.txt` as a multiplicity and summing:

| file | rows | multiplicities sum to | |
| --- | ---: | ---: | --- |
| `data/2/intervals.txt` | 6 | 20 | `= d(3)` |
| `data/3/intervals.txt` | 18 | 168 | `= d(4)` |
| `data/4/intervals.txt` | 134 | **7581** | `= d(5)` |

That is a real confirmation, and it is the first strand of the assessment.
Jäkel's files are a **weighted decomposition of `MBF(n+1)` over the intervals of
`FDL(n)`** — the free distributive lattice on `n` generators. His `data/4/` is
already a decomposition of the five-variable space over four-variable data.
Whatever else is true, the shape of the proposed approach is the shape of the
published `d(9)` computation, which is the strongest available evidence that it
is the right decomposition.

**But the equivalence is the wrong one, and the files cannot be used as the
classification.** 134 classes is not 210, and it is not 620 (the `S_4`-orbit
count derived in §3) either. Comparing the candidate partitions of the 7581
comparable pairs of `FDL(4)`:

| partition | classes |
| --- | ---: |
| by `S_4`-orbit | 620 |
| by isomorphism type of the interval `[f, g]` | 227 – 620 |
| by length `\|[f, g]\|` alone | 89 |
| **as Jäkel ships it** | **134** |

Isomorphism is coarser than the `S_4`-action, since a relabelling carries an
interval to an isomorphic one, so 620 bounds it above; 227 is a lower bound from
order-independent colour refinement, which is an isomorphism invariant and so can
only under-count. Jäkel's 134 falls below that lower bound, so his classes
**merge non-isomorphic intervals**. The mechanism is visible by hand at `n = 2`,
where his row `0 7 2` has multiplicity 2 and covers the two five-element
intervals `[0,7]` and `[1,15]`: one is a diamond with a tail below, the other a
diamond with a tail above. They are anti-isomorphic, not isomorphic. Merging
them is perfectly sound for Jäkel, because everything he needs from an interval
is its *length*, and an order dual has the same length.

So the conclusion of the assessment is a clean split:

- **usable**: the decomposition itself, and the total. `data/4/intervals.txt`
  summing to 7581 is an independent check on §3's orbit sizes, from a source
  that had no interest in this question.
- **not usable**: the classes. They are a length-preserving dedup internal to a
  summation, not a symmetry classification, and they are coarser than
  isomorphism, let alone than the `S_4`-action. No relabelling-invariant
  question can be answered from them.
- **not worth building**: the code. It is C++ needing Eigen, Intel TBB and CUDA,
  and about 20 GB of precomputed data for the `d(9)` path. The classification
  below runs in under a second in pure Python. The snapshot stays what
  `Dedekind/README.md` already says it is — a reference for the scale of the
  space, not a dependency.

I did not fully reverse-engineer Jäkel's equivalence; I bounded it. The claims
above are that his class count sits below the isomorphism bound and above the
length count, and that at `n = 2` an explicit anti-isomorphic pair shares a row.

## 2. The atoms, and why five variables is a pair of them

Split an MBF on `n + 1` variables on its last variable. Monotone Shannon
expansion gives

    f  =  f|x=0  v  ( x ^ f|x=1 )

and `f` is monotone exactly when both cofactors are monotone **and**
`f|x=0 <= f|x=1`. Nothing is lost and nothing is chosen, so this is a bijection:

> **(2.1)**  `MBF(n+1)  <->  { (f0, f1) in MBF(n)^2 : f0 <= f1 }`

A five-variable function *is* a comparable pair of four-variable functions. The
168 atoms are not an encoding of the 7581 — they generate them, and
`d(5) = 7581` is precisely the number of comparable pairs in `FDL(4)`. This is
the recursion `Dedekind/` implements, and (2.1) is why its `data/n` tables sum
to `d(n+1)`.

The 30 atom *classes* are the `S_4`-orbits, tabulated with their stabilisers in
[`results/dedekind-atoms.md`](../results/dedekind-atoms.md).

## 3. The `S_4`-orbits, by orbit-stabiliser

`S_4` is the stabiliser of `x_5` in `S_5`, so it acts on the pairs of (2.1)
coordinatewise. Its orbits could be found by orbiting all 7581 pairs. They
should not be, and they need not be:

> **(3.1)** The `S_4`-orbits on comparable pairs are in bijection with
>
>     ⊔_{A an atom class}  { orbits of Stab(a) on up(a) }
>
> for any one representative `a` of each `A`, where `up(a) = {g : a <= g}` is
> the principal filter above it.

This is orbit-stabiliser applied to the first coordinate. Every pair is
`S_4`-equivalent to one whose lower half is a chosen representative `a`, and two
such pairs `(a, g)` and `(a, g')` are equivalent exactly when `Stab(a)` carries
`g` to `g'`. The cost is 30 principal filters — **1568 memberships in total**,
against 7581 objects or the 28,224 comparisons a naive double loop would make.

It yields **620** orbits, and their sizes sum to 7581. That sum is the proof of
exhaustiveness: the orbits are known to cover the space without the space ever
being listed.

## 4. Fusion to `S_5`, and the trap in it

`S_5` is generated by `S_4` together with any transposition moving `x_5`, so
with `tau = (4 5)`:

> **(4.1)** The `S_5`-classes are the connected components of the graph on the
> 620 `S_4`-orbits whose edges are given by `tau`.

The trap is that **`tau` does not normalise `S_4`**. `tau(S_4.x)` is a coset,
not an orbit, and it meets several `S_4`-orbits at once. Applying `tau` to one
representative per orbit finds only some of the edges and returns **216**
classes — six too many, and wrong in a way that looks plausible. The edges out
of an orbit are `tau * p` over all `p in S_4`. With that fixed the components
number **210**, matching A003182. `tests/test_dedekind_atoms.py` keeps the
undercounting version as the thing the correct one is compared against.

Each image is identified by canonical form — the numerically least relabelling,
24 steps — rather than by a lookup table over the level above. That is not
incidental: a table keyed on all 7581 functions is exactly the enumeration being
avoided, and it is the form this derivation first took before the contract in §6
caught it. Peak memory is `O(#orbits)`.

## 5. Two independent checks, and one finding

**Cauchy-Frobenius.** The class count is recomputed by averaging fixed points
over `S_5`, and the atom decomposition pays off again: the five cycle types with
a fixed point are conjugate into `S_4`, so for them `Fix(sigma)` is the number of
comparable pairs among the `sigma`-invariant atoms — level-4 data alone. Only
the two fixed-point-free types, `(3,2)` and `(5)`, need the quotient poset of
`B_5`, which has 12 and 8 classes respectively.

| cycle type | class size | `Fix(sigma)` | from |
| --- | ---: | ---: | --- |
| 1⁵ | 1 | 7581 | 168 invariant atoms |
| 2·1³ | 10 | 887 | 50 invariant atoms |
| 2²·1 | 15 | 309 | 28 invariant atoms |
| 3·1² | 20 | 105 | 15 invariant atoms |
| 4·1 | 30 | 35 | 8 invariant atoms |
| 3·2 | 20 | 35 | 12-class quotient of `B_5` |
| 5 | 24 | 11 | 8-class quotient of `B_5` |

`25200 / 120 = 210`. Note that the `1⁵` row *is* `d(5)`, so this table also
recovers 7581 as a by-product.

**Lower levels.** The same code run at `n = 1, 2, 3` returns 5, 10 and 30 — and
at those levels the answer can be computed directly, by orbiting the lattice one
level up, because that lattice is small enough to build. It agrees, class sizes
included. The machinery is validated on levels where it is unnecessary before it
is trusted on the level where it is.

**The finding.** Define the *cofactor profile* of `f` as the multiset, over all
five variables, of the pair of atom classes `([f|xi=0], [f|xi=1])`. It is
`S_5`-invariant by construction, since permuting variables permutes the multiset.
It is also, at `n = 5`, **complete**: all 210 classes have distinct profiles, and
so do all 30 at `n = 4` and all 10 at `n = 3`.

That is a usable classification of the five-variable space in terms of the
four-variable atoms and nothing else — no canonical form, no isomorphism test,
no backtracking search. A single atom pair `{[f|x=0], [f|x=1]}` is not enough
(161 pairs are used, and one carries 4 different classes); taking all five
variables at once is.

It is a verified fact at three levels, **not a theorem**. The profile is a
one-round Weisfeiler-Leman refinement with atom classes as colours, and
invariants of that shape do fail eventually. Whether it survives at `n = 6` is
open and is not cheaply settled: it would need the 16,353 classes there, and the
fusion step as written is `O(#orbits)` in memory but still visits every orbit.

## 6. The note: why nothing here enumerates 7581

This was a stated constraint on the work, and it is worth recording why it is a
research contract and not a performance target.

- **It is the wrong list.** 7581 labelled functions collapse to 210 classes. An
  enumeration answers a question nobody asked and then requires the quotient
  anyway.
- **It does not survive one more step.** `d(6) = 7,828,354` and
  `d(9) ≈ 2.9 × 10^41`. A method that lists the space is finished at `n = 5`; the
  orbit-stabiliser step in §3 is `O(#atom classes × |lattice|)` and the shape of
  the argument does not change. If the technique is to say anything about the
  `n = 8` instances the thesis actually uses, it cannot begin by listing.
- **It hides the structure.** (2.1), (3.1) and (4.1) are the content. A loop
  over 7581 objects would return 210 without explaining it, and would not have
  produced the cofactor profile, which fell out of asking what the atoms
  determine.

The contract is enforced rather than documented.
`fka.dedekind.free_distributive_lattice` **raises** above
`MAX_LATTICE = 1000` elements, so `FDL(5)` cannot be built at all; the message
names the alternative. `test_the_lift_never_builds_the_level_above` spies on the
constructor and asserts the largest lattice the lift ever requests is `FDL(4)`,
and `test_the_lift_stays_under_budget` pins the 1568 memberships. The first
draft of §4 violated the contract — it keyed fusion on a table over all 7581
masks — and the budget test is what a future draft will hit.

## 7. What this does not claim

- The 210 classes are counted, represented and separated here; they are not
  *named*. Attaching structure descriptions to them is a separate job for
  `fka.automorphism` and the Sage backend.
- Nothing here touches duality. These are classes of monotone functions, not of
  dual pairs, and `Tr` does not respect the classification in any way this note
  establishes. The `S_5`-class of `f` does determine that of `Tr(f)`, since
  relabelling commutes with transversal, but the induced map on the 210 classes
  is not computed.
- No claim is made about `n >= 6`, for either the class count or the
  completeness of the cofactor profile.
- The reading of Jäkel's `intervals.txt` in §1 is inferred from the file
  contents and verified against `d(3)`, `d(4)` and `d(5)`; it is not taken from
  his paper, and his exact equivalence relation is bounded rather than
  identified.

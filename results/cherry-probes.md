# Degree-sum FK-A on GK: bottom pairs and the remaining obstruction

2026-10-23, based on `49d86eb`. Remote main was fetched; there were no later changes.
Conjectures 4.19 and 4.30 remain unresolved. No uniform linear upper bound has been obtained.

The statements below separate Lean theorems, written proofs and computations. None uses
isomorphism-cache visits in place of the quotient of the full labelled reach.

## Exact formal target and sufficient fuel

`GkDegreeSum.lean` defines `GK.reach k`, `GK.edges k`, `GK.delta k`, `GK.isoDelta k`,
`GK.IsoGrowth` and `GK.LabelledGrowth`. Its index zero denotes `f₁`:
the input is `gkH (2*k+1)` on `Fin (2^(2*k+1))`. The reach uses `splitVar`, modified=true,
fuel `n+1`, and the existing recursion without changing any stop or reduction.
`SD.isoKey` is the ordered-pair quotient by permutations of this fixed ground set.

**Lean:** `fkADagR_stable` proves that adding any fuel beyond the live support size changes
no reached pair, under any valid rule, even for nondual inputs. At a recursive step the
chosen live vertex disappears from both child supports; reductions can only shrink them.
The short-circuit verdict is fuel-independent by `fkAR_correct`. Thus `GK.reach_stable`
establishes sufficient fuel, not merely correctness of a fuel-truncated verdict.

**Lean:** `GK.edges_eq` identifies the actual finite-ground-set edge count as
`3*2^(2*2^k-2)`; `GK.edges_succ` proves `3*N_(k+1)=4*N_k²` exactly.
`GK.isoDelta_le` gives the quotient inequality and `GK.labelledGrowth_of_isoGrowth`
proves the implication between the two quantified conjectures.

**Lean, conditional:** `GK.isoGrowth_of_squaring` assumes `c>0`, a level `k₀`,
`X_(k+1) >= c*X_k²` at every `k>=k₀`, and `c*X_k₀ > (4/3)*N_k₀`, with
`X=GK.isoDelta`. It concludes the exact quantified growth assertion. There is a separate
`GK.labelledGrowth_of_squaring`. The proof normalizes `u=cX/((4/3)N)`, obtains
`u_(j+1)>=u_j²` and `u₀>1`, and proves `u_j>=1+(j+1)(u₀-1)`, which is unbounded.
The stronger bound `u_j>=u₀^(2^j)` also follows by induction (written, unused).
Neither the uniform recurrence nor a sufficient finite quotient seed is certified here.
In particular, the recorded `f₄` count is still a computation, not a Lean base case.

## Why an original bottom pair is completed immediately

An original bottom pair consists of consecutive labels `x=2i`, `y=2i+1` under an OR gate.
The following argument also applies to original AND pairs with the two sides exchanged.

**Lean local theorem:** `splitVar_or_mate` assumes the current reduced pair is Sperner,
`x` is its exact `splitVar`, `y=x+1`, the two vertices have equal degree sum, no first-side
edge contains both, and second-side edges contain `x` iff they contain `y`. It proves
that the reduced identity child `(C-x,D/x)` has exact split vertex `y`.
`splitVar_and_mate` proves the side-exchanging version.

The proof checks reductions as well as degrees. Deleting `x` removes no first-side edge
containing `y`. On the second side, erasure of `x` is injective on edges containing `y`,
and preserves Spernerness because `x,y` always occur together. Thus both degrees of `y`
are unchanged. `degree_minimal_del_le` and `degree_minimal_con_le` show that no other
degree increases. `splitVar_earlier` proves from the actual fold implementation that every
label before `x` had strictly smaller score. There is no label between `x` and `y`, and
`x` now has score zero. `splitVar_successor` therefore selects `y`, including least-label ties.
This is a pivot theorem: a leaf test can still terminate before another pivot is needed.

**Written GK application, not yet formalized:** whenever both members of an original
bottom pair survive a restriction, exchanging them preserves that restriction. Their two
degrees therefore agree. The read-once OR gate gives exactly the separation/cooccurrence
hypotheses above; global dualization exchanges their roles. At a state with no half-live
pair, the smaller member of the chosen pair is selected. Its absorbing child removes both
members, and its identity child leaves just the mate. Every other original pair remains
full or absent: exchanging its two unassigned leaves remains an automorphism after this
restriction. If the identity child continues, the local theorem forces its mate next.
Induction proves that every reached support has at most one half-live original pair.

Consequently two disjoint unions of original bottom pairs cannot both have odd support
size in the same state. This explains the odd-size obstruction in Observation 4.39,
including all odd/odd target pairs. It does not explain every other missing pair, and
does not imply that arbitrary even/even pairs occur.

The stronger assertion that *any* exposed leaf dominates its nonleaf siblings is false:
in `x OR ((a OR b) AND (c OR d))`, the degree points of `x` and `a` are `(1,4)` and `(2,2)`.
For weight `λ<1/2`, `a` beats `x`. The consecutive-original-pair argument avoids this claim.

## An exact weighted recursion on whole pairs

**Written proof, checked on finite runs:** at a state with no half-live original pair,
write its underlying primal formula as `F=H[z_i <- (x_2i OR x_(2i+1))]`. Each macro atom
has term/clause counts `(2,1)`. If `C_H` is the minimal DNF of `H`, then

```text
A(H) = sum_(e in C_H) 2^|e|,     B(H) = |Tr(C_H)|,
q_H(i) = sum_(e in C_H, i in e) 2^(|e|-1) + degree_(Tr(C_H))(i).
```

The exact macro pivot maximizes `q_H`, breaking ties by least original pair index.
It stops under precisely `A*B<=1` or `A=1` or `B=1`.

Let `P=F|z_i=0`, `Q=F|z_i=1` and `B'=F|x_2i=0`. For parent orientation `F`, the original
children are `B'` and `Q^d`; for orientation `F^d`, they are `Q^d` and `B'`. The forced
mate at `B'` has children `P` and `Q^d`. The two orientations therefore give the same
two macro children, in primal and dual orientation respectively, plus one transient `B'`.

Here `B'` cannot stop prematurely if its whole-pair parent splits. Every nonconstant macro
minterm contributes an even power of two to `A`. If `A=2`, there is exactly one singleton
macro minterm and no other relevant atom, so `B=1` and the parent was terminal. A splitting
parent thus has `A>=4`, `B>=2`. Removing one member of its chosen pair leaves `B` unchanged
and leaves `A' >= A/2 >=2`: for each macro term through that atom the number of expansions
halves, while the other terms remain. The identity child is nonterminal and its mate is
indeed split. This argument uses whole OR pairs; the unrestricted claim is false for
`(x OR y) AND z`, whose identity child `y AND z` is a modified leaf.

For labelled counts, if `E_k` counts whole-pair states, then `E_k<=δ_k<=2E_k`: every
transient comes from a deterministic pivot at some whole-pair ordered state. This does
not give the corresponding constant-factor comparison for isomorphism classes: differently
labelled copies of one whole-pair shape can select structurally different tied pairs.

## Local singleton stopping must be suppressed in the hull relaxation

**Checked by Lean evaluation:** `gk2_embedded_singleton` certifies that the first split
of `f₂` is 0, its zero child belongs to the actual reached set, and the child's support
in block `{0,1}` is `{1}`. Standalone `f₁` has `(2,1)` edges and stops under every rule,
including every positive weight (`fkADagR_singleton`). Its modified hull reach therefore
does not contain this projection. Lemma 4.36 must use an open-block hull process that
continues past local singleton-edge stops; it may stop at constants and literals when
only supports are counted. That is a relaxation, not standalone modified FK-A.

`experiments/cherry_probe.py` enumerates all pivots maximizing `deg_C+λ deg_D` for some
`λ>0`, chosen afresh at each state. It solves the rational linear inequalities exactly,
including strict inequalities against smaller labels. A second relaxation additionally
forces a surviving mate whenever a half pair exists. Both suppress local edge-count stops.

**Computed, complete:** original labels, full labelled DFS (right child first), no seed,
200,000-state cap and 60 seconds per hull run; no cap was reached. Raw output and source
hashes: [`cherry-probes.json`](cherry-probes.json).

| input | δ | δ_iso | whole-pair states | transient states | whole-pair classes | transient classes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| f₁ | 1 | 1 | 1 | 0 | 1 | 0 |
| f₂ | 8 | 8 | 5 | 3 | 5 | 3 |
| f₃ | 369 | 160 | 203 | 166 | 92 | 68 |

| local input | open-hull ordered states | open-hull supports | forced-mate ordered states | forced-mate supports |
| --- | ---: | ---: | ---: | ---: |
| f₁ | 3 | 3 | 3 | 3 |
| f₂ | 17 | 15 | 15 | 14 |
| f₃ | 8,992 | 6,604 | 2,712 | 2,387 |

Support counts include the empty support. The unrestricted hull on `f₃` allows up to five
half pairs at once; the forced-mate relaxation allows at most one. Yet its 2,387 supports
still exceed the recorded 1,893–1,908 top-block marginals inside `f₄`. Thus environmental
scheduling imposes constraints beyond the local hull and mate completion. The `f₄`
marginal counts are the prior computation, reproduced for blocks `a,c` by the new run below.

Reproduce with `python experiments/cherry_probe.py --out results/cherry-probes.json`.
Six targeted tests pass: macro reach is compared with the independent hypergraph memo
on `f₁–f₃`; feasible hull pivots are compared with all line crossings and intervening
intervals on the actual `f₃` reach; the singleton witness and incomplete-run flag are checked.
These are finite checks, not certification of an asymptotic base case.

## Isomorphism and visible block boundaries

**Written all-size canonicalization argument:** on active variables, join two vertices
when a minimal DNF term contains both. For a reduced read-once formula, OR gives disjoint
union of the children's graphs; AND gives graph join. At an OR root each child graph is
connected (a leaf or an AND root); its connected components recover the children. At an
AND root, the complement graph similarly recovers the children. A graph and its complement
cannot both be disconnected. Induction therefore recovers the reduced alternating cotree
uniquely, up to permuting children. Operation-coloured AHU equality is exactly isomorphism
of the minimal DNF and hence of the ordered dual pair. Constants have separate codes.
At fixed ambient `n`, equal shapes have equal active counts, and an active bijection extends
over the equally many isolated vertices. Side exchange is never added.

The Python normalizer absorbs constants. Rust prunes dead subtrees through its support
encoding; at a live gate the omitted inputs are identities. Both collapse unary gates and
flatten adjacent equal operations before interning sorted child shapes. Rust's hash table compares exact
codes/child vectors within each hash bucket. This argument justifies the shape equivalence;
it does not certify arbitrary machine executions or remove resource/index limits.

**Written bounded-multiplicity lemma:** restrict to reached states where all four top
blocks are nonconstant and retain their original OR roots. The reduced cotree then retains
the global binary OR, its two binary AND children, and the four OR-rooted block subtrees
(or all operations exchanged in the other orientation). One global ordered class permits
at most eight ordered `(shape(a),shape(c))` values: exchange the halves, then exchange
the two blocks in either half. Hence `P` distinct such shape pairs imply at least `P/8`
global classes. This does not apply to the existing support-pair table without further
proof: supports can share shapes, and the table does not require boundary preservation.

## Why a shape-only upper bound also fails

**Written obstruction, about all minors only:** even with every original bottom pair
full or absent, there are exponentially many possible residual shapes. At `f₂`, OR₂,
OR₄ and `f₂` itself give three distinct OR-rooted shapes, obtainable by whole-pair
restrictions. From `b` OR-rooted block shapes, unordered pairs give `t=b(b+1)/2` AND
shapes, and unordered pairs of those give `b'=t(t+1)/2 >= b⁴/8` OR shapes at the next level.
The intact cotree boundaries prove distinctness. Starting at `b₂=3` gives
`b_k >= 2*(3/2)^(4^(k-2))`, exponential in `n_k`, whereas
`N_k=(3/4)*2^(2^k)`. These are independently realizable restrictions, not states shown
reachable under degree sum. Thus neither the one-half-pair invariant nor counting whole-pair
minors supplies a uniform `O(N)` upper bound on the actual quotient.

## Equal degree profiles do not ensure synchronization, even for shapes

**Computed counterexample, complete `f₄` traversal:** a second mechanism was tested after
the hull obstruction. Restrict standalone `f₃` targets to nonempty unions of whole bottom
pairs. Group them by the edge counts and the full multiset of paired term/clause degrees,
in their underlying original orientation. Test whether every same-profile pair occurs
jointly in opposite blocks `a,c` of `f₄`.

The existing Rust joint traversal was extended only to retain its entire target incidence
matrix. On all 12 small family/rule configurations the matrix agrees entry by entry with
the independent formula traversal. The complete `f₄` run used original labels, modified
singleton stops and decreasing-live-support level traversal, with a 600-second cap and
disk spill. It finished in 161 s with `δ=67,247,387`. Its previous joint/equal-size records
are identical to `gk4-joint.json`. No random seed and no isomorphism pruning are involved.

| same-profile whole-pair targets | possible | reached |
| --- | ---: | ---: |
| ordered labelled support pairs | 696 | 578 |
| ordered underlying shape pairs | 71 | 66 |

There are 182 labelled targets, 71 degree profiles and 71 underlying shapes in this finite
set: each profile happens to identify a single shape here. Thus the second row consists
of 71 shape diagonals, five of which never occur, across any standalone label variants.
This 71 is not the 92 ordered whole-pair classes in the earlier table: here the actual
state's primal/dual orientation has been forgotten before taking block shapes.

For an explicit missing shape diagonal, a standalone support is
`{10,11,12,13,14,15,20,21,22,23,30,31}`. In original orientation its formula is

```text
(x10 OR x11)
OR ((x12 OR x13) AND (x14 OR x15))
OR ((x20 OR x21) AND (x22 OR x23) AND (x30 OR x31)).
```

Its edge counts are `(14,6)` and its degree-point multiset is
`2×(1,6), 4×(2,3), 6×(4,2)`. It has two standalone support variants; all four joint
incidence entries for these variants are zero. Thus even replacing identical labelled
targets by isomorphic targets does not repair this finite embedding candidate. It does
not refute Conjecture 4.40's constant-share assertion or either growth conjecture.

The five missing diagonals have the following edge counts and numbers of standalone
support variants; the analysis JSON records their complete degree profiles.

| terms | clauses | support variants |
| ---: | ---: | ---: |
| 14 | 6 | 2 |
| 20 | 3 | 1 |
| 28 | 3 | 1 |
| 32 | 6 | 1 |
| 52 | 20 | 3 |

Raw matrix: [`block-probes/gk4-incidence.json`](block-probes/gk4-incidence.json).
Profile analysis and source hashes: [`block-probes/gk4-profiles.json`](block-probes/gk4-profiles.json).
Reproduce the analysis with
`python experiments/block_profiles.py results/block-probes/gk4-incidence.json --out OUT.json`.
The test file checks this witness across its whole shape fiber and checks preservation of
the previous complete counts. All 29 targeted tests across `test_cherry_probe.py`,
`test_readonce_probe.py` and `test_block_profiles.py` pass. The full Python suite was not run.
The `f₄` absence is a computation, not a Lean-certified finite theorem.

## Unresolved lemma

The exact weighted macro rule is deterministic, including labels, but its reachable
class count has no proved growing lower bound relative to `N`, and no proved linear cover.
A sufficient next result is a uniform shape-pair reachability bound on a boundary-preserving
subclass large enough to meet a certified squaring seed. It must constrain realizable
environmental weight histories; neither open-hull membership nor identical endpoint
degree profiles can substitute for it.
Conjecture 4.40 remains an unproved labelled-support statement and supplies no automatic
control of shape collisions. The fixed-rule problem remains separate from C3 and from
the already proved tree lower bounds.

The primary source [Kaplan–Kushilevitz–Mansour, STOC 2005, §2.2](https://www.tau.ac.il/~mansour/papers/05stoc.pdf)
was checked for a scheduling method. Theorem 2.7 assumes uniform query costs and a uniform
input distribution, alternates separate term-frequency and clause-frequency maxima, and
bounds expected query cost. Its pivot and measured quantity both differ from this task;
no bound on the present reached classes follows.

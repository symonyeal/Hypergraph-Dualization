# Symmetry bounds the number of FK-A classes at shallow depth

Research of 2026-10-23. The upper bounds below are proved in
[`SymmetryDepth.lean`](../lean/HypergraphDualization/SymmetryDepth.lean).
The finite attainments are computations. The infinite sharpness construction in
the last section has a written proof and is not formalised. Priority in the
literature is not asserted.

## Statement

Let `G` be a Sperner hypergraph on `n` vertices, `0 ≤ k ≤ n`, and suppose
`Aut(G)` is `k`-transitive. Run either FK-A variant on `(G, Tr G)`, using any
rule that chooses a vertex in the current support. Neither symmetry under
exchanging the sides nor equivariance under relabelling is required of the rule.
Count isomorphisms of **ordered** pairs, preserving both side colours and the
ambient vertex set.

At each positive depth `j ≤ k`, there are at most `2j` classes. Including the
root, there are at most

```text
1 + k(k+1)
```

classes through depth `k`. If `G = Tr G`, the respective bounds are `j` and

```text
1 + k(k+1)/2.
```

The general argument also applies to an arbitrary pair `(C,D)` when its common
automorphism group is `k`-transitive. It requires only transitivity on disjoint
two-colour subsets with specified cardinalities; full `k`-transitivity is a
sufficient condition.

## Proof

For disjoint `A,B`, write

```text
M(C,A,B) = min { e \ B : e ∈ C, e ∩ A = ∅ },
P(C,D,A,B) = (M(C,A,B), M(D,B,A)).
```

Every node at depth `j` has the form `P(C,D,A,B)` or `P(D,C,A,B)`, with
`|A|+|B|=j`. At positive depth, **`A` is nonempty**. To see this, the root has
`A=B=∅`. At a fresh split vertex `x`, the two children of `P(C,D,A,B)` are

```text
left:   P(C,D,A∪{x},B),
right:  P(D,C,B∪{x},A).
```

Each inserts the latest split vertex into the first deletion set. This is the
invariant proved by `SD.Trace.normal`; `SD.fkADag_trace` connects it to the
actual recursion. In particular `|B|` lies in `0,…,j−1`.

For each source-side choice and each value of `|B|`, `j`-transitivity maps any
such `(A,B)` to any other. Reduction and restriction commute with relabelling
(`SD.cut_pimg`), so these nodes are isomorphic. This gives `2j` classes. If
`C=D`, the source-side choice disappears, giving `j`. Summing and adding the
root proves the bounds; classes shared between depths only reduce the total.

`SD.isoKey_eq_iff` identifies equality of the formal quotient with an actual
common vertex permutation of both sides. The final theorems
`SD.dual_transitive_bound` and `SD.self_transitive_bound` count this quotient,
with `SD.hom_of_ktransitive` supplying the group-action hypothesis. Their
`fkADagR` fuel is `k`: on a dual input this collects precisely the prefix of
the recursion through depth `k`. The proof also bounds all fresh-vertex split
paths, so stopping conditions and the choice of representatives cannot enlarge
the bound. `Axioms.lean` checks the standard trust base.

## Finite attainments and a false parity shortcut

The [generated table](../results/symmetry-depth.md) uses the actual Python FK-A
trees and exact isomorphism of three-colour incidence graphs, independently of
the cardinality signatures used in the proof.

| Pair | Depth cap | Classes at successive depths | Total |
| --- | ---: | --- | ---: |
| Complete 3-uniform family on 10 vertices and its 8-uniform dual | 2 | 1, 2, 4 | 7 |
| Fano plane with itself | 2 | 1, 1, 2 | 4 |
| Witt design `S(4,5,11)` with itself | 4 | 1, 1, 2, 3, 4 | 11 |

Each row was reproduced for degree-sum, leftmost and guarded rules, under both
variants: 18 configurations. Fano and Witt attain the self-transversal bound at
their respective transitivity depths.

The old proposed shortcut, that orientation is determined by the number of
original contracted vertices, is false. In the complete-family example,
paths `LR` and `RR` fix original bits `01` and `10`. Both contract one original
variable, but their first sides have ranks 7 and 2 on the remaining eight
vertices. The orientation is the **last original assigned bit**: it toggles
on an `R` branch. It is not the parity of the number of original ones.
Consequently `(k+1)(k+2)/2` is not a universal bound: at `k=2` it is 6,
whereas the completely symmetric example has 7 classes.

The tests also reconstruct the normal form at every node of all nine
instance/rule trees for the modified variant. The isomorphism oracle is tested
both on a relabelled pair and on a pair whose two side colours must remain
distinguished.

## Sharpness for arbitrary depth: written proof

Let `K(m,s)` be the family of all `s`-subsets of an `m`-set, with
`1 ≤ s ≤ m`. Its transversal is `K(m,m−s+1)`. Splitting any live vertex gives
first-side ranks `s` and `m−s+1`, on `m−1` remaining vertices. Hence, as long
as the nodes have not terminated, the attainable first-side ranks at positive
depth `j` from `K(n,r)` are exactly

```text
[r−j+1, r] ∪ [n−r−j+2, n−r+1].
```

This follows by induction from the rank transition above: retain each old rank
for a left child, and reflect it about `n−j+1` for a right child from depth
`j−1`. All variables have the same role, so the rank sets are independent of
the live-vertex rule.

For the general bound choose `n=4k+2`, `r=k+1`, `k≥1`. The two intervals are
disjoint and each has `j` ranks, for every `1≤j≤k`. No node before depth `k`
has a singleton side, so both variants reach them. Different ranks give
different ordered classes; different depths have different covered-support
sizes. This attains `1+k(k+1)` for every `k`.

For the self-transversal bound choose `n=2k+3`, `r=k+2`. The two intervals
coincide, giving `j` ranks at each positive depth. Again there is no early
termination, and covered-support sizes separate depths. This attains
`1+k(k+1)/2` for every `k`.

The rank recurrence and these infinite attainments are argued here, not Lean
declarations. The formal upper bounds do not depend on them.

## Limits

The result concerns a prefix of depth at most the transitivity degree. It gives
no bound on deeper states, on the number of labelled states, or on the time
needed to canonicalise a pair. It does not settle the GK asymptotics, the
isomorphism-cache correctness task, or the general dualization problem.

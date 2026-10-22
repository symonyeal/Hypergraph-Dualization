# Frequency equality and the Steiner classification: source audit

Research checked on 2026-10-21. This note separates elementary deductions from cited
structure theorems. No priority claim is made. The existing theorem and observation
register remains [`thesis/CLAIMS.md`](../thesis/CLAIMS.md).

The proved statements and their Lean names are consolidated in
[`research-2026-10.md`, Theorems 3.4–3.5 and Corollary 3.6](research-2026-10.md#the-gap-and-its-equality-case).
`FrequencyGap.lean` proves the excess identity, stability bound, full equality structure,
Sperner consequence and strict self-transversal gap. Its four-point counterexample and
Fano excess use `decide +kernel`. `#print axioms` lists only `propext`, `Classical.choice`
and `Quot.sound` for these results. The Gurvich and coding-theory connections below remain
cited statements. This note records the source checks behind the consolidated claims.

The later Proposition 3.7 strengthens the template exclusion: with both families
`r`-uniform on `r²` points, regularity of either one suffices for singleton cross intersections
(`uniform_regular_cross_singleton`). By the cited characterization, any remaining
non-read-once D3 candidate must have both sides irregular.

## 1. Frequency results and the boundary of the deduction

The incidence identity, stability bound and equality classification are proved in
`FrequencyGap.lean` and stated once in research Theorems 3.4–3.5. Equality forces
square order, uniformity, regularity, singleton cross intersections and the Sperner
property, without assuming Sperner initially. Corollary 3.6 gives the diagonal
correction for self-transversal families. In the regular uniform case it is the
same count as `intersecting_regular_bound`, not a second independent discovery.

The smallest-edge theorem `eps_bound` remains useful: its integral edge size can
strengthen the square-root bound on nonsquare orders. The new incidence proof
therefore complements it. Shared degree caps and `eps_ge_inv` consolidate its
repeated arguments.

## 2. Gurvich supplies the cited structural implication

For a monotone function with Sperner minterm family `G`, the maxterms are `Tr(G)`.
Gurvich's characterization says that this function is read-once precisely when
every minterm meets every maxterm in one variable. The original reference is
[Gurvich, *Repetition-free Boolean functions*, 1977, pp. 183–184](https://www.mathnet.ru/eng/rm3055).
A readable research-paper statement is [Das–Straßburger 2016, Theorem 4.10,
p. 9](https://lmcs.episciences.org/2621/pdf).

Combined with the Lean equality theorem, this implies that every equality
transversal pair is read-once. Its contrapositive gives the quantitative gap for
non-read-once pairs. The equivalence with this repository's `ReadOnce` definition
is cited, not proved in Lean.

This excludes non-read-once regular convergent templates in `hard-classes.md`
for every rank, extending the interpretation of the finite `r = 2,3` searches.
It leaves D3, which only assumes uniformity, open. The kernel-checked example
`path_four_not_extremal` has both sides 2-uniform on four points, but `eps = 2/3`
and cross excess 1: uniformity does not imply frequency equality. Proposition 3.7
further proves that either side being regular forces singleton cross
intersections; Gurvich then restricts any remaining D3 candidate to have both
sides irregular.

## 3. The Steiner conjecture needs precise scope and older connections

Use `2 <= t < k < v` in Conjecture 2.12. This makes its nontrivial Steiner
scope explicit. Bretto's local *Hypergraph Theory*, printed p. 3 (PDF p. 14),
defines Steiner systems with `2 <= t <= k < v`; the project intentionally
also handles degenerate parameters in Lean, so prose must state its restriction.

The parameter family `S(t,t+1,2t+3)` is classical in coding theory. With
`m = t+1`, it is `S(m-1,m,2m+1)`. Godsil records its equivalence with perfect
1-codes in the odd graph `O(m+1)`, whose vertices are the `m`-subsets of a
`(2m+1)`-set and whose adjacency is disjointness. The Fano and eleven-point Witt
examples are stated there. [Godsil, *Problems in Algebraic Combinatorics*, 1995,
§9, p. 13](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v2i1f1/pdf/).
This supplies a concrete older connection for Theorem 2.11; it does not establish
priority for its self-transversality formulation or classify all such designs.

For the projective-plane exclusion, cite an existence statement for nontrivial
blocking sets, rather than inferring existence from a lower bound on their size.
Bierbrauer explicitly states that every projective plane of order `q > 2`
contains a blocking set with no line and size `2q`. Such a set is a 2-colouring
witness for the line hypergraph. [Bierbrauer, *Blocking sets of maximal type in
finite projective planes*, 1981, introduction,
p. 85](https://www.numdam.org/item/RSMUP_1981__65__85_0.pdf).

Neither this exclusion nor the finite admissibility scan proves the full Steiner
classification. The stated conjecture remains open here. In particular, a scan
through `v <= 100` is evidence about parameters in that range, not a theorem
about every design at arbitrary order.

The phrase *self-blocking design* requires care in further searches. Jungnickel
uses it for designs whose **minimum-cardinality** blocking sets form a mutually
blocking design pair, a different condition from equality with the family of
**all inclusion-minimal** transversals. [Jungnickel, *Some self-blocking block
designs*, 1989,
abstract](https://www.sciencedirect.com/science/article/pii/0012365X89903567).

## 4. Local sources checked

`G:/idaholab/eitar makino gottlob 2008.pdf` is Eiter–Makino–Gottlob,
*Computational aspects of monotone dualization: A brief survey*, Discrete Applied
Mathematics 156 (2008), 2035–2049. Its §1, printed p. 2036 (PDF p. 2), explicitly
connects `Tr(H) = H` with intersecting edge-critical hypergraphs. This confirms
the existing criticality identification; it is cited background, not a new result.

`G:/idaholab/bretto_hypergraph-theory.pdf`, printed p. 53 (PDF p. 63), states
Theorem 3.6, the edge/vertex bound for a critical hypergraph. Its incidence-matrix
proof is the source already reflected in `Critical.lean`. The repository's
covered-support hypothesis is material: adding isolated ambient vertices cannot
increase the required number of edges.

These local files were read directly with `pypdf` using the installed Python 3.14.
The web references above were checked against publisher, journal, author, or
archival primary-source pages. Unsuccessful keyword searches provide no evidence
of novelty.

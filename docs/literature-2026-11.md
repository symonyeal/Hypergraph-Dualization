# Literature review, November 2026

Sources that bear on the open items of [`research-2026-10.md`](research-2026-10.md) §7,
checked on 17 November 2026 against revision `71f35a4`. Each entry says what was read
(full text, part, or abstract only) and what it changes here. Earlier source assessments and their reading limits are consolidated below.

## 1. Lower bounds for the Fredman–Khachiyan algorithms

**Elbassioni, *Unconditional lower bounds for the Fredman–Khachiyan algorithms for
monotone Boolean duality testing*, arXiv:2610.34474, v3, 3 November 2026.** Read: the
first 80k and last 35k of 175k characters of the HTML; Section 6, the references and
Appendix A only through a fetch summary.

- Theorem 3.6: on the Gurvich–Khachiyan alternating trees (the GK family here), every
  execution of Algorithm A, under every choice of branching variable, has at least
  `3^{(v_k+4)/12}/α(N)` terminal calls, so `N^{Θ(log N)}` on that family. The method is
  complex evaluation: a decision tree for `F` has at least `|P_F(z, …, z)|` leaves for
  `|z| ≤ 1`, `|1 − z| ≤ 1` (Lemma 3.4), evaluated at `z = (1 + i√3)/2` (Lemma 3.5).
- Theorem 4.10: Algorithm B makes `N^{Ω(√(log N/log log N))}` recursive calls on padded
  instances built from polynomials over `F_q`, after Kobayashi–Kurita–Wasa. This is the
  first unconditional lower bound for FK-B we know of.
- Definition 3.1(iv) excludes memoisation ("calls are not merged or memoized"). The
  distinct-subproblem count `δ` of Track C is not addressed.

*Relation to this repository.* Theorems 4.24–4.25 (Lean, 23 October 2026) give
`τ ≥ 2·(27/16)^{n/4}/(n + 1)` under every valid rule on GK and TK, through the Fourier `ℓ₁`
norm (JRSW). Per variable the bases are `(27/16)^{1/4} ≈ 1.1398` here and
`3^{1/12} ≈ 1.0959` in Elbassioni; both give `N^{Θ(log N)}`. The statement itself is older:
Gurvich–Khachiyan 1997 (§3 below), p. 246, say that alternating trees give an
`(|F| + |G|)^{Ω(log(|F| + |G|))}` lower bound for Algorithm A, without proof in that note.
So neither this repository nor Elbassioni has priority for the bound. Our Fourier proof is
machine-checked and has the larger constant; both sources are cited here. His Lemma 3.5
loses a factor 3 per level (`|u_{k+1}| ≥ |u_k|⁴/3`); his own bound, evaluated exactly, has
rate `0.37245` bits per variable, above both; our measures on blocks of eight variables
raise the rate to `0.41433` (see [`complex-evaluation.md`](complex-evaluation.md) §§1, 4, written
proofs). A size-optimal
decision tree for GK `f_k`, `k ≥ 4`, is not known (for `k ≤ 3` it is depth-first,
[`complex-evaluation.md`](complex-evaluation.md)): depth-first evaluation gives 62,833 leaves on `f₃`
(`n = 32`), `1.41` per variable, against the lower base `2^{0.41433} ≈ 1.33` (computed from the recursion
`(L₁, L₀)` of an OR/AND of disjoint parts; not measured further).

**Kobayashi, Kurita, Wasa, *An ETH-based quasipolynomial lower bound for Dualization*,
arXiv:2610.11473, v2, 9 October 2026.** Read in full (HTML).

- Theorem 1: from a 3-CNF with `n` variables, a deterministic algorithm builds `H` and `L`
  with `L ⊆ Tr(H)`, `φ` satisfiable iff `L ≠ Tr(H)`, of size `2^{O(n^{2/3}(log n)^{1/3})}`,
  in that time. The clause count is assumed `O(n³)`.
- Corollaries 8 and 10: under ETH, no `N^{o(√(log N/log log N))}` algorithm for Dual or
  Dualization.
- Section 4: the proof of Theorem 1 "was originally discovered by GPT-6 Astra (OpenAI)";
  the authors reconstructed, verified and rewrote it. Their stated open question is a
  conclusion under a weaker assumption.

**Mary, arXiv:2610.28012** (bounded-dimension transversal enumeration, maximum minimal
hitting set). Abstract only: ETH and SETH lower bounds.

**Takata** (Berge multiplication, `N^{Ω(log log N)}`) is the thesis's citation; not re-read.

## 2. The October 2026 SAT claims and Proposition 4.6

OpenAI posted *The Exponential Time Hypothesis is False* (26 October, with a Lean proof);
Anthropic posted a counting algorithm with a Lean statement the same week. News reports
of 27 October say Impagliazzo, Paturi and Williams are leading an examination; neither
claim was independently confirmed in the sources read. The bounds are
`2^{O(n log log n/√log n)}`. The reduction above needs less than ETH.

**Proposition L1 (written proof, from KKW Theorem 1).**
(a) If 3-SAT has no deterministic algorithm running in time `2^{O(n^{2/3}(log n)^{1/3})}`,
then for no split rule computable in polynomial time does a polynomial `p` satisfy `δ ≤ p(N)` on all dual pairs.
(b) For `2/3 < γ ≤ 1`: if 3-SAT has no `2^{o(n^γ)}` algorithm, then Dual has no
`N^{o((log N)^{(3γ − 2)/2}/(log log N)^{γ/2})}` algorithm. At `γ = 1` this is KKW's bound.

*Proof.* (a) is research Proposition 4.6.
(b) KKW Theorem 1 gives `log₂N ≤ L₀ = K n^{2/3}(log n)^{1/3}` for a constant `K`, and
`n = Θ(L₀^{3/2}/(log L₀)^{1/2})`. Take a Dual algorithm in time `N^{h(N)}` with `h`
nondecreasing (its running maximum satisfies the same bound) and `h(M) = o((log M)^{(3γ−2)/2}/(log log M)^{γ/2})`. It solves 3-SAT in
`2^{O(n^{2/3}(log n)^{1/3})} + 2^{log₂N · h(N)}` time, and
`log₂N · h(N) ≤ L₀ · h(2^{L₀}) = o(L₀^{3γ/2}/(log L₀)^{γ/2}) = o(n^γ)`. The first term is
also `2^{o(n^γ)}`, since `γ > 2/3`. ∎

The October algorithms run in `2^{n^{1−o(1)}}`; they refute no hypothesis of (a), nor of
(b) for any `γ < 1`. So the conditional picture is nearly unchanged: Dual stays
superpolynomial under (a), and for each `γ ∈ (2/3, 1)` keeps the bound of (b), under
hypotheses those algorithms leave open.

## 3. The frequency lemma

**Gurvich, Khachiyan, *On the frequency of the most frequently occurring variable in dual
monotone DNFs*, Discrete Math. 169 (1997) 245–248.** Read in full (copy supplied by the
author of this repository).

- (1) Some edge of `F ∪ G` has at most `log(|F| + |G|)` points (Seymour 1974, p. 310;
  Beck 1978). (2) Hence `max frequency ≥ 1/log(|F| + |G|)`; FK96 use (2).
- Proposition: the alternating trees have every edge of size at least `log(|F|+|G|)/2` and
  every frequency at most `2/log(|F|+|G|)`, with `|F_k| = 2^{2^k−1}`, `|G_k| = 2^{2^k−2}`.
- The note bounds the constant in (2) between 1 and 2. Neither a product form nor the
  value `3/2` appears.

*Consequence here:* [`frequency-constant.md`](frequency-constant.md) proves the product
form `|C||D| ≥ 4^{1/eps − 1}` (stronger than (2) when `|C| ≠ |D|`) and shows that the word
families meet `|C||D| = 8^{1/eps − 1}` exactly. The base 8 fails on a 36-variable
read-once pair (Proposition 7 there). For read-once pairs it proves
`|C||D| ≥ e^{2(1/eps − 1)}`, so their asymptotic constant is at least `log₂ e ≈ 1.443`.
Whether `3/2` is the asymptotic constant in general (as `eps → 0`; over all pairs the
constant is 1, from a single variable) is open.

**Gurvich, Khachiyan, *On generating the irredundant conjunctive and disjunctive normal
forms of monotone Boolean functions*, Rutgers LCSR-TR-251, 1995.** Read in full.
Theorem 1: joint generation of `C ⊔ D` in incremental quasi-polynomial time from an
evaluation oracle. Lemma 1: in a dual pair every term has at most `|D|` points and every
clause at most `|C|`. Theorems 4–7: separate generation of `C` or `D` is coNP-hard for
depth-3 formulas, relay circuits, positional games and polyhedral systems.

**Khachiyan, Boros, Elbassioni, Gurvich, *On enumerating minimal dicuts and strongly
connected subgraphs*, Algorithmica 50 (2008) 159–172.** Read pp. 159–162 and 168–172.
Generating minimal dicuts is NP-hard (Theorem 1); minimal strongly connected subgraphs
are generated in incremental polynomial time (Theorem 2); enumerating the "bodies" of a
point set contains hypergraph transversal (Proposition 1). Relevant to
the application interfaces in [`architecture.md`](architecture.md#interfaces), not to the open items.

## 4. Decision trees, FBDDs and proof complexity

- **JRSW Question 1** (Proposition 4.27). No answer found on 17 November 2026. Gál's and
  Bollig–Wegener's exponential read-once bounds are for functions with a small CNF, or a
  small DNF, not both (search snippets; papers not read).
- **Decision-tree size against DNF/CNF size.** The bound `exp(O(log n · log² N))` and the
  open `log n` factor are as recorded (Dahiya, *On (simple) decision tree rank*,
  arXiv:2209.12877, abstract and snippet only).
- **FBDDs and regular resolution.** Let `C,D` be a dual pair, with `C` the prime DNF of
  a monotone `f`. The CNF
  `F_{C,D} = ⋀_{c∈C} ⋁_{v∈c} ¬x_v ∧ ⋀_{d∈D} ⋁_{v∈d} x_v` is unsatisfiable. A read-once
  program that outputs a falsified clause computes `f` by reading the polarity of the clause:
  a negative clause gives 1 and a positive clause gives 0.
  The reverse translation requires a fixed witness at each sink. Different paths into the
  same Boolean sink can force different clauses. For example, an FBDD for `x ∨ y` can merge
  the paths certifying `x = 1` and `x = 0, y = 1` at its 1-sink. No one negative clause is
  falsified along both paths. A witness-labelled read-once program therefore needs its own
  construction and size bound. The cited regular-resolution correspondence concerns these
  witness-labelled programs. Theorems 4.13–4.14 relate unmodified FK-A to function-labelled
  FBDDs, and Theorem 4.25 gives a decision-tree bound. A size-preserving reduction to regular
  refutations, and polynomial-size general refutations of all such `F_{C,D}`, remain open here.
- **Decision-tree size against partitions.** Savický, *On determinism versus unambiguous
  nondeterminism for decision trees* (ECCC TR02-009; pages 1–4 read as page images, 17 November
  2026). It separates `dt(f)` from the partition number `p(f)` quasipolynomially for iterates of
  `g = (x₁ ∨ x₂ ∨ x₃)x₄ ∨ x₁x₂x₃`, not for the AND–OR tree, and proves `dt(f₁ ⊕ f₂) ≥ dt(f₁)dt(f₂)`
  on disjoint variables (Lemma 2.1) by the induction used for Lemma 15 of
  [`complex-evaluation.md`](complex-evaluation.md). Its Lemma 3.5 multiplies `r`, the least number of 1-leaves
  at full depth, under composition; `r(x ∧ y) = r(x ∨ y) = 1`, so on AND–OR trees it gives only `r ≥ 1`.
- **Memoised DPLL.** Beame, Impagliazzo, Pitassi, Segerlind, *Formula caching in DPLL*
  (CCC 2003; ACM TOCT 2010; abstract read): formula-caching DPLL simulates regular
  resolution, and some variants are stronger. Memoised FK-A is formula caching without
  component decomposition.
- **Knowledge compilation.** Beame, Li, Roy, Suciu: decision-DNNF converts to FBDD with
  quasi-polynomial blowup, polynomial for monotone `k`-DNF (snippet only).

## 5. Not read

FK96 itself (a PDF at `cs.tau.ac.il` was found, not read); the middle of Elbassioni's
paper; the proofs of the October SAT manuscripts; Gál; Bollig–Wegener; Dahiya beyond the
abstract; Tarsi, *Optimal search on some game trees* (J. ACM 30, 1983), whose depth-first
optimality for i.i.d. leaves is cited from secondary sources only; Savický TR02-009 beyond page 4.
Unsuccessful searches do not establish novelty.

## Sources

- [Elbassioni, arXiv:2610.34474](https://arxiv.org/html/2610.34474)
- [Kobayashi, Kurita, Wasa, arXiv:2610.11473](https://arxiv.org/abs/2610.11473)
- [Mary, arXiv:2610.28012](https://arxiv.org/html/2610.28012)
- [Gurvich, Khachiyan 1997, Discrete Math. 169](https://www.sciencedirect.com/science/article/pii/S0012365X96000908)
- [Gurvich, Khachiyan 1995, LCSR-TR-251](https://doi.org/10.7282/T3Z89GWD)
- [Khachiyan, Boros, Elbassioni, Gurvich 2008, Algorithmica 50](https://d-nb.info/1240129971/34)
- [Fredman, Khachiyan 1996, J. Algorithms 21](https://www.cs.tau.ac.il/~fiat/dmsem03/On%20the%20complexity%20of%20Dualization%20of%20monotone%20Disjunctive%20Normal%20Forms%20-%201996.pdf)
- [Dahiya, arXiv:2209.12877](https://arxiv.org/pdf/2209.12877)
- [Beame, Impagliazzo, Pitassi, Segerlind, formula caching](https://www.cs.toronto.edu/~toni/Papers/memoization.pdf)
- [Razgon, read-once branching programs and bounded-treewidth CNFs](https://arxiv.org/pdf/1411.0264)
- [Washington Times on the ETH verification, 27 October 2026](https://www.washingtontimes.com/news/2026/oct/27/openai-says-model-refuted-exponential-time-hypothesis/)
- [Eiter, Makino, Gottlob, survey (DAM 2008)](https://dl.acm.org/doi/10.1016/j.dam.2007.04.017)

## 6. SAT source scope and the transfer encoding

[OpenAI's manuscript](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf),
dated 17 October and revised 25 October, states a deterministic algorithm for
exactly counting satisfying assignments of fixed-width CNF formulas in polynomial
space. Theorem 1.1 bounds its time by
`(n+m)^{O_k(1)} 2^{O_k(n log log n / sqrt(log n))}`; at fixed clause density the
exponent improves to `O_{k,D}(n / sqrt(log n))`. Here `n` counts variables, `m`
counts clauses and `k` bounds clause width.

[Anthropic's manuscript](https://github.com/anthropics/formal-math/blob/main/eth/paper.pdf),
dated 26 October, states a deterministic counting algorithm with time
`2^{O(min{k² n log log n / sqrt(log n), k m / sqrt(log m)})}`. Both results would
refute ETH, and their fixed-width guarantees also contradict SETH.

Both publishers provide Lean formalizations. The main theorem statements and
introductory scope of both manuscripts were read; the complete proofs were not
audited. Anthropic's [statement file](https://github.com/anthropics/formal-math/blob/main/eth/MainResults.lean)
explicitly defines the machine, input encoding, count and time bound; its
[README](https://github.com/anthropics/formal-math/blob/main/eth/README.md) documents
axiom and comparator checks. These external builds were not run here.
[OpenAI's announcement](https://openai.com/index/building-scientific-understanding-with-academic-communities/)
describes an independent examination led by Impagliazzo, Paturi and Williams.
The status used below is therefore a published claim with accompanying formal
artifacts, not an independently reproduced theorem in this project.

The following is a standard encoding argument, not a new theorem from either
manuscript. First check `L ⊆ Tr(H)` explicitly. Then a missing transversal exists
exactly when the formula

`F(x) = (AND_{E in H} OR_{v in E} x_v) AND (AND_{T in L} OR_{v in T} NOT x_v)`

is satisfiable. A satisfying assignment is a hitting set containing no listed
transversal. Minimizing it preserves that property and gives a missing minimal
transversal; conversely a missing minimal transversal contains no other minimal
transversal. This proves the stated equivalence under the inclusion check.

Its width is the largest edge on either side, not just the rank of `H`. Thus a
bounded-rank input alone does not provide fixed-width CNF. A conversion to 3-CNF
can introduce a number of variables proportional to the total incidence size.
A subexponential bound in that expanded size need not improve on FK-B's existing
quasipolynomial input-size bound. No such improvement has been established here.

The new algebraic and tensor-contraction methods could motivate algorithms beyond
variable splitting. A useful transfer must specify a representation, include its
construction and arithmetic costs, and beat the existing bound in the same input
parameter. A faster evaluation algorithm alone does not compress the FK-A DAG.


## 7. Frequency equality and Steiner sources

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

### Steiner scope and coding theory

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

### Sources read locally in October 2026

Eiter–Makino–Gottlob,
*Computational aspects of monotone dualization: A brief survey*, Discrete Applied
Mathematics 156 (2008), 2035–2049. Its §1, printed p. 2036 (PDF p. 2), explicitly
connects `Tr(H) = H` with intersecting edge-critical hypergraphs. This confirms
the existing criticality identification; it is cited background, not a new result.

Bretto, *Hypergraph Theory*, printed p. 53 (PDF p. 63), states
Theorem 3.6, the edge/vertex bound for a critical hypergraph. Its incidence-matrix
proof is the source already reflected in `Critical.lean`. The repository's
covered-support hypothesis is material: adding isolated ambient vertices cannot
increase the required number of edges.

These local files were read directly with `pypdf` using the installed Python 3.14.
The web references above were checked against publisher, journal, author, or
archival primary-source pages. Unsuccessful keyword searches provide no evidence
of novelty.

## 8. Connections to openai/math

[`openai/math`](https://github.com/openai/math) collects 719 manuscripts in 372 result families,
with a Lean library for some of them. This note records which of those results touch the thesis,
surveyed on 2026-10-20 from the repository's `CONTENTS.md`, `overview.tex` and
`lean/formalization.yaml`. Every statement made here about the thesis side is proved in
[`lean/HypergraphDualization/Connections.lean`](../lean/HypergraphDualization/Connections.lean);
statements about the `openai/math` results are theirs and are cited, not re-proved.

### Direct connections

| Family | Result | Bridge to the thesis | Lean |
| --- | --- | --- | --- |
| 162 | Counterexamples to Ryser's covering conjecture: intersecting `(q+1)`-partite `(q+1)`-uniform hypergraphs with covering number `q+1`, formalized as `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank` | A cover is a transversal, and the covering number `τ(H)` is the size of a smallest edge of `Tr(H)`. An intersecting `r`-uniform `H` always has `τ ≤ r`; Ryser's bound is `r − 1`, so the counterexamples are the extremal case `τ = r`. In that case every edge of `H` and of `Tr(H)` has at least `r` vertices, and Corollary 2.3.1 (corrected) gives `|H| + |Tr(H)| ≥ 2^r` | `isCover_iff_hits`, `coverNumber_eq_tr_min`, `coverNumber_le_of_intersecting`, `ryser_extremal_size` |
| 186, 176, 175 | Friedgut–Kalai threshold widths; the second Kahn–Kalai conjecture (formalized as `OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds`); Talagrand's expectation-threshold conjectures | A Sperner hypergraph is a monotone property: a set has it when it contains an edge. For a transversal pair `(G, H)`, `P_p(G) + P_{1−p}(H) = 1`, with `P_p` the product measure `bernoulliProbability` of the formalization. Duality is complementation composed with `p ↦ 1 − p`, so a self-transversal hypergraph (`K₃`, the Fano plane; `hw₃` likewise, not instantiated in Lean) has `P_{1/2} = 1/2`: its critical probability is exactly `1/2` | `bernoulli_dual`, `bernoulli_self_dual`, `fano_k3_balanced` |
| 186 | The Friedgut–Kalai hypothesis is relabeling invariance: a transitive symmetry group | A transitive `Aut(H)` makes every vertex equally frequent, the frequency FK-A splits on (§5.2.2); this is the setting in which the Fano plane is hard for FK-A | `degree_eq_of_transitive` |

The definitions `IsCover`, `Intersecting`, `coverCardinalities`, `coverNumber`,
`bernoulliWeight` and `bernoulliProbability` are restated verbatim from
`lean/ComparatorChallenges/RyserCovering.lean` and `SecondKahnKalai.lean`, so the bridge
theorems are statements about the same objects. The `openai/math` library itself is not imported:
it pins Lean `v4.34.1` and this project pins `v4.35.0`.

### Reproduction

`lake build HypergraphDualization.Connections` from `lean/` checks the bridge declarations
named in the table. It does not check the cited manuscripts or their identifications.
The candidates were drawn from the theoretical computer science, combinatorics and group theory
sections of `overview.tex`, read entry by entry, and from a keyword search of the whole catalogue
(transversal, hypergraph, covering, monotone, Boolean, DNF, threshold, self-dual, automorphism,
permutation group, projective plane, Sperner, antichain, Dedekind). Families outside those
sections that match no keyword were not read.

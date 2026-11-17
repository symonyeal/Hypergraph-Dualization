# Literature review, November 2026

Sources that bear on the open items of [`research-2026-10.md`](research-2026-10.md) §7,
checked on 17 November 2026 against revision `71f35a4`. Each entry says what was read
(full text, part, or abstract only) and what it changes here. The earlier surveys are
[`openai-math-connections.md`](openai-math-connections.md) and
[`complexity-update-2026-10.md`](complexity-update-2026-10.md); this note does not repeat them.

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
machine-checked and has the larger constant; research §4 should cite both. His Lemma 3.5
loses a factor 3 per level (`|u_{k+1}| ≥ |u_k|⁴/3`); his own bound, evaluated exactly, has
rate `0.37245` bits per variable, above both; our measures on blocks of eight variables
raise the rate to `0.41433` (see [`complex-evaluation.md`](complex-evaluation.md) §§2, 4, written
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
`2^{O(n log log n/√log n)}` (see `complexity-update-2026-10.md`).

`complexity-update-2026-10.md` said that, if these claims hold, Proposition 4.6 "supplies
no obstruction to a polynomial bound". That overstates it. The reduction above needs much
less than ETH.

**Proposition L1 (written proof, from KKW Theorem 1).**
(a) If 3-SAT has no deterministic algorithm running in time `2^{O(n^{2/3}(log n)^{1/3})}`,
then no polynomial `p` satisfies `δ ≤ p(N)` on all dual pairs.
(b) For `2/3 < γ ≤ 1`: if 3-SAT has no `2^{o(n^γ)}` algorithm, then Dual has no
`N^{o((log N)^{(3γ − 2)/2}/(log log N)^{γ/2})}` algorithm. At `γ = 1` this is KKW's bound.

*Proof.* (a) As in Proposition 4.6, `δ ≤ p(N)` gives a polynomial-time duality test
(memoised FK-A, answering "not dual" past `p(N)` subproblems). On KKW's instances,
`N = 2^{O(n^{2/3}(log n)^{1/3})}`, so 3-SAT would run in `2^{O(n^{2/3}(log n)^{1/3})}`.
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
[`applications.md`](applications.md), not to the open items.

## 4. Decision trees, FBDDs and proof complexity

- **JRSW Question 1** (Proposition 4.27). No answer found on 17 November 2026. Gál's and
  Bollig–Wegener's exponential read-once bounds are for functions with a small CNF, or a
  small DNF, not both (search snippets; papers not read).
- **Decision-tree size against DNF/CNF size.** The bound `exp(O(log n · log² N))` and the
  open `log n` factor are as recorded (Dahiya, *On (simple) decision tree rank*,
  arXiv:2209.12877, abstract and snippet only).
- **FBDDs are regular resolution here (argued, not in Lean).** For a dual pair, let
  `F_{C,D} = ⋀_{c∈C} ⋁_{v∈c} ¬x_v ∧ ⋀_{d∈D} ⋁_{v∈d} x_v`, unsatisfiable exactly when
  `D = Tr C` (review row 40). An FBDD for the monotone `f` is a read-once branching program
  for the search problem of `F_{C,D}`: a 1-sink's path contains a term, so it falsifies a
  negative clause; a 0-sink's path misses a clause of `D`. Conversely, every read-once
  program for that search problem computes `f`, since each sink names a falsified clause
  and so fixes `f`. By the standard correspondence between regular resolution and
  read-once branching programs for search problems (cited, not read), the least FBDD of
  `f` and the least regular refutation of `F_{C,D}` agree up to constant factors. With
  Theorems 4.13–4.14, C3 for unmodified FK-A, and the monotone case of JRSW Question 1, ask
  for a superpolynomial *regular-resolution* lower bound for these split, cross-intersecting
  CNFs. Theorem 4.25 is the tree-like case. Whether *general* resolution refutes every
  `F_{C,D}` in polynomial size is open here.
- **Memoised DPLL.** Beame, Impagliazzo, Pitassi, Segerlind, *Formula caching in DPLL*
  (CCC 2003; ACM TOCT 2010; abstract read): formula-caching DPLL simulates regular
  resolution, and some variants are stronger. Memoised FK-A is formula caching without
  component decomposition.
- **Knowledge compilation.** Beame, Li, Roy, Suciu: decision-DNNF converts to FBDD with
  quasi-polynomial blowup, polynomial for monotone `k`-DNF (snippet only).

## 5. Not read

FK96 itself (a PDF at `cs.tau.ac.il` was found, not read); the middle of Elbassioni's
paper; the proofs of the October SAT manuscripts; Gál; Bollig–Wegener; Dahiya beyond the
abstract. Unsuccessful searches do not establish novelty.

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

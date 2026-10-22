# Applications of dualization: a catalogue for future work

Sources: Hagen, *Algorithmic and Computational Complexity Issues of MONET* (PhD thesis, Jena
2008), Chapter 3, a survey of about seventy applications with references (bracketed keys below
are Hagen's); Eiter, Makino and Gottlob, *Computational aspects of monotone dualization*,
Discrete Appl. Math. 156 (2008), §7; Defrain, *On the dualization problem in graphs, hypergraphs,
and lattices* (PhD thesis, Clermont-Ferrand 2020); Pawelski and Szepietowski, *Counting
self-dual monotone Boolean functions*, J. Integer Seq. 28 (2025). The one industrial study
already carried out, qualified supplier panels, is its own repository,
[Resilient-Supplier-Panels](https://github.com/symonyeal/Resilient-Supplier-Panels).

Nothing below has been run on application data. Each entry states the reduction to `Tr`; the
shortlist in §3 states what a first study would measure.

## 1. Four formulations

Every application uses one of four forms of the same problem. Each has a counterpart in this
repository.

| Form | Question | Here |
| --- | --- | --- |
| Generation | list `Tr(H)` | `fka.transversal`; FK-A as an enumerator |
| Duality check | is `G = Tr(H)`? If not, give a witness set | `fka.algorithm.fk_a`, FK-B; `fkA_correct` (Lean) |
| Incremental | given `G ⊆ Tr(H)`, find a new minimal transversal or certify `G = Tr(H)` | the FK-A witness, extended to a minimal transversal |
| Self-duality | is `Tr(H) = H`? | Proposition A3, counting test, Seymour bound (`SelfTransversal`, `Critical`) |

The incremental form is the one most applications need: the output is produced one set at a
time, each step being a duality check on the sets found so far (joint generation). Its cost per
step is that of FK-A or FK-B.

No form is known to be polynomial. Kobayashi, Kurita and Wasa (arXiv:2610.11473, Oct 2026,
preprint) show that, under the exponential-time hypothesis, the duality check has no
`N^{o(√(log N / log log N))}` algorithm; FK-B runs in `N^{o(log N)}`. Practical use therefore
depends on structure. The polynomial classes surveyed by Hagen (Ch. 4) and Eiter–Makino–Gottlob
(§6.2) include bounded edge size, bounded degree, read-once (Hertel 2004: polynomial with
memoisation), acyclic, bounded treewidth, regular, aligned and 2-monotonic hypergraphs. The first
question about any application instance is which of these it falls into.

## 2. Catalogue

Grouped by what `H` and `Tr(H)` are. "Gen." is generation, "Dual" the duality check, "Self" the
self-duality test.

### 2.1 Reliability: paths and cuts

| Application | `H` | `Tr(H)` | Form |
| --- | --- | --- | --- |
| Network reliability | minimal source–sink path sets | minimal cut sets | Gen. |
| Metabolic cut sets [KG04, Kla06, HKS08, IB07] | elementary modes through the target reaction | minimal reaction knockouts that block it | Gen. |
| Vaccination strategies [BG07b] | transmission chains from the infected set | minimal vaccination sets | Gen. |
| Supplier continuity | qualified suppliers per product, per scenario | minimal resilient panels | Gen. (Resilient-Supplier-Panels) |

The identity `P_p(G) + P_{1−p}(Tr G) = 1` (`Connections`) is the Moore–Shannon duality between a
system and its cuts: the reliability of a path family at component reliability `p` is one minus
that of its cut family at `1 − p`.

### 2.2 Diagnosis and repair

| Application | `H` | `Tr(H)` | Form |
| --- | --- | --- | --- |
| Model-based diagnosis [Rei87, GSW89] | minimal conflict sets of components | minimal diagnoses | Gen. |
| Infeasible linear systems [Pfe02] | irreducibly infeasible subsystems | minimal deletions restoring feasibility | Gen. |
| Type-error diagnosis [BS05], UML repair [SKU06], specification revision [SU05] | minimal unsatisfiable constraint sets | minimal corrections | Gen. |
| Failing database queries [God97] | minimal failing subqueries | minimal relaxations | Gen. |

### 2.3 Data mining and learning

| Application | `H` | `Tr(H)` | Form |
| --- | --- | --- | --- |
| Frequent itemsets [BGKM03, GKMT97] | complements of maximal `t`-frequent sets | minimal `t`-infrequent sets | Incremental |
| Emerging patterns [BMR03, DL05] | differences of transactions between two data sets | minimal discriminating itemsets | Gen. |
| Minimal generators of closed itemsets [PT02] | per closed set, the obstructions | minimal generators | Gen. |
| Rough-set reducts [Pop04] | discernibility sets of object pairs | minimal attribute reducts | Gen. |
| Learning a monotone function by membership queries [BI95a, GKMT97] | minimal true points found so far | candidate maximal false points to query | Incremental |

Eiter–Makino–Gottlob (§7) report experiments in which refined Berge variants
(Kavvadias–Stavropoulos, Bailey–Manoukian–Ramamohanarao, Uno) outran FK-B, and note that a
systematic comparison and a collection of hard instances were missing; `results/fk-a-vs-fk-b.md` and
`docs/hard-cases.md` are a start on the second.

### 2.4 Databases and lattices

| Application | `H` | `Tr(H)` | Form |
| --- | --- | --- | --- |
| Minimal keys of a relation [DT87, EG95] | complements of agree sets of tuple pairs | minimal keys | Gen. / Dual |
| Functional dependencies from data [MR86, KM95] | per attribute `a`, complements of the agree sets of tuple pairs that differ on `a` | minimal left-hand sides `X → a` | Gen. |
| Armstrong relations [MR86, EG95] | minimal keys | maximal non-keys | Dual |
| Implicational bases, formal concept analysis (Defrain Ch. 3–4) | meet-irreducibles of a closure system | minimal generators / critical sets | Gen., generalised |

Defrain shows that dualization in lattices given by implicational bases is hard already in
dimension two, and tractable for bounded independent-width; the Boolean case is ordinary `Tr`.

### 2.5 Distributed systems and games: the self-dual case

| Application | `H` | Question | Form |
| --- | --- | --- | --- |
| Mutual exclusion [GB85, IK93] | a coterie (quorum system): pairwise intersecting Sperner family | is it non-dominated? | Self |
| Simple games [EG95] | minimal winning coalitions | is the game constant-sum (decisive)? | Self |
| Tight game forms, Nash solvability [Gur75, BGM07] | the two players' outcome DNFs | are they dual? | Dual |
| Intersecting 2-colouring, NAESPI [EG95, GK04b] | an intersecting family | is there a 2-colouring? | complement of Self |

A coterie is non-dominated iff it is self-transversal (Garcia-Molina–Barbara 1985;
Ibaraki–Kameda 1993). Here every result of Track A reads as a statement about quorum systems:

- A3: non-dominated iff intersecting and not 2-colourable; the counting test: iff exactly
  `2^{n−1}` node sets contain a quorum (`tr_eq_self_iff_card`).
- Seymour's bound: a non-dominated coterie on `n` nodes has at least `n` quorums
  (`card_le_of_tr_eq_self`).
- Every Steiner system `S(t, t+1, 2t+3)` is a non-dominated coterie with quorums of size `t+1`
  on `2t+3` nodes (`witt_tr_eq`), smaller than the majority quorum `t+2`: the Fano plane (3 of 7)
  and the Witt design (5 of 11). Their automorphism groups are transitive, so every node carries
  the same load.
- Edge-transitive non-dominated coteries are node-transitive (`transitive_of_edge_transitive`).
- Composition of coteries (join of quorum systems) is substitution `T[Γ]` (Track D).

Pawelski and Szepietowski count the self-dual monotone functions: `λ_7 = 1,422,564`,
`λ_8 = 229,809,982,112`, and `q_8 = 6,001,501` classes up to permutation of the nodes (`q_7 = 716`).
These are the non-dominated coteries, so a complete classification on at most 7 nodes is 716
cases.

### 2.6 Logic and knowledge representation

Abduction over Horn theories [EG02, EM07]; Horn envelopes and characteristic models [Kha95];
propositional circumscription for monotone inputs [DH08]; version-space convergence for monotone
concepts [HMP04]; IMSAT and bi-hitting satisfiability, which are complements of Dual [EG95,
GK04a]. Khardon's translation between a Horn CNF and its characteristic models is equivalent to
dualization.

### 2.7 Graphs, optimisation, geometry

- Minimal dominating sets: enumeration is equivalent to dualization (Kanté, Limouzy, Mary and
  Nourine 2014); Defrain Ch. 2 gives output-polynomial algorithms on classes related to `K_t`-free graphs
  and to posets of bounded dimension. The ETH bound above transfers to co-bipartite graphs.
- Maximal independent sets of a hypergraph are complements of minimal transversals [BEGK04].
- Minimal feasible solutions of a monotone 0/1 system `Ax ≥ b` [BEG+02], of polymatroid
  inequalities [BEGK03a], partial and multiple transversals [BGKM01]: dual-bounded, so generated in
  quasi-polynomial incremental time.
- Matroids: maximal sets spanning none of a given set, cut-conjunctions [KBB+08].
- Geometry and topology: minimal point sets containing `z` in their convex hull [KBEG08b];
  maximal `k`-boxes [KBE+07]; minimal non-faces of a simplicial complex [BCE+00].
- Other: an attack on anonymity protocols uses FK-B directly [KP04]; channel assignment [MS94];
  two-layer planarization [DFH+01].

## 3. Shortlist for this repository

Ranked by how much of the existing work transfers. None has been started.

1. **Quorum systems (§2.5).** The self-dual theory is the strongest part of the repository.
   Deliverable: a certified non-dominated-coterie checker (counting test and A3, with a Lean
   certificate for each verdict), the symmetric coteries from Steiner systems with quorum size,
   load and availability `P_p` against majority, and FK-A/FK-B node counts on all 716 classes
   on at most 7 nodes (which also supplies the data item A6 asks for).
2. **Metabolic minimal cut sets (§2.1).** Public genome-scale models (BiGG) give large, real,
   sparse instances. Measure FK-A, FK-B and the memoised `δ` against the elementary-mode
   duality tools; record which easy class the instances fall into.
3. **Frequent-itemset borders (§2.3).** The FIMI benchmark data give the incremental form at
   scale. Compare joint generation through FK-A with the Berge variants of §7 of
   Eiter–Makino–Gottlob, on the instances where they disagree most.
4. **Model-based diagnosis (§2.2).** ISCAS-85 circuits are the standard benchmark; conflicts
   to diagnoses is one `Tr`.
5. **Keys and functional dependencies (§2.4).** UCI tables; minimal keys from agree sets.

Data sources named in this section were not downloaded or inspected.

## 4. Dictionary: FK-A's notions in other formulations

§2 lists what `H` and `Tr(H)` are in each application. This section maps FK-A's own notions,
for the formulations where the map transfers a theorem or technique in either direction with a
consequence checkable here. Write `f` for the monotone function with DNF `G`. Throughout,
deletion `G − x` is `f|x=0`, contraction `min(G/x)` is `f|x=1`, the split at `x` is the Shannon
expansion `f = x̄·f|x=0 ∨ x·f|x=1`, and the subproblems are the restrictions `f|ρ` with a side tag
(research §4, Theorem 4.7). The vocabulary of hypergraphs and normal forms is in
[`dictionary.md`](dictionary.md). Status: *Lean*, *Python*, *Cited* (read), *Unchecked* (cited
from memory or a secondary source); each row is a row of the review log, research §8.

| Formulation | `(G, Tr G)` | FK-A's split; the memo DAG | frequency `ε` | Transfer, direction, check | Status |
| --- | --- | --- | --- | --- | --- |
| Knowledge compilation: OBDD, FBDD | `f`; its DNF and CNF | Shannon decision node; the memo DAG is an FBDD named by its functions (Thm 4.13), an OBDD under a static order | — | KC → FK-A: an FBDD lower bound for `f` bounds `δ` for every rule (Cor. 4.15); the OBDD of a read-once formula in leaf order has one node per variable, so `δ ≤ 2n + 2` under the leftmost rule (Thm 4.16). Check: `δ = n` on GK `f₂–f₅`, TK `S₁–S₄` | Lean (8 theorems), Rust |
| Decision-DNNF, component caching (model counting) | — | FK-A has no decomposition node: on disjoint inputs its subproblems are pairs of input states (Lemma 4.17), where a decomposition node would make them a sum | — | KC → FK-A: split off disjoint components before branching. Check: the product structure is Lemma 4.17; the decomposing variant is not implemented | Lean (lemma); technique open |
| DPLL, tree and regular resolution | `(G, H)` is dual iff cross-intersecting and `⋀_g ⋁_{i∈g} x̄ᵢ ∧ ⋀_h ⋁_{i∈h} xᵢ` (`N` clauses) is unsatisfiable | a DPLL branch; the tree is a tree-like refutation shape, the memo DAG a read-once branching program, the model of regular resolution | condition (iv), `Σ 2^{-\|c\|} ≥ 1`, is the counting bound for unsatisfiable CNFs | Proof complexity → FK-A: the short-clause lemma behind Ehrenfeucht–Haussler (Savický's proof) is FK96 Lemma 2.3.2; it also caps FBDD mixedness at `log₂ N` (research §4) | Lean (`kraft_sum`, `two_pow_shortest_le`, `exists_frequent_vertex`); reading cited |
| Fault trees, coherent structure functions | top event `f`; minimal cut sets `G`, minimal path sets `Tr G` | Shannon decomposition on a basic event; the fault tree's BDD | Birnbaum importance (an influence) | FTA → FK-A: the depth-first left-most order for trees without repeated events is the leftmost rule; FK-A → FTA: its linear size is Theorem 4.16 | Lean for the bound; Rauzy 1993 unchecked |
| Matroids | circuits of `M`; `Tr` = bases of `M*` | matroid deletion and contraction (Tutte's recursion); subproblems are minors `M\S/T` | — | Matroids → FK-A: `U(k, n)` has only the minor types `U(k′, n′)`; all degrees tie, so every rule follows the least live vertex and `δ` is quadratic in `n` (`(n/2)²` at `k = n/2`) | Matroid facts cited; `δ` Python (`results/split-rules.md`, `tests/test_memo.py`) |
| Squarefree monomial ideals | `I_G = (x^g)`; minimal primes `(xᵢ : i ∈ T)`, `T ∈ Tr G`; Alexander dual `I_{Tr G}` | colon and sum `(I : x)`, `(I, x)`; pivot recursions for Hilbert series (Bigatti) and Roune's slice algorithm for the Alexander dual | — | Algebra → FK-A: pivot strategies are split rules. Check: the colon/sum identities are `Fm.dnf_restrict_true`, `Fm.dnf_restrict_false`; the strategies were not measured | Lean for the identities; sources unchecked |
| Simple games, voting | minimal winning coalitions `G`; blocking coalitions `Tr G`; decisive games are `Tr G = G` | — | `deg_G x` is the numerator of Holler's public good index | FK-A → games: automorphisms preserve Banzhaf power, so anonymous games have equal power (`influence_aut`); decisive iff intersecting and not 2-colourable (`tr_eq_self_iff`) | Lean (existing); Holler unchecked, no transfer |
| Percolation, sharp thresholds | crossing event and its dual | — | influences | `P_p(G) + P_{1−p}(Tr G) = 1`, self-dual threshold `1/2` (`bernoulli_dual`, `bernoulli_self_dual`; `openai-math-connections.md`) | Lean (existing) |

Discarded, with the reason:

- *Karchmer–Wigderson games.* On `(G, Tr G)` the monotone KW relation is the cross-intersection
  `g ∩ h ≠ ∅` (`edges_meet`); no bound on `δ` or on split rules follows.
- *Exact learning with membership queries; borders and Dualize-and-Advance; minimal keys and
  Armstrong relations; Reiter's diagnoses; metabolic cut sets; network reliability; attack
  trees; coteries.* Catalogued in §2 as instances of `Tr`; none transfers a statement about the
  split rule or the memo DAG.
- *Lehman's theorem, ideal clutters.* It concerns minimally non-ideal clutters; candidates for
  D3 (research, Open problem 5.3) need not be, so it does not settle D3 at `r = 3`.
- *Influence lemmas (KKL, Friedgut–Kalai) against FK96's frequent vertex.* Influence is not
  frequency, and no implication between them was found.

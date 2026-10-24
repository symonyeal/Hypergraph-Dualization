# Applications and algorithmic connections

The applied study using this implementation is
[Resilient-Supplier-Panels](https://github.com/symonyeal/Resilient-Supplier-Panels):
qualified suppliers per product form the hyperedges, and minimal resilient panels
are their minimal transversals. Its data and findings belong in that repository.

## Interfaces

| Task | Implementation |
| --- | --- |
| Generate `Tr(H)` | `fka.transversal` |
| Decide whether `G = Tr(H)`, with a witness when false | `fka.algorithm.fk_a`, FK-B |
| Test self-transversality | `SelfTransversal.lean`, `Critical.lean` |
| Measure distinct subproblems and compare split rules | `fka.memo`, `experiments/split_rules.py` |

The former application catalogue and ranked shortlist had no application data or
executed comparisons. They remain in git history; they are not project results.
The table below retains connections with a checked consequence or a specific
algorithmic question. Cited structural facts and computed counts remain distinct
from Lean proofs.

## Algorithmic dictionary

Write `f` for the monotone function with DNF `G`. Throughout,
deletion `G − x` is `f|x=0`, contraction `min(G/x)` is `f|x=1`, the split at `x` is the Shannon
expansion `f = x̄·f|x=0 ∨ x·f|x=1`, and the subproblems are the restrictions `f|ρ` with a side tag
(research §4, Theorem 4.7). The vocabulary of hypergraphs and normal forms is in
[`dictionary.md`](dictionary.md). Status: *Lean*, *Python*, *Cited* (read), *Unchecked* (cited
from memory or a secondary source); each row is a row of the review log, research §8.

| Formulation | `(G, Tr G)` | FK-A's split; the memo DAG | frequency `ε` | Transfer, direction, check | Status |
| --- | --- | --- | --- | --- | --- |
| Knowledge compilation: OBDD, FBDD | `f`; its DNF and CNF | Shannon decision node; the memo DAG is an FBDD named by its functions (Thm 4.13), an OBDD under a static order | — | KC → FK-A: an FBDD lower bound for `f` bounds `δ` of unmodified FK-A under every valid symmetric rule (Cor. 4.15; qualifications in research §4); under the leftmost rule a read-once formula in leaf order has `δ ≤ 2n + 2` and an FBDD of at most `n + 2` nodes (Thm 4.16). Check: `δ = n` on GK `f₂–f₅`, TK `S₂–S₄` | Lean (research §4 names the theorems); checks Rust |
| Decision-DNNF, component caching (model counting) | — | FK-A has no decomposition node: on disjoint inputs its subproblems are pairs of input states (Lemma 4.17), where a decomposition node would make them a sum | — | KC → FK-A: split off disjoint components before branching. Check: the product structure is Lemma 4.17; the decomposing variant is not implemented | Lean (lemma); technique open |
| DPLL, tree and regular resolution | `(G, H)` is dual iff cross-intersecting and `⋀_g ⋁_{i∈g} x̄ᵢ ∧ ⋀_h ⋁_{i∈h} xᵢ` (`N` clauses) is unsatisfiable | a DPLL branch; the tree is a tree-like refutation shape, the memo DAG a read-once branching program, the model of regular resolution | condition (iv), `Σ 2^{-\|c\|} ≥ 1`, is the counting bound for unsatisfiable CNFs | Proof complexity → FK-A: the short-clause lemma behind Ehrenfeucht–Haussler (Savický's proof) is FK96 Lemma 2.3.2; it also caps FBDD mixedness at `log₂ N` (research §4) | Lean (`kraft_sum`, `two_pow_shortest_le`, `exists_frequent_vertex`); reading cited |
| Matroids | circuits of `M`; `Tr` = bases of `M*` | matroid deletion and contraction (Tutte's recursion); subproblems are minors `M\S/T` | — | Matroids → FK-A: `U(k, n)` has only the minor types `U(k′, n′)`; all degrees tie, so every rule follows the least live vertex and `δ` is quadratic in `n` (`(n/2)²` at `k = n/2`) | Matroid facts cited; `δ` Python (`results/split-rules.md`, `tests/test_memo.py`) |
| Simple games, voting | minimal winning coalitions `G`; blocking coalitions `Tr G`; decisive games are `Tr G = G` | — | `deg_G x` is the numerator of Holler's public good index | FK-A → games: automorphisms preserve Banzhaf power, so anonymous games have equal power (`influence_aut`); decisive iff intersecting and not 2-colourable (`tr_eq_self_iff`) | Lean (existing); Holler unchecked, no transfer |
| Percolation, sharp thresholds | crossing event and its dual | — | influences | `P_p(G) + P_{1−p}(Tr G) = 1`, self-dual threshold `1/2` (`bernoulli_dual`, `bernoulli_self_dual`) | Lean (existing) |

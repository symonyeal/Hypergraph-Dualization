# Claim register

Every statement the 2024 thesis makes on its own authority, with its status after the 2026
audit and the Lean declaration that settles it. Cited results (Fredman–Khachiyan, Berge,
Corneil–Lerchs–Burlingham, Cameron) are attributed in the text and are not
listed. Lean names are in [`lean/HypergraphDualization/`](../lean/HypergraphDualization); vertices
there are 0-indexed (thesis `v_i` is `i - 1`).

The register distinguishes proved corrections from finite checks, computations and open
claims. Where available, the library includes a counterexample to the printed statement.

## Status key

| Status | Meaning |
| --- | --- |
| Proved | Holds as printed; proved in Lean for every input |
| Proved, generalised | Holds with a weaker hypothesis than printed |
| Corrected | False or ill-posed as printed; the row identifies the corrected statement and its evidence |
| Checked | A finite fact about named instances; native evaluation trusts the Lean compiler, while a kernel evaluation is labelled explicitly |
| Open | Not established; the corrected thesis no longer claims it |
| Computed | Produced by the Python engine (`src/fka`), not formalized in Lean; reported as computation, not as a proved statement |
| Computed (Rust) | Produced by a Rust program under `experiments/`; reported as computation |
| Written proof | Proved in the cited document, not formalised in Lean |
| Argued | A proof sketch whose gap the cited document names |
| Cited, Conditional | Rests on a named external source or hypothesis, stated in the row |
| Refuted, Withdrawn | False, with a counterexample, or no longer claimed, with the reason |

## Chapters 1 and 2

Literature. The results are cited, not registered here; the Lean lemmas in `Basic`,
`Duality` and `Conditions` exist because later proofs use them. Printed errors in these
chapters are listed under the mathematical audit below.

## Chapter 3

The corrected §3.5 retains the stabilizer and reduction inclusions below. Its former
claims of larger child groups, child subgroups and equality when the split vertex
is fixed are withdrawn; they do not follow from those inclusions (research §4, Q4).

| Statement | Status | Lean |
| --- | --- | --- |
| §3.2, 168 Sperner hypergraphs on 4 vertices in 30 classes | Checked | `sperner_four_card`, `classes_four` |
| §3.2, 13 pairs of distinct hypergraphs | Checked, with the reading made explicit: 13 pairs of classes with `G ≇ Tr G` plus 4 classes with `G ≅ Tr G` | `self_dual_classes_four` |
| §3.2, largest tree on 3 and 4 vertices: 3 and 7 nodes, depth 3 | Checked; "depth 3" is three levels (height 2) | `max_tree_three`, `max_tree_four` |
| §3.2, `Aut(D_{m,1}) ≅ S_m × S_{n-m}` | Proved for every `n`, `m` | `young_aut_singletons` |
| §3.2, the table of automorphism groups and orbit sizes | Checked | `table_aut`, `table_orbits` |
| Fig. 3.3(b), the transversal of `D₃,₁` drawn as `K₃` | **Corrected**: `Tr(D₃,₁) = {{v₁,v₂,v₃}}` | `d31_tr` |
| §3.2, `P_{n_3}` printed as three families | **Corrected** (typesetting): `G = {{v₁,v₂},{v₁,v₃},{v₁,v₄},{v₃,v₄}}` | `pn3_tr` |
| §3.2, `Pn₃‾` printed as `{{v₂,v₃},{v₃,v₄},{v₁}}` with transversal `{{v₁,v₂},{v₁,v₃,v₄}}` | **Corrected** (labelling): the transversal, the figure and the prose all belong to `{{v₁},{v₂,v₃},{v₂,v₄}}`; the printed pair is not transversal | `pn3bar_tr`, `pn3bar_printed_not_tr`, `pn3bar_freq` |
| §3.2, `P₄` pair printed with an extra edge `{v₁,v₂}` and as its own transversal | **Corrected**: `P₄ = {{v₁,v₂},{v₂,v₃},{v₃,v₄}}`, `Tr = {{v₁,v₃},{v₂,v₃},{v₂,v₄}}` | `p4_tr`, `p4_printed_not_tr` |
| §3.2, `K₃˙` printed with edge `{v₂,v₄}` (not Sperner) and transversal `{{v₁,v₂,v₃,v₄}}` | **Corrected**: `K₃˙ = {{v₂},{v₁,v₃},{v₁,v₄},{v₃,v₄}}`, `Tr = {{v₁,v₂,v₃},{v₁,v₂,v₄},{v₂,v₃,v₄}}` | `k3dot_tr`, `k3dot_printed_not_sperner` |
| §3.2, transversal of `K₄⁻` | **Corrected**: `{{v₁,v₂,v₃},{v₁,v₂,v₄},{v₃,v₄}}` | `k4minus_tr`, `k4minus_printed_not_tr` |
| §3.2, `K₂··` printed as `{{v₁,v₂},{v₃,v₄}}`, self-transversal | **Corrected**: `K₂·· = {{v₁},{v₂},{v₃,v₄}}`, `Tr = {{v₁,v₂,v₃},{v₁,v₂,v₄}}`, the labelling under which the prose (frequencies, tree sizes) is right | `k2dd_tr`, `k2dd_printed_not_tr`, `k2dd_freq` |
| §3.2, `C₄` printed as a copy of the `P₄` pair | **Corrected**: `C₄ = {{v₁,v₂},{v₂,v₃},{v₃,v₄},{v₁,v₄}}`, `Tr = {{v₁,v₃},{v₂,v₄}}` | `c4_tr` |
| §3.2, transversal of `K₄` printed as three copies of `V` | **Corrected**: the four 3-subsets | `k4_tr`, `k4_printed_not_tr` |
| §3.2, frequencies of `Pn₃` (`v₁`: `2/3`) | **Corrected**: `v₁` has `3/4` | `pn3_freq` |
| §3.2, `K₂··`: the most frequent vertex is not the best split | Checked | `k2dd_mfv_not_optimal` |
| §3.2, all other frequencies and tree sizes per split vertex | Checked | `*_freq`, `*_splits` |
| Lemma 3.3.1, `Aut(Tr H) = Aut(H)` | **Corrected**: needs `H` Sperner; in general `Aut(Tr H) = Aut(min H)` | `aut_tr_of_sperner`, `aut_tr_eq_aut_minimal`; counterexample `lemma_3_3_1_needs_sperner` |
| Lemma 3.3.2, the split eliminates all symmetries involving `v_i` | **Corrected** (ill-posed): in either child an automorphism moves `v_i` only to a vertex in no edge; automorphisms fixing `v_i` survive in both children | `aut_child_moves_split_to_isolated`, `stab_mem_aut_del`, `stab_mem_aut_con` |
| Lemma 3.3.3, independent transpositions survive the split | **False**: `G = {{v₁,v₃},{v₂,v₄}}`, split on `v₁`, `(v₃ v₄)` survives in neither child | `lemma_3_3_3_false` |
| Cor. 3.3.4, `Aut(H) ≅ Aut(min H)` | **Corrected**: `Aut(H) ≤ Aut(min H)`; equality fails | `aut_le_aut_minimal`; counterexample `cor_3_3_4_not_iso` |
| Example of §3.4, `α = (v₁ v₃) ∈ Aut(G(H))` | **Corrected**: `(v₁ v₃)` is not a primal-graph automorphism; `(v₁ v₄)` is, and is not in `Aut(H)` | `ex34_corrected` |
| Observation 3.4.5, FK-A induces a minor map | **Corrected** (made precise): each child's primal graph is a subgraph of `G(H) − v`, a minor by deletions only | `primal_children_le` |

## Chapter 4

| Statement | Status | Lean |
| --- | --- | --- |
| §4.1, `Tr` of union and join | Proved | `tr_union`, `tr_join`, `tr_union_disjoint`, `tr_join_disjoint` |
| §4.2, `Tr(f_k) = g_k`, `Tr(S_k) = r_k` | Proved for every `k` | `tr_alt`, `tr_coalt` |
| §4.2.3, edge-count recurrences | **Corrected**: the two cases are swapped in print | `card_alt_succ`, `card_coalt_succ`; counterexample `printed_recurrence_fails` |
| §4.2.3, closed forms `|E_i| = 2^{2^{(i/2)-1}}`, `|E'_i| = 2^{(i/2)-1}` (even `i`) | **Corrected**: `2^{2^{i/2}-1}` and `2^{2^{i/2+1}-2}` (e.g. `|E₄| = 8`) | `alt_counts` |
| §4.3, `|E(f₂)| = 2²` | **Corrected**: `2³` | `alt_counts` |
| §4.3, `|E(g_{k+1})| = (2·|E(f_k)|)²` | **Corrected**: `(2·|E(g_k)|)²` | `alt_counts` |
| §4.3, closed forms `|f_k| = 2^{2^k-1}`, `|g_k| = 2^{2^k-2}`, `|S_i| = 2^{2(2^i-1)}`, `|r_i| = 2^{2^i-1}` | Proved for every `k` | `alt_counts` |
| §4.3, uniform edge sizes and frequencies `2^-k`, `2^{1-k}`, `2^-i` | Proved for every level | `alt_shape` |
| §4.2.1, `f₂, g₂` as printed | Checked | `f2_g2_printed` |
| Observation 4.4.9, the alternating tree is a cotree of the GK family | Proved for every level, for both families | `primalAdj_alt`, `support_alt` |
| Lemma 4.4.13, twins permute in `H` and `Tr(H)` (distance-hereditary `G`) | Proved, generalised: every graph. The printed proof is wrong (a stable set containing `u` need not contain its false twin `v`) and is replaced | `twins_mem_aut_cliques` |
| §4.4.2, cographs and chordal graphs are distance-hereditary | **Corrected**: chordal graphs need not be; the gem is chordal and not distance-hereditary. The cograph half is cited | `gem_chordal_four`, `gem_chordal_five`, `gem_not_distance_hereditary` |
| Lemma 4.4.14, automorphisms preserve twin type | Proved | `twins_map` |
| §4.4.2, no vertex has both a true and a false twin | Proved | `not_trueTwin_and_falseTwin` |

## Chapter 5

| Statement | Status | Lean |
| --- | --- | --- |
| §5.2.1, the instance pairs are transversal pairs | Checked | `*_dual` |
| 6-A and 8-Ver as printed | **Corrected**: as printed neither is a transversal pair; the corrected edge sets are in `data/instances` | `sixA_printed_not_dual`, `eightVer_printed_not_dual` |
| Tree sizes of Figs. 5.1–5.6 | Checked | `*_nodes`, `faithful_nodes` |
| Split vertex and group order at every node of the eight automorphism trees (140 nodes) | Checked, after three label corrections below | `*_tree` in `TreeFacts` |
| 6-D node 9, 7-Ver nodes 3 and 7: group `C₃` | **Corrected**: `S₃` (order 6); the node is `({{a,b,c}}, {{a},{b},{c}})` | `sixD_tree`, `sevenVer_tree` |
| 8-Ver node 4: group `D₄` | **Corrected**: `C₂` (order 2) | `eightVer_tree` |
| f₂/g₂ nodes 10 and 19: "`C₄` graph" | **Clarified**: `C₄` plus an isolated vertex | — |
| Hypergraph and graph property labels of the eight automorphism trees | Computed: a historical check on 2026-10-21 validated each label on C or D on its support. The checker was retired with the edition pipeline. The November recheck of 6-B, 6-C and 6-D found read-once on both sides and alpha-acyclicity only on D; Chapter 5 now states that scope | — |
| §5.2.2, frequencies `ε` | Checked | `*_eps`, `eightVer_uniform` |
| Observation 5.2.2, a false twin of the split vertex leaves the contraction | Proved (general lemma) and checked on `f₂, g₂` | `falseTwin_filtered`, `f2g2_false_twin_filtered` |
| Observation 5.2.3, `ε(3) = 2/3` | Checked (exhaustion by evaluation); `K₃` is the unique minimiser | `eps_three` |
| Observation 5.2.3, `ε(7) = 3/7` | Lower bound Proved (2026-10): every non-trivial pair on `n` points has `s·ε ≥ 1` and `s ≤ nε` for its smallest edge size `s`, which forces `ε ≥ 3/7` on seven points. Attainment Checked: Fano. Also `ε(5) = ε(6) = 1/2`, `ε(9) = 1/3` (bounds Proved, attainment Checked) and `ε(4) = 1/2` (bound Proved by `eps_ge_inv`, attainment Checked) | `eps_bound` (Proved); `eps_seven`, `eps_four`, `eps_five`, `eps_six`, `eps_nine` (bounds Proved, attainment Checked) |
| §5.2.2, Fano and `K₃` are self-transversal; `PG(2,3)` is not | Checked | `fano_self_tr`, `k3_self_tr`, `pg23_not_self_dual` |
| Def. 5.2.1, `7k` edges and the transversal count `(k−2)²/4 + k/2 + 1` | **Corrected**: `k` disjoint Fano planes have `7k` edges and `7^k` minimal transversals, for every `k` | `kFano_card`, `tr_kFano_card` |

## Trust base

General theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Statements marked
*Checked* entries identify finite evaluations. Native evaluation (`native_decide`) adds the Lean compiler to the trust base; explicitly labelled kernel evaluations do not. `lean/HypergraphDualization/Axioms.lean` checks the registered standard and native classes; a kernel-only (`decide +kernel`) run was tried on 2026-10-21 and is practical only for the
smallest instances. `lake build` reproduces everything; see [`lean/README.md`](../lean/README.md).

## Research beyond the thesis (2026-10)

New statements of the October 2026 research program, each written up in
[`docs/research-2026-10.md`](../docs/research-2026-10.md).

| Statement | Status | Lean |
| --- | --- | --- |
| Observation A1: `w11` is a Steiner system `S(4,5,11)`, self-transversal; distinct blocks meet in 1, 2 or 3 points (495, 660, 990 pairs) | Checked | `w11_steiner`, `w11_self_tr`, `w11_meet` |
| Observation A2: `|Aut(w11)| = 7920`, sharply 4-transitive, primitive | Checked (the finite checks use `native_decide`) | `card_aut_w11`, `w11_four_transitive`, `w11_four_free`, `w11_preprimitive` |
| Proposition A3: for Sperner `H` inside `U`, `Tr(H) = H` iff `H` is intersecting, `∅ ∉ H` and `H` is not 2-colourable; the Sperner hypothesis is needed | Proved | `tr_eq_self_iff`, `tr_eq_self_iff_needs_sperner` |
| Theorem A4: intersecting, `r`-uniform, `d`-regular on `t` points gives `d(r² − t) ≥ r(r − 1)`, equality iff distinct edges meet in one point | Proved | `intersecting_regular_bound` |
| Lemma: a relation preserved by a primitive action is connected or relates only equal points | Proved | `connected_or_trivial` |
| Proposition A7: a read-once hypergraph on `n ≥ 2` points with primitive `Aut(H)` has `Aut(H) = Sₙ` | Proved | `aut_eq_top_of_readOnce` |
| `w11` and the Fano plane are not read-once (complete primal graph) | `w11`: Checked (completeness by evaluation); Fano: Proved (kernel `decide`) | `w11_not_readOnce`, `fano_not_readOnce` |
| Theorem A5a: in `S(t,k,v)`, `1 ≤ t ≤ k`, every block is disjoint from exactly `n₀(t,k,v) = Σ_{i<t} (−1)^i C(k,i)(λ_i − 1)` blocks; hence `n₀ ≥ 0` for every existing system | Proved | `steiner_disjoint`, `steiner_n0_nonneg` |
| Observation A5b: `n₀` for 19 parameter sets; no `S(t,k,v)` with `n₀ > 0` (nine sets, including every `S(2,3,15)`, `S(3,4,16)`, `S(5,8,24)`) is self-transversal; none with `n₀ < 0` (ten sets) exists | Proved (kernel `decide`) | `n0_table`, `steiner_tr_ne_of_table`, `not_steiner_of_table` |
| `PG(2,4)` and `S(4,7,23)` are intersecting Steiner systems with a 2-colouring, so not self-transversal | Checked | `pg24_steiner`, `pg24_tr_ne`, `s4723_steiner`, `s4723_tr_ne` |
| Theorem B: `s·ε ≥ 1` and `s ≤ nε` for the smallest edge size `s`; hence `nε² ≥ 1` | Proved | `eps_bound`, `eps_sq` |
| B4: for nonempty cross-intersecting `G,H`, `ab + X ≤ nε²ab`, where `X = Σ_{g,h} (|g ∩ h|−1)`; each cross pair with nonsingleton intersection adds at least 1 to `X` | Proved (kernel) | `sum_degree_mul_eq_excess`, `crossExcess_bound`, `eps_crossExcess`, `eps_overlap_gap` |
| B5: equality forces `n=m²`, both families `m`-uniform and regular with frequency `1/m`, Sperner, every cross intersection singleton; nonsquares have strict inequality | Proved (kernel) | `eps_eq_rigid`, `eps_eq_sperner`, `eps_eq_cross_singleton`, `eps_strict_of_nonsquare` |
| Equality transversal pairs are read-once; so are regular convergent templates for every `r` | Cited consequence of B5 and Gurvich (Das–Straßburger 2016, Thm 4.10); bridge not formalised | — |
| B6: self-transversal `G` satisfies `|G|² + Σ_g (|g|−1) ≤ nε²|G|²`; `n>1` implies `nε²>1` | Proved (kernel) | `eps_self_diagonal`, `eps_self_strict` |
| Both sides 2-uniform on four points need not attain the frequency bound; Fano has cross excess 14 | Proved (finite, kernel `decide +kernel`) | `path_four_not_extremal`, `fano_crossExcess` |
| `n ≤ m(m+1)`, `m>0` implies `ε ≥ 1/m`; shared proof for `ε(5),ε(6)` | Proved (kernel) | `eps_ge_inv` |
| B7: two `r`-uniform cross-intersecting families on `r²` points have singleton cross intersections if either side is regular | Proved (kernel); a non-read-once D3 candidate must have both sides irregular by cited Gurvich | `uniform_regular_cross_singleton` |
| `ε(8) = 2/5` | Open: `3/8 ≤ ε(8) ≤ 2/5` proved (`eps_eight`, `eightVer_eps`); CP-SAT finds no pair below `2/5` (`experiments/eps_search.py`) | `eps_eight`, `eightVer_eps` |
| Theorem C1: `matching(v)` has `τ = 2^{v/2+1} − 3`, `δ = v` (even `v ≥ 4`); `threshold(v)` has `τ = δ = v − 1` (even `v ≥ 2`); modified FK-A | Proved | `matching_tau_delta`, `threshold_tau_delta` |
| Theorem A5c: every Steiner system `S(t, t+1, 2t+3)` is self-transversal, and `t` is even | Proved | `witt_tr_eq` |
| Theorem (Seymour 1974): a 3-critical hypergraph covering `n` points has at least `n` edges | Proved | `card_le_of_critical` |
| A self-transversal hypergraph covering `n` points has `|H| ≥ n` (equality for `K₃`, Fano) | Proved | `card_le_of_tr_eq_self`, `erase_twoColourable` |
| Counting test: for intersecting Sperner `H` without `∅`, `Tr(H) = H` iff `2^{n−1}` subsets contain an edge | Proved | `tr_eq_self_iff_card` |
| If `Tr(H) ⊆ H` and `Aut(H)` is edge-transitive, it is transitive on covered points | Proved | `transitive_of_edge_transitive` |
| Hertel's alternating-tree bound (cited in Chapter 4) is a lower bound on DPLL trees, not an upper bound on subproblems | Corrected citation (corrected thesis, Chapter 4) | — |
| Observation 4.4: FK-A's degree-sum rule exceeds Hertel's memoised `2k + 3` on GK `f₃` (`δ = 369 > 65`) | Computed historically with the retired Python formula engine; the surviving Rust engine and generic hypergraph tests reproduce the bounded count | — |
| Conjecture 4.5: `δ ≤ 2N` on read-once pairs under the degree-sum rule | **Refuted**: the read-once `ro12` on 12 points has `δ = 43 > 2N = 42` (evaluation); GK `f₄` has `δ/N = 1368` (Rust) | `ro12_readOnce`, `ro12_delta` |
| Theorem 4.7: under any split rule every FK-A subproblem of `(G, Tr G)` is `(H, Tr H)` or `(Tr H, H)`, `H` a minor of `G`; `δ ≤ 2·#minors` | Proved | `fkADag_minor`, `card_fkADag_le_minors` |
| Proposition 4.8: `τ(C, D) = τ(D, C)` on dual pairs | Proved | `fkA_comm`, `splitVar_comm` |
| Theorem 4.16: under the leftmost rule, a read-once formula with leaves in order has `δ ≤ 2n + 2`, and its states form an FBDD of at most `n + 2` nodes (cf. Hertel's Thm 4.4.1, cited); Observation 4.11: measured `δ = n` on GK `f₂–f₅`, TK `S₂–S₄`, far below the degree-sum rule | Proved; measurements Computed (`experiments/split_rules.py`) | `Fm.leftmost_delta`, `Fm.leftmost_fbdd`, `Fm.St_closed`, `Fm.card_St_le` |
| Remark 4.12: a restriction of a read-once formula with nonempty support is determined by its support | Proved | `Fm.rminor_determined` |
| `dnf(f\|x=0) = dnf f − x`, `dnf(f\|x=1) = dnf f / x`, `Tr(dnf f) = min dnf(f^d)` for every monotone formula; `= dnf(f^d)` for read-once `f` | Proved | `Fm.dnf_restrict_false`, `Fm.dnf_restrict_true`, `Fm.tr_dnf`, `Fm.tr_dnf_readOnce` |
| FK-A under an arbitrary split rule is correct; the degree-sum instance is `fkA` | Proved | `fkAR_correct`; `fkA`, `fkADag` are `abbrev`s of `fkAR splitVar`, `fkADagR splitVar` |
| Theorem 4.13: under a valid symmetric rule the memo DAG of unmodified FK-A is an FBDD named by its functions for `f`, of size `≤ 2δ + 2`; under modified FK-A a branching program with term and clause leaves; an FBDD computes its functions and reads each variable once per path | Proved | `memo_fbdd`, `memo_bp`, `memo_good`, `run_correct`, `path_nodup` |
| Proposition 4.14: an FBDD of size `s` named by its functions gives a valid symmetric rule with `δ ≤ 2s`, either variant | Proved | `fbddRule`, `rule_of_fbdd` |
| Corollary 4.15: on unmodified FK-A, `δ ≥ (s − 2)/2` under every valid symmetric rule, `s` the least FBDD named by its functions; an explicit family defeating every such rule needs a monotone family with polynomial `N` and superpolynomial FBDD size | Proved for the bound; the step from FBDDs named by their functions to arbitrary FBDDs argued; the modified-variant bound argued; no such family known (literature, research §4) | `memo_fbdd`, `rule_of_fbdd` |
| Lemma 4.17: minors of `A ∪ B`, `A ∧ B` are unions, joins of minors | Proved (the step of Remark 4.12) | `Fm.minor_union`, `Fm.minor_join` |
| A read-once formula on all of `V` has a read-once DNF (Sperner, conformal, cograph primal graph); the converse is Gurvich's theorem | Proved for this direction; converse cited | `Fm.readOnce_dnf` |
| Proposition 4.18: the guarded rule is valid, symmetric, and has frequency `≥ 1/⌊log₂ N⌋` at an eligible split | Proved; choosing the least eligible vertex follows from its ascending search definition | `guardRule_frequent`, `valid_guardRule`, `guardRule_symm` |
| `δ` of GK `f₂` is 8 under all three rules; `ro12` has `δ = 91` under the leftmost and guarded rules | Checked | `gk2_rules`, `ro12_rules` |
| Conjecture 4.19: `δ/N` is unbounded on GK under the degree-sum rule | Open; `δ/N = 0.67, 1.92, 1368` for `k = 2, 3, 4` (Rust) | — |
| Proposition 4.6: unless 3-SAT runs in `2^{O(n^{2/3}(log n)^{1/3})}`, for no polynomial-time split rule does a polynomial bound `δ` on all dual pairs (C3 false) | Conditional: a short argument from the Kobayashi–Kurita–Wasa 2026 reduction; the premise is weaker than ETH; not in Lean | — |
| Theorem D1: `Tr(T[Γ]) = min(Tr(T)[Tr Γ])`; on disjoint supports no reduction, Sperner, `|T[Γ]| = Σ_t Π_i |Γ i|` | Proved | `tr_subst`, `tr_subst_of_disjoint`, `subst_isSperner`, `card_subst` |
| Proposition D2: `(P)` `k·k* ≥ 8^{r−1}` is closed under composition | Proved as arithmetic (`prop_P_comp`) with the counts of `card_subst_uniform`; the template statement is assembled in prose. It is the count case of F Lemma 4 (`Δ(T[S]) = rΔ(S) + Δ(T)`) | `card_subst_uniform`, `prop_P_comp` |
| Proposition 5.4: D3 at `r = 2` has no counterexample; `(k, k*) ∈ {(2,4),(4,2),(3,3)}` | Checked for the product bound over 64 families; the full-support three-class classification is a separate finite computation, with triangle plus an isolated point as a fourth ambient class | `template_rank_two` |
| Proposition E2: automorphisms preserve influences; Fano's seven influences agree at every `p` | Proved | `influence_aut`, `influence_eq_of_transitive`, `fano_influence_eq` |
| Proposition 4.21: common relabelling preserves equality with the transversal family and duality, including redundant families; any two FK-A split rules give the same verdict on relabelled inputs | Proved; the cache is Theorem 4.28 | `pimg_injective`, `tr_eq_pimg_iff`, `minimal_pimg`, `dual_pimg`, `fkAR_pimg` |
| Theorem 4.22: k-transitivity bounds ordered classes through depth k by 1+k(k+1); for self-transversal input by 1+k(k+1)/2, under every live-vertex rule and either variant | Proved | `SD.dual_transitive_bound`, `SD.self_transitive_bound`; normal form, transitivity bridge and exact isomorphism quotient in `SymmetryDepth` |
| Observation 4.23: Fano and Witt attain the self-transversal bound; complete(10,3) has 7 classes through depth 2, refuting the universal triangular shortcut | Computed; exact incidence-graph isomorphism in 18 configurations | `experiments/symmetry_depth.py`, `tests/test_symmetry_depth.py` |
| The symmetry-depth bounds are attained for every k by complete uniform families | Written proof, not formalised | `docs/symmetry-depth.md` |
| Theorem 4.24: every decision tree for `coalt i` (GK, TK; `n = 2^i ≥ 4`) has at least `2·(27/16)^{n/4}` leaves (JRSW 1999, restated) | Proved | `l1_le_leaves`, `wc_gk_succ`, `dsum_eq`, `gk_leaves` |
| Theorem 4.25: FK-A's recursion tree on a dual pair is a decision tree with at most `(n+1)τ` leaves; on GK and TK `τ ≥ 2·(27/16)^{n/4}/(n+1)` under every valid rule | Proved | `fkA_tree_dt`, `fkA_gk_tree` |
| Corollary 4.26: (a) under the leftmost rule `τ/δ` is exponential in `n` on GK and TK; (b) under every valid rule FK-A is eventually slower than FK-B's `N^{4χ(N)+O(1)}` | (a) Proved; (b) uses FK96's bound, cited | `gk_memo_gap`, `dnf_coFm_gkH`, `fkA_gk_tree` |
| Proposition 4.27: C3 is equivalent to the monotone case of JRSW's Question 1 (1997) | Cited reading; the equivalence rests on Theorem 4.13, Proposition 4.14 and the argued reduction after research Proposition 4.14 | `memo_fbdd`, `rule_of_fbdd` |
| Theorem 4.28: FK-A with a memo keyed by any map sending each pair to a relabelling of it returns `Dual` under every rule and fuel, and its memo stays sound | Proved | `fkAI`, `fkAI_correct`, `fkAI_eq_fkAR` |
| Observation 4.29: `δ`, `δ_Aut`, `δ_iso`, `d_iso` on GK, TK, `alt3` and the library under three rules; GK `f₄` degree sum `δ_iso = 827,175`, `δ/δ_iso = 81.3`, `δ_iso/N = 16.8`; leftmost `δ = δ_iso = n` | Computed (Rust); historical checks against the retired Python engines, an orbit canon and group enumeration. Current bounded tests use retained counts and independent hypergraph/incidence-graph checks | `experiments/iso_classes.py`, `results/iso-memo.md`, `tests/test_readonce_dag.py` |
| Conjecture 4.30: `δ_iso/N` is unbounded on GK under the degree-sum rule | Open; `0.67, 0.83, 16.8` for `k = 2, 3, 4` (Rust) | — |
| Observation 4.31: the joint top-block projections of GK `f₃` contain only 21 of the 49 pairs of standalone `f₂` supports, so the unrestricted embedding route to Q1 fails | Computed (Rust), historically checked against the retired formula engine; retained projections are regression fixtures | `experiments/block_probe.py`, `results/block-probes.md`, `tests/test_readonce_probe.py` |
| Observation 4.32: on GK `f₅` the guarded rule never falls back to the degree sum and leaves the leftmost vertex at 92,776 of 124,874 splits | Computed (Rust); first departure historically re-derived in Python and retained as a regression fixture | `results/block-probes/gk5-guard.json`, `tests/test_readonce_probe.py` |
| Proposition 4.34: on GK `deg_C v = deg_D v` for every vertex; on TK `deg_C v · |D| = deg_D v · |C|` | Proved | `gk_degree_balance`, `tk_degree_ratio` |
| Observation 4.35: `δ_{k+1} ≥ δ_k²/4` holds at every measured step of GK and TK; TK's falling `δ/N` comes from `N_{k+1}/N_k² → 4` | Computed from existing values | — |
| Lemma 4.36: a top block's projected states are reached on the block by the hull rule | Argued, not in Lean | — |
| Proposition 4.37: a squaring step losing `A·n_k` with `A < 2.004` settles Conjecture 4.19; for `δ_iso` only a constant `A < 12.6` | Written proof | — |
| Observation 4.39: on GK `f₃`, `f₄` no pair of equal odd size occurs jointly; the share of target pairs occurring is `0.43`, `0.53` | Computed (Rust), equal-size counts checked against the formula engine at small levels | `results/block-probes/`, `tests/test_readonce_probe.py` |
| Conjecture 4.40: on GK `J_{k+1} ≥ σ_k²/4`; for `k ≥ 4` and any `A < 513` in place of 4 it implies Conjecture 4.19 | Open; holds for `k ≤ 3` | — |
| Observation 4.41: TK `S₄` degree sum, stopped at memory: `δ ≥ 330,149,945`, `δ/N ≥ 0.307`, `log δ/log N ≥ 0.943` | Computed (Rust, partial); lower bound only | — |

## November 2026

F is [`frequency-constant.md`](../docs/frequency-constant.md) and E is
[`complex-evaluation.md`](../docs/complex-evaluation.md). None of these is formalised in Lean.

| Statement | Status | Source |
| --- | --- | --- |
| F Theorem 2: every dual pair has `\|C\|·\|D\| ≥ 4^{1/ε − 1}` | Written proof | F §1 |
| F Proposition 3: the alternating words attain `\|C\|·\|D\| = 8^{1/ε − 1}` | Written proof | F §2 |
| F Conjecture 6: every dual pair has `\|C\|·\|D\| ≥ 8^{1/ε − 1}` | **Refuted** by F Proposition 7: the read-once `T₆` on 36 points has `ε = 1/6`, `\|C\|·\|D\| = 31,104 < 8⁵` | `experiments/frequency_readonce.py check` |
| F Theorem 8: every read-once dual pair has `\|C\|·\|D\| ≥ e^{2(1/ε − 1)}` | Written proof | F §5 |
| E Corollary 10: on GK `f_k` and TK `S_k` every valid rule has `τ ≥ 2^{0.41433 n}/(n + 1)` | Written proof; exact integer check | `experiments/subcube_norm.py check` |
| E Proposition 4: the leftmost rule has `τ ≤ 2^{(0.469254 + o(1)) n}` on GK and TK | Argued, and computed | `experiments/alternating_dt.py rates 6` |
| E Proposition 12: depth-first trees minimise every leaf weighting `aL₁ + bL₀` on GK `f₁–f₃`, TK `S₁–S₂` and 52 balanced formulas | Computed, exact | `experiments/alternating_dt.py least 3`, `balanced` |
| E Conjecture DF: depth-first trees minimise every leaf weighting on balanced read-once formulas | Open | E §3 |
| E Conjecture 17: `m₀(g ∧ g′) ≥ θ·m₀(g)(1 + m₁(g))` with an absolute `θ > 0.1609` | Open; it would lift the GK/TK lower rate past the subcube barrier `0.41434` | E §5 |

## Source review and consolidation (2026-11)

The repository retains one corrected thesis and fixed drawing assets. The recovery,
edition overlay, exact-span revision and figure-generation pipeline was retired.
Historical reproduction commands belong to the archived source at revision `9e840c1`.

| Location | Correction and evidence |
| --- | --- |
| §1.1–1.2 | Minimal terms and dual normal forms are distinguished; the set-cover reduction uses incidence duality, rather than the minimal-transversal operator |
| §2.1, equation 2.1 | Non-duality has two certificate polarities: disjoint cross edges or a hitting set containing no listed blocker. The latter alone requires cross-intersection; `eq_tr_iff_partition` |
| §2.2 | Support and edge-size proofs use minimal-transversal witnesses; the weight inequality is the union bound over partitions, `support_eq`, `card_le_card_tr`, `kraft_sum` |
| §2.3 | FK-B uses χ satisfying χ^χ=N, hence χ∼log N/log log N; the earlier log log and logarithmic-time statements were false |
| §3.1 | The direct product acts separately on the disjoint vertex sets; translates of one nonempty block form a partition |
| §3.2 | Isomorphism preserves edge families onto each other. Dedekind counts are labelled counts, distinct from isomorphism classes; the exact earlier six-vertex illustration has two automorphisms |
| §3.3–3.4 | Invalid historical proofs and unsupported minor-map formalism were removed. The surviving primal-child conclusion follows by vertex and edge deletion, `primal_children_le` |
| §4.2 | GK f_k has 2^(2k−1) vertices and height 2k−1; the four-copy recurrence and `alt_counts`, `alt_shape` agree |
| §4.4 | Read-once characterization is for Sperner hypergraphs on support; automorphisms permute twin classes, and sharing an orbit does not imply twinhood |
| §5.1 | Implementation prose now describes canonical bitsets, the shared Sperner reduction and exported HTML reports |
| Frequency campaigns | The old W11 composition campaign used 1-based data as 0-based bitsets. Its 16,000-trial evidence is withdrawn; `frequency_families.py` uses the canonical design and has a regression test |

The independent final source review corrected the star-count arithmetic
`C(4,3)·3=12`, removed a repeated GK recurrence with the wrong fixed copies,
and scoped Chapter 5's 7-Ver/8-Ver property observations by side, node and split
rule. These changes preserve all numbered statement slots and drawing assets.

## Mathematical audit (2026-11-18)

The thesis now marks each statement below in red strikethrough, with its correction in blue
(`\wrong`, `\fix` in `preamble.tex`). Computations are standard-library scripts that import no
repository code; they are kept with the audit report outside the repository.

| Location | Printed statement | Correction and evidence |
| --- | --- | --- |
| Ch. 1, introduction | Takata: exponential-size intermediates | superpolynomial, `n^{Ω(log log n)}` (as in Ch. 4) |
| Ch. 1, Boolean functions | "on `n` literals"; an assignment called an expression | variables; assignment |
| Ch. 1, CNF and DNF | the conjunction of all prime implicates is irredundant | true for monotone `f`; `(x₁∨x₂)(¬x₁∨x₃)` has the redundant prime implicate `x₂∨x₃` |
| Ch. 1, irredundant | a property of the function | a property of a DNF or CNF |
| Ch. 1, applications | dominating sets from neighbourhoods; diagnosis as a transversal of the observations; metabolic cut sets as transversals of the reaction hypergraph; strains as vertices | closed neighbourhoods; minimal transversals of the minimal conflict sets; minimal transversals of the elementary modes; strains are edges, antibiotics vertices |
| Ch. 1, large edges | every edge of `Tr(H)` lies in `τ(E_H)^c` | false: `H = {{v₁},{v₂}}` on three points |
| Ch. 1, bounded conformality | `S ∈ e_i` | `S ⊆ e_i` |
| Ch. 2 §2.3 | the bounds give a lower limit on FK-A's performance | they give its running-time upper bound |
| Cor. 2.3.1 | `s ≥ log n` | reversed: `2^s ≤ n`; `K₃` has `s = 2`, `n = 6` |
| Obs. 2.3.3 | `for any i = 1,…,n` with `n = |G|+|H|` | `i` ranges over vertices |
| Def. 3.1.1 | every element of a permutation group preserves `E(H)` | only subgroups of `Aut(H)` do |
| §3.1, orbits | each orbit partitions `V`; classes permuted | the orbits partition `V`; each is fixed setwise |
| §3.1, alternating group | `Alt(V)` is never an automorphism group | true for `|V| ≥ 3`; at `|V| = 2` it is `Aut({{v₁}})` |
| §3.2, Table 3.2 | "the first nine Dedekind numbers" | ten values, `d(0)`–`d(9)` |
| §3.2, two vertices | every edge has at most one vertex | `{v₁,v₂}` is the transversal side of `D₂,₁` |
| §3.2, three vertices | reason for the maximum tree size 3 | children of a split have at most 2 vertices and are leaves |
| §3.2, `P₄` | splitting `v₂` or `v₃` gives "3 nodes at the least, up to 7" | exactly 3 |
| §3.2, `Pn₃‾` | child `D₃,₁` labelled `{v₁},{v₂},{v₃}` | `{v₁},{v₃},{v₄}` |
| §3.2, `S₃` list | `D₁,₁` on 3 vertices has `Aut ≅ S₃` | `S₂` on 3 vertices, `S₃` on 4 |
| §3.2, after `K₃` | the next self-transversal hypergraph is on 7 vertices | the 3-subsets of 5 points are self-transversal |
| §3.2, `K₄⁻` | every split gives `K₃` and `D₂,₁` | `v₁, v₂`: `K₃` and `D₁,₂`; `v₃, v₄`: `St₂`-type and `D₁,₃`; all 5 nodes |
| Ch. 4, introduction and §4.2.1 | alternating trees in GK99, used to prove FK-A's upper bounds | GK97 (Discrete Math. 169), showing the frequency bound is tight up to a factor 2 |
| §4.4.3 | two twins lie in the same automorphism orbit | holds for graphs and clique hypergraphs; the thesis's own example `{{v₁,v₂},{v₂,v₃,v₄},{v₁,v₃}}` has false twins `v₁, v₄` of degrees 2 and 1 |
| §4.4.3, after Prop. 4.4.15 | `Aut` of a disjoint union of copies is a product of wreath products | needs connected, pairwise non-isomorphic components: four singleton edges read as two copies of `{{v₁},{v₂}}` give order 8, `Aut = S₄` has 24; a broken grouping gives a subgroup. Reduced-cotree children of a union node are connected, not pairwise non-isomorphic: group them by type. No computed result uses the formula (groups come from the search in `fka.automorphism`, and no split rule reads `Aut`) |
| §5.2.2, two `C₄` | one top `C₂` acts within each cycle independently | two factors `C₂`, one per cycle |

Outside the thesis the same audit corrected: the A6 conjecture's status (unresolved; the cited pair
agrees with it), the naming of the degree-sum rule (the implementation's choice, not FK96's
frequency rule), the scope of README's memoisation sentence (leftmost rule), the Lean scope of
`N^{Ω(log N)}`, Proposition 4.6's quantifier over polynomial-time rules, `fk-a-vs-fk-b.md` §3's
claim that symmetry causes the repeats, the primitivity-depth caption, and the rows above for
Theorem B, `ε(4)`, `ε(8)` and D2.

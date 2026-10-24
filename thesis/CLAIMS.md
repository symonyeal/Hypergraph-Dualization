# Claim register

Every statement the 2024 thesis makes on its own authority, with its status after the 2026
audit and the Lean declaration that settles it. Cited results (Fredman–Khachiyan, Berge,
Corneil–Lerchs–Burlingham, Cameron, Ang–Gurvich–Tarjan) are attributed in the text and are not
listed. Lean names are in [`lean/HypergraphDualization/`](../lean/HypergraphDualization); vertices
there are 0-indexed (thesis `v_i` is `i - 1`).

**In plain terms.** The thesis was checked statement by statement against a computer-verified
proof library. Most statements hold as printed. Where a statement was false, vague or mislabelled,
the revised edition states a corrected version, and the library proves the correction. Where
possible it also gives a concrete example on which the printed version fails.

## Status key

| Status | Meaning |
| --- | --- |
| Proved | Holds as printed; proved in Lean for every input |
| Proved, generalised | Holds with a weaker hypothesis than printed |
| Corrected | False or ill-posed as printed; the corrected form is proved, and a counterexample to the printed form is in Lean |
| Checked | A finite fact about named instances, verified in Lean by evaluation (`native_decide`, which trusts the Lean compiler as well as the kernel) |
| Open | Not established; the revised edition no longer claims it |
| Computed | Produced by the Python engine (`src/fka`), not formalized in Lean; reported as computation, not as a proved statement |

## Chapter 1

| Statement | Status | Lean |
| --- | --- | --- |
| Prop. 1.1.5, `Tr(H) = Tr(min H)` | Proved | `tr_minimal` |
| `Tr(H)` is Sperner (Def. 1.1.4) | Proved | `tr_isSperner` |
| §1.1.1, complements of maximal independent sets are the minimal transversals | Proved, generalised: no hypothesis `I ⊆ U` | `isMinHit_compl_iff` |
| §1.1.2, `Tr(H)` is the CNF of the function whose DNF is `H` | Proved | `hits_tr_iff` |

## Chapter 2

| Statement | Status | Lean |
| --- | --- | --- |
| Lemma 2.1.1, partition criterion | Proved, generalised: `G` need not be Sperner | `eq_tr_iff_partition` |
| Cor. 2.1.2, `H = Tr G ⟺ G = Tr H` | Proved | `eq_tr_comm` |
| Cor. 2.1.3, `Tr(Tr H) = H` | Proved; for non-Sperner `H` the value is `min(H)` | `tr_tr_of_sperner`, `tr_tr` |
| Props. 2.2.1–2.2.4, conditions (i)–(iv) | Proved; (iv) generalised: `G` need not be Sperner | `edges_meet`, `support_eq`, `card_le_card_tr`, `kraft_sum` |
| Cor. 2.3.1, `s ≥ log n` | **Corrected**: the inequality is reversed, `2^s ≤ n`, i.e. `s ≤ log₂ n`; `G` need not be Sperner | `two_pow_shortest_le`; counterexample `k3_refutes_printed_cor_2_3_1` |
| Lemma 2.3.2, a vertex of frequency `≥ 1/log n` | Proved (as `≥ 1/s` with `2^s ≤ n`) | `exists_frequent_vertex` |
| §2.2.2, `(G, H)` dual iff both FK-A subproblems are | Proved, generalised: `G`, `H` need not lie in `U` | `dual_split` |
| Algorithm 1 decides `Trans-Hyp` | Proved for every input, both leaf rules and every split rule | `fkAR_correct`, `fkA_correct`, `conds_of_dual` |

## Chapter 3

| Statement | Status | Lean |
| --- | --- | --- |
| Claim 3.1.6, invariant vertex sets are precisely the orbits | **Corrected**: they are the unions of orbits; orbits are the minimal ones | `invariant_eq_union_orbits`, `orbit_minimal`; counterexample `claim_3_1_6_counterexample` |
| §3.2, 168 Sperner hypergraphs on 4 vertices in 30 classes | Checked | `sperner_four_card`, `classes_four` |
| §3.2, 13 pairs of distinct hypergraphs | Checked, with the reading made explicit: 13 pairs `G ≇ Tr G` plus 4 self-transversal classes | `self_dual_classes_four` |
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
| Split vertex and group order at every node of the eight automorphism trees (205 nodes) | Checked, after three label corrections below | `*_tree` in `TreeFacts` |
| 6-D node 9, 7-Ver nodes 3 and 7: group `C₃` | **Corrected**: `S₃` (order 6); the node is `({{a,b,c}}, {{a},{b},{c}})` | `sixD_tree`, `sevenVer_tree` |
| 8-Ver node 4: group `D₄` | **Corrected**: `C₂` (order 2) | `eightVer_tree` |
| f₂/g₂ nodes 10 and 19: "`C₄` graph" | **Clarified**: `C₄` plus an isolated vertex | — |
| Hypergraph and graph property labels of the eight automorphism trees (conformal, α-acyclic, read-once, chordal, split, bipartite, cograph, perfect), and §5.2.2's "6-B, 6-C, 6-D are read-once and α-acyclic" | Computed: in the revised edition every group label has the computed order and every property label holds for `C` or `D` on the vertices present (`python thesis/tools/check_tree_labels.py revised`, exit 0 on 2026-10-21); the 2024 labels fail at the six nodes corrected above | — |
| §5.2.2, frequencies `ε` | Checked | `*_eps`, `eightVer_uniform` |
| Observation 5.2.2, a false twin of the split vertex leaves the contraction | Proved (general lemma) and checked on `f₂, g₂` | `falseTwin_filtered`, `f2g2_false_twin_filtered` |
| Observation 5.2.3, `ε(3) = 2/3` | Checked (exhaustion by evaluation); `K₃` is the unique minimiser | `eps_three` |
| Observation 5.2.3, `ε(7) = 3/7` | Lower bound Proved (2026-10): every non-trivial pair on `n` points has `s·ε ≥ 1` and `s ≤ nε` for its smallest edge size `s`, which forces `ε ≥ 3/7` on seven points. Attainment Checked: Fano. Also `ε(4) = ε(5) = ε(6) = 1/2`, `ε(9) = 1/3` (bounds Proved, attainment Checked) | `eps_bound` (Proved); `eps_seven`, `eps_four`, `eps_five`, `eps_six`, `eps_nine` (Checked) |
| §5.2.2, Fano and `K₃` are self-transversal; `PG(2,3)` is not | Checked | `fano_self_tr`, `k3_self_tr`, `pg23_not_self_dual` |
| Def. 5.2.1, `7k` edges and the transversal count `(k−2)²/4 + k/2 + 1` | **Corrected**: `k` disjoint Fano planes have `7k` edges and `7^k` minimal transversals, for every `k` | `kFano_card`, `tr_kFano_card`, `two_fano_tr_card` |

## Trust base

General theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Statements marked
*Checked* are evaluations proved with `native_decide`, which adds the Lean compiler to the trust
base. `lean/HypergraphDualization/Axioms.lean` makes `lake build` fail if either class is
mislabelled; a kernel-only (`decide +kernel`) run was tried on 2026-10-21 and is practical only for the
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
| `w11` and the Fano plane are not read-once | `w11`: Checked (through A2); Fano: Proved (kernel `decide`) | `w11_not_readOnce`, `fano_not_readOnce` |
| Theorem A5a: in `S(t,k,v)`, `1 ≤ t ≤ k`, every block is disjoint from exactly `n₀(t,k,v) = Σ_{i<t} (−1)^i C(k,i)(λ_i − 1)` blocks; hence `n₀ ≥ 0` for every existing system | Proved | `steiner_disjoint`, `steiner_n0_nonneg` |
| Observation A5b: `n₀` for 19 parameter sets; no `S(t,k,v)` with `n₀ > 0` (nine sets, including every `S(2,3,15)`, `S(3,4,16)`, `S(5,8,24)`) is self-transversal; none with `n₀ < 0` (ten sets) exists | Proved (kernel `decide`) | `n0_table`, `steiner_tr_ne_of_table`, `not_steiner_of_table` |
| `PG(2,4)` and `S(4,7,23)` are intersecting Steiner systems with a 2-colouring, so not self-transversal | Checked | `pg24_steiner`, `pg24_tr_ne`, `s4723_steiner`, `s4723_tr_ne` |
| Theorem B: `s·ε ≥ 1` and `s ≤ nε` for the smallest edge size `s`; hence `nε² ≥ 1` | Proved | `eps_bound`, `eps_sq` |
| B4: for nonempty cross-intersecting `G,H`, `ab + X ≤ nε²ab`, where `X = Σ_{g,h} (|g ∩ h|−1)`; at most `(nε²−1)ab` cross pairs have nonsingleton intersection | Proved (kernel) | `sum_degree_mul_eq_excess`, `crossExcess_bound`, `eps_crossExcess`, `eps_badCross`, `eps_overlap_gap` |
| B5: equality forces `n=m²`, both families `m`-uniform and regular with frequency `1/m`, Sperner, every cross intersection singleton; nonsquares have strict inequality | Proved (kernel) | `eps_eq_rigid`, `eps_eq_sperner`, `eps_eq_cross_singleton`, `eps_strict_of_nonsquare` |
| Equality transversal pairs are read-once; so are regular convergent templates for every `r` | Cited consequence of B5 and Gurvich (Das–Straßburger 2016, Thm 4.10); bridge not formalised | — |
| B6: self-transversal `G` satisfies `|G|² + Σ_g (|g|−1) ≤ nε²|G|²`; `n>1` implies `nε²>1` | Proved (kernel) | `eps_self_diagonal`, `eps_self_strict` |
| Both sides 2-uniform on four points need not attain the frequency bound; Fano has cross excess 14 | Proved (finite, kernel `decide +kernel`) | `path_four_not_extremal`, `fano_crossExcess` |
| `n ≤ m(m+1)`, `m>0` implies `ε ≥ 1/m`; shared proof for `ε(5),ε(6)` | Proved (kernel) | `eps_ge_inv` |
| B7: two `r`-uniform cross-intersecting families on `r²` points have singleton cross intersections if either side is regular | Proved (kernel); a non-read-once D3 candidate must have both sides irregular by cited Gurvich | `uniform_regular_cross_singleton` |
| `ε(8) = 2/5` | Open: `3/8 ≤ ε(8) ≤ 2/5` proved; CP-SAT finds no pair below `2/5` (`experiments/eps_search.py`) | `eps_bound`, `eightVer_eps` |
| Theorem C1: `matching(v)` has `τ = 2^{v/2+1} − 3`, `δ = v` (even `v ≥ 4`); `threshold(v)` has `τ = δ = v − 1` (even `v ≥ 2`); modified FK-A | Proved | `matching_tau_delta`, `threshold_tau_delta` |
| Theorem A5c: every Steiner system `S(t, t+1, 2t+3)` is self-transversal, and `t` is even | Proved | `witt_tr_eq` |
| Theorem (Seymour 1974): a 3-critical hypergraph covering `n` points has at least `n` edges | Proved | `card_le_of_critical` |
| A self-transversal Sperner hypergraph covering `n` points has `|H| ≥ n` (equality for `K₃`, Fano) | Proved | `card_le_of_tr_eq_self`, `erase_twoColourable` |
| Counting test: for intersecting Sperner `H` without `∅`, `Tr(H) = H` iff `2^{n−1}` subsets contain an edge | Proved | `tr_eq_self_iff_card` |
| If `Tr(H) ⊆ H` and `Aut(H)` is edge-transitive, it is transitive on covered points | Proved | `transitive_of_edge_transitive` |
| Hertel's alternating-tree bound (cited in Chapter 4) is a lower bound on DPLL trees, not an upper bound on subproblems | Corrected citation (revised edition, Chapter 4) | — |
| Observation 4.4: FK-A's degree-sum rule exceeds Hertel's memoised `2k + 3` on GK `f₃` (`δ = 369 > 65`) | Computed (`experiments/readonce_sim.py`) | — |
| Conjecture 4.5: `δ ≤ 2N` on read-once pairs under FK-A's rule | **Refuted**: the read-once `ro12` on 12 points has `δ = 43 > 2N = 42` (evaluation); GK `f₄` has `δ/N = 1368` (Rust) | `ro12_readOnce`, `ro12_delta` |
| Theorem 4.7: under any split rule every FK-A subproblem of `(G, Tr G)` is `(H, Tr H)` or `(Tr H, H)`, `H` a minor of `G`; `δ ≤ 2·#minors` | Proved | `fkADag_minor`, `card_fkADag_le_minors` |
| Proposition 4.8: `τ(C, D) = τ(D, C)` on dual pairs | Proved | `fkA_comm`, `splitVar_comm` |
| Theorem 4.9: `d`-resilient `G` has `τ ≥ 2^{d+1} − 1` (fuel `≥ d`); `matching(8)` is not 3-resilient | Proved; the matching fact Checked | `tau_ge_of_resilient`, `matching_eight_not_resilient` |
| Proposition 4.10: under any split rule `δ ≤ τ`; `τ − δ ≥ (τ_L − δ_L) + (τ_R − δ_R) + |Δ_L ∩ Δ_R|` at a split | Proved | `card_fkADag_le`, `excess_split` |
| Theorem 4.16: under the leftmost rule, a read-once formula with leaves in order has `δ ≤ 2n + 2`, and its states form an FBDD of at most `n + 2` nodes (cf. Hertel's Thm 4.4.1, cited); Observation 4.11: measured `δ = n` on GK `f₂–f₅`, TK `S₂–S₄`, far below the degree-sum rule | Proved; measurements Computed (`experiments/split_rules.py`) | `Fm.leftmost_delta`, `Fm.leftmost_fbdd`, `Fm.St_closed`, `Fm.card_St_le` |
| Remark 4.12: a restriction of a read-once formula with nonempty support is determined by its support | Proved | `Fm.rminor_determined` |
| `dnf(f\|x=0) = dnf f − x`, `dnf(f\|x=1) = dnf f / x`, `Tr(dnf f) = min dnf(f^d)` for every monotone formula; `= dnf(f^d)` for read-once `f` | Proved | `Fm.dnf_restrict_false`, `Fm.dnf_restrict_true`, `Fm.tr_dnf`, `Fm.tr_dnf_readOnce` |
| FK-A under an arbitrary split rule is correct; the degree-sum instance is `fkA` | Proved | `fkAR_correct`, `fkAR_splitVar`, `fkADagR_splitVar` |
| Theorem 4.13: under a valid symmetric rule the memo DAG of unmodified FK-A is an FBDD named by its functions for `f`, of size `≤ 2δ + 2`; under modified FK-A a branching program with term and clause leaves; an FBDD computes its functions and reads each variable once per path | Proved | `memo_fbdd`, `memo_bp`, `memo_good`, `run_correct`, `path_nodup` |
| Proposition 4.14: an FBDD of size `s` named by its functions gives a valid symmetric rule with `δ ≤ 2s`, either variant | Proved | `fbddRule`, `rule_of_fbdd` |
| Corollary 4.15: on unmodified FK-A, `δ ≥ (s − 2)/2` under every valid symmetric rule, `s` the least FBDD named by its functions; an explicit family defeating every such rule needs a monotone family with polynomial `N` and superpolynomial FBDD size | Proved for the bound; the step from FBDDs named by their functions to arbitrary FBDDs argued; the modified-variant bound argued; no such family known (literature, research §4) | `memo_fbdd`, `rule_of_fbdd` |
| Lemma 4.17: minors of `A ∪ B`, `A ∧ B` are unions, joins of minors; parts recoverable on disjoint supports | Proved; the consequence for `δ` argued | `Fm.minor_union`, `Fm.minor_join`, `Fm.union_left_part`, `Fm.join_left_part` |
| A read-once formula on all of `V` has a read-once DNF (Sperner, conformal, cograph primal graph); the converse is Gurvich's theorem | Proved for this direction; converse cited | `Fm.readOnce_dnf` |
| Proposition 4.18: the guarded rule is valid, symmetric, and splits on the least vertex of frequency `≥ 1/⌊log₂ N⌋`, which exists by FK96 Lemma 2.3.2 | Proved | `guardRule_frequent`, `valid_guardRule`, `guardRule_symm` |
| `δ` of GK `f₂` is 8 under all three rules; `ro12` has `δ = 91` under the leftmost and guarded rules | Checked | `gk2_rules`, `ro12_rules` |
| Conjecture 4.19: `δ/N` is unbounded on GK under the degree-sum rule | Open; `δ/N = 0.67, 1.92, 1368` for `k = 2, 3, 4` (Rust) | — |
| Proposition 4.6: under ETH no polynomial bounds `δ` on all dual pairs (C3 false) | Cited, conditional on ETH: a short argument from Kobayashi–Kurita–Wasa 2026; not in Lean | — |
| Theorem D1: `Tr(T[Γ]) = min(Tr(T)[Tr Γ])`; on disjoint supports no reduction, Sperner, `|T[Γ]| = Σ_t Π_i |Γ i|` | Proved | `tr_subst`, `tr_subst_of_disjoint`, `subst_isSperner`, `card_subst` |
| Proposition D2: `(P)` `k·k* ≥ 8^{r−1}` is closed under composition | Proved | `card_subst_uniform`, `prop_P_comp` |
| Proposition 5.4: D3 at `r = 2` has no counterexample; `(k, k*) ∈ {(2,4),(4,2),(3,3)}` | Checked (evaluation over 64 families) | `template_rank_two` |
| Proposition E2: automorphisms preserve influences; Fano's seven influences agree at every `p` | Proved | `influence_aut`, `influence_eq_of_transitive`, `fano_influence_eq` |
| Observation 4.20: GK f3 under modified degree-sum FK-A has 369 labelled states, 160 reached isomorphism classes and 155 cache visits | Computed; 15 bounded table rows checked against the hypergraph engine, shape equality checked against incidence-graph isomorphism | — |
| Proposition 4.21: common relabelling preserves equality with the transversal family and duality, including redundant families; any two FK-A split rules give the same verdict on relabelled inputs | Proved; the cache is Theorem 4.28 | `pimg_injective`, `tr_eq_pimg_iff`, `minimal_pimg`, `dual_pimg`, `fkAR_pimg` |
| Theorem 4.22: k-transitivity bounds ordered classes through depth k by 1+k(k+1); for self-transversal input by 1+k(k+1)/2, under every live-vertex rule and either variant | Proved | `SD.dual_transitive_bound`, `SD.self_transitive_bound`; normal form, transitivity bridge and exact isomorphism quotient in `SymmetryDepth` |
| Observation 4.23: Fano and Witt attain the self-transversal bound; complete(10,3) has 7 classes through depth 2, refuting the universal triangular shortcut | Computed; exact incidence-graph isomorphism in 18 configurations | `experiments/symmetry_depth.py`, `tests/test_symmetry_depth.py` |
| The symmetry-depth bounds are attained for every k by complete uniform families | Written proof, not formalised | `docs/symmetry-depth.md` |
| Theorem 4.24: every decision tree for `coalt i` (GK, TK; `n = 2^i ≥ 4`) has at least `2·(27/16)^{n/4}` leaves (JRSW 1999, restated) | Proved | `l1_le_leaves`, `wc_gk_succ`, `dsum_eq`, `gk_leaves` |
| Theorem 4.25: FK-A's recursion tree on a dual pair is a decision tree with at most `(n+1)τ` leaves; on GK and TK `τ ≥ 2·(27/16)^{n/4}/(n+1)` under every valid rule | Proved | `fkA_tree_dt`, `fkA_gk_tree`, `fkA_gk_degree_sum` |
| Corollary 4.26: (a) under the leftmost rule `τ/δ` is exponential in `n` on GK and TK; (b) under every valid rule FK-A is eventually slower than FK-B's `N^{4χ(N)+O(1)}` | (a) Proved; (b) uses FK96's bound, cited | `gk_memo_gap`, `dnf_coFm_gkH`, `fkA_gk_tree` |
| Proposition 4.27: C3 is equivalent to the monotone case of JRSW's Question 1 (1997) | Cited reading; the equivalence rests on Theorem 4.13, Proposition 4.14 and review row 29 | `memo_fbdd`, `rule_of_fbdd` |
| Theorem 4.28: FK-A with a memo keyed by any map sending each pair to a relabelling of it returns `Dual` under every rule and fuel, and its memo stays sound | Proved | `fkAI`, `fkAI_correct`, `fkAI_eq_fkAR` |
| Observation 4.29: `δ`, `δ_Aut`, `δ_iso`, `d_iso` on GK, TK, `alt3` and the library under three rules; GK `f₄` degree sum `δ_iso = 827,175`, `δ/δ_iso = 81.3`, `δ_iso/N = 16.8`; leftmost `δ = δ_iso = n` | Computed (Rust and Python); checked against `iso_memo.py`, an orbit canon and a group enumeration | `experiments/iso_classes.py`, `results/iso-memo.md`, `tests/test_readonce_dag.py` |
| Conjecture 4.30: `δ_iso/N` is unbounded on GK under the degree-sum rule | Open; `0.67, 0.83, 16.8` for `k = 2, 3, 4` (Rust) | — |
| Observation 4.31: the joint top-block projections of GK `f₃` contain only 21 of the 49 pairs of standalone `f₂` supports, so the unrestricted embedding route to Q1 fails | Computed (Rust), checked against the formula engine | `experiments/block_probe.py`, `results/block-probes.md`, `tests/test_readonce_probe.py` |
| Observation 4.32: on GK `f₅` the guarded rule never falls back to the degree sum and leaves the leftmost vertex at 92,776 of 124,874 splits | Computed (Rust); first departure re-derived in Python | `results/block-probes/gk5-guard.json`, `tests/test_readonce_probe.py` |
| Audit 4.33: no Chapter 3 statement about `Aut` at a node predicts `δ/δ_Aut` or `δ/δ_iso` | Reading of existing Lean statements; review rows 73–78 | — |
| Proposition 4.34: on GK `deg_C v = deg_D v` for every vertex; on TK `deg_C v · |D| = deg_D v · |C|` | Proved | `gk_degree_balance`, `tk_degree_ratio` |
| Observation 4.35: `δ_{k+1} ≥ δ_k²/4` holds at every measured step of GK and TK; TK's falling `δ/N` comes from `N_{k+1}/N_k² → 4` | Computed from existing values | — |
| Lemma 4.36: a top block's projected states are reached on the block by the hull rule | Argued, not in Lean | — |
| Proposition 4.37: a squaring step losing `A·n_k` with `A < 2.004` settles Conjecture 4.19; for `δ_iso` only a constant `A < 12.6` | Written proof | — |
| Conjecture 4.38: on GK `f_{k+1}`, `k ≥ 4`, every pair of equal-size standalone `f_k` supports occurs jointly in blocks `a`, `c` | Withdrawn: the equal-size form fails at `k = 2, 3` (Observation 4.39) | — |
| Observation 4.39: on GK `f₃`, `f₄` no pair of equal odd size occurs jointly; the share of target pairs occurring is `0.43`, `0.53` | Computed (Rust), equal-size counts checked against the formula engine at small levels | `results/block-probes/`, `tests/test_readonce_probe.py` |
| Conjecture 4.40: on GK `J_{k+1} ≥ σ_k²/4`; for `k ≥ 4` and any `A < 513` in place of 4 it implies Conjecture 4.19 | Open; holds for `k ≤ 3` | — |
| Observation 4.41: TK `S₄` degree sum, stopped at memory: `δ ≥ 330,149,945`, `δ/N ≥ 0.307`, `log δ/log N ≥ 0.943` | Computed (Rust, partial); lower bound only | — |
| Proposition 4.42: reduced-child degree monotonicity, exact least-label maximality, and consecutive OR/AND mate completion under stated edge hypotheses | Proved locally; all-reached-state GK parity corollary has a written proof, not Lean | `degree_minimal_del_le`, `degree_minimal_con_le`, `splitVar_earlier`, `splitVar_or_mate`, `splitVar_and_mate` |
| Proposition 4.43: exact weighted whole-pair recursion on GK and `E≤δ≤2E` for labelled whole-pair states | Written proof; macro reach checked against formula and hypergraph engines on `f₁–f₃`; no class-count recurrence | `experiments/cherry_probe.py`, `results/cherry-probes.md` |
| Observation 4.44: Lemma 4.36 must suppress local singleton stops; `f₂` embeds a singleton projection absent from standalone modified `f₁`; open hull on `f₃` has 6,604 supports, forced-mate hull 2,387 | Finite witness Checked; hull counts Computed, complete within stated caps | `gk2_embedded_singleton` (evaluation), `fkADagR_singleton`; `results/cherry-probes.json` |
| Lemma 4.45: normalized AHU equality characterizes ordered dual-pair isomorphism at fixed ground-set size; intact four-block boundaries give projection-shape multiplicity at most eight | Written proof, not Lean; no reachability or large-subclass assertion | `results/cherry-probes.md` |
| Proposition 4.46: exact GK growth predicates, sufficient fuel, edge squaring and conditional growth from a uniform squaring step with strict seed | Proved; uniform recurrence and sufficient seed remain hypotheses, Conjectures 4.19 and 4.30 open | `GK.reach_stable`, `GK.edges_succ`, `GK.isoGrowth_of_squaring`, `GK.labelledGrowth_of_squaring`, `GK.labelledGrowth_of_isoGrowth` |
| Observation 4.47: even whole-pair minors have exponentially many shapes, so mate completion alone cannot supply an `O(N)` shape cover | Written proof about all minors; no claim that degree sum reaches this subclass | `results/cherry-probes.md` |
| Observation 4.48: on `f₄`, 118 of 696 equal-profile whole-pair target pairings are absent; five of 71 underlying shape diagonals are absent across all standalone label variants | Computed, complete bounded traversal; not Lean-certified, does not refute either growth conjecture | `results/block-probes/gk4-incidence.json`, `gk4-profiles.json`; `test_even_shape_diagonal_counterexample` |

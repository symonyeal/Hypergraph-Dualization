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
| §1.1.1, complements of maximal independent sets are the minimal transversals | Proved | `isMinHit_compl_iff` |
| §1.1.2, `Tr(H)` is the CNF of the function whose DNF is `H` | Proved | `hits_tr_iff` |

## Chapter 2

| Statement | Status | Lean |
| --- | --- | --- |
| Lemma 2.1.1, partition criterion | Proved | `eq_tr_iff_partition` |
| Cor. 2.1.2, `H = Tr G ⟺ G = Tr H` | Proved | `eq_tr_comm` |
| Cor. 2.1.3, `Tr(Tr H) = H` | Proved; for non-Sperner `H` the value is `min(H)` | `tr_tr_of_sperner`, `tr_tr` |
| Props. 2.2.1–2.2.4, conditions (i)–(iv) | Proved | `edges_meet`, `support_eq`, `card_le_card_tr`, `kraft_sum` |
| Cor. 2.3.1, `s ≥ log n` | **Corrected**: the inequality is reversed, `2^s ≤ n`, i.e. `s ≤ log₂ n` | `two_pow_shortest_le`; counterexample `k3_refutes_printed_cor_2_3_1` |
| Lemma 2.3.2, a vertex of frequency `≥ 1/log n` | Proved (as `≥ 1/s` with `2^s ≤ n`) | `exists_frequent_vertex` |
| §2.2.2, `(G, H)` dual iff both FK-A subproblems are | Proved | `dual_split` |
| Algorithm 1 decides `Trans-Hyp` | Proved for every input and both leaf rules | `fkA_correct`, `conds_of_dual` |

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
| Observation 5.2.3, `ε(3) = 2/3` | Proved by exhaustion; `K₃` is the unique minimiser | `eps_three` |
| Observation 5.2.3, `ε(7) = 3/7` | Proved (2026-10): every non-trivial pair on `n` points has `s·ε ≥ 1` and `s ≤ nε` for its smallest edge size `s`, which forces `ε ≥ 3/7` on seven points; Fano attains it. Also `ε(4) = ε(5) = ε(6) = 1/2`, `ε(9) = 1/3` | `eps_seven`, `eps_bound`, `eps_four`, `eps_five`, `eps_six`, `eps_nine` |
| §5.2.2, Fano and `K₃` are self-transversal; `PG(2,3)` is not | Checked | `fano_self_tr`, `k3_self_tr`, `pg23_not_self_dual` |
| Def. 5.2.1, `7k` edges and the transversal count `(k−2)²/4 + k/2 + 1` | **Corrected**: `k` disjoint Fano planes have `7k` edges and `7^k` minimal transversals, for every `k` | `kFano_card`, `tr_kFano_card`, `two_fano_tr_card` |

## Trust base

General theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Statements marked
*Checked* are evaluations proved with `native_decide`, which adds the Lean compiler to the trust
base; a kernel-only (`decide +kernel`) run was tried on 2026-10-21 and is practical only for the
smallest instances. `lake build` reproduces everything; see [`lean/README.md`](../lean/README.md).

## Research beyond the thesis (2026-10)

New statements of the October 2026 research program, each written up in
[`docs/research-2026-10.md`](../docs/research-2026-10.md).

| Statement | Status | Lean |
| --- | --- | --- |
| Observation A1: `w11` is a Steiner system `S(4,5,11)`, self-transversal; distinct blocks meet in 1, 2 or 3 points (495, 660, 990 pairs) | Checked | `w11_steiner`, `w11_self_tr`, `w11_meet` |
| Theorem A2: `|Aut(w11)| = 7920`, sharply 4-transitive, primitive | Proved (finite checks by `native_decide`) | `card_aut_w11`, `w11_four_transitive`, `w11_four_free`, `w11_preprimitive` |
| Proposition A3: for Sperner `H` inside `U`, `Tr(H) = H` iff `H` is intersecting, `∅ ∉ H` and `H` is not 2-colourable; the Sperner hypothesis is needed | Proved | `tr_eq_self_iff`, `tr_eq_self_iff_needs_sperner` |
| Theorem A4: intersecting, `r`-uniform, `d`-regular on `t` points gives `d(r² − t) ≥ r(r − 1)`, equality iff distinct edges meet in one point | Proved | `intersecting_regular_bound` |
| Lemma: a relation preserved by a primitive action is connected or relates only equal points | Proved | `connected_or_trivial` |
| Proposition A7: a read-once hypergraph on `n ≥ 2` points with primitive `Aut(H)` has `Aut(H) = Sₙ` | Proved | `aut_eq_top_of_readOnce` |
| `w11` and the Fano plane are not read-once | Proved (`w11` via A2's finite checks; Fano by kernel `decide`) | `w11_not_readOnce`, `fano_not_readOnce` |
| Theorem A5a: in `S(t,k,v)`, `1 ≤ t ≤ k`, every block is disjoint from exactly `n₀(t,k,v) = Σ_{i<t} (−1)^i C(k,i)(λ_i − 1)` blocks; hence `n₀ ≥ 0` for every existing system | Proved | `steiner_disjoint`, `steiner_n0_nonneg` |
| Observation A5b: `n₀` for 19 parameter sets; no `S(t,k,v)` with `n₀ > 0` (nine sets, including every `S(2,3,15)`, `S(3,4,16)`, `S(5,8,24)`) is self-transversal; none with `n₀ < 0` (ten sets) exists | Proved (kernel `decide`) | `n0_table`, `steiner_tr_ne_of_table`, `not_steiner_of_table` |
| `PG(2,4)` and `S(4,7,23)` are intersecting Steiner systems with a 2-colouring, so not self-transversal | Checked | `pg24_steiner`, `pg24_tr_ne`, `s4723_steiner`, `s4723_tr_ne` |
| Theorem B: `s·ε ≥ 1` and `s ≤ nε` for the smallest edge size `s`; hence `nε² ≥ 1` | Proved | `eps_bound`, `eps_sq` |
| `ε(8) = 2/5` | Open: `3/8 ≤ ε(8) ≤ 2/5` proved; CP-SAT finds no pair below `2/5` (`experiments/eps_search.py`) | `eps_bound`, `eightVer_eps` |
| Theorem C1: `matching(v)` has `τ = 2^{v/2+1} − 3`, `δ = v`; `threshold(v)` has `τ = δ = v − 1` (modified FK-A, every even `v`) | Proved | `matching_tau_delta`, `threshold_tau_delta` |
| Theorem A5c: every Steiner system `S(t, t+1, 2t+3)` is self-transversal, and `t` is even | Proved | `witt_tr_eq` |
| Theorem (Seymour 1974): a 3-critical hypergraph covering `n` points has at least `n` edges | Proved | `card_le_of_critical` |
| A self-transversal Sperner hypergraph covering `n` points has `|H| ≥ n` (equality for `K₃`, Fano) | Proved | `card_le_of_tr_eq_self`, `erase_twoColourable` |
| Counting test: for intersecting Sperner `H` without `∅`, `Tr(H) = H` iff `2^{n−1}` subsets contain an edge | Proved | `tr_eq_self_iff_card` |
| If `Tr(H) ⊆ H` and `Aut(H)` is edge-transitive, it is transitive on covered points | Proved | `transitive_of_edge_transitive` |
| Hertel's alternating-tree bound (cited in Chapter 4) is a lower bound on DPLL trees, not an upper bound on subproblems | Corrected citation (revised edition, Chapter 4) | — |
| Observation 4.4: FK-A's degree-sum rule exceeds Hertel's memoised `2k + 3` on GK `f₃` (`δ = 369 > 65`) | Computed (`experiments/readonce_sim.py`) | — |
| Conjecture 4.5: `δ ≤ 2N` on read-once pairs under FK-A's rule | Open; `δ/N ≤ 1.93` on every pair measured | — |
| Proposition 4.6: under ETH no polynomial bounds `δ` on all dual pairs (C3 false) | Proved conditionally, from Kobayashi–Kurita–Wasa 2026 (cited) | — |
| Theorem D1: `Tr(T[Γ]) = min(Tr(T)[Tr Γ])`; on disjoint supports no reduction, Sperner, `|T[Γ]| = Σ_t Π_i |Γ i|` | Proved | `tr_subst`, `tr_subst_of_disjoint`, `subst_isSperner`, `card_subst` |
| Proposition D2: `(P)` `k·k* ≥ 8^{r−1}` is closed under composition | Proved | `card_subst_uniform`, `prop_P_comp` |
| Proposition E2: automorphisms preserve influences; Fano's seven influences agree at every `p` | Proved | `influence_aut`, `influence_eq_of_transitive`, `fano_influence_eq` |

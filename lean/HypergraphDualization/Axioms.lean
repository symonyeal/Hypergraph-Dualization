/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The trust base, checked

`lake build` fails if a general theorem cited in the documents depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound` (an unfinished proof shows up as `sorryAx`), or if a fact the
documents label *Checked* or *Observation (evaluation)* is not in fact an evaluation
(`native_decide`, which adds the Lean compiler to the trust base).
-/
import HypergraphDualization.Basic
import HypergraphDualization.Duality
import HypergraphDualization.Conditions
import HypergraphDualization.Decomposition
import HypergraphDualization.Algorithm
import HypergraphDualization.Symmetry
import HypergraphDualization.Operations
import HypergraphDualization.Data
import HypergraphDualization.Instances
import HypergraphDualization.Families
import HypergraphDualization.Twins
import HypergraphDualization.Section32
import HypergraphDualization.Recursion
import HypergraphDualization.Frequency
import HypergraphDualization.Cotree
import HypergraphDualization.Trees
import HypergraphDualization.TreeFacts
import HypergraphDualization.Connections
import HypergraphDualization.Corrections
import HypergraphDualization.AltShape
import HypergraphDualization.FanoCopies
import HypergraphDualization.Witt
import HypergraphDualization.SelfTransversal
import HypergraphDualization.Critical
import HypergraphDualization.Primitive
import HypergraphDualization.Steiner
import HypergraphDualization.SteinerInstances
import HypergraphDualization.EpsSeven
import HypergraphDualization.Dag
import HypergraphDualization.Substitution
import HypergraphDualization.Influence
import HypergraphDualization.FrequencyGap
import HypergraphDualization.Blowup
import HypergraphDualization.SplitRule
import HypergraphDualization.ReadOnceFormula
import HypergraphDualization.BranchingProgram
import HypergraphDualization.RuleInstances
import HypergraphDualization.SymmetryDepth
import HypergraphDualization.GkMemo
import HypergraphDualization.IsoMemo

open Lean Elab Command

/-- Fail unless every named constant depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (· ∉ #[``propext, ``Classical.choice, ``Quot.sound])
    unless bad.isEmpty do throwErrorAt id m!"{n} depends on {bad}"

/-- Fail unless every named constant depends on an evaluation (`native_decide`) axiom. -/
elab "#assert_evaluation " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    unless axs.any (fun a => (`_native).isPrefixOf a || a.toString.contains "_native") do
      throwErrorAt id m!"{n} is not an evaluation: {axs}"

/-! ### General theorems -/

#assert_standard_axioms
  HD.l1_le_leaves HD.wc_gk_succ HD.dsum_succ HD.dsum_zero HD.dsum_eq HD.gk_leaves
  HD.eval_fkDT HD.leaves_fkDT HD.fkA_tree_dt HD.fkA_gk_tree HD.fkA_gk_degree_sum
  HD.ordered_coFm HD.dnf_coFm HD.dnf_coFm_gkH HD.gk_memo_gap
  HD.SD.Trace.normal HD.SD.fkADag_trace HD.SD.cut_pimg HD.SD.hom_of_transitive
  HD.SD.depth_bound HD.SD.self_depth_bound HD.SD.upto_bound HD.SD.self_upto_bound
  HD.SD.isoKey_eq_iff HD.SD.transitive_bound HD.SD.self_transitive_bound HD.SD.dual_transitive_bound
  HD.pimg_injective HD.tr_eq_pimg_iff HD.minimal_pimg HD.dual_pimg HD.fkAR_pimg
  HD.dual_of_key_eq HD.fkAI_correct HD.fkAI_eq_fkAR
  HD.Data.fanoC HD.Fix.gem_chordal_five HD.Fix.gem_chordal_four HD.Fix.gem_not_distance_hereditary
  HD.Fix.printed_recurrence_fails HD.Fm.ReadOnce HD.Fm.St HD.Fm.St_closed HD.Fm.card_St_le
  HD.Fm.cograph_dnf HD.Fm.conformal_dnf HD.Fm.dnf_restrict_false HD.Fm.dnf_restrict_true
  HD.Fm.eq_of_support_eq HD.Fm.join_left_part HD.Fm.leftRule_closed HD.Fm.leftmost_delta
  HD.Fm.leftmost_delta_le HD.Fm.leftmost_fbdd HD.Fm.minor_join HD.Fm.minor_union HD.Fm.readOnce_dnf
  HD.Fm.rminor_determined HD.Fm.support_dnf HD.Fm.tr_dnf HD.Fm.tr_dnf_readOnce
  HD.Fm.union_left_part HD.Fm.upHit_dnf HD.IsBP HD.IsCograph HD.IsFBDD HD.IsSteiner
  HD.OpenAI.IsCover HD.OpenAI.bernoulliProbability HD.OpenAI.bernoulliWeight
  HD.OpenAI.bernoulli_dual HD.OpenAI.bernoulli_self_dual HD.OpenAI.coverCardinalities
  HD.OpenAI.coverNumber HD.OpenAI.coverNumber_eq_tr_min HD.OpenAI.coverNumber_le_of_intersecting
  HD.OpenAI.isCover_iff_hits HD.OpenAI.ryser_extremal_size HD.ReadOnce HD.S32.crossExcess_bound
  HD.S32.eps_badCross HD.S32.eps_bound HD.S32.eps_crossExcess HD.S32.eps_eq_cross_singleton
  HD.S32.eps_eq_rigid HD.S32.eps_eq_sperner HD.S32.eps_ge_inv HD.S32.eps_overlap_gap
  HD.S32.eps_self_diagonal HD.S32.eps_self_strict HD.S32.eps_sq HD.S32.eps_strict_of_nonsquare
  HD.S32.fano_crossExcess HD.S32.path_four_not_extremal HD.S32.sizeAt
  HD.S32.sum_degree_mul_eq_excess HD.S32.uniform_regular_cross_singleton
  HD.S32.young_aut_singletons HD.TwoColourable HD.alt_counts HD.alt_shape
  HD.aut_child_moves_split_to_isolated HD.aut_eq_top_of_readOnce HD.aut_le_aut_minimal
  HD.aut_tr_eq_aut_minimal HD.aut_tr_of_sperner HD.bernoulliWeight_pmap HD.card_alt_succ
  HD.card_between HD.card_coalt_succ HD.card_disjoint_eq HD.card_fkADagR_le_closed
  HD.card_fkADag_le HD.card_fkADag_le_minors HD.card_join_of_disjoint HD.card_le_card_tr
  HD.card_le_of_critical HD.card_le_of_tr_eq_self HD.card_subst HD.card_subst_uniform
  HD.conds_of_dual HD.connected_or_trivial HD.degree_eq_of_transitive HD.degree_join_left
  HD.degree_mapH_shift HD.degree_union_left HD.dual_empty_left HD.dual_erase_of_notMem
  HD.dual_singleton_left HD.dual_split HD.edges_meet HD.eq_tr_comm HD.eq_tr_iff_partition
  HD.eq_univ_of_complete HD.erase_twoColourable HD.excess_split HD.exists_frequent_vertex
  HD.f2_g2_printed HD.falseTwin_filtered HD.fano_influence_eq HD.fano_not_readOnce HD.fbddRule_symm
  HD.fkA HD.fkADag HD.fkADagR HD.fkADagR_closed HD.fkADagR_left HD.fkADagR_minimal HD.fkADagR_right
  HD.fkADagR_splitVar HD.fkADagR_sub HD.fkADag_minor HD.fkADag_split HD.fkADag_within HD.fkAR
  HD.fkAR_correct HD.fkAR_left HD.fkAR_minimal HD.fkAR_right HD.fkAR_split HD.fkAR_splitVar
  HD.fkATree HD.fkA_comm HD.fkA_correct HD.fkA_split HD.guardRule HD.guardRule_frequent
  HD.guardRule_symm HD.hits_subst HD.hits_tr_iff HD.influence_aut HD.influence_eq_of_transitive
  HD.intersecting_regular_bound HD.invariant_eq_union_orbits HD.invariant_iff_orbits
  HD.isFBDD_of_closed HD.isMinHit_compl_iff HD.isSteiner_of_packing HD.join_isSperner_of_disjoint
  HD.kFano_card HD.kids_eq HD.kids_mem HD.kraft_sum HD.leftRule HD.leftRule_symm HD.matching_law
  HD.matching_tau_delta HD.mem_fkADagR_succ HD.memo_bp HD.memo_fbdd HD.memo_good HD.minimal_con_tr
  HD.n0_table HD.not_steiner_of_table HD.not_trueTwin_and_falseTwin HD.orbit_minimal HD.path_nodup
  HD.primalAdj_alt HD.primalAdj_con HD.primalAdj_del HD.primalAdj_minimal HD.primal_children_le
  HD.prop_P_comp HD.root_mem_fkADagR HD.rule_of_fbdd HD.run_correct HD.splitVar HD.splitVar_comm
  HD.splitVar_spec HD.splitVar_symm HD.stab_mem_aut_con HD.stab_mem_aut_del HD.steiner_count
  HD.steiner_disjoint HD.steiner_n0_nonneg HD.steiner_tr_ne HD.steiner_tr_ne_of_table
  HD.subst_isSperner HD.support_alt HD.support_eq HD.swap_isAut_of_twins HD.tau_ge_of_resilient
  HD.threshold_tau_delta HD.tr_alt HD.tr_coalt HD.tr_con_eq HD.tr_eq_self_iff
  HD.tr_eq_self_iff_card HD.tr_eq_self_iff_needs_sperner HD.tr_equivariant HD.tr_isSperner
  HD.tr_join HD.tr_join_disjoint HD.tr_kFano_card HD.tr_minimal HD.tr_singleton HD.tr_subst
  HD.tr_subst_of_disjoint HD.tr_tr HD.tr_tr_of_sperner HD.tr_union HD.tr_union_disjoint
  HD.transitive_of_edge_transitive HD.twins_map HD.twins_mem_aut_cliques HD.two_pow_shortest_le
  HD.upHit_con HD.upHit_del HD.upHit_pimg HD.upHit_subst HD.valid_fbddRule HD.valid_guardRule
  HD.valid_leftRule HD.valid_splitVar HD.witt_tr_eq

/-! ### Evaluations (*Checked*, *Observation (evaluation)*) -/

#assert_evaluation
  HD.Data.eightVer_eps HD.Data.eightVer_printed_not_dual HD.Data.eightVer_tree
  HD.Data.eightVer_uniform HD.Data.faithful_nodes HD.Data.fano_self_tr
  HD.Data.k3_refutes_printed_cor_2_3_1 HD.Data.k3_self_tr HD.Data.pg23_not_self_dual
  HD.Data.sevenVer_tree HD.Data.sixA_printed_not_dual HD.Data.sixD_tree HD.Data.two_fano_tr_card
  HD.Fix.claim_3_1_6_counterexample HD.Fix.cor_3_3_4_not_iso HD.Fix.lemma_3_3_1_needs_sperner
  HD.OpenAI.fano_k3_balanced HD.S32.c4_tr HD.S32.classes_four HD.S32.d31_tr HD.S32.eps_five
  HD.S32.eps_four HD.S32.eps_nine HD.S32.eps_seven HD.S32.eps_six HD.S32.eps_three
  HD.S32.ex34_corrected HD.S32.k2dd_freq HD.S32.k2dd_mfv_not_optimal HD.S32.k2dd_printed_not_tr
  HD.S32.k2dd_tr HD.S32.k3dot_printed_not_sperner HD.S32.k3dot_tr HD.S32.k4_printed_not_tr
  HD.S32.k4_tr HD.S32.k4minus_printed_not_tr HD.S32.k4minus_tr HD.S32.max_tree_four
  HD.S32.max_tree_three HD.S32.p4_printed_not_tr HD.S32.p4_tr HD.S32.pn3_freq HD.S32.pn3_tr
  HD.S32.pn3bar_freq HD.S32.pn3bar_printed_not_tr HD.S32.pn3bar_tr HD.S32.self_dual_classes_four
  HD.S32.sperner_four_card HD.S32.table_aut HD.S32.table_orbits HD.Steiner.pg24_intersecting
  HD.Steiner.pg24_steiner HD.Steiner.pg24_tr_ne HD.Steiner.s4723_intersecting
  HD.Steiner.s4723_steiner HD.Steiner.s4723_tr_ne HD.Witt.card_aut_w11 HD.Witt.eq_one_of_fixes_base
  HD.Witt.mem_of_mask HD.Witt.stab_check HD.Witt.w11_four_free HD.Witt.w11_four_transitive
  HD.Witt.w11_meet HD.Witt.w11_preprimitive HD.Witt.w11_self_tr HD.Witt.w11_steiner
  HD.Witt.witCheck_eq HD.Witt.wit_check HD.f2g2_false_twin_filtered HD.gk2_rules
  HD.lemma_3_3_3_false HD.matching_eight HD.matching_eight_not_resilient HD.ro12_delta
  HD.ro12_readOnce HD.ro12_rules HD.template_rank_two HD.template_rank_two_check
  HD.threshold_twelve HD.w11_not_readOnce

/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Self-transversal hypergraphs are 3-critical (research track A)

A self-transversal Sperner hypergraph is not 2-colourable (Proposition A3), but becomes
2-colourable on deleting any edge. Seymour's theorem on such hypergraphs then bounds its size,
and transitivity on edges forces transitivity on points.

| Lean | Statement |
| --- | --- |
| `card_le_of_critical` | **Seymour (1974).** Not 2-colourable, 2-colourable after deleting any edge, no isolated point: `n ≤ |H|` |
| `erase_twoColourable` | a self-transversal Sperner `H` is 2-colourable after deleting any edge `e`: take `A = e` |
| `card_le_of_tr_eq_self` | a self-transversal Sperner `H` covering `n` points has `n ≤ |H|`; equality for `K₃` and Fano |
| `tr_eq_self_iff_card` | for intersecting Sperner `H` without `∅`: `Tr(H) = H` iff exactly `2^{n−1}` subsets contain an edge |
| `transitive_of_edge_transitive` | if `Tr(H) ⊆ H` and `Aut(H)` is transitive on edges, it is transitive on covered points |
-/
import HypergraphDualization.SelfTransversal
import HypergraphDualization.Symmetry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace HD

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
/-- In a vector `y` whose sum over `e` vanishes, a nonzero entry on `e` forces entries of both
signs on `e`. -/
theorem pos_neg_of_sum_zero {e : Finset α} {y : α → ℚ} (h : ∑ x ∈ e, y x = 0)
    (hne : ∃ x ∈ e, y x ≠ 0) : (∃ x ∈ e, 0 < y x) ∧ ∃ x ∈ e, y x < 0 := by
  obtain ⟨z, hz, hyz⟩ := hne
  constructor
  · by_contra hp
    push Not at hp
    exact hyz ((sum_eq_zero_iff_of_nonpos hp).1 h z hz)
  · by_contra hn
    push Not at hn
    exact hyz ((sum_eq_zero_iff_of_nonneg hn).1 h z hz)

/-- **Seymour (1974)**; Bretto, *Hypergraph Theory*, Thm 3.6. Let `H` cover every point, be
not 2-colourable, and be 2-colourable after deleting any one edge. Then `n ≤ |H|`.

Proof: if `|H| < n`, the incidence columns `x ↦ ([x ∈ e])_{e ∈ H}` in `ℚ^H` are dependent, so
some `y ≠ 0` has `Σ_{x∈e} y_x = 0` for every edge. An edge carrying a nonzero entry has entries
of both signs. Let `e₀` carry a nonzero entry and `A'` 2-colour `H − e₀`. Colour `y > 0` red,
`y < 0` blue, and `y = 0` as `A'`: every edge is bichromatic, a contradiction. -/
theorem card_le_of_critical {H : Finset (Finset α)} (hcov : ∀ x, ∃ e ∈ H, x ∈ e)
    (h2 : ¬ TwoColourable univ H) (hcrit : ∀ e ∈ H, TwoColourable univ (H.erase e)) :
    Fintype.card α ≤ H.card := by
  by_contra hlt
  push Not at hlt
  let col : α → (H → ℚ) := fun x e => if x ∈ (e : Finset α) then 1 else 0
  have hdep : ¬ LinearIndependent ℚ col := fun hli => by
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    omega
  obtain ⟨y, hy, x0, hx0⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hsum : ∀ e ∈ H, ∑ x ∈ e, y x = 0 := fun e he => by
    have := congrFun hy ⟨e, he⟩
    simpa [col, Finset.sum_apply, ← Finset.sum_filter] using this
  obtain ⟨e0, he0, hx0e⟩ := hcov x0
  obtain ⟨A', -, h1, h2'⟩ := hcrit e0 he0
  let A := A'.filter (fun x => y x = 0) ∪ univ.filter (fun x => 0 < y x)
  refine h2 ⟨A, subset_univ _, ?_, ?_⟩
  · rintro ⟨f, hf, hfA⟩
    by_cases hz : ∃ x ∈ f, y x ≠ 0
    · obtain ⟨z, hz, hyz⟩ := (pos_neg_of_sum_zero (hsum f hf) hz).2
      rcases mem_union.1 (hfA hz) with h | h <;> linarith [(mem_filter.1 h).2]
    · push Not at hz
      have hfe : f ≠ e0 := fun h => hx0 (hz x0 (h ▸ hx0e))
      refine h1 ⟨f, mem_erase.2 ⟨hfe, hf⟩, fun x hx => ?_⟩
      rcases mem_union.1 (hfA hx) with h | h
      · exact (mem_filter.1 h).1
      · simp [hz x hx] at h
  · rintro ⟨f, hf, hfA⟩
    by_cases hz : ∃ x ∈ f, y x ≠ 0
    · obtain ⟨z, hz, hyz⟩ := (pos_neg_of_sum_zero (hsum f hf) hz).1
      exact (mem_sdiff.1 (hfA hz)).2 (mem_union_right _ (by simpa using hyz))
    · push Not at hz
      have hfe : f ≠ e0 := fun h => hx0 (hz x0 (h ▸ hx0e))
      refine h2' ⟨f, mem_erase.2 ⟨hfe, hf⟩, fun x hx => ?_⟩
      refine mem_sdiff.2 ⟨mem_univ x, fun hA' => ?_⟩
      exact (mem_sdiff.1 (hfA hx)).2 (mem_union_left _ (mem_filter.2 ⟨hA', hz x hx⟩))

/-- A self-transversal Sperner `H` is 2-colourable after deleting any edge `e`: no other edge
lies inside `e` (Sperner) or avoids it (intersecting). -/
theorem erase_twoColourable {H : Finset (Finset α)} (sH : IsSperner H)
    (hI : OpenAI.Intersecting H) {e : Finset α} (he : e ∈ H) :
    TwoColourable univ (H.erase e) := by
  refine ⟨e, subset_univ e, fun ⟨f, hf, hfe⟩ => ?_, fun ⟨f, hf, hfe⟩ => ?_⟩
  · exact (ne_of_mem_erase hf) (sH f (mem_of_mem_erase hf) e he hfe)
  · obtain ⟨x, hx⟩ := hI e he f (mem_of_mem_erase hf) (ne_of_mem_erase hf).symm
    rw [mem_inter] at hx
    exact (mem_sdiff.1 (hfe hx.2)).2 hx.1

/-- A self-transversal Sperner hypergraph covering all `n` points has at least `n` edges.
Equality holds for `K₃` and the Fano plane; `w11` has 66 edges on 11 points. -/
theorem card_le_of_tr_eq_self {H : Finset (Finset α)} (sH : IsSperner H)
    (hT : tr univ H = H) (hcov : ∀ x, ∃ e ∈ H, x ∈ e) : Fintype.card α ≤ H.card := by
  obtain ⟨hI, -, h2⟩ := (tr_eq_self_iff (fun e _ => subset_univ e) sH).1 hT
  exact card_le_of_critical hcov h2 fun e he => erase_twoColourable sH hI he

omit [Fintype α] in
/-- **Counting test.** Let `H` be Sperner, inside `U`, intersecting, without the empty edge. Then
`Tr(H) = H` iff exactly half of the subsets of `U` contain an edge. (Mezzini et al. 2025, Lemma 4,
in the language of self-dual functions: `f ≤ f^d` and `#f⁻¹(1) = 2^{n−1}`.)

Proof: `A ↦ U \ A` maps the sets containing an edge onto the sets whose complement contains one;
the two families are disjoint because `H` is intersecting; by Proposition A3, `Tr(H) = H` iff they
cover the power set. -/
theorem tr_eq_self_iff_card {U : Finset α} {H : Finset (Finset α)} (hH : Within U H)
    (sH : IsSperner H) (hI : OpenAI.Intersecting H) (h0 : ∅ ∉ H) :
    tr U H = H ↔ 2 * (U.powerset.filter (upHit H)).card = 2 ^ U.card := by
  set W := U.powerset.filter (upHit H)
  set W' := U.powerset.filter fun A => upHit H (U \ A)
  have hc : W'.card = W.card := by
    refine card_nbij' (U \ ·) (U \ ·) ?_ ?_ ?_ ?_ <;> intro A hA <;>
      simp only [W, W', coe_filter, Set.mem_ofPred_eq, mem_powerset] at hA ⊢
    · exact ⟨sdiff_subset, hA.2⟩
    · exact ⟨sdiff_subset, by rw [Finset.sdiff_sdiff_eq_self hA.1]; exact hA.2⟩
    · exact Finset.sdiff_sdiff_eq_self hA.1
    · exact Finset.sdiff_sdiff_eq_self hA.1
  have hd : Disjoint W W' := by
    refine disjoint_filter.2 fun A _ ⟨e, he, heA⟩ ⟨f, hf, hfA⟩ => ?_
    by_cases hef : e = f
    · subst hef
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 fun h => h0 (h ▸ he)
      exact (mem_sdiff.1 (hfA hx)).2 (heA hx)
    · obtain ⟨x, hx⟩ := hI e he f hf hef
      rw [mem_inter] at hx
      exact (mem_sdiff.1 (hfA hx.2)).2 (heA hx.1)
  have hu : (W ∪ W').card = 2 * W.card := by rw [card_union_of_disjoint hd, hc, two_mul]
  rw [tr_eq_self_iff hH sH, ← hu, ← filter_or, ← card_powerset U, card_filter_eq_iff]
  simp only [mem_powerset, TwoColourable, not_exists, not_and, hI, h0, not_false_eq_true,
    true_and]
  exact ⟨fun h A hA => by by_contra hn; push Not at hn; exact h A hA hn.1 hn.2,
    fun h A hA h1 h2 => (h A hA).elim h1 h2⟩

/-- If every minimal transversal of `H` is an edge (`Tr(H) ⊆ H`, e.g. `H` self-transversal) and
`Aut(H)` is transitive on edges, then `Aut(H)` is transitive on the points `H` covers.

Proof: the orbit `O` of `x` meets every edge (move an edge through `x` onto it), so it contains a
minimal transversal, which is an edge; moving that edge onto an edge through `y` puts `y` in
`O`. -/
theorem transitive_of_edge_transitive {H : Finset (Finset α)} (hT : tr univ H ⊆ H)
    (hE : ∀ e ∈ H, ∀ f ∈ H, ∃ σ ∈ aut H, pmap σ e = f) {x y : α}
    (hx : ∃ e ∈ H, x ∈ e) (hy : ∃ e ∈ H, y ∈ e) : ∃ σ ∈ aut H, σ x = y := by
  classical
  let O := univ.filter fun z => ∃ σ ∈ aut H, σ x = z
  obtain ⟨e0, he0, hxe⟩ := hx
  have hO : Hits H O := fun f hf => by
    obtain ⟨σ, hσ, rfl⟩ := hE e0 he0 f hf
    exact ⟨σ x, mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _, σ, hσ, rfl⟩, by simpa using hxe⟩⟩
  obtain ⟨T, hTO, hTmin⟩ := exists_isMinHit_subset _ O rfl hO
  obtain ⟨e2, he2, hye⟩ := hy
  obtain ⟨τ, hτ, hτT⟩ := hE T (hT (mem_tr.2 ⟨subset_univ T, hTmin⟩)) e2 he2
  rw [← hτT, mem_pmap] at hye
  obtain ⟨σ, hσ, hσx⟩ := (mem_filter.1 (hTO hye)).2
  exact ⟨τ * σ, mul_mem hτ hσ, by simp [Equiv.Perm.mul_apply, hσx]⟩

end HD

/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Bridges to the `openai/math` results

Definitions marked *(openai/math)* are restated verbatim from the comparator challenges
`lean/ComparatorChallenges/RyserCovering.lean` and `SecondKahnKalai.lean` of
<https://github.com/openai/math>, so the statements below are about the same objects. That
library is not imported (it pins another Lean toolchain).

| Lean | Connection |
| --- | --- |
| `isCover_iff_hits` | a Ryser cover is a transversal (Def. 1.1.4) |
| `coverNumber_eq_tr_min` | the covering number `τ(H)` is the size of a smallest edge of `Tr(H)` |
| `coverNumber_le_of_intersecting` | an intersecting `r`-uniform hypergraph has `τ ≤ r`; Ryser's conjecture asks for `r - 1`, and the `openai/math` counterexamples attain `r` |
| `ryser_extremal_size` | if `τ(H) = r` for an `r`-uniform `H`, then `|H| + |Tr(H)| ≥ 2^r` (Cor. 2.3.1, corrected) |
| `bernoulli_dual` | for a transversal pair, `P_p(G) + P_{1-p}(H) = 1`: duality is complementation of monotone properties |
| `bernoulli_self_dual` | a self-transversal hypergraph (`K₃`, `hw₃`, Fano) has `P_{1/2} = 1/2` exactly |
-/
import HypergraphDualization.Instances
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace HD.OpenAI

open HD Finset

variable {V : Type*} [DecidableEq V]

/-! ### Ryser's covering conjecture (`openai/math` result family 162) -/

/-- *(openai/math)* `C` meets every edge. -/
def IsCover (H : Finset (Finset V)) (C : Finset V) : Prop := ∀ e ∈ H, ∃ v ∈ C, v ∈ e

/-- *(openai/math)* Distinct edges meet. -/
def Intersecting (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).Nonempty

/-- *(openai/math)* The sizes of covers. -/
def coverCardinalities (H : Finset (Finset V)) : Set ℕ :=
  {n | ∃ C : Finset V, IsCover H C ∧ C.card = n}

/-- *(openai/math)* The covering number `τ(H)`. -/
noncomputable def coverNumber (H : Finset (Finset V)) : ℕ := sInf (coverCardinalities H)

theorem isCover_iff_hits {H : Finset (Finset V)} {C : Finset V} : IsCover H C ↔ Hits H C := by
  constructor
  · intro h e he
    obtain ⟨v, hv, hve⟩ := h e he
    exact ⟨v, mem_inter.2 ⟨hv, hve⟩⟩
  · intro h e he
    obtain ⟨v, hv⟩ := h e he
    exact ⟨v, (mem_inter.1 hv).1, (mem_inter.1 hv).2⟩

variable [Fintype V]

/-- **`τ(H)` is the smallest edge size of `Tr(H)`**: some minimal transversal has exactly
`τ(H)` vertices and none has fewer. -/
theorem coverNumber_eq_tr_min {H : Finset (Finset V)} (h0 : ∅ ∉ H) :
    (∃ T ∈ tr univ H, T.card = coverNumber H) ∧ ∀ T ∈ tr univ H, coverNumber H ≤ T.card := by
  have hne : (coverCardinalities H).Nonempty := by
    refine ⟨(univ : Finset V).card, univ, fun e he => ?_, rfl⟩
    obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ he))
    exact ⟨v, mem_univ v, hv⟩
  have low : ∀ T ∈ tr univ H, coverNumber H ≤ T.card := fun T hT =>
    Nat.sInf_le ⟨T, isCover_iff_hits.2 (mem_tr.1 hT).2.1, rfl⟩
  refine ⟨?_, low⟩
  obtain ⟨C, hC, hcard⟩ := Nat.sInf_mem hne
  obtain ⟨T, hTC, hT⟩ := exists_isMinHit_subset _ C rfl (isCover_iff_hits.1 hC)
  have hTtr : T ∈ tr univ H := mem_tr.2 ⟨subset_univ _, hT⟩
  refine ⟨T, hTtr, le_antisymm ?_ (low T hTtr)⟩
  calc T.card ≤ C.card := card_le_card hTC
    _ = coverNumber H := hcard

/-- An intersecting hypergraph whose edges all have `r` vertices has `τ(H) ≤ r`: any edge is
a cover. Ryser's conjecture asserts `τ ≤ r - 1` for `r`-partite ones; the `openai/math`
counterexamples are exactly the extremal case `τ = r`. -/
theorem coverNumber_le_of_intersecting {H : Finset (Finset V)} {r : ℕ} (hI : Intersecting H)
    (hu : ∀ e ∈ H, e.card = r) (hr : 0 < r) (hH : H.Nonempty) : coverNumber H ≤ r := by
  obtain ⟨e, he⟩ := hH
  have hcov : IsCover H e := fun f hf => by
    by_cases hef : e = f
    · subst hef
      obtain ⟨v, hv⟩ := card_pos.1 ((hu e he).symm ▸ hr)
      exact ⟨v, hv, hv⟩
    · obtain ⟨v, hv⟩ := hI e he f hf hef
      exact ⟨v, (mem_inter.1 hv).1, (mem_inter.1 hv).2⟩
  exact Nat.sInf_le (show r ∈ coverCardinalities H from ⟨e, hcov, hu e he⟩)

/-- **The extremal case is large.** If every edge of `H` has `r` vertices and `τ(H) = r`
(as in the `openai/math` Ryser counterexamples), then `|H| + |Tr(H)| ≥ 2^r`: every edge of
`H` and of `Tr(H)` has at least `r` vertices, and Corollary 2.3.1 (corrected) applies. -/
theorem ryser_extremal_size {H : Finset (Finset V)} {r : ℕ} (hu : ∀ e ∈ H, e.card = r)
    (hr : 0 < r) (hτ : coverNumber H = r) : 2 ^ r ≤ H.card + (tr univ H).card := by
  have h0 : ∅ ∉ H := fun h => by have := hu ∅ h; simp at this; omega
  have sH : IsSperner H := fun e he f hf hef =>
    eq_of_subset_of_card_le hef (by rw [hu e he, hu f hf])
  refine two_pow_shortest_le (fun _ _ => subset_univ _) sH rfl r fun e he => ?_
  rcases mem_union.1 he with he | he
  · exact (hu e he).ge
  · exact hτ ▸ (coverNumber_eq_tr_min h0).2 e he

/-! ### Thresholds of monotone properties (families 175, 176, 186) -/

/-- *(openai/math)* The product measure of a set `W`. -/
noncomputable def bernoulliWeight (p : ℝ) (W : Finset V) : ℝ := ∏ x, if x ∈ W then p else 1 - p

/-- *(openai/math)* The probability of a property under the product measure. -/
noncomputable def bernoulliProbability (p : ℝ) (P : Finset V → Prop) : ℝ := by
  classical
  exact ∑ W, if P W then bernoulliWeight p W else 0

theorem bernoulliWeight_compl (p : ℝ) (W : Finset V) :
    bernoulliWeight (1 - p) Wᶜ = bernoulliWeight p W := by
  unfold bernoulliWeight
  refine prod_congr rfl fun x _ => ?_
  by_cases hx : x ∈ W <;> simp [hx]

theorem sum_bernoulliWeight (p : ℝ) : ∑ W : Finset V, bernoulliWeight p W = 1 := by
  have h := Finset.prod_add (fun _ : V => p) (fun _ => 1 - p) (univ : Finset V)
  simp only [add_sub_cancel, prod_const_one, powerset_univ] at h
  refine Eq.trans ?_ h.symm
  refine sum_congr rfl fun W _ => ?_
  unfold bernoulliWeight
  rw [prod_ite]
  congr 1 <;> refine prod_congr ?_ fun _ _ => rfl <;> ext x <;> simp

/-- **Duality is complementation.** For a transversal pair `(G, H)` on `V`, the probability
that a `p`-random set contains an edge of `G`, plus the probability that a `(1-p)`-random
set contains an edge of `H`, is `1`. -/
theorem bernoulli_dual {G H : Finset (Finset V)} (h : Dual univ G H) (p : ℝ) :
    bernoulliProbability p (upHit G) + bernoulliProbability (1 - p) (upHit H) = 1 := by
  rw [dual_iff] at h
  have hc : ∀ W : Finset V, upHit H Wᶜ ↔ ¬ upHit G W := by
    intro W
    have := h W (subset_univ _)
    rw [show univ \ W = Wᶜ from (compl_eq_univ_sdiff W).symm] at this
    tauto
  let e : Finset V ≃ Finset V := ⟨compl, compl, compl_compl, compl_compl⟩
  unfold bernoulliProbability
  conv_lhs => arg 2; rw [← Equiv.sum_comp e]
  rw [← sum_add_distrib]
  refine (sum_congr rfl fun W _ => ?_).trans (sum_bernoulliWeight p)
  simp only [e, Equiv.coe_fn_mk]
  by_cases hG : upHit G W
  · have : ¬ upHit H Wᶜ := fun hh => (hc W).1 hh hG
    simp [hG, this]
  · have : upHit H Wᶜ := (hc W).2 hG
    simp [hG, this, bernoulliWeight_compl]

/-- **Self-transversal hypergraphs are balanced at `p = 1/2`.** -/
theorem bernoulli_self_dual {G : Finset (Finset V)} (h : Dual univ G G) :
    bernoulliProbability (1 / 2 : ℝ) (upHit G) = 1 / 2 := by
  have := bernoulli_dual h (1 / 2)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
  linarith

open HD.Data in
/-- The Fano plane and `K₃`: a random half of the points contains a line with probability
exactly `1/2`. -/
theorem fano_k3_balanced :
    bernoulliProbability (1 / 2 : ℝ) (upHit fanoC) = 1 / 2 ∧
    bernoulliProbability (1 / 2 : ℝ) (upHit k3C) = 1 / 2 :=
  ⟨bernoulli_self_dual (by have := fano_dual; rwa [show fanoD = fanoC by native_decide] at this),
    bernoulli_self_dual (by have := k3_dual; rwa [show k3D = k3C by native_decide] at this)⟩

end HD.OpenAI

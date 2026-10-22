/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Self-transversal hypergraphs (research track A, items A3–A5)

| Lean | Statement |
| --- | --- |
| `TwoColourable` | some partition `(A, U \ A)` has no edge inside either part |
| `tr_eq_self_iff` | **Proposition A3.** For Sperner `H` inside `U`: `Tr(H) = H` iff `H` is intersecting, has no empty edge, and is not 2-colourable |
| `tr_eq_self_iff_needs_sperner` | the Sperner hypothesis of A3 cannot be dropped: `{{0}, {0, 1}}` |
| `intersecting_regular_bound` | **Theorem A4.** intersecting, `r`-uniform, `d`-regular on `t` points: `d(r² − t) ≥ r(r − 1)`, with equality iff distinct edges meet in exactly one point |
-/
import HypergraphDualization.Connections
import Mathlib.Tactic.LinearCombination

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

instance (H : Finset (Finset α)) : Decidable (OpenAI.Intersecting H) := by
  unfold OpenAI.Intersecting; infer_instance

/-- `H` is 2-colourable on `U`: some `A ⊆ U` such that neither `A` nor `U \ A` contains an
edge. -/
def TwoColourable (U : Finset α) (H : Finset (Finset α)) : Prop :=
  ∃ A ⊆ U, ¬ upHit H A ∧ ¬ upHit H (U \ A)

instance (U : Finset α) (H : Finset (Finset α)) : Decidable (TwoColourable U H) :=
  decidable_of_iff (∃ A ∈ U.powerset, ¬ upHit H A ∧ ¬ upHit H (U \ A)) (by simp [TwoColourable])

/-- **Proposition A3.** Let `H` be Sperner with every edge inside `U`. Then `Tr(H) = H` iff
`H` is intersecting, `∅ ∉ H`, and `H` is not 2-colourable on `U`. (Lemma 2.1.1 with `G = H`.) -/
theorem tr_eq_self_iff {U : Finset α} {H : Finset (Finset α)} (hH : Within U H)
    (sH : IsSperner H) :
    tr U H = H ↔ OpenAI.Intersecting H ∧ ∅ ∉ H ∧ ¬ TwoColourable U H := by
  rw [eq_comm, eq_tr_iff_partition hH hH sH sH, dual_iff]
  constructor
  · intro h
    refine ⟨fun e he f hf _ => ?_, fun h0 => ?_, fun ⟨A, hA, h1, h2⟩ => h1 ((h A hA).2 h2)⟩
    · by_contra hef
      refine (h e (hH e he)).1 ⟨e, he, subset_rfl⟩
        ⟨f, hf, fun x hx => mem_sdiff.2 ⟨hH f hf hx, fun hxe => hef ⟨x, mem_inter.2 ⟨hxe, hx⟩⟩⟩⟩
    · exact (h ∅ (empty_subset U)).1 ⟨∅, h0, subset_rfl⟩ ⟨∅, h0, empty_subset _⟩
  · rintro ⟨hI, h0, h2⟩ A hA
    constructor
    · rintro ⟨e, he, heA⟩ ⟨f, hf, hfA⟩
      by_cases hef : e = f
      · subst hef
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 fun h => h0 (h ▸ he)
        exact (mem_sdiff.1 (hfA hx)).2 (heA hx)
      · obtain ⟨x, hx⟩ := hI e he f hf hef
        rw [mem_inter] at hx
        exact (mem_sdiff.1 (hfA hx.2)).2 (heA hx.1)
    · intro hn
      by_contra hA'
      exact h2 ⟨A, hA, hA', hn⟩

/-- The Sperner hypothesis of `tr_eq_self_iff` is needed: `H = {{0}, {0, 1}}` on `Fin 2` is
intersecting, has no empty edge and is not 2-colourable, but `Tr(H) = {{0}} ≠ H`. -/
theorem tr_eq_self_iff_needs_sperner :
    let H : Finset (Finset (Fin 2)) := {{0}, {0, 1}}
    OpenAI.Intersecting H ∧ ∅ ∉ H ∧ ¬ TwoColourable univ H ∧ tr univ H = {{0}} ∧
      tr univ H ≠ H := by
  decide

/-! ### Theorem A4: intersecting regular uniform hypergraphs -/

/-- For an edge `e` of an intersecting, `r`-uniform, `d`-regular `H`:
`r·d = r + Σ_{f ≠ e} |e ∩ f|`, each term at least `1`. -/
theorem regular_sum_inter {U : Finset α} {H : Finset (Finset α)} {r d : ℕ} (hH : Within U H)
    (hr : ∀ e ∈ H, e.card = r) (hd : ∀ v ∈ U, degree H v = d) {e : Finset α} (he : e ∈ H) :
    r * d = r + ∑ f ∈ H.erase e, (e ∩ f).card := by
  have h := sum_card_inter (s := e) (B := H) (n := d) fun a ha => hd a (hH e he ha)
  rw [← add_sum_erase H _ he, inter_self, hr e he] at h
  exact h.symm

/-- **Theorem A4.** Let `H` be a nonempty, intersecting, `r`-uniform (`r > 0`) hypergraph
inside a ground set `U` of `t` points, in which every point of `U` has degree `d`. Then
`d(r² − t) ≥ r(r − 1)`, with equality iff distinct edges meet in exactly one point.

Proof: fix `e ∈ H`. Each of the other `b − 1` edges meets `e`, so
`r(d − 1) = Σ_{x∈e}(deg x − 1) = Σ_{f ≠ e} |e ∩ f| ≥ b − 1`; with `br = td` this is the bound,
and equality forces `|e ∩ f| = 1` for every `f ≠ e`. -/
theorem intersecting_regular_bound {U : Finset α} {H : Finset (Finset α)} {r d : ℕ}
    (hH : Within U H) (hne : H.Nonempty) (hI : OpenAI.Intersecting H) (r0 : 0 < r)
    (hr : ∀ e ∈ H, e.card = r) (hd : ∀ v ∈ U, degree H v = d) :
    (r * (r - 1) : ℤ) ≤ d * (r ^ 2 - U.card) ∧
      ((r * (r - 1) : ℤ) = d * (r ^ 2 - U.card) ↔
        ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card = 1) := by
  -- `b·r = t·d`: count incidences of `U`.
  have hbt : H.card * r = U.card * d := by
    have h := sum_card_inter (s := U) (B := H) (n := d) hd
    rw [sum_congr rfl fun f hf => by rw [inter_eq_right.2 (hH f hf), hr f hf], sum_const,
      smul_eq_mul] at h
    exact h
  -- for each edge, the excess `Σ_{f ≠ e} (|e ∩ f| − 1)` is `r·d − r − b + 1`.
  have key : ∀ e ∈ H, (d * (r ^ 2 - U.card) - r * (r - 1) : ℤ) =
      r * ((∑ f ∈ H.erase e, (e ∩ f).card : ℕ) - (H.erase e).card) := by
    intro e he
    have e1 := regular_sum_inter hH hr hd he
    have e2 : ((H.erase e).card : ℤ) + 1 = H.card := by exact_mod_cast card_erase_add_one he
    have e1' : (r * d : ℤ) = r + (∑ f ∈ H.erase e, (e ∩ f).card : ℕ) := by exact_mod_cast e1
    have hbt' : (H.card * r : ℤ) = U.card * d := by exact_mod_cast hbt
    linear_combination (r : ℤ) * e1' + hbt' + (r : ℤ) * e2
  have one_le : ∀ e ∈ H, ∀ f ∈ H.erase e, 1 ≤ (e ∩ f).card := fun e he f hf =>
    card_pos.2 (hI e he f (mem_of_mem_erase hf) (ne_of_mem_erase hf).symm)
  have ge : ∀ e ∈ H, (H.erase e).card ≤ ∑ f ∈ H.erase e, (e ∩ f).card := fun e he => by
    simpa using sum_le_sum (one_le e he)
  obtain ⟨e, he⟩ := hne
  refine ⟨?_, ⟨fun heq e he f hf hef => ?_, fun h1 => ?_⟩⟩
  · have := key e he
    have : (0 : ℤ) ≤ r * ((∑ f ∈ H.erase e, (e ∩ f).card : ℕ) - (H.erase e).card) :=
      mul_nonneg (by positivity) (sub_nonneg.2 (by exact_mod_cast ge e he))
    linarith
  · have h0 := key e he
    rw [heq, sub_self, eq_comm, mul_eq_zero, sub_eq_zero] at h0
    have hs : ∑ f ∈ H.erase e, (e ∩ f).card = ∑ f ∈ H.erase e, 1 := by
      rcases h0 with h0 | h0
      · omega
      · simpa using (Nat.cast_inj.1 h0)
    have := (sum_eq_sum_iff_of_le (one_le e he)).1 hs.symm f (mem_erase.2 ⟨hef.symm, hf⟩)
    exact this.symm
  · have h0 := key e he
    rw [sum_congr rfl fun f hf => h1 e he f (mem_of_mem_erase hf) (ne_of_mem_erase hf).symm]
      at h0
    simp at h0
    linarith

end HD

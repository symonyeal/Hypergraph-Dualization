/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Blocker duality

The transversal hypergraph is the CNF of the function whose DNF is `H` (§1.1.2):
a set meets every minimal transversal exactly when it contains an edge. Everything in
Chapter 2.1 follows from this one equivalence.

| Lean | Thesis |
| --- | --- |
| `hits_tr_iff` | §1.1.2: `Tr(H)` is the CNF of the function whose DNF is `H` |
| `tr_tr` | Cor. 2.1.3, for every hypergraph: `Tr(Tr(H)) = min(H)` |
| `tr_tr_of_sperner` | Cor. 2.1.3 as stated |
| `eq_tr_comm` | Cor. 2.1.2 |
| `eq_tr_iff_partition` | Lemma 2.1.1 |
| `Dual` | the `DUAL` predicate of Problem 2.1.5 on edge families |
| `isMinHit_compl_iff` | §1.1.1: `Iᶜ` is a minimal transversal iff `I` is a maximal independent set |
-/
import HypergraphDualization.Basic

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-- A set meets every minimal transversal of `H` iff it contains an edge of `H`. -/
theorem hits_tr_iff {U : Finset α} {H : Finset (Finset α)} (hH : Within U H) (S : Finset α) :
    Hits (tr U H) S ↔ upHit H S := by
  constructor
  · intro hS
    by_contra hno
    -- `U \ S` meets every edge, since no edge fits inside `S`.
    have hcomp : Hits H (U \ S) := by
      intro e he
      have : ¬ e ⊆ S := fun hes => hno ⟨e, he, hes⟩
      obtain ⟨x, hxe, hxS⟩ := not_subset.1 this
      exact ⟨x, mem_inter.2 ⟨mem_sdiff.2 ⟨hH e he hxe, hxS⟩, hxe⟩⟩
    obtain ⟨T, hTsub, hT⟩ := exists_isMinHit_subset _ (U \ S) rfl hcomp
    have hTtr : T ∈ tr U H := mem_tr.2 ⟨hTsub.trans sdiff_subset, hT⟩
    obtain ⟨x, hx⟩ := hS T hTtr
    rw [mem_inter] at hx
    exact (mem_sdiff.1 (hTsub hx.2)).2 hx.1
  · rintro ⟨e, he, heS⟩ T hT
    obtain ⟨x, hx⟩ := (mem_tr.1 hT).2.1 e he
    rw [mem_inter] at hx
    exact ⟨x, mem_inter.2 ⟨heS hx.2, hx.1⟩⟩

/-- **Corollary 2.1.3**, for an arbitrary hypergraph: `Tr(Tr(H)) = min(H)`. -/
theorem tr_tr {U : Finset α} {H : Finset (Finset α)} (hH : Within U H) :
    tr U (tr U H) = minimal H := by
  ext T
  simp only [mem_tr, IsMinHit, hits_tr_iff hH, minimal, mem_filter, upHit]
  constructor
  · rintro ⟨hTU, ⟨e, he, heT⟩, hmin⟩
    have hTe : e = T := by
      by_contra hne
      obtain ⟨v, hvT, hve⟩ := exists_of_ssubset (_root_.ssubset_iff_subset_ne.2 ⟨heT, hne⟩)
      exact hmin v hvT ⟨e, he, fun x hx => mem_erase.2 ⟨fun h => hve (h ▸ hx), heT hx⟩⟩
    subst hTe
    refine ⟨he, fun f hf hfe => ?_⟩
    by_contra hne
    obtain ⟨v, hvT, hvf⟩ := exists_of_ssubset (_root_.ssubset_iff_subset_ne.2 ⟨hfe, hne⟩)
    exact hmin v hvT ⟨f, hf, fun x hx => mem_erase.2 ⟨fun h => hvf (h ▸ hx), hfe hx⟩⟩
  · rintro ⟨he, hmin⟩
    refine ⟨hH T he, ⟨T, he, subset_rfl⟩, fun v hv ⟨f, hf, hfT⟩ => ?_⟩
    have hfeq := hmin f hf (hfT.trans (erase_subset v T))
    rw [hfeq] at hfT
    exact notMem_erase v T (hfT hv)

/-- **Corollary 2.1.3.** For a Sperner hypergraph, `Tr(Tr(H)) = H`. -/
theorem tr_tr_of_sperner {U : Finset α} {H : Finset (Finset α)} (hH : Within U H)
    (hS : IsSperner H) : tr U (tr U H) = H := by
  rw [tr_tr hH, minimal_eq_self hS]

/-- **Corollary 2.1.2.** For Sperner `G`, `H` inside `U`: `H = Tr(G)` iff `G = Tr(H)`. -/
theorem eq_tr_comm {U : Finset α} {G H : Finset (Finset α)} (hG : Within U G) (hH : Within U H)
    (sG : IsSperner G) (sH : IsSperner H) : H = tr U G ↔ G = tr U H := by
  constructor
  · rintro rfl; exact (tr_tr_of_sperner hG sG).symm
  · rintro rfl; exact (tr_tr_of_sperner hH sH).symm

/-- Two Sperner families with the same up-sets on `U` are equal. -/
theorem eq_of_upHit_iff {U : Finset α} {F H : Finset (Finset α)} (hF : Within U F)
    (hH : Within U H) (sF : IsSperner F) (sH : IsSperner H)
    (h : ∀ A ⊆ U, upHit F A ↔ upHit H A) : F = H := by
  have key : ∀ {X Y : Finset (Finset α)}, Within U X → IsSperner X → IsSperner Y →
      (∀ A ⊆ U, upHit X A ↔ upHit Y A) → X ⊆ Y := by
    intro X Y hX sX sY hXY e he
    obtain ⟨f, hf, hfe⟩ := (hXY e (hX e he)).1 ⟨e, he, subset_rfl⟩
    have hfU : f ⊆ U := hfe.trans (hX e he)
    obtain ⟨g, hg, hgf⟩ := (hXY f hfU).2 ⟨f, hf, subset_rfl⟩
    have hge : g = e := sX g hg e he (hgf.trans hfe)
    subst hge
    have : f = g := le_antisymm hfe hgf
    exact this ▸ hf
  exact Subset.antisymm (key hF sF sH h) (key hH sH sF fun A hA => (h A hA).symm)

/-- `G` and `H` are dual on `U`: for every `A ⊆ U`, exactly one of `A ⊇ e ∈ G` and
`U \ A ⊇ f ∈ H` holds. This is Problem 2.1.5 (`DUAL`) on edge families. -/
def Dual (U : Finset α) (G H : Finset (Finset α)) : Prop :=
  ∀ A ∈ U.powerset, (upHit G A ↔ ¬ upHit H (U \ A))

instance (U : Finset α) (G H : Finset (Finset α)) : Decidable (Dual U G H) := by
  unfold Dual; infer_instance

theorem dual_iff {U : Finset α} {G H : Finset (Finset α)} :
    Dual U G H ↔ ∀ A ⊆ U, (upHit G A ↔ ¬ upHit H (U \ A)) := by
  simp [Dual]

/-- `Tr(H)` meets `U \ A` exactly when `A` contains no minimal transversal. -/
theorem upHit_sdiff_iff {U : Finset α} {G : Finset (Finset α)} (hG : Within U G) {A : Finset α}
    (hA : A ⊆ U) : upHit G (U \ A) ↔ ¬ upHit (tr U G) A := by
  rw [← hits_tr_iff hG]
  constructor
  · rintro h ⟨t, ht, htA⟩
    obtain ⟨x, hx⟩ := h t ht
    rw [mem_inter] at hx
    exact (mem_sdiff.1 hx.1).2 (htA hx.2)
  · intro h t ht
    by_contra hne
    apply h
    refine ⟨t, ht, fun x hx => ?_⟩
    by_contra hxA
    exact hne ⟨x, mem_inter.2 ⟨mem_sdiff.2 ⟨(mem_tr.1 ht).1 hx, hxA⟩, hx⟩⟩

/-- **Lemma 2.1.1.** For Sperner `G`, `H` inside `U`: `H = Tr(G)` iff for every partition
`(A, U \ A)` exactly one of "`A` contains an edge of `H`" and "`U \ A` contains an edge of
`G`" holds. -/
theorem eq_tr_iff_partition {U : Finset α} {G H : Finset (Finset α)} (hG : Within U G)
    (hH : Within U H) (sG : IsSperner G) (sH : IsSperner H) :
    H = tr U G ↔ Dual U H G := by
  rw [dual_iff]
  constructor
  · rintro rfl A hA
    rw [upHit_sdiff_iff hG hA, not_not]
  · intro h
    refine eq_of_upHit_iff hH (tr_within U G) sH (tr_isSperner U G) fun A hA => ?_
    rw [h A hA, upHit_sdiff_iff hG hA, not_not]

/-- Duality on `U` is symmetric. -/
theorem dual_comm {U : Finset α} {G H : Finset (Finset α)} : Dual U G H ↔ Dual U H G := by
  rw [dual_iff, dual_iff]
  constructor <;> intro h A hA
  all_goals
    have := h (U \ A) sdiff_subset
    rw [Finset.sdiff_sdiff_eq_self hA] at this
    tauto

/-- Duality depends only on the minimal edges. -/
theorem dual_minimal {U : Finset α} {G H : Finset (Finset α)} :
    Dual U (minimal G) (minimal H) ↔ Dual U G H := by
  simp only [Dual, upHit_minimal]

/-- On `U`, a family is dual to `Tr` of the other exactly when it has the same minimal edges.
This is the predicate FK-A decides. -/
theorem dual_iff_minimal_eq_tr {U : Finset α} {G H : Finset (Finset α)} (hG : Within U G)
    (hH : Within U H) : Dual U G H ↔ minimal G = tr U H := by
  rw [← dual_minimal (G := G) (H := H),
    ← eq_tr_iff_partition (fun e he => hH e (minimal_subset H he))
      (fun e he => hG e (minimal_subset G he)) (minimal_isSperner H) (minimal_isSperner G),
    tr_minimal]

/-! ### Independent sets (§1.1.1) -/

/-- `I` is independent in `H`: it contains no edge. -/
def IsIndep (H : Finset (Finset α)) (I : Finset α) : Prop := ¬ upHit H I

/-- §1.1.1: inside `U`, the complement of an independent set is a transversal, and
`U \ I` is a minimal transversal iff `I` is a maximal independent subset of `U`. -/
theorem hits_compl_iff {U : Finset α} {H : Finset (Finset α)} (hH : Within U H) {I : Finset α} :
    Hits H (U \ I) ↔ IsIndep H I := by
  constructor
  · rintro h ⟨e, he, heI⟩
    obtain ⟨x, hx⟩ := h e he
    rw [mem_inter, mem_sdiff] at hx
    exact hx.1.2 (heI hx.2)
  · intro h e he
    have : ¬ e ⊆ I := fun heI => h ⟨e, he, heI⟩
    obtain ⟨x, hxe, hxI⟩ := not_subset.1 this
    exact ⟨x, mem_inter.2 ⟨mem_sdiff.2 ⟨hH e he hxe, hxI⟩, hxe⟩⟩

theorem isMinHit_compl_iff {U : Finset α} {H : Finset (Finset α)} (hH : Within U H)
    {I : Finset α} (hI : I ⊆ U) :
    IsMinHit H (U \ I) ↔ IsIndep H I ∧ ∀ v ∈ U \ I, ¬ IsIndep H (insert v I) := by
  unfold IsMinHit
  rw [hits_compl_iff hH]
  refine and_congr_right fun _ => forall₂_congr fun v hv => ?_
  have : (U \ I).erase v = U \ insert v I := by
    ext x; simp only [mem_erase, mem_sdiff, mem_insert]; tauto
  rw [this, hits_compl_iff hH]

end HD

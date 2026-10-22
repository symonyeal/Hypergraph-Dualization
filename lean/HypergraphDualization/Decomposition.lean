/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The FK-A decomposition

For a vertex `x`, write `G₁ = del G x` (the edges avoiding `x`, Def. 2.2.6) and
`G₀ ∨ G₁ = con G x` (every edge with `x` removed, Def. 2.2.5). Algorithm 1 recurses on
`L = (G₁, H₀ ∨ H₁)` and `R = (H₁, G₀ ∨ G₁)`.

| Lean | Thesis |
| --- | --- |
| `del`, `con` | Defs. 2.2.6, 2.2.5; `G₁` and `G₀ ∨ G₁` of §2.2.2 |
| `dual_split` | §2.2.2: `(G, H)` is dual iff both `L` and `R` are |
| `dual_erase_of_notMem` | a vertex outside both supports does not affect duality |
| `tr_singleton` | §5.1.1, the `D₁,ₖ` rule: `Tr({e})` is the singletons of `e` |
-/
import HypergraphDualization.Conditions

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-- The edges of `H` avoiding `x`: `H₁`, the deletion subhypergraph `H \ x`. -/
def del (H : Finset (Finset α)) (x : α) : Finset (Finset α) := H.filter (x ∉ ·)

/-- Every edge of `H` with `x` removed: `H₀ ∨ H₁`, the contraction `H / x`. -/
def con (H : Finset (Finset α)) (x : α) : Finset (Finset α) := H.image (·.erase x)

theorem del_within {U : Finset α} {H : Finset (Finset α)} (hH : Within U H) (x : α) :
    Within (U.erase x) (del H x) := by
  intro e he
  rw [del, mem_filter] at he
  intro y hy
  exact mem_erase.2 ⟨fun h => he.2 (h ▸ hy), hH e he.1 hy⟩

theorem con_within {U : Finset α} {H : Finset (Finset α)} (hH : Within U H) (x : α) :
    Within (U.erase x) (con H x) := by
  intro e he
  rw [con, mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact erase_subset_erase x (hH f hf)

/-- `S` contains an edge of `H − x` iff `S − x` contains an edge of `H`: `(f|x=0)(S) = f(S − x)`. -/
theorem upHit_del {H : Finset (Finset α)} {x : α} {S : Finset α} :
    upHit (del H x) S ↔ upHit H (S.erase x) := by
  simp only [upHit, del, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hx⟩, heS⟩
    exact ⟨e, he, fun y hy => mem_erase.2 ⟨fun h => hx (h ▸ hy), heS hy⟩⟩
  · rintro ⟨e, he, heS⟩
    exact ⟨e, ⟨he, fun hx => (notMem_erase x S) (heS hx)⟩, heS.trans (erase_subset x S)⟩

/-- `S` contains an edge of `H / x` iff `S + x` contains an edge of `H`: `(f|x=1)(S) = f(S + x)`. -/
theorem upHit_con {H : Finset (Finset α)} {x : α} {S : Finset α} :
    upHit (con H x) S ↔ upHit H (insert x S) := by
  simp only [upHit, con, mem_image]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, heS⟩
    exact ⟨e, he, fun y hy => by
      by_cases h : y = x
      · exact h ▸ mem_insert_self x S
      · exact mem_insert_of_mem (heS (mem_erase.2 ⟨h, hy⟩))⟩
  · rintro ⟨e, he, heS⟩
    exact ⟨e.erase x, ⟨e, he, rfl⟩, fun y hy => by
      obtain ⟨hyx, hy⟩ := mem_erase.1 hy
      exact (mem_insert.1 (heS hy)).resolve_left hyx⟩

/-- **The FK-A decomposition (§2.2.2).** For `x ∈ U`, `(G, H)` is dual on `U` iff
`L = (del G x, con H x)` and `R = (del H x, con G x)` are dual on `U \ {x}`. -/
theorem dual_split {U : Finset α} {G H : Finset (Finset α)} {x : α} (hx : x ∈ U) :
    Dual U G H ↔ Dual (U.erase x) (del G x) (con H x) ∧ Dual (U.erase x) (del H x) (con G x) := by
  simp only [dual_iff]
  -- `U \ A` for `A ⊆ U \ {x}` contains `x`; removing it gives `(U \ {x}) \ A`.
  have key : ∀ A ⊆ U.erase x, (U \ A).erase x = U.erase x \ A := by
    intro A _; ext y; simp only [mem_erase, mem_sdiff]; tauto
  have hxA : ∀ A ⊆ U.erase x, x ∉ A := fun A hA hxA => (mem_erase.1 (hA hxA)).1 rfl
  have hxUA : ∀ A ⊆ U.erase x, x ∈ U \ A := fun A hA => mem_sdiff.2 ⟨hx, hxA A hA⟩
  constructor
  · intro h
    refine ⟨fun A hA => ?_, fun A hA => ?_⟩
    · -- `L`: a set without `x`.
      have hAU : A ⊆ U := hA.trans (erase_subset x U)
      rw [upHit_del, erase_eq_of_notMem (hxA A hA), ← key A hA, upHit_con,
        insert_erase (hxUA A hA)]
      exact h A hAU
    · -- `R`: the complement of a set containing `x`.
      have hAU : A ⊆ U := hA.trans (erase_subset x U)
      rw [upHit_del, erase_eq_of_notMem (hxA A hA), ← key A hA, upHit_con, insert_erase (hxUA A hA)]
      have := h (U \ A) sdiff_subset
      rw [Finset.sdiff_sdiff_eq_self hAU] at this
      tauto
  · rintro ⟨hL, hR⟩ A hA
    by_cases hxA' : x ∈ A
    · -- `B = U \ A` avoids `x`; read off `R` at `B`.
      have hB : U \ A ⊆ U.erase x := fun y hy =>
        mem_erase.2 ⟨fun h => (mem_sdiff.1 hy).2 (h ▸ hxA'), (mem_sdiff.1 hy).1⟩
      have := hR (U \ A) hB
      rw [upHit_del, erase_eq_of_notMem (hxA _ hB), ← key _ hB, upHit_con, insert_erase (hxUA _ hB),
        Finset.sdiff_sdiff_eq_self hA] at this
      tauto
    · have hA' : A ⊆ U.erase x := fun y hy =>
        mem_erase.2 ⟨fun h => hxA' (h ▸ hy), hA hy⟩
      have := hL A hA'
      rwa [upHit_del, erase_eq_of_notMem hxA', ← key A hA', upHit_con, insert_erase (hxUA A hA')] at this

/-- Removing from the ground set a vertex in no edge does not change duality. -/
theorem dual_erase_of_notMem {U : Finset α} {G H : Finset (Finset α)} {x : α}
    (hxG : ∀ e ∈ G, x ∉ e) (hxH : ∀ e ∈ H, x ∉ e) :
    Dual (U.erase x) G H ↔ Dual U G H := by
  simp only [dual_iff]
  have upG : ∀ A, upHit G (A.erase x) ↔ upHit G A := fun A =>
    ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.trans (erase_subset x A)⟩,
     fun ⟨e, he, h⟩ => ⟨e, he, fun y hy => mem_erase.2 ⟨fun hyx => hxG e he (hyx ▸ hy), h hy⟩⟩⟩
  have upH : ∀ A, upHit H (A.erase x) ↔ upHit H A := fun A =>
    ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.trans (erase_subset x A)⟩,
     fun ⟨e, he, h⟩ => ⟨e, he, fun y hy => mem_erase.2 ⟨fun hyx => hxH e he (hyx ▸ hy), h hy⟩⟩⟩
  constructor
  · intro h A hA
    have hA' : A.erase x ⊆ U.erase x := erase_subset_erase x hA
    have := h (A.erase x) hA'
    rw [upG, show U.erase x \ A.erase x = (U \ A).erase x by
      ext y; simp only [mem_erase, mem_sdiff]; tauto, upH] at this
    exact this
  · intro h A hA
    have hAU : A ⊆ U := hA.trans (erase_subset x U)
    have := h A hAU
    rw [← upH (U \ A), show (U \ A).erase x = U.erase x \ A by
      ext y; simp only [mem_erase, mem_sdiff]; tauto] at this
    exact this

/-- `Tr({e}) = {{v} : v ∈ e}`: the single-edge rule of §5.1.1. -/
theorem tr_singleton {U e : Finset α} (he : e ⊆ U) : tr U {e} = e.image ({·}) := by
  ext T
  simp only [mem_tr, IsMinHit, Hits, mem_singleton, forall_eq, mem_image]
  constructor
  · rintro ⟨hTU, ⟨v, hv⟩, hmin⟩
    rw [mem_inter] at hv
    refine ⟨v, hv.2, ?_⟩
    by_contra hne
    have : ∃ w ∈ T, w ≠ v := by
      by_contra hall; push Not at hall
      exact hne (eq_singleton_iff_unique_mem.2 ⟨hv.1, hall⟩).symm
    obtain ⟨w, hwT, hwv⟩ := this
    exact hmin w hwT ⟨v, mem_inter.2 ⟨mem_erase.2 ⟨hwv.symm, hv.1⟩, hv.2⟩⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨singleton_subset_iff.2 (he hv), ⟨v, by simp [hv]⟩, fun w hw ⟨y, hy⟩ => ?_⟩
    rw [mem_singleton] at hw; subst hw
    simp at hy

end HD

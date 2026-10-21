/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Automorphisms of hypergraphs (Chapter 3)

`aut H` is the subgroup of `Equiv.Perm α` mapping the edge family onto itself
(Def. 3.1.3). The ground set is all of `α` (`Fintype α`, `U = univ`).

| Lean | Thesis |
| --- | --- |
| `tr_equivariant` | `Tr` commutes with relabelling |
| `aut_tr_eq_aut_minimal` | Lemma 3.3.1, general form: `Aut(Tr H) = Aut(min H)` |
| `aut_tr_of_sperner` | Lemma 3.3.1 **corrected**: `Aut(Tr H) = Aut(H)` for Sperner `H` |
| `aut_le_aut_minimal` | Cor. 3.3.4 **corrected**: `Aut(H) ≤ Aut(min H)` (equality fails) |
| `stab_mem_aut_del`, `stab_mem_aut_con` | replace Lemmas 3.3.2-3.3.3: automorphisms fixing the split vertex survive in both FK-A children |
| `invariant_iff_orbits`, `orbit_minimal` | Claim 3.1.6 **corrected**: invariant sets are unions of orbits; orbits are the minimal ones |
| `degree_eq_of_transitive` | a transitive `Aut` makes every vertex equally frequent (§5.2.2, Fano) |
-/
import HypergraphDualization.Duality

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-- `σ(e)`. -/
def pmap (σ : Equiv.Perm α) (e : Finset α) : Finset α := e.map σ.toEmbedding

/-- `σ(H)`: every edge relabelled. -/
def pimg (σ : Equiv.Perm α) (H : Finset (Finset α)) : Finset (Finset α) := H.image (pmap σ)

@[simp] theorem mem_pmap {σ : Equiv.Perm α} {e : Finset α} {v : α} :
    v ∈ pmap σ e ↔ σ.symm v ∈ e := by
  simp only [pmap, mem_map_equiv]

theorem pmap_injective (σ : Equiv.Perm α) : Function.Injective (pmap σ) :=
  map_injective σ.toEmbedding

theorem pmap_mul (σ τ : Equiv.Perm α) (e : Finset α) : pmap (σ * τ) e = pmap σ (pmap τ e) := by
  ext v; simp [mem_pmap, Equiv.Perm.mul_def]

theorem pmap_one (e : Finset α) : pmap 1 e = e := by ext v; rw [mem_pmap]; exact Iff.rfl

theorem pmap_inter (σ : Equiv.Perm α) (a b : Finset α) :
    pmap σ (a ∩ b) = pmap σ a ∩ pmap σ b := by ext v; simp

theorem pmap_erase (σ : Equiv.Perm α) (e : Finset α) (v : α) :
    pmap σ (e.erase v) = (pmap σ e).erase (σ v) := by
  ext w; simp only [mem_pmap, mem_erase]
  constructor
  · rintro ⟨hne, h⟩; exact ⟨fun hw => hne (by rw [hw]; simp), h⟩
  · rintro ⟨hne, h⟩; exact ⟨fun hw => hne (by rw [← hw]; simp), h⟩

theorem pmap_subset_iff (σ : Equiv.Perm α) {a b : Finset α} : pmap σ a ⊆ pmap σ b ↔ a ⊆ b :=
  map_subset_map

theorem pmap_nonempty (σ : Equiv.Perm α) {a : Finset α} : (pmap σ a).Nonempty ↔ a.Nonempty :=
  map_nonempty

theorem pimg_mul (σ τ : Equiv.Perm α) (H : Finset (Finset α)) :
    pimg (σ * τ) H = pimg σ (pimg τ H) := by
  simp only [pimg, image_image]; congr 1; funext e; exact pmap_mul σ τ e

theorem pimg_one (H : Finset (Finset α)) : pimg 1 H = H := by
  have h1 : pmap (1 : Equiv.Perm α) = id := funext pmap_one
  rw [pimg, h1, image_id]

theorem pimg_inv_pimg (σ : Equiv.Perm α) (H : Finset (Finset α)) : pimg σ⁻¹ (pimg σ H) = H := by
  rw [← pimg_mul, inv_mul_cancel, pimg_one]

theorem mem_pimg {σ : Equiv.Perm α} {H : Finset (Finset α)} {e : Finset α} :
    pmap σ e ∈ pimg σ H ↔ e ∈ H :=
  ⟨fun h => by obtain ⟨f, hf, hfe⟩ := mem_image.1 h; rwa [← pmap_injective σ hfe], fun h =>
    mem_image_of_mem _ h⟩

/-- The automorphism group of `H` (Def. 3.1.3). -/
def aut (H : Finset (Finset α)) : Subgroup (Equiv.Perm α) where
  carrier := {σ | pimg σ H = H}
  one_mem' := pimg_one H
  mul_mem' := by
    intro σ τ hσ hτ
    show pimg (σ * τ) H = H
    rw [pimg_mul, show pimg τ H = H from hτ, show pimg σ H = H from hσ]
  inv_mem' := by
    intro σ hσ
    show pimg σ⁻¹ H = H
    have h : pimg σ H = H := hσ
    calc pimg σ⁻¹ H = pimg σ⁻¹ (pimg σ H) := by rw [h]
      _ = H := pimg_inv_pimg σ H

theorem mem_aut {H : Finset (Finset α)} {σ : Equiv.Perm α} : σ ∈ aut H ↔ pimg σ H = H :=
  Iff.rfl

instance (H : Finset (Finset α)) : DecidablePred (· ∈ aut H) := fun σ =>
  decidable_of_iff (pimg σ H = H) mem_aut.symm

/-- An inclusion `pimg σ H ⊆ H` already makes `σ` an automorphism. -/
theorem mem_aut_of_subset {H : Finset (Finset α)} {σ : Equiv.Perm α} (h : pimg σ H ⊆ H) :
    σ ∈ aut H :=
  eq_of_subset_of_card_le h (by rw [pimg, card_image_of_injective _ (pmap_injective σ)])

section Fintype

variable [Fintype α]

theorem hits_pmap {σ : Equiv.Perm α} {H : Finset (Finset α)} {T : Finset α} :
    Hits (pimg σ H) (pmap σ T) ↔ Hits H T := by
  constructor
  · intro h e he
    have := h (pmap σ e) (mem_image_of_mem _ he)
    rwa [← pmap_inter, pmap_nonempty] at this
  · intro h e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    rw [← pmap_inter, pmap_nonempty]; exact h e he

theorem pimg_tr_subset (σ : Equiv.Perm α) (H : Finset (Finset α)) :
    pimg σ (tr univ H) ⊆ tr univ (pimg σ H) := by
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hT'
  have hmin := (mem_tr.1 hT).2
  refine mem_tr.2 ⟨subset_univ _, hits_pmap.2 hmin.1, fun w hw hhit => ?_⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v ∈ T, σ v = w := ⟨σ.symm w, (mem_pmap.1 hw), by simp⟩
  rw [← pmap_erase, hits_pmap] at hhit
  exact hmin.2 v hv hhit

/-- `Tr(σ(H)) = σ(Tr(H))`. -/
theorem tr_equivariant (σ : Equiv.Perm α) (H : Finset (Finset α)) :
    tr univ (pimg σ H) = pimg σ (tr univ H) := by
  refine Subset.antisymm ?_ (pimg_tr_subset σ H)
  have := pimg_tr_subset σ⁻¹ (pimg σ H)
  rw [pimg_inv_pimg] at this
  intro T hT
  have h2 := mem_image_of_mem (pmap σ) (this (mem_image_of_mem (pmap σ⁻¹) hT))
  rwa [← pmap_mul, mul_inv_cancel, pmap_one] at h2

/-- Every automorphism of `H` is an automorphism of `Tr(H)`. -/
theorem aut_le_aut_tr (H : Finset (Finset α)) : aut H ≤ aut (tr univ H) := by
  intro σ hσ
  rw [mem_aut] at hσ ⊢
  rw [← tr_equivariant, hσ]

/-- **Corollary 3.3.4, corrected.** Every automorphism of `H` is one of `min(H)`. -/
theorem aut_le_aut_minimal (H : Finset (Finset α)) : aut H ≤ aut (minimal H) := by
  intro σ hσ
  refine mem_aut_of_subset fun e' he' => ?_
  obtain ⟨e, he, rfl⟩ := mem_image.1 he'
  rw [mem_minimal] at he ⊢
  rw [mem_aut] at hσ
  refine ⟨hσ ▸ mem_image_of_mem _ he.1, fun f' hf' hsub => ?_⟩
  rw [← hσ] at hf'
  obtain ⟨f, hf, rfl⟩ := mem_image.1 hf'
  rw [pmap_subset_iff] at hsub
  rw [he.2 f hf hsub]

/-- **Lemma 3.3.1, general form.** `Aut(Tr(H)) = Aut(min(H))`. -/
theorem aut_tr_eq_aut_minimal (H : Finset (Finset α)) : aut (tr univ H) = aut (minimal H) := by
  apply le_antisymm
  · have := aut_le_aut_tr (tr univ H)
    rwa [tr_tr (fun _ _ => subset_univ _)] at this
  · have := aut_le_aut_tr (minimal H)
    rwa [tr_minimal] at this

/-- **Lemma 3.3.1, corrected.** For a Sperner hypergraph, `Aut(Tr(H)) = Aut(H)`. -/
theorem aut_tr_of_sperner {H : Finset (Finset α)} (h : IsSperner H) :
    aut (tr univ H) = aut H := by
  rw [aut_tr_eq_aut_minimal, minimal_eq_self h]

end Fintype

/-! ### Automorphisms fixing the split vertex (replacing Lemmas 3.3.2-3.3.3) -/

theorem stab_mem_aut_del {G : Finset (Finset α)} {σ : Equiv.Perm α} (hσ : σ ∈ aut G) {x : α}
    (hx : σ x = x) : σ ∈ aut (G.filter (x ∉ ·)) := by
  refine mem_aut_of_subset fun e' he' => ?_
  obtain ⟨e, he, rfl⟩ := mem_image.1 he'
  rw [mem_filter] at he ⊢
  refine ⟨(mem_aut.1 hσ) ▸ mem_image_of_mem _ he.1, fun hxe => he.2 ?_⟩
  rwa [mem_pmap, (Equiv.symm_apply_eq σ).2 hx.symm] at hxe

theorem stab_mem_aut_con {G : Finset (Finset α)} {σ : Equiv.Perm α} (hσ : σ ∈ aut G) {x : α}
    (hx : σ x = x) : σ ∈ aut (G.image (·.erase x)) := by
  refine mem_aut_of_subset fun e' he' => ?_
  obtain ⟨e, he, rfl⟩ := mem_image.1 he'
  obtain ⟨f, hf, rfl⟩ := mem_image.1 he
  refine mem_image.2 ⟨pmap σ f, (mem_aut.1 hσ) ▸ mem_image_of_mem _ hf, ?_⟩
  rw [pmap_erase, hx]

/-! ### Orbits (Claim 3.1.6) -/

section Orbits

variable (Γ : Subgroup (Equiv.Perm α))

/-- A set is `Γ`-invariant iff it contains the orbit of each of its points. -/
theorem invariant_iff_orbits (S : Set α) :
    (∀ g ∈ Γ, ∀ v ∈ S, g v ∈ S) ↔ ∀ v ∈ S, ∀ g ∈ Γ, g v ∈ S :=
  ⟨fun h v hv g hg => h g hg v hv, fun h g hg v hv => h v hv g hg⟩

/-- The orbit `{g v : g ∈ Γ}`. -/
def orbitOf (v : α) : Set α := {w | ∃ g ∈ Γ, g v = w}

theorem orbit_invariant (v : α) : ∀ g ∈ Γ, ∀ w ∈ orbitOf Γ v, g w ∈ orbitOf Γ v := by
  rintro g hg w ⟨h, hh, rfl⟩
  exact ⟨g * h, Γ.mul_mem hg hh, rfl⟩

/-- **Claim 3.1.6, corrected.** An invariant set is the union of the orbits of its points. -/
theorem invariant_eq_union_orbits {S : Set α} (hS : ∀ g ∈ Γ, ∀ v ∈ S, g v ∈ S) :
    S = ⋃ v ∈ S, orbitOf Γ v := by
  ext w
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hw; exact ⟨w, hw, 1, Γ.one_mem, rfl⟩
  · rintro ⟨v, hv, g, hg, rfl⟩; exact hS g hg v hv

/-- Orbits are the minimal nonempty invariant sets. -/
theorem orbit_minimal {S : Set α} (v : α) (hS : ∀ g ∈ Γ, ∀ w ∈ S, g w ∈ S) (hsub : S ⊆ orbitOf Γ v)
    (hne : S.Nonempty) : S = orbitOf Γ v := by
  refine Set.Subset.antisymm hsub ?_
  obtain ⟨u, hu⟩ := hne
  obtain ⟨g, hg, rfl⟩ := hsub hu
  rintro w ⟨h, hh, rfl⟩
  have := hS (h * g⁻¹) (Γ.mul_mem hh (Γ.inv_mem hg)) _ hu
  simpa [Equiv.Perm.mul_apply] using this

end Orbits

/-! ### Transitivity and frequency -/

theorem degree_pimg (σ : Equiv.Perm α) (H : Finset (Finset α)) (v : α) :
    degree (pimg σ H) (σ v) = degree H v := by
  unfold degree pimg
  rw [filter_image]
  rw [card_image_of_injective _ (pmap_injective σ)]
  congr 1
  ext e; simp [mem_pmap]

/-- If `Aut(H)` moves `u` to `v`, the two vertices have the same degree; under a transitive
automorphism group every vertex has the same frequency. -/
theorem degree_eq_of_transitive {H : Finset (Finset α)} {u v : α} {σ : Equiv.Perm α}
    (hσ : σ ∈ aut H) (huv : σ u = v) : degree H u = degree H v := by
  rw [← huv, ← degree_pimg σ H u, mem_aut.1 hσ]

end HD

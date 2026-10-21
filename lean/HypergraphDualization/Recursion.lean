/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Symmetry and the primal graph under one FK-A step (§3.3-3.4, §5.2.2)

| Lean | Thesis |
| --- | --- |
| `aut_child_moves_split_to_isolated` | Lemma 3.3.2 **corrected**: in either child an automorphism can move the split vertex only to a vertex lying in no edge |
| `lemma_3_3_3_false` | Lemma 3.3.3 **refuted**: a transposition of a generator need not survive |
| `primalAdj_del`, `primalAdj_con`, `primalAdj_minimal` | Observation 3.4.5 **made precise**: each child's primal graph is a subgraph of `G(H) - v` |
| `falseTwin_filtered` | Observation 5.2.2: a false twin of the split vertex leaves the Sperner-reduced contraction |
-/
import HypergraphDualization.Section32

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Lemma 3.3.2, corrected -/

theorem degree_del_self (G : Finset (Finset α)) (x : α) : degree (del G x) x = 0 := by
  unfold degree del
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he; exact (mem_filter.1 he).2

theorem degree_con_self (G : Finset (Finset α)) (x : α) : degree (con G x) x = 0 := by
  unfold degree con
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he
  obtain ⟨f, -, rfl⟩ := mem_image.1 he
  exact notMem_erase x f

theorem degree_minimal_le (G : Finset (Finset α)) (x : α) : degree (minimal G) x ≤ degree G x :=
  card_le_card (filter_subset_filter _ (minimal_subset G))

/-- **Lemma 3.3.2, corrected.** The split vertex `x` lies in no edge of either child, so an
automorphism of a child (before or after Sperner reduction) sends `x` to a vertex that also
lies in no edge of that child. The symmetries of the parent that fix `x` survive in both
children (`stab_mem_aut_del`, `stab_mem_aut_con`); nothing more general holds. -/
theorem aut_child_moves_split_to_isolated (G : Finset (Finset α)) (x : α) (σ : Equiv.Perm α) :
    (σ ∈ aut (del G x) → degree (del G x) (σ x) = 0) ∧
    (σ ∈ aut (con G x) → degree (con G x) (σ x) = 0) ∧
    (σ ∈ aut (minimal (con G x)) → degree (minimal (con G x)) (σ x) = 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← degree_eq_of_transitive h rfl, degree_del_self]
  · rw [← degree_eq_of_transitive h rfl, degree_con_self]
  · rw [← degree_eq_of_transitive h rfl]
    exact Nat.eq_zero_of_le_zero ((degree_minimal_le _ x).trans (degree_con_self G x).le)

/-! ### Lemma 3.3.3, refuted -/

open HD.Data in
/-- **Lemma 3.3.3 is false.** `G = {{v₁,v₃},{v₂,v₄}}` has the automorphism
`(v₁ v₂)(v₃ v₄)`, and FK-A splits on `v₁`. The lemma asserts that `(v₃ v₄)` survives the
split; it is an automorphism of neither child, before or after Sperner reduction. -/
theorem lemma_3_3_3_false :
    let G : HG 4 := {{0, 2}, {1, 3}}
    let H := tr univ G
    Equiv.swap 0 1 * Equiv.swap 2 3 ∈ aut G ∧ splitVar G H = some 0 ∧
    Equiv.swap 2 3 ∉ aut (del G 0) ∧ Equiv.swap 2 3 ∉ aut (con H 0) ∧
    Equiv.swap 2 3 ∉ aut (del H 0) ∧ Equiv.swap 2 3 ∉ aut (minimal (con G 0)) := by
  native_decide

/-! ### Observation 3.4.5, made precise -/

/-- Adjacency in the primal graph `G(H)`: distinct vertices sharing an edge. -/
def primalAdj (H : Finset (Finset α)) (u v : α) : Prop := u ≠ v ∧ ∃ e ∈ H, u ∈ e ∧ v ∈ e

theorem primalAdj_del {G : Finset (Finset α)} {x u v : α} (h : primalAdj (del G x) u v) :
    primalAdj G u v ∧ u ≠ x ∧ v ≠ x := by
  obtain ⟨huv, e, he, hu, hv⟩ := h
  rw [del, mem_filter] at he
  exact ⟨⟨huv, e, he.1, hu, hv⟩, fun h => he.2 (h ▸ hu), fun h => he.2 (h ▸ hv)⟩

theorem primalAdj_con {G : Finset (Finset α)} {x u v : α} (h : primalAdj (con G x) u v) :
    primalAdj G u v ∧ u ≠ x ∧ v ≠ x := by
  obtain ⟨huv, e, he, hu, hv⟩ := h
  obtain ⟨f, hf, rfl⟩ := mem_image.1 he
  exact ⟨⟨huv, f, hf, mem_of_mem_erase hu, mem_of_mem_erase hv⟩, ne_of_mem_erase hu,
    ne_of_mem_erase hv⟩

theorem primalAdj_minimal {G : Finset (Finset α)} {u v : α} (h : primalAdj (minimal G) u v) :
    primalAdj G u v := by
  obtain ⟨huv, e, he, hu, hv⟩ := h
  exact ⟨huv, e, minimal_subset G he, hu, hv⟩

/-- **Observation 3.4.5, made precise.** Both FK-A children of a pair split at `x`, after
Sperner reduction, have primal graphs that are subgraphs of `G(C) - x` and `G(D) - x`. Each
child's primal graph is therefore a minor of the parent's, obtained by deleting `x` and
edges only; no contraction is needed. -/
theorem primal_children_le (C D : Finset (Finset α)) (x u v : α) :
    (primalAdj (minimal (del C x)) u v → primalAdj C u v ∧ u ≠ x ∧ v ≠ x) ∧
    (primalAdj (minimal (con D x)) u v → primalAdj D u v ∧ u ≠ x ∧ v ≠ x) :=
  ⟨fun h => primalAdj_del (primalAdj_minimal h), fun h => primalAdj_con (primalAdj_minimal h)⟩

/-! ### Observation 5.2.2 -/

/-- **Observation 5.2.2.** Let `u ≠ x` and suppose every edge of `G` through `u` is a pair
`{u, w}` with `{x, w}` also an edge (in a graph: `N(u) ⊆ N(x)`, so in particular when `u` is a
false twin of `x`). Then `u` lies in no edge of the Sperner-reduced contraction `min(G / x)`:
the false twin is filtered out. -/
theorem falseTwin_filtered {G : Finset (Finset α)} {x u : α}
    (h : ∀ e ∈ G, u ∈ e → ∃ w, w ≠ u ∧ e = {u, w} ∧ {x, w} ∈ G) :
    ∀ e ∈ minimal (con G x), u ∉ e := by
  intro e' he' hu
  obtain ⟨he'G, hmin⟩ := mem_minimal.1 he'
  obtain ⟨e, he, rfl⟩ := mem_image.1 he'G
  obtain ⟨w, hwu, rfl, hxw⟩ := h e he (mem_of_mem_erase hu)
  -- `{x, w}` contracts to a subset of `{w}`, which lies strictly inside `{u, w}.erase x`.
  have hsub : ({x, w} : Finset α).erase x ⊆ ({u, w} : Finset α).erase x := by
    intro y hy
    rw [mem_erase, mem_insert, mem_singleton] at hy
    rcases hy with ⟨hyx, rfl | rfl⟩
    · exact absurd rfl hyx
    · exact mem_erase.2 ⟨hyx, by simp⟩
  have heq := hmin _ (mem_image_of_mem _ hxw) hsub
  have : u ∈ ({x, w} : Finset α).erase x := heq ▸ hu
  rw [mem_erase, mem_insert, mem_singleton] at this
  rcases this.2 with h' | h'
  · exact this.1 h'
  · exact hwu h'.symm

open HD.Data in
/-- **Observation 5.2.2 on `f₂, g₂`.** FK-A splits the root on `v₁`; `v₂` is a false twin of
`v₁` in the primal graph of `f₂`, appears in the contraction `f₂ / v₁`, and is gone after
Sperner reduction. -/
theorem f2g2_false_twin_filtered :
    splitVar f2g2C f2g2D = some 0 ∧
    S32.PAdj f2g2C 0 2 ∧ S32.PAdj f2g2C 1 2 ∧ S32.PAdj f2g2C 0 3 ∧ S32.PAdj f2g2C 1 3 ∧
    (∀ w, S32.PAdj f2g2C 0 w ↔ S32.PAdj f2g2C 1 w) ∧ ¬ S32.PAdj f2g2C 0 1 ∧
    (∃ e ∈ con f2g2C 0, 1 ∈ e) ∧ (∀ e ∈ minimal (con f2g2C 0), 1 ∉ e) := by
  native_decide

end HD

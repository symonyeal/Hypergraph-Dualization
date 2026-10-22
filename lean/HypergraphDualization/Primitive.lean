/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# A read-once certificate from primitivity (research track A, item A7)

A hypergraph is *read-once* if it is Sperner, conformal (every nonempty clique of its primal
graph lies in an edge) and its primal graph is a cograph. A cograph is given here by its cotree
decomposition on a `Finset`: a single vertex, or a disjoint union or join of two cographs.

| Lean | Statement |
| --- | --- |
| `connected_or_trivial` | **Lemma.** A relation preserved by a primitive group action is connected (its equivalence closure is everything) or relates only equal points |
| `aut_eq_top_of_readOnce` | **Proposition A7.** A read-once hypergraph on `n ≥ 2` points with a primitive automorphism group has `Aut(H) = Sₙ` |
| `eq_univ_of_complete` | a conformal Sperner hypergraph with complete primal graph is `{V}` |
| `w11_not_readOnce` | `w11` is not read-once: `Aut(w11)` is primitive of order `7920 ≠ 11!` |
| `fano_not_readOnce` | the Fano plane is not read-once: complete primal graph, not `{V}` |
-/
import HypergraphDualization.Witt
import HypergraphDualization.Recursion
import Mathlib.GroupTheory.GroupAction.Primitive

namespace HD

open Finset
open scoped Pointwise

variable {α : Type*} [DecidableEq α]

/-! ### The core lemma -/

section Core

omit [DecidableEq α]

variable {G : Type*} [Group G] [MulAction G α] {R : α → α → Prop}

theorem eqvGen_smul (hR : ∀ (g : G) u v, R u v → R (g • u) (g • v)) (g : G) {u v : α}
    (h : Relation.EqvGen R u v) : Relation.EqvGen R (g • u) (g • v) := by
  induction h with
  | rel x y hxy => exact .rel _ _ (hR g x y hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- The class of `v` under the equivalence closure of `R`. -/
def eqvClass (R : α → α → Prop) (v : α) : Set α := {w | Relation.EqvGen R v w}

theorem smul_eqvClass (hR : ∀ (g : G) u v, R u v → R (g • u) (g • v)) (g : G) (v : α) :
    g • eqvClass R v = eqvClass R (g • v) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h
    have := eqvGen_smul hR g h
    rwa [smul_inv_smul] at this
  · intro h
    have := eqvGen_smul hR g⁻¹ h
    rwa [inv_smul_smul] at this

theorem isBlock_eqvClass (hR : ∀ (g : G) u v, R u v → R (g • u) (g • v)) (v : α) :
    MulAction.IsBlock G (eqvClass R v) := by
  rw [MulAction.isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨x, hx₁, hx₂⟩
  rw [smul_eqvClass hR] at hx₁ ⊢
  ext w
  have hvx : Relation.EqvGen R v x := hx₂
  have hgx : Relation.EqvGen R (g • v) x := hx₁
  exact ⟨fun h => .trans _ _ _ hvx (.trans _ _ _ (.symm _ _ hgx) h),
    fun h => .trans _ _ _ hgx (.trans _ _ _ (.symm _ _ hvx) h)⟩

/-- **Lemma.** Let `G` act primitively on `α` and preserve `R`. Then either every two points are
joined in the equivalence closure of `R`, or `R` relates only equal points. (The classes of the
closure are blocks; a primitive action has only trivial blocks.) -/
theorem connected_or_trivial [MulAction.IsPreprimitive G α]
    (hR : ∀ (g : G) u v, R u v → R (g • u) (g • v)) :
    (∀ u v, Relation.EqvGen R u v) ∨ ∀ u v, R u v → u = v := by
  by_cases h : ∃ v, eqvClass R v = Set.univ
  · obtain ⟨v, hv⟩ := h
    left
    intro u w
    have hu : u ∈ eqvClass R v := hv ▸ Set.mem_univ u
    have hw : w ∈ eqvClass R v := hv ▸ Set.mem_univ w
    exact .trans _ _ _ (.symm _ _ hu) hw
  · push Not at h
    right
    intro u v huv
    have hb := MulAction.IsPreprimitive.isTrivialBlock_of_isBlock (isBlock_eqvClass hR u)
    rcases hb with hs | hs
    · exact hs (Relation.EqvGen.refl u) (Relation.EqvGen.rel _ _ huv)
    · exact absurd hs (h u)

end Core

/-! ### Read-once hypergraphs -/

/-- `A` carries a cograph structure for the relation `R`, by its cotree. -/
inductive IsCograph (R : α → α → Prop) : Finset α → Prop
  | single (v : α) : IsCograph R {v}
  | union (A B : Finset α) : Disjoint A B → IsCograph R A → IsCograph R B →
      (∀ a ∈ A, ∀ b ∈ B, ¬ R a b) → IsCograph R (A ∪ B)
  | join (A B : Finset α) : Disjoint A B → IsCograph R A → IsCograph R B →
      (∀ a ∈ A, ∀ b ∈ B, R a b) → IsCograph R (A ∪ B)

theorem IsCograph.nonempty {R : α → α → Prop} {A : Finset α} (h : IsCograph R A) :
    A.Nonempty := by
  induction h with
  | single v => exact singleton_nonempty v
  | union A B _ _ _ _ hA _ => exact hA.mono subset_union_left
  | join A B _ _ _ _ hA _ => exact hA.mono subset_union_left

/-- Every nonempty clique of the primal graph lies in an edge. -/
def Conformal (H : Finset (Finset α)) : Prop :=
  ∀ S : Finset α, S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → primalAdj H u v) → ∃ e ∈ H, S ⊆ e

/-- `H` is read-once on the points of `α`: Sperner, conformal, and its primal graph is a
cograph. -/
def ReadOnce [Fintype α] (H : Finset (Finset α)) : Prop :=
  IsSperner H ∧ Conformal H ∧ IsCograph (primalAdj H) univ

omit [DecidableEq α] in
theorem primalAdj_symm {H : Finset (Finset α)} {u v : α} (h : primalAdj H u v) :
    primalAdj H v u := by
  obtain ⟨huv, e, he, hu, hv⟩ := h
  exact ⟨huv.symm, e, he, hv, hu⟩

theorem primalAdj_aut {H : Finset (Finset α)} {σ : Equiv.Perm α} (hσ : σ ∈ aut H) {u v : α}
    (h : primalAdj H u v) : primalAdj H (σ u) (σ v) := by
  obtain ⟨huv, e, he, hu, hv⟩ := h
  refine ⟨σ.injective.ne huv, pmap σ e, ?_, mem_pmap.2 ?_, mem_pmap.2 ?_⟩
  · rw [← mem_aut.1 hσ]; exact mem_pimg.2 he
  · simpa using hu
  · simpa using hv

omit [DecidableEq α] in
/-- In a cograph decomposition `A ∪ B` with no `R`-pair across, the equivalence closure of `R`
stays on the side it starts from, when every point lies in `A ∪ B`. -/
theorem eqvGen_side {R : α → α → Prop} {A B : Finset α} (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ R a b ∧ ¬ R b a) {u v : α}
    (h : Relation.EqvGen R u v) : u ∈ A ↔ v ∈ A := by
  induction h with
  | rel x y hxy =>
    constructor
    · intro hx
      rcases hcov y with hy | hy
      · exact hy
      · exact absurd hxy (hno x hx y hy).1
    · intro hy
      rcases hcov x with hx | hx
      · exact hx
      · exact absurd hxy (hno y hy x hx).2
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Proposition A7.** Let `H` be read-once on the `n ≥ 2` points of `α`, with `Aut(H)` acting
primitively. Then `Aut(H) = Sₙ`.

Proof: the root of the cotree is a union or a join of nonempty `A`, `B`. The primal graph `P`
and its complement are `Aut(H)`-invariant. For a union, `P` is disconnected, so by the Lemma it
has no edges: every edge of `H` has at most one point, and transitivity carries a singleton edge
to every singleton. For a join, the complement of `P` is disconnected, so `P` is complete;
conformality puts all points in one edge, and Sperner gives `H = {V}`. -/
theorem aut_eq_top_of_readOnce [Fintype α] {H : Finset (Finset α)} (hn : 2 ≤ Fintype.card α)
    (hH : ReadOnce H) [MulAction.IsPreprimitive (aut H) α] : aut H = ⊤ := by
  obtain ⟨sH, cH, hcog⟩ := hH
  have act : ∀ (g : aut H) (x : α), g • x = (g : Equiv.Perm α) x := fun _ _ => rfl
  generalize hU : (univ : Finset α) = U at hcog
  have hcov : ∀ {A B : Finset α}, A ∪ B = univ → ∀ x, x ∈ A ∨ x ∈ B := fun h x =>
    mem_union.1 (h ▸ mem_univ x)
  cases hcog with
  | single v =>
    have := congrArg card hU
    rw [card_univ, card_singleton] at this
    omega
  | union A B hd hA hB hno =>
    have hAB := hcov hU.symm
    -- the primal graph has no edges
    have hP : ∀ u v, primalAdj H u v → u = v := by
      refine (connected_or_trivial (G := aut H) fun g u v h => ?_).resolve_left ?_
      · exact primalAdj_aut g.2 h
      · intro hall
        obtain ⟨a, ha⟩ := hA.nonempty
        obtain ⟨b, hb⟩ := hB.nonempty
        have := (eqvGen_side hAB (fun a ha b hb => ⟨hno a ha b hb,
          fun h => hno a ha b hb (primalAdj_symm h)⟩) (hall a b)).1 ha
        exact disjoint_left.1 hd this hb
    have hle : ∀ e ∈ H, e.card ≤ 1 := fun e he =>
      card_le_one.2 fun u hu v hv => by
        by_contra huv
        exact huv (hP u v ⟨huv, e, he, hu, hv⟩)
    refine eq_top_iff.2 fun σ _ => mem_aut_of_subset fun f hf => ?_
    obtain ⟨e, he, rfl⟩ := mem_image.1 hf
    rcases e.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simpa [pmap] using he
    · obtain rfl : e = {v} :=
        eq_singleton_iff_unique_mem.2 ⟨hv, fun w hw => card_le_one.1 (hle e he) w hw v hv⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (aut H) v (σ v)
      rw [act] at hg
      have : pmap (g : Equiv.Perm α) {v} ∈ pimg (g : Equiv.Perm α) H := mem_pimg.2 he
      rw [mem_aut.1 g.2] at this
      simpa [pmap, hg] using this
  | join A B hd hA hB hall =>
    have hAB := hcov hU.symm
    let Q : α → α → Prop := fun u v => u ≠ v ∧ ¬ primalAdj H u v
    -- the complement of the primal graph has no edges
    have hQ : ∀ u v, Q u v → u = v := by
      refine (connected_or_trivial (G := aut H) fun g u v h => ?_).resolve_left ?_
      · refine ⟨fun h' => h.1 ((g : Equiv.Perm α).injective h'), fun h' => h.2 ?_⟩
        have := primalAdj_aut (inv_mem g.2) h'
        simpa [act] using this
      · intro hall'
        obtain ⟨a, ha⟩ := hA.nonempty
        obtain ⟨b, hb⟩ := hB.nonempty
        have := (eqvGen_side hAB (fun a ha b hb => ⟨fun h => h.2 (hall a ha b hb),
          fun h => h.2 (primalAdj_symm (hall a ha b hb))⟩) (hall' a b)).1 ha
        exact disjoint_left.1 hd this hb
    have hcl : ∀ u ∈ (univ : Finset α), ∀ v ∈ (univ : Finset α), u ≠ v → primalAdj H u v :=
      fun u _ v _ huv => by
        by_contra h
        exact huv (hQ u v ⟨huv, h⟩)
    have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨e, he, hue⟩ := cH univ univ_nonempty hcl
    have heU : e = univ := eq_univ_of_forall fun x => hue (mem_univ x)
    subst heU
    refine eq_top_iff.2 fun σ _ => mem_aut_of_subset fun f hf => ?_
    obtain ⟨e', he', rfl⟩ := mem_image.1 hf
    have : e' = univ := sH e' he' univ he (subset_univ e')
    subst this
    simpa [pmap] using he

omit [DecidableEq α] in
/-- A conformal Sperner hypergraph whose primal graph is complete on `n ≥ 1` points is `{V}`. -/
theorem eq_univ_of_complete [Fintype α] [Nonempty α] {H : Finset (Finset α)} (sH : IsSperner H)
    (cH : Conformal H) (hc : ∀ u v : α, u ≠ v → primalAdj H u v) : H = {univ} := by
  obtain ⟨e, he, hue⟩ := cH univ univ_nonempty fun u _ v _ => hc u v
  have heU : e = univ := eq_univ_of_forall fun x => hue (mem_univ x)
  subst heU
  ext f
  rw [mem_singleton]
  exact ⟨fun hf => sH f hf univ he (subset_univ f), fun hf => hf ▸ he⟩

/-- **Corollary.** `w11` is not read-once: `Aut(w11)` is primitive (`w11_preprimitive`), and
`|Aut(w11)| = 7920 ≠ 11!`. -/
theorem w11_not_readOnce : ¬ ReadOnce Witt.w11 := by
  intro h
  have := Witt.w11_preprimitive
  have htop := aut_eq_top_of_readOnce (by simp) h
  have hc := Witt.card_aut_w11
  rw [htop, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hc
  revert hc
  decide

instance (H : Finset (Finset α)) (u v : α) : Decidable (primalAdj H u v) := by
  unfold primalAdj; infer_instance

/-- **Corollary.** The Fano plane is not read-once: its primal graph is complete, so a read-once
Fano plane would be `{V}`. -/
theorem fano_not_readOnce : ¬ ReadOnce Data.fanoC := by
  rintro ⟨sH, cH, _⟩
  have := eq_univ_of_complete sH cH (by decide)
  revert this
  decide

end HD

/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Symmetry depth

Legend: C,D are the input families; A is the deleted set; B is the contracted
set; U is the set of queried vertices; j is depth; q is an isomorphism key.
Every nonroot FK-A state has a first side with at least one deletion, from
either C or D. This saves two classes at every positive depth.
-/
import HypergraphDualization.Dag
import HypergraphDualization.Symmetry
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

namespace HD.SD
open Finset
variable {n : ℕ}

def cut (C : HG n) (A B : Finset (Fin n)) : HG n :=
  minimal ((C.filter (fun e => Disjoint e A)).image (fun e => e \ B))

theorem upHit_cut (C : HG n) {A B : Finset (Fin n)} (h : Disjoint A B)
    (S : Finset (Fin n)) : upHit (cut C A B) S ↔ upHit C ((S \ A) ∪ B) := by
  rw [cut, upHit_minimal]
  simp only [upHit, mem_image, mem_filter]
  constructor
  · rintro ⟨_, ⟨e, ⟨he, heA⟩, rfl⟩, heS⟩
    refine ⟨e, he, fun x hx => ?_⟩
    by_cases hxB : x ∈ B
    · exact mem_union_right _ hxB
    · exact mem_union_left _ (mem_sdiff.2 ⟨heS (mem_sdiff.2 ⟨hx, hxB⟩),
        fun hxA => disjoint_left.1 heA hx hxA⟩)
  · rintro ⟨e, he, heS⟩
    have heA : Disjoint e A := by
      apply disjoint_left.2
      intro x hx hxA
      rcases mem_union.1 (heS hx) with hxS | hxB
      · exact (mem_sdiff.1 hxS).2 hxA
      · exact disjoint_left.1 h hxA hxB
    exact ⟨e \ B, ⟨e, ⟨he, heA⟩, rfl⟩, fun x hx =>
      (mem_sdiff.1 ((mem_union.1 (heS (mem_sdiff.1 hx).1)).resolve_right
        (mem_sdiff.1 hx).2)).1⟩

theorem cut_empty (C : HG n) : cut C ∅ ∅ = minimal C := by
  simp [cut]

theorem cut_del (C : HG n) {A B : Finset (Fin n)} (h : Disjoint A B)
    {x : Fin n} (hx : x ∉ B) :
    minimal (del (cut C A B) x) = cut C (insert x A) B := by
  apply eq_of_upHit_iff (within_univ _) (within_univ _) (minimal_isSperner _)
    (minimal_isSperner _)
  intro S _
  change upHit (minimal (del (cut C A B) x)) S ↔ upHit (cut C (insert x A) B) S
  rw [upHit_minimal, upHit_del, upHit_cut C h,
    upHit_cut C (disjoint_insert_left.2 ⟨hx, h⟩)]
  have he : S.erase x \ A ∪ B = S \ insert x A ∪ B := by
    ext y
    simp only [mem_union, mem_sdiff, mem_erase, mem_insert]
    tauto
  rw [he]

theorem cut_con (C : HG n) {A B : Finset (Fin n)} (h : Disjoint A B)
    {x : Fin n} (hx : x ∉ A) :
    minimal (con (cut C A B) x) = cut C A (insert x B) := by
  apply eq_of_upHit_iff (within_univ _) (within_univ _) (minimal_isSperner _)
    (minimal_isSperner _)
  intro S _
  change upHit (minimal (con (cut C A B) x)) S ↔ upHit (cut C A (insert x B)) S
  rw [upHit_minimal, upHit_con, upHit_cut C h,
    upHit_cut C (disjoint_insert_right.2 ⟨hx, h⟩)]
  have he : insert x S \ A ∪ B = S \ A ∪ insert x B := by
    ext y
    simp only [mem_union, mem_sdiff, mem_insert]
    by_cases hy : y = x
    · subst y; simp [hx]
    · simp [hy]
  rw [he]

def pair (C D : HG n) (A B : Finset (Fin n)) : HG n × HG n :=
  (cut C A B, cut D B A)

def step (b : Bool) (p : HG n × HG n) (x : Fin n) : HG n × HG n :=
  if b then (minimal (del p.2 x), minimal (con p.1 x))
  else (minimal (del p.1 x), minimal (con p.2 x))

theorem step_pair_left (C D : HG n) {A B : Finset (Fin n)} (h : Disjoint A B)
    {x : Fin n} (hx : x ∉ B) :
    step false (pair C D A B) x = pair C D (insert x A) B := by
  simp only [step, Bool.false_eq_true, ite_false, pair]
  rw [cut_del C h hx, cut_con D h.symm hx]

theorem step_pair_right (C D : HG n) {A B : Finset (Fin n)} (h : Disjoint A B)
    {x : Fin n} (hx : x ∉ A) :
    step true (pair C D A B) x = pair D C (insert x B) A := by
  simp only [step, ite_true, pair]
  rw [cut_del D h.symm hx, cut_con C h hx]

/-- A path of FK-A splits at fresh vertices; stopping conditions can only remove paths. -/
inductive Trace (C D : HG n) : Finset (Fin n) → HG n × HG n → Prop
  | root : Trace C D ∅ (minimal C, minimal D)
  | next {U p} (h : Trace C D U p) (b : Bool) (x : Fin n) (hx : x ∉ U) :
      Trace C D (insert x U) (step b p x)

/-- The first family of a nonroot state has a deletion in its normal form. -/
theorem Trace.normal {C D : HG n} {U : Finset (Fin n)} {p : HG n × HG n}
    (h : Trace C D U p) : ∃ A B, Disjoint A B ∧ A ∪ B = U ∧
      (U.Nonempty → A.Nonempty) ∧ (p = pair C D A B ∨ p = pair D C A B) := by
  induction h with
  | root => exact ⟨∅, ∅, by simp, by simp, by simp,
      Or.inl (by simp [pair, cut_empty])⟩
  | @next U p h b x hx ih =>
    obtain ⟨A, B, hd, hu, _, hp⟩ := ih
    have hxA : x ∉ A := fun ha => hx (hu ▸ mem_union_left B ha)
    have hxB : x ∉ B := fun hb => hx (hu ▸ mem_union_right A hb)
    cases b
    · refine ⟨insert x A, B, disjoint_insert_left.2 ⟨hxB, hd⟩,
        by rw [insert_union, hu], fun _ => insert_nonempty _ _, ?_⟩
      rcases hp with rfl | rfl
      · exact Or.inl (step_pair_left C D hd hxB)
      · exact Or.inr (step_pair_left D C hd hxB)
    · refine ⟨insert x B, A, disjoint_insert_left.2 ⟨hxA, hd.symm⟩,
        by rw [insert_union, union_comm B A, hu], fun _ => insert_nonempty _ _, ?_⟩
      rcases hp with rfl | rfl
      · exact Or.inr (step_pair_right C D hd hxA)
      · exact Or.inl (step_pair_right D C hd hxA)

theorem Trace.within {C D : HG n} {U : Finset (Fin n)} {p : HG n × HG n}
    (h : Trace C D U p) : Within (univ \ U) p.1 ∧ Within (univ \ U) p.2 := by
  induction h with
  | root => simp only [sdiff_empty]; exact ⟨within_univ _, within_univ _⟩
  | @next U p h b x hx ih =>
    have he : (univ \ U).erase x = univ \ insert x U := by
      ext y; simp only [mem_erase, mem_sdiff, mem_univ, true_and, mem_insert]; tauto
    have h0 := within_minimal (del_within ih.1 x)
    have h1 := within_minimal (con_within ih.2 x)
    have h2 := within_minimal (del_within ih.2 x)
    have h3 := within_minimal (con_within ih.1 x)
    rw [he] at h0 h1 h2 h3
    cases b
    · exact ⟨h0, h1⟩
    · exact ⟨h2, h3⟩

theorem Trace.fresh {C D : HG n} {U : Finset (Fin n)} {p : HG n × HG n}
    (h : Trace C D U p) {x : Fin n} (hx : x ∈ support p.1 ∪ support p.2) : x ∉ U := by
  obtain ⟨h0, h1⟩ := h.within
  rcases mem_union.1 hx with hx | hx
  · obtain ⟨e, he, hx⟩ := mem_biUnion.1 hx
    exact (mem_sdiff.1 (h0 e he hx)).2
  · obtain ⟨e, he, hx⟩ := mem_biUnion.1 hx
    exact (mem_sdiff.1 (h1 e he hx)).2

/-- Every actual FK-A subproblem extends the split trace, for any rule choosing
a live vertex. No equivariance or symmetry of the rule is assumed. -/
theorem trace_fkADag {C₀ D₀ : HG n} (r : Rule n)
    (hr : ∀ C D x, r C D = some x → x ∈ support C ∪ support D)
    (fuel : ℕ) (b : Bool) : ∀ C D U,
    Trace C₀ D₀ U (minimal C, minimal D) → ∀ p ∈ fkADagR r fuel b C D,
    ∃ V, V.card ≤ U.card + fuel ∧ Trace C₀ D₀ V p := by
  induction fuel with
  | zero =>
    intro C D U ht p hp
    have hp' : p = (minimal C, minimal D) := mem_singleton.1 hp
    exact ⟨U, by omega, hp' ▸ ht⟩
  | succ f ih =>
    intro C D U ht p hp
    rcases mem_fkADagR_succ hp with hp | ⟨x, hx, hp⟩
    · exact ⟨U, by omega, hp ▸ ht⟩
    have hfresh := ht.fresh (hr _ _ x hx)
    have hcard := card_insert_of_notMem hfresh
    rcases hp with hp | hp
    · obtain ⟨V, hv, ht'⟩ := ih _ _ (insert x U) (ht.next false x hfresh) p hp
      exact ⟨V, by omega, ht'⟩
    · obtain ⟨V, hv, ht'⟩ := ih _ _ (insert x U) (ht.next true x hfresh) p hp
      exact ⟨V, by omega, ht'⟩

theorem fkADag_trace (r : Rule n)
    (hr : ∀ C D x, r C D = some x → x ∈ support C ∪ support D)
    (fuel : ℕ) (b : Bool) (C D : HG n) (p : HG n × HG n)
    (hp : p ∈ fkADagR r fuel b C D) :
    ∃ U, U.card ≤ fuel ∧ Trace C D U p := by
  simpa using trace_fkADag r hr fuel b C D ∅ Trace.root p hp

theorem pmap_sdiff (σ : Equiv.Perm (Fin n)) (A B : Finset (Fin n)) :
    pmap σ (A \ B) = pmap σ A \ pmap σ B := by ext x; simp

theorem pmap_disjoint (σ : Equiv.Perm (Fin n)) (A B : Finset (Fin n)) :
    Disjoint (pmap σ A) (pmap σ B) ↔ Disjoint A B := by
  simp only [disjoint_left, mem_pmap]
  constructor
  · intro h x hx hy; exact h (by simpa using hx : σ.symm (σ x) ∈ A)
      (by simpa using hy : σ.symm (σ x) ∈ B)
  · intro h x hx hy; exact h hx hy

theorem cut_pimg (σ : Equiv.Perm (Fin n)) (C : HG n) (A B : Finset (Fin n)) :
    cut (pimg σ C) (pmap σ A) (pmap σ B) = pimg σ (cut C A B) := by
  unfold cut
  rw [← minimal_pimg]
  simp only [pimg, filter_image, pmap_disjoint, image_image]
  congr 2
  funext e
  exact (pmap_sdiff σ e B).symm

/-- Two-colour homogeneity at depth j; j-transitivity of a common automorphism
group suffices. This hypothesis also allows groups weaker than j-transitive. -/
def Hom (C D : HG n) (j : ℕ) : Prop :=
  ∀ A B A' B' : Finset (Fin n), Disjoint A B → Disjoint A' B' →
    A.card + B.card = j → A'.card + B'.card = j → B.card = B'.card →
    ∃ σ : Equiv.Perm (Fin n), pimg σ C = C ∧ pimg σ D = D ∧
      pmap σ A = A' ∧ pmap σ B = B'

def sumEmb {A B : Finset (Fin n)} (h : Disjoint A B) : (A ⊕ B) ↪ Fin n where
  toFun := Sum.elim Subtype.val Subtype.val
  inj' := by
    intro x y he
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (Subtype.ext he)
      | inr b =>
        change a.val = b.val at he
        exact False.elim (disjoint_left.1 h a.property (he.symm ▸ b.property))
    | inr b =>
      cases y with
      | inl a =>
        change b.val = a.val at he
        exact False.elim (disjoint_left.1 h a.property (he ▸ b.property))
      | inr b' => exact congrArg Sum.inr (Subtype.ext he)

@[simp] theorem sumEmb_inl {A B : Finset (Fin n)} (h : Disjoint A B) (a : A) :
    sumEmb h (.inl a) = a.val := rfl

@[simp] theorem sumEmb_inr {A B : Finset (Fin n)} (h : Disjoint A B) (b : B) :
    sumEmb h (.inr b) = b.val := rfl

theorem pmap_eq_of_equiv {A B : Finset (Fin n)} (σ : Equiv.Perm (Fin n))
    (e : A ≃ B) (he : ∀ a : A, σ a.val = (e a).val) : pmap σ A = B := by
  ext x
  constructor
  · intro hx
    have ha : σ.symm x ∈ A := mem_pmap.1 hx
    have hh := he ⟨σ.symm x, ha⟩
    change σ (σ.symm x) = (e ⟨σ.symm x, ha⟩).val at hh
    rw [Equiv.apply_symm_apply] at hh
    rw [hh]
    exact (e ⟨σ.symm x, ha⟩).property
  · intro hx
    let a := e.symm ⟨x, hx⟩
    have hh : σ a.val = x := by simpa [a] using he a
    rw [← hh]
    exact mem_pmap.2 (by simp)

/-- Multiple transitivity implies the two-colour homogeneity used in the count. -/
theorem hom_of_transitive (C D : HG n) (j : ℕ)
    [MulAction.IsMultiplyPretransitive ↥(aut C ⊓ aut D) (Fin n) j] : Hom C D j := by
  classical
  intro A B A' B' hd hd' hc hc' hb
  have ha : A.card = A'.card := by omega
  let eA : A ≃ A' := Fintype.equivOfCardEq (by simpa using ha)
  let eB : B ≃ B' := Fintype.equivOfCardEq (by simpa using hb)
  let e : Fin j ≃ A ⊕ B := (Fintype.equivFinOfCardEq (by simpa using hc)).symm
  let s : Fin j ↪ Fin n := e.toEmbedding.trans (sumEmb hd)
  let t : Fin j ↪ Fin n :=
    (e.trans (Equiv.sumCongr eA eB)).toEmbedding.trans (sumEmb hd')
  obtain ⟨σ, hs⟩ := MulAction.exists_smul_eq (M := ↥(aut C ⊓ aut D)) s t
  have hA : ∀ a : A, (σ : Equiv.Perm (Fin n)) a.val = (eA a).val := by
    intro a
    have hh := congrArg (fun u : Fin j ↪ Fin n => u (e.symm (.inl a))) hs
    change (σ : Equiv.Perm (Fin n)) (s (e.symm (.inl a))) = t (e.symm (.inl a)) at hh
    simpa [s, t, Function.Embedding.trans_apply] using hh
  have hB : ∀ b : B, (σ : Equiv.Perm (Fin n)) b.val = (eB b).val := by
    intro b
    have hh := congrArg (fun u : Fin j ↪ Fin n => u (e.symm (.inr b))) hs
    change (σ : Equiv.Perm (Fin n)) (s (e.symm (.inr b))) = t (e.symm (.inr b)) at hh
    simpa [s, t, Function.Embedding.trans_apply] using hh
  exact ⟨σ, σ.property.1, σ.property.2,
    pmap_eq_of_equiv σ eA hA, pmap_eq_of_equiv σ eB hB⟩

def Inv {β : Type*} (q : (HG n × HG n) → β) : Prop :=
  ∀ σ C D, q (pimg σ C, pimg σ D) = q (C, D)

theorem key_pair {β : Type*} {q : (HG n × HG n) → β} (hq : Inv q)
    {C D : HG n} {j : ℕ} (h : Hom C D j) {A B A' B' : Finset (Fin n)}
    (hd : Disjoint A B) (hd' : Disjoint A' B') (hc : A.card + B.card = j)
    (hc' : A'.card + B'.card = j) (hb : B.card = B'.card) :
    q (pair C D A B) = q (pair C D A' B') ∧
      q (pair D C A B) = q (pair D C A' B') := by
  obtain ⟨σ, hC, hD, hA, hB⟩ := h A B A' B' hd hd' hc hc' hb
  have h1 := cut_pimg σ C A B
  have h2 := cut_pimg σ D B A
  have h3 := cut_pimg σ D A B
  have h4 := cut_pimg σ C B A
  rw [hC, hA, hB] at h1 h4
  rw [hD, hA, hB] at h2 h3
  constructor
  · exact (hq σ (cut C A B) (cut D B A)).symm.trans (by rw [← h1, ← h2]; rfl)
  · exact (hq σ (cut D A B) (cut C B A)).symm.trans (by rw [← h3, ← h4]; rfl)

/-- A finite image factors through any finite signature separating its values. -/
theorem card_image_le_signature {α β γ : Type*} [DecidableEq β] [Fintype γ]
    (R : Finset α) (f : α → β) (g : R → γ)
    (h : ∀ x y : R, g x = g y → f x.val = f y.val) :
    (R.image f).card ≤ Fintype.card γ := by
  classical
  have ex : ∀ y : R.image f, ∃ x : R, f x.val = y.val := by
    intro y; obtain ⟨x, hx, he⟩ := mem_image.1 y.property; exact ⟨⟨x, hx⟩, he⟩
  choose a ha using ex
  have hi : Function.Injective (fun y => g (a y)) := by
    intro x y he
    apply Subtype.ext
    rw [← ha x, ← ha y]
    exact h (a x) (a y) he
  simpa using Fintype.card_le_of_injective _ hi

/-- A normal form and its finite signature at a positive depth. -/
theorem normal_code {C D : HG n} {j : ℕ} (hj : 0 < j)
    {p : HG n × HG n} (hp : ∃ U, U.card = j ∧ Trace C D U p) :
    ∃ (b : Bool) (A B : Finset (Fin n)), Disjoint A B ∧ A.card + B.card = j ∧
      B.card < j ∧ p = if b then pair D C A B else pair C D A B := by
  obtain ⟨U, hu, ht⟩ := hp
  obtain ⟨A, B, hd, hab, ha, hp⟩ := ht.normal
  have hc : A.card + B.card = j := by rw [← card_union_of_disjoint hd, hab, hu]
  have ha' := card_pos.2 (ha (card_pos.1 (hu ▸ hj)))
  rcases hp with hp | hp
  · exact ⟨false, A, B, hd, hc, by omega, hp⟩
  · exact ⟨true, A, B, hd, hc, by omega, hp⟩

/-- At positive depth j there are at most 2j ordered isomorphism classes. -/
theorem depth_bound {β : Type*} [DecidableEq β] {q : (HG n × HG n) → β}
    (hq : Inv q) {C D : HG n} {j : ℕ} (hj : 0 < j) (hh : Hom C D j)
    (R : Finset (HG n × HG n))
    (hR : ∀ p ∈ R, ∃ U, U.card = j ∧ Trace C D U p) :
    (R.image q).card ≤ 2 * j := by
  classical
  have hn := fun p : R => normal_code hj (hR p.val p.property)
  choose b A B hd hc hb hp using hn
  let g : R → Bool × Fin j := fun p => (b p, ⟨(B p).card, hb p⟩)
  have h := card_image_le_signature R q g (by
    intro p p' he
    have he1 : b p = b p' := congrArg Prod.fst he
    have he2 : (B p).card = (B p').card := congrArg (fun t : Bool × Fin j => t.2.val) he
    rw [hp p, hp p', ← he1]
    obtain ⟨h0, h1⟩ := key_pair hq hh (hd p) (hd p') (hc p) (hc p') he2
    cases b p <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> assumption)
  simpa using h

/-- Equal input sides remove the source-side bit: at most j classes at depth j. -/
theorem self_depth_bound {β : Type*} [DecidableEq β] {q : (HG n × HG n) → β}
    (hq : Inv q) {C : HG n} {j : ℕ} (hj : 0 < j) (hh : Hom C C j)
    (R : Finset (HG n × HG n))
    (hR : ∀ p ∈ R, ∃ U, U.card = j ∧ Trace C C U p) :
    (R.image q).card ≤ j := by
  classical
  have hn := fun p : R => normal_code hj (hR p.val p.property)
  choose b A B hd hc hb hp using hn
  have hp' : ∀ p : R, p.val = pair C C (A p) (B p) := by intro p; simpa using hp p
  let g : R → Fin j := fun p => ⟨(B p).card, hb p⟩
  have h := card_image_le_signature R q g (by
    intro p p' he
    rw [hp' p, hp' p']
    exact (key_pair hq hh (hd p) (hd p') (hc p) (hc p') (congrArg Fin.val he)).1)
  simpa using h

open Classical in
noncomputable def layer (C D : HG n) (j : ℕ) : Finset (HG n × HG n) :=
  univ.filter fun p => ∃ U, U.card = j ∧ Trace C D U p

noncomputable def upto (C D : HG n) (k : ℕ) : Finset (HG n × HG n) :=
  (range (k + 1)).biUnion (layer C D)

theorem mem_layer {C D : HG n} {j : ℕ} {p : HG n × HG n} :
    p ∈ layer C D j ↔ ∃ U, U.card = j ∧ Trace C D U p := by
  classical
  simp [layer]

theorem Trace.zero {C D : HG n} {U : Finset (Fin n)} {p : HG n × HG n}
    (h : Trace C D U p) (hu : U = ∅) : p = (minimal C, minimal D) := by
  cases h with
  | root => rfl
  | next h b x hx => simp at hu

theorem layer_zero (C D : HG n) : layer C D 0 = {(minimal C, minimal D)} := by
  ext p
  rw [mem_layer, mem_singleton]
  constructor
  · rintro ⟨U, hu, ht⟩; exact ht.zero (card_eq_zero.1 hu)
  · rintro rfl; exact ⟨∅, rfl, Trace.root⟩

theorem upto_zero (C D : HG n) : upto C D 0 = {(minimal C, minimal D)} := by
  simp [upto, layer_zero]

theorem upto_succ (C D : HG n) (k : ℕ) :
    upto C D (k + 1) = layer C D (k + 1) ∪ upto C D k := by
  rw [upto, range_add_one, biUnion_insert]
  rfl

/-- Sum the layer bounds; classes at different depths may coincide. -/
theorem upto_count {β : Type*} [DecidableEq β] (q : (HG n × HG n) → β)
    (C D : HG n) (c k : ℕ)
    (hh : ∀ j, 0 < j → j ≤ k → ((layer C D j).image q).card ≤ c * j) :
    2 * ((upto C D k).image q).card ≤ 2 + c * k * (k + 1) := by
  induction k with
  | zero => simp [upto_zero]
  | succ k ih =>
    have h0 := ih (fun j hj hk => hh j hj (by omega))
    have h1 := hh (k + 1) (by omega) le_rfl
    rw [upto_succ, image_union]
    have h2 := card_union_le ((layer C D (k + 1)).image q) ((upto C D k).image q)
    nlinarith

theorem upto_bound {β : Type*} [DecidableEq β] {q : (HG n × HG n) → β}
    (hq : Inv q) {C D : HG n} {k : ℕ} (hh : ∀ j ≤ k, Hom C D j) :
    ((upto C D k).image q).card ≤ 1 + k * (k + 1) := by
  have h := upto_count q C D 2 k (fun j hj hk =>
    depth_bound hq hj (hh j hk) _ (fun p hp => mem_layer.1 hp))
  nlinarith

theorem self_upto_bound {β : Type*} [DecidableEq β] {q : (HG n × HG n) → β}
    (hq : Inv q) {C : HG n} {k : ℕ} (hh : ∀ j ≤ k, Hom C C j) :
    ((upto C C k).image q).card ≤ 1 + k * (k + 1) / 2 := by
  have h := upto_count q C C 1 k (fun j hj hk => by
    simpa using self_depth_bound hq hj (hh j hk) _ (fun p hp => mem_layer.1 hp))
  simp only [one_mul] at h
  omega

theorem fkADag_subset_upto (r : Rule n)
    (hr : ∀ C D x, r C D = some x → x ∈ support C ∪ support D)
    (k : ℕ) (b : Bool) (C D : HG n) : fkADagR r k b C D ⊆ upto C D k := by
  intro p hp
  obtain ⟨U, hu, ht⟩ := fkADag_trace r hr k b C D p hp
  exact mem_biUnion.2 ⟨U.card, mem_range.2 (by omega), mem_layer.2 ⟨U, rfl, ht⟩⟩

theorem fkADag_iso_bound {β : Type*} [DecidableEq β] {q : (HG n × HG n) → β}
    (hq : Inv q) (r : Rule n)
    (hr : ∀ C D x, r C D = some x → x ∈ support C ∪ support D)
    (k : ℕ) (b : Bool) (C D : HG n) (hh : ∀ j ≤ k, Hom C D j) :
    ((fkADagR r k b C D).image q).card ≤ 1 + k * (k + 1) :=
  (card_le_card (image_subset_image (fkADag_subset_upto r hr k b C D))).trans
    (upto_bound hq hh)

theorem fkADag_self_iso_bound {β : Type*} [DecidableEq β] {q : (HG n × HG n) → β}
    (hq : Inv q) (r : Rule n)
    (hr : ∀ C D x, r C D = some x → x ∈ support C ∪ support D)
    (k : ℕ) (b : Bool) (C : HG n) (hh : ∀ j ≤ k, Hom C C j) :
    ((fkADagR r k b C C).image q).card ≤ 1 + k * (k + 1) / 2 :=
  (card_le_card (image_subset_image (fkADag_subset_upto r hr k b C C))).trans
    (self_upto_bound hq hh)

theorem hom_of_ktransitive (C D : HG n) (k : ℕ) (hk : k ≤ n)
    [MulAction.IsMultiplyPretransitive ↥(aut C ⊓ aut D) (Fin n) k] :
    ∀ j ≤ k, Hom C D j := by
  intro j hj
  have := MulAction.isMultiplyPretransitive_of_le
    (G := ↥(aut C ⊓ aut D)) (α := Fin n) hj (by simpa using hk)
  exact hom_of_transitive C D j

def Iso (p q : HG n × HG n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), p = (pimg σ q.1, pimg σ q.2)

def isoSetoid (n : ℕ) : Setoid (HG n × HG n) where
  r := Iso
  iseqv := {
    refl := fun p => ⟨1, by simp [pimg_one]⟩
    symm := by
      rintro p q ⟨σ, rfl⟩
      exact ⟨σ⁻¹, by simp [pimg_inv_pimg]⟩
    trans := by
      rintro p q z ⟨σ, rfl⟩ ⟨ρ, rfl⟩
      exact ⟨σ * ρ, by simp [pimg_mul]⟩ }

def isoKey (p : HG n × HG n) : Quotient (isoSetoid n) := Quotient.mk _ p

theorem isoKey_eq_iff (p q : HG n × HG n) : isoKey p = isoKey q ↔ Iso p q :=
  Quotient.eq

theorem isoKey_inv : Inv (isoKey (n := n)) := fun σ _ _ => Quotient.sound ⟨σ, rfl⟩

open Classical in
/-- The actual ordered-pair isomorphism quotient, under k-transitivity. -/
theorem transitive_bound (C D : HG n) (k : ℕ) (hk : k ≤ n)
    [MulAction.IsMultiplyPretransitive ↥(aut C ⊓ aut D) (Fin n) k]
    (r : Rule n) (hr : ∀ E F x, r E F = some x → x ∈ support E ∪ support F) (b : Bool) :
    ((fkADagR r k b C D).image isoKey).card ≤ 1 + k * (k + 1) :=
  fkADag_iso_bound isoKey_inv r hr k b C D (hom_of_ktransitive C D k hk)

open Classical in
theorem self_transitive_bound (C : HG n) (k : ℕ) (hk : k ≤ n)
    [MulAction.IsMultiplyPretransitive (aut C) (Fin n) k]
    (r : Rule n) (hr : ∀ E F x, r E F = some x → x ∈ support E ∪ support F) (b : Bool) :
    ((fkADagR r k b C C).image isoKey).card ≤ 1 + k * (k + 1) / 2 := by
  have he : aut C ⊓ aut C = aut C := inf_idem _
  have : MulAction.IsMultiplyPretransitive ↥(aut C ⊓ aut C) (Fin n) k := by
    rw [he]; infer_instance
  exact fkADag_self_iso_bound isoKey_inv r hr k b C (hom_of_ktransitive C C k hk)

open Classical in
theorem dual_transitive_bound (C : HG n) (k : ℕ) (hk : k ≤ n)
    [MulAction.IsMultiplyPretransitive (aut C) (Fin n) k]
    (r : Rule n) (hr : ∀ E F x, r E F = some x → x ∈ support E ∪ support F) (b : Bool) :
    ((fkADagR r k b C (tr univ C)).image isoKey).card ≤ 1 + k * (k + 1) := by
  have he : aut C ⊓ aut (tr univ C) = aut C := inf_eq_left.2 (aut_le_aut_tr C)
  have : MulAction.IsMultiplyPretransitive ↥(aut C ⊓ aut (tr univ C)) (Fin n) k := by
    rw [he]; infer_instance
  exact transitive_bound C (tr univ C) k hk r hr b

end HD.SD

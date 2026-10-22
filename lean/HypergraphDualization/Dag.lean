/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A's recursion tree against its subproblem DAG (research track C)

`fkA` counts the nodes `τ` of the recursion tree. `fkADag` collects the distinct
Sperner-reduced pairs `(C, D)` the recursion visits; its cardinality is `δ`, the number of
subproblems a memoised FK-A solves.

| Lean | Statement |
| --- | --- |
| `fkADag` | the set of distinct subproblems of the FK-A recursion |
| `tr_con_eq`, `minimal_con_tr` | `Tr(G / x) = Tr(G) − x` and `min(Tr(G) / x) = Tr(G − x)` |
| `fkA_split`, `fkADag_split` | one step of the recursion at a dual node |
| `splitVar_spec` | the split vertex has the largest positive degree sum |
| `fkADag_within` | every subproblem lives on the vertices of its root |
-/
import HypergraphDualization.Trees
import Mathlib.Tactic.Linarith

namespace HD

open Finset

variable {n : ℕ}

/-! ### The subproblem DAG -/

/-- The distinct Sperner-reduced pairs visited by FK-A, node for node with `fkA`. -/
def fkADag : ℕ → Bool → HG n → HG n → Finset (HG n × HG n)
  | 0, _, C₀, D₀ => {(minimal C₀, minimal D₀)}
  | fuel + 1, modified, C₀, D₀ =>
    let C := minimal C₀
    let D := minimal D₀
    if !conds C D then {(C, D)}
    else if C.card * D.card ≤ 1 || (modified && (C.card == 1 || D.card == 1)) then {(C, D)}
    else
      match splitVar C D with
      | none => {(C, D)}
      | some x =>
        let l := fkADag fuel modified (del C x) (con D x)
        if (fkA fuel modified (del C x) (con D x)).1 then
          insert (C, D) (l ∪ fkADag fuel modified (del D x) (con C x))
        else insert (C, D) l

theorem minimal_minimal {α : Type*} [DecidableEq α] (H : Finset (Finset α)) :
    minimal (minimal H) = minimal H :=
  minimal_eq_self (minimal_isSperner H)

theorem fkA_minimal (fuel : ℕ) (b : Bool) (C D : HG n) :
    fkA fuel b (minimal C) (minimal D) = fkA fuel b C D := by
  cases fuel <;> simp only [fkA, minimal_minimal]

theorem fkADag_minimal (fuel : ℕ) (b : Bool) (C D : HG n) :
    fkADag fuel b (minimal C) (minimal D) = fkADag fuel b C D := by
  cases fuel <;> simp only [fkADag, minimal_minimal]

/-- The two FK-A children of a dual pair are dual. -/
theorem dual_children {C D : HG n} (h : Dual univ C D) (x : Fin n) :
    Dual univ (del C x) (con D x) ∧ Dual univ (del D x) (con C x) := by
  have hsplit := (dual_split (within_univ C) (within_univ D) (mem_univ x)).1 h
  have hL := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
    (G := del C x) (H := con D x) (x := x)
    (fun e he => (mem_filter.1 he).2) (fun e he => by
      obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
  have hR := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
    (G := del D x) (H := con C x) (x := x)
    (fun e he => (mem_filter.1 he).2) (fun e he => by
      obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
  exact ⟨hL.1 hsplit.1, hR.1 hsplit.2⟩

/-- One step of FK-A (modified) at a dual node with both sides of size at least 2. -/
theorem fkA_split {fuel : ℕ} {C D : HG n} (sC : IsSperner C) (sD : IsSperner D)
    (h : Dual univ C D) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) {x : Fin n}
    (hx : splitVar C D = some x) :
    (fkA (fuel + 1) true C D).2 =
      1 + (fkA fuel true (del C x) (con D x)).2 + (fkA fuel true (del D x) (con C x)).2 := by
  have hl : (fkA fuel true (del C x) (con D x)).1 = true := by
    rw [fkA_correct]; exact decide_eq_true (dual_children h x).1
  have hsize : ¬ (C.card * D.card ≤ 1) := by nlinarith
  simp [fkA, minimal_eq_self sC, minimal_eq_self sD, conds_of_dual sC sD h, hx, hl, hsize,
    show C.card ≠ 1 by omega, show D.card ≠ 1 by omega]

theorem fkADag_split {fuel : ℕ} {C D : HG n} (sC : IsSperner C) (sD : IsSperner D)
    (h : Dual univ C D) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) {x : Fin n}
    (hx : splitVar C D = some x) :
    fkADag (fuel + 1) true C D =
      insert (C, D) (fkADag fuel true (del C x) (con D x) ∪
        fkADag fuel true (del D x) (con C x)) := by
  have hl : (fkA fuel true (del C x) (con D x)).1 = true := by
    rw [fkA_correct]; exact decide_eq_true (dual_children h x).1
  have hsize : ¬ (C.card * D.card ≤ 1) := by nlinarith
  simp [fkADag, minimal_eq_self sC, minimal_eq_self sD, conds_of_dual sC sD h, hx, hl, hsize,
    show C.card ≠ 1 by omega, show D.card ≠ 1 by omega]

/-- A dual node with a single edge on one side is a leaf of the modified FK-A. -/
theorem fkA_single {fuel : ℕ} {C D : HG n} (sC : IsSperner C) (sD : IsSperner D)
    (h : Dual univ C D) (hC : C.card = 1) :
    (fkA fuel true C D).2 = 1 ∧ fkADag fuel true C D = {(C, D)} := by
  cases fuel with
  | zero => simp [fkA, fkADag, minimal_eq_self sC, minimal_eq_self sD]
  | succ fuel =>
    simp [fkA, fkADag, minimal_eq_self sC, minimal_eq_self sD, conds_of_dual sC sD h, hC]

/-- A node whose reduced left side is empty is a leaf. -/
theorem fkA_empty {fuel : ℕ} {b : Bool} {C D : HG n} (hC : minimal C = ∅) :
    (fkA fuel b C D).2 = 1 ∧ fkADag fuel b C D = {(∅, minimal D)} := by
  cases fuel with
  | zero => simp [fkA, fkADag, hC]
  | succ fuel =>
    simp only [fkA, fkADag, hC, card_empty, zero_mul, zero_le, decide_true, Bool.true_or,
      ite_true]
    split_ifs <;> simp

/-! ### The split vertex -/

/-- The degree sum used by the split rule. -/
def key (C D : HG n) (x : Fin n) : ℕ := degree C x + degree D x

/-- The fold of `splitVar`, one step. -/
def splitStep (C D : HG n) (acc : Option (Fin n × ℕ)) (x : Fin n) : Option (Fin n × ℕ) :=
  let k := degree C x + degree D x
  if k = 0 then acc else
    match acc with
    | none => some (x, k)
    | some (y, k') => if k' < k then some (x, k) else some (y, k')

theorem splitVar_eq (C D : HG n) :
    splitVar C D = ((List.finRange n).foldl (splitStep C D) none).map Prod.fst := rfl

/-- The fold invariant: `none` while every key seen is `0`; otherwise a seen vertex with a
positive key no smaller than any key seen. -/
theorem splitStep_fold (C D : HG n) :
    ∀ (l : List (Fin n)) (acc : Option (Fin n × ℕ)),
      (acc = none → (∀ y ∈ l, key C D y = 0) → l.foldl (splitStep C D) acc = none) ∧
      ∀ z k, acc = some (z, k) → k = key C D z → 0 < k →
        ∃ z' k', l.foldl (splitStep C D) acc = some (z', k') ∧ k' = key C D z' ∧ 0 < k' ∧
          k ≤ k' ∧ ∀ y ∈ l, key C D y ≤ k' := by
  intro l
  induction l with
  | nil =>
    intro acc
    exact ⟨fun h _ => h, fun z k h hk hp => ⟨z, k, h, hk, hp, le_rfl, by simp⟩⟩
  | cons a l ih =>
    intro acc
    refine ⟨fun hacc hl => ?_, fun z k hacc hk hp => ?_⟩
    · subst hacc
      have ha := hl a (List.mem_cons_self ..)
      simp only [List.foldl_cons, splitStep, key] at ha ⊢
      rw [if_pos ha]
      exact (ih none).1 rfl fun y hy => hl y (List.mem_cons_of_mem a hy)
    · subst hacc
      simp only [List.foldl_cons]
      by_cases ha : key C D a ≤ k
      · have hstep : splitStep C D (some (z, k)) a = some (z, k) := by
          simp only [splitStep]
          split_ifs with h1 h2
          · rfl
          · exact absurd ha (by unfold key; omega)
          · rfl
        rw [hstep]
        obtain ⟨z', k', h1, h2, h3, h4, h5⟩ := (ih (some (z, k))).2 z k rfl hk hp
        refine ⟨z', k', h1, h2, h3, h4, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · exact h5 y hy
      · have hstep : splitStep C D (some (z, k)) a = some (a, key C D a) := by
          simp only [splitStep, key] at ha ⊢
          rw [if_neg (by omega), if_pos (by omega)]
        rw [hstep]
        obtain ⟨z', k', h1, h2, h3, h4, h5⟩ :=
          (ih (some (a, key C D a))).2 a _ rfl rfl (by omega)
        refine ⟨z', k', h1, h2, h3, by omega, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h4
        · exact h5 y hy

/-- If some vertex has a positive degree sum, `splitVar` returns a vertex of largest degree
sum. -/
theorem splitVar_spec (C D : HG n) {y₀ : Fin n} (hy₀ : 0 < key C D y₀) :
    ∃ x, splitVar C D = some x ∧ 0 < key C D x ∧ ∀ y, key C D y ≤ key C D x := by
  -- split the fold at the first vertex with a positive key
  have main : ∀ (l : List (Fin n)) (acc : Option (Fin n × ℕ)),
      (∃ y ∈ l, 0 < key C D y) →
      (acc = none ∨ ∃ z k, acc = some (z, k) ∧ k = key C D z ∧ 0 < k) →
      ∃ z' k', l.foldl (splitStep C D) acc = some (z', k') ∧ k' = key C D z' ∧ 0 < k' ∧
        ∀ y ∈ l, key C D y ≤ k' := by
    intro l
    induction l with
    | nil => intro _ ⟨y, hy, _⟩; simp at hy
    | cons a l ih =>
      intro acc ⟨y, hy, hpos⟩ hacc
      rcases hacc with rfl | ⟨z, k, rfl, hk, hp⟩
      · by_cases ha : key C D a = 0
        · have hstep : splitStep C D none a = none := by
            simp only [splitStep]; rw [if_pos (show degree C a + degree D a = 0 from ha)]
          simp only [List.foldl_cons, hstep]
          rcases List.mem_cons.1 hy with rfl | hy
          · omega
          · obtain ⟨z', k', h1, h2, h3, h4⟩ := ih none ⟨y, hy, hpos⟩ (Or.inl rfl)
            exact ⟨z', k', h1, h2, h3, fun w hw => by
              rcases List.mem_cons.1 hw with rfl | hw
              · omega
              · exact h4 w hw⟩
        · have hstep : splitStep C D none a = some (a, key C D a) := by
            simp only [splitStep]; rw [if_neg (show ¬ degree C a + degree D a = 0 from ha)]; rfl
          simp only [List.foldl_cons, hstep]
          obtain ⟨z', k', h1, h2, h3, h4, h5⟩ :=
            (splitStep_fold C D l _).2 a _ rfl rfl (by omega)
          exact ⟨z', k', h1, h2, h3, fun w hw => by
            rcases List.mem_cons.1 hw with rfl | hw
            · exact h4
            · exact h5 w hw⟩
      · obtain ⟨z', k', h1, h2, h3, h4, h5⟩ :=
          (splitStep_fold C D (a :: l) _).2 z k rfl hk hp
        exact ⟨z', k', h1, h2, h3, h5⟩
  obtain ⟨z, k, h1, h2, h3, h4⟩ :=
    main (List.finRange n) none ⟨y₀, List.mem_finRange y₀, hy₀⟩ (Or.inl rfl)
  refine ⟨z, by rw [splitVar_eq, h1]; rfl, h2 ▸ h3, fun y => h2 ▸ h4 y (List.mem_finRange y)⟩

/-! ### Transversals of the children -/

section Tr

variable {α : Type*} [DecidableEq α] {U : Finset α}

theorem hits_con_iff {G : Finset (Finset α)} {x : α} {T : Finset α} (hx : x ∉ T) :
    Hits (con G x) T ↔ Hits G T := by
  constructor
  · intro h e he
    obtain ⟨y, hy⟩ := h _ (mem_image_of_mem _ he)
    rw [mem_inter] at hy
    exact ⟨y, mem_inter.2 ⟨hy.1, mem_of_mem_erase hy.2⟩⟩
  · intro h e he
    obtain ⟨f, hf, rfl⟩ := mem_image.1 he
    obtain ⟨y, hy⟩ := h f hf
    rw [mem_inter] at hy
    exact ⟨y, mem_inter.2 ⟨hy.1, mem_erase.2 ⟨fun h => hx (h ▸ hy.1), hy.2⟩⟩⟩

/-- A vertex in no edge lies in no minimal transversal. -/
theorem notMem_of_isMinHit {G : Finset (Finset α)} {x : α} (hx : ∀ e ∈ G, x ∉ e) {T : Finset α}
    (hT : IsMinHit G T) : x ∉ T := by
  intro hxT
  refine hT.2 x hxT fun e he => ?_
  obtain ⟨y, hy⟩ := hT.1 e he
  rw [mem_inter] at hy
  exact ⟨y, mem_inter.2 ⟨mem_erase.2 ⟨fun h => hx e he (h ▸ hy.2), hy.1⟩, hy.2⟩⟩

/-- `Tr(G / x) = Tr(G) − x`: the minimal transversals of the contraction are those of `G`
avoiding `x`. -/
theorem tr_con_eq (G : Finset (Finset α)) (x : α) : tr U (con G x) = del (tr U G) x := by
  ext T
  simp only [mem_tr, del, mem_filter]
  constructor
  · rintro ⟨hTU, hT⟩
    have hx : x ∉ T := notMem_of_isMinHit (fun e he => by
      obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f) hT
    refine ⟨⟨hTU, (hits_con_iff hx).1 hT.1, fun v hv h => hT.2 v hv ?_⟩, hx⟩
    exact (hits_con_iff fun h' => hx (mem_of_mem_erase h')).2 h
  · rintro ⟨⟨hTU, hT⟩, hx⟩
    refine ⟨hTU, (hits_con_iff hx).2 hT.1, fun v hv h => hT.2 v hv ?_⟩
    exact (hits_con_iff fun h' => hx (mem_of_mem_erase h')).1 h

/-- `min(Tr(G) / x) = Tr(G − x)`. -/
theorem minimal_con_tr {G : Finset (Finset α)} (hG : Within U G) {x : α} (hxU : x ∈ U) :
    minimal (con (tr U G) x) = tr U (del G x) := by
  -- every `T − x` with `T ∈ Tr G` hits `G − x`
  have hA : ∀ S ∈ con (tr U G) x, Hits (del G x) S ∧ S ⊆ U := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hS
    refine ⟨fun e he => ?_, (erase_subset x T).trans (mem_tr.1 hT).1⟩
    rw [del, mem_filter] at he
    obtain ⟨y, hy⟩ := (mem_tr.1 hT).2.1 e he.1
    rw [mem_inter] at hy
    exact ⟨y, mem_inter.2 ⟨mem_erase.2 ⟨fun h => he.2 (h ▸ hy.2), hy.1⟩, hy.2⟩⟩
  -- every minimal transversal of `G − x` is some `T − x`
  have hB : ∀ S ∈ tr U (del G x), S ∈ con (tr U G) x := by
    intro S hS
    obtain ⟨hSU, hSm⟩ := mem_tr.1 hS
    have hxS : x ∉ S := notMem_of_isMinHit (fun e he => (mem_filter.1 he).2) hSm
    have hhit : Hits G (insert x S) := by
      intro e he
      by_cases hxe : x ∈ e
      · exact ⟨x, mem_inter.2 ⟨mem_insert_self x S, hxe⟩⟩
      · obtain ⟨y, hy⟩ := hSm.1 e (mem_filter.2 ⟨he, hxe⟩)
        rw [mem_inter] at hy
        exact ⟨y, mem_inter.2 ⟨mem_insert_of_mem hy.1, hy.2⟩⟩
    obtain ⟨T, hTsub, hT⟩ := exists_isMinHit_subset _ (insert x S) rfl hhit
    have hTU : T ⊆ U := hTsub.trans (insert_subset hxU hSU)
    have hTtr : T ∈ tr U G := mem_tr.2 ⟨hTU, hT⟩
    have hsub : T.erase x ⊆ S := fun y hy => by
      obtain ⟨hyx, hyT⟩ := mem_erase.1 hy
      rcases mem_insert.1 (hTsub hyT) with h | h
      · exact absurd h hyx
      · exact h
    have := (isMinHit_iff.1 hSm).2 _ hsub (hA _ (mem_image_of_mem _ hTtr)).1
    exact this ▸ mem_image_of_mem _ hTtr
  ext S
  rw [mem_minimal]
  constructor
  · rintro ⟨hS, hmin⟩
    obtain ⟨hhit, hSU⟩ := hA S hS
    obtain ⟨S', hS'S, hS'⟩ := exists_isMinHit_subset _ S rfl hhit
    have hS'tr : S' ∈ tr U (del G x) := mem_tr.2 ⟨hS'S.trans hSU, hS'⟩
    have := hmin S' (hB S' hS'tr) hS'S
    exact this ▸ hS'tr
  · intro hS
    refine ⟨hB S hS, fun S' hS' hS'S => ?_⟩
    obtain ⟨hhit, hS'U⟩ := hA S' hS'
    obtain ⟨S'', hS''S', hS''⟩ := exists_isMinHit_subset _ S' rfl hhit
    have h1 := tr_isSperner U (del G x) S'' (mem_tr.2 ⟨hS''S'.trans hS'U, hS''⟩) S hS
      (hS''S'.trans hS'S)
    exact le_antisymm hS'S (h1 ▸ hS''S')

end Tr

/-! ### Every subproblem lives on the root's vertices -/

theorem within_minimal {α : Type*} [DecidableEq α] {V : Finset α} {H : Finset (Finset α)}
    (h : Within V H) : Within V (minimal H) := fun e he => h e (minimal_subset H he)

theorem within_del {α : Type*} [DecidableEq α] {V : Finset α} {H : Finset (Finset α)}
    (h : Within V H) (x : α) : Within V (del H x) := fun e he => h e (mem_filter.1 he).1

theorem within_con {α : Type*} [DecidableEq α] {V : Finset α} {H : Finset (Finset α)}
    (h : Within V H) (x : α) : Within V (con H x) := fun e he => by
  obtain ⟨f, hf, rfl⟩ := mem_image.1 he
  exact (erase_subset x f).trans (h f hf)

theorem fkADag_within {V : Finset (Fin n)} :
    ∀ (fuel : ℕ) (b : Bool) (C D : HG n), Within V C → Within V D →
      ∀ p ∈ fkADag fuel b C D, Within V p.1 ∧ Within V p.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro b C D hC hD p hp
    simp only [fkADag, mem_singleton] at hp
    subst hp
    exact ⟨within_minimal hC, within_minimal hD⟩
  | succ fuel ih =>
    intro b C D hC hD p hp
    have hC' := within_minimal hC
    have hD' := within_minimal hD
    simp only [fkADag] at hp
    split_ifs at hp
    · rw [mem_singleton] at hp; subst hp; exact ⟨hC', hD'⟩
    · rw [mem_singleton] at hp; subst hp; exact ⟨hC', hD'⟩
    · split at hp
      · rw [mem_singleton] at hp; subst hp; exact ⟨hC', hD'⟩
      · rename_i x _
        split_ifs at hp
        · rcases mem_insert.1 hp with rfl | hp
          · exact ⟨hC', hD'⟩
          rcases mem_union.1 hp with hp | hp
          · exact ih b _ _ (within_del hC' x) (within_con hD' x) p hp
          · exact ih b _ _ (within_del hD' x) (within_con hC' x) p hp
        · rcases mem_insert.1 hp with rfl | hp
          · exact ⟨hC', hD'⟩
          · exact ih b _ _ (within_del hC' x) (within_con hD' x) p hp

/-! ### Facts about transversals used by the families -/

theorem dual_tr (C : HG n) : Dual univ C (tr univ C) :=
  dual_comm.1 ((dual_iff_minimal_eq_tr (within_univ _) (within_univ C)).2
    (minimal_eq_self (tr_isSperner univ C)))

theorem degree_pos_iff {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {v : α} :
    0 < degree H v ↔ ∃ e ∈ H, v ∈ e := by
  simp [degree, card_pos, Finset.Nonempty]

/-- If every edge through `a` also contains `b ≠ a`, no minimal transversal contains both. -/
theorem not_both_of_isMinHit {α : Type*} [DecidableEq α] {G : Finset (Finset α)} {a b : α}
    (hab : a ≠ b) (h : ∀ e ∈ G, a ∈ e → b ∈ e) {T : Finset α} (hT : IsMinHit G T)
    (ha : a ∈ T) : b ∉ T := by
  intro hb
  refine hT.2 a ha fun e he => ?_
  by_cases hae : a ∈ e
  · exact ⟨b, mem_inter.2 ⟨mem_erase.2 ⟨hab.symm, hb⟩, h e he hae⟩⟩
  · obtain ⟨y, hy⟩ := hT.1 e he
    rw [mem_inter] at hy
    exact ⟨y, mem_inter.2 ⟨mem_erase.2 ⟨fun h => hae (h ▸ hy.2), hy.1⟩, hy.2⟩⟩

/-- A vertex of an edge of a Sperner family lies in some minimal transversal. -/
theorem exists_tr_mem {G : HG n} (sG : IsSperner G) {v : Fin n} {e : Finset (Fin n)}
    (he : e ∈ G) (hv : v ∈ e) : ∃ T ∈ tr univ G, v ∈ T := by
  have := support_eq (within_univ G) sG rfl
  have hv' : v ∈ support G := mem_biUnion.2 ⟨e, he, hv⟩
  rw [this] at hv'
  obtain ⟨T, hT, hvT⟩ := mem_biUnion.1 hv'
  exact ⟨T, hT, hvT⟩

/-- A minimal transversal through `v` puts `v` in an edge. -/
theorem exists_edge_of_mem_tr {G : HG n} {v : Fin n} {T : Finset (Fin n)} (hT : T ∈ tr univ G)
    (hv : v ∈ T) : ∃ e ∈ G, v ∈ e := by
  by_contra h
  push Not at h
  exact notMem_of_isMinHit h (mem_tr.1 hT).2 hv

/-! ### The matching family -/

/-- The pair `{2k, 2k+1}` of `Fin n`. -/
def blk (k : ℕ) : Finset (Fin n) := univ.filter fun z => z.val / 2 = k

@[simp] theorem mem_blk {k : ℕ} {z : Fin n} : z ∈ blk k ↔ z.val / 2 = k := by simp [blk]

/-- The perfect matching on the pairs indexed by `S`. -/
def matchS (S : Finset ℕ) : HG n := S.image blk

/-- The pairs indexed by `S` lie inside `Fin n`. -/
def Fits (n : ℕ) (S : Finset ℕ) : Prop := ∀ i ∈ S, 2 * i + 1 < n

section Matching

variable {S : Finset ℕ}

def lo (i : ℕ) (h : 2 * i + 1 < n) : Fin n := ⟨2 * i, by omega⟩
def hi (i : ℕ) (h : 2 * i + 1 < n) : Fin n := ⟨2 * i + 1, h⟩

theorem lo_mem {i : ℕ} (h : 2 * i + 1 < n) : lo i h ∈ (blk i : Finset (Fin n)) := by
  simp only [lo, mem_blk]; omega
theorem hi_mem {i : ℕ} (h : 2 * i + 1 < n) : hi i h ∈ (blk i : Finset (Fin n)) := by
  simp only [hi, mem_blk]; omega

theorem blk_nonempty {i : ℕ} (h : 2 * i + 1 < n) : (blk i : Finset (Fin n)).Nonempty :=
  ⟨_, lo_mem h⟩

theorem blk_injOn (hS : Fits n S) : Set.InjOn (blk (n := n)) S := by
  intro i hi j hj hij
  obtain ⟨z, hz⟩ := blk_nonempty (hS i hi)
  have := hz
  rw [hij, mem_blk] at this
  rw [mem_blk] at hz
  omega

theorem card_matchS (hS : Fits n S) : (matchS (n := n) S).card = S.card :=
  card_image_of_injOn (blk_injOn hS)

theorem mem_matchS {e : Finset (Fin n)} : e ∈ matchS S ↔ ∃ i ∈ S, blk i = e := by
  simp [matchS]

theorem matchS_sperner (hS : Fits n S) : IsSperner (matchS (n := n) S) := by
  intro e he f hf hef
  obtain ⟨i, hi, rfl⟩ := mem_matchS.1 he
  obtain ⟨j, hj, rfl⟩ := mem_matchS.1 hf
  obtain ⟨z, hz⟩ := blk_nonempty (hS i hi)
  have h1 := hz
  have h2 := hef hz
  rw [mem_blk] at h1 h2
  rw [show i = j by omega]

/-- The other point of the pair of `x`. -/
def mate (x : Fin n) (h : x.val / 2 * 2 + 1 < n) : Fin n :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by split_ifs <;> omega⟩

theorem blk_erase {x : Fin n} (h : x.val / 2 * 2 + 1 < n) :
    (blk (x.val / 2) : Finset (Fin n)).erase x = {mate x h} := by
  ext z
  simp only [mem_erase, mem_blk, mem_singleton, mate, Fin.ext_iff]
  split_ifs <;> omega

theorem mate_ne (x : Fin n) (h : x.val / 2 * 2 + 1 < n) : mate x h ≠ x := by
  simp only [mate, ne_eq, Fin.ext_iff]; split_ifs <;> omega

theorem mate_div (x : Fin n) (h : x.val / 2 * 2 + 1 < n) : (mate x h).val / 2 = x.val / 2 := by
  simp only [mate]; split_ifs <;> omega

theorem del_matchS {x : Fin n} : del (matchS (n := n) S) x = matchS (S.erase (x.val / 2)) := by
  ext e
  simp only [del, mem_filter, mem_matchS, mem_erase]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, ⟨fun h => hx (by rw [mem_blk]; omega), hi⟩, rfl⟩
  · rintro ⟨i, ⟨hne, hi⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, fun h => hne (by rw [mem_blk] at h; omega)⟩

theorem con_matchS {x : Fin n} (hS : Fits n S) (hx : x.val / 2 ∈ S) :
    con (matchS (n := n) S) x =
      insert {mate x (by have := hS _ hx; omega)} (matchS (S.erase (x.val / 2))) := by
  have hfit : x.val / 2 * 2 + 1 < n := by have := hS _ hx; omega
  ext e
  simp only [con, matchS, mem_image, mem_insert, mem_erase]
  constructor
  · rintro ⟨f, ⟨i, hi, rfl⟩, rfl⟩
    by_cases hix : i = x.val / 2
    · subst hix; exact Or.inl (blk_erase hfit)
    · refine Or.inr ⟨i, ⟨hix, hi⟩, ?_⟩
      rw [erase_eq_of_notMem (by rw [mem_blk]; omega)]
  · rintro (rfl | ⟨i, ⟨hix, hi⟩, rfl⟩)
    · exact ⟨blk (x.val / 2), ⟨_, hx, rfl⟩, blk_erase hfit⟩
    · refine ⟨blk i, ⟨i, hi, rfl⟩, ?_⟩
      rw [erase_eq_of_notMem (by rw [mem_blk]; omega)]

end Matching

theorem minimal_of_empty_mem {α : Type*} [DecidableEq α] {H : Finset (Finset α)} (h : ∅ ∈ H) :
    minimal H = {∅} := by
  ext e
  rw [mem_minimal, mem_singleton]
  constructor
  · rintro ⟨_, hmin⟩; exact (hmin ∅ h (empty_subset e)).symm
  · rintro rfl; exact ⟨h, fun f _ hf => subset_empty.1 hf⟩

/-- A Sperner family with two points `a ≠ b` that lie in exactly the same edges, one of which
exists, has at least two minimal transversals. -/
theorem two_le_card_tr {G : HG n} (sG : IsSperner G) {e : Finset (Fin n)} (he : e ∈ G)
    {a b : Fin n} (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) (h₁ : ∀ f ∈ G, a ∈ f → b ∈ f) :
    2 ≤ (tr univ G).card := by
  obtain ⟨T, hT, haT⟩ := exists_tr_mem sG he ha
  obtain ⟨T', hT', hbT'⟩ := exists_tr_mem sG he hb
  have hbT : b ∉ T := not_both_of_isMinHit hab h₁ (mem_tr.1 hT).2 haT
  exact one_lt_card.2 ⟨T, hT, T', hT', fun h => hbT (h ▸ hbT')⟩

section Matching

variable {S : Finset ℕ}

theorem fits_erase (hS : Fits n S) (i : ℕ) : Fits n (S.erase i) :=
  fun j hj => hS j (mem_of_mem_erase hj)

theorem lo_ne_hi {i : ℕ} (h : 2 * i + 1 < n) : lo i h ≠ hi i h := by
  simp [lo, hi, Fin.ext_iff]

/-- Edges of a matching through a point of the pair `i` are that pair. -/
theorem matchS_edge {e : Finset (Fin n)} (he : e ∈ matchS (n := n) S) {z : Fin n} (hz : z ∈ e) :
    e = blk (z.val / 2) := by
  obtain ⟨j, -, rfl⟩ := mem_matchS.1 he
  rw [mem_blk] at hz
  rw [hz]

theorem two_le_card_tr_matchS (hS : Fits n S) {j : ℕ} (hj : j ∈ S) :
    2 ≤ (tr univ (matchS (n := n) S)).card := by
  have h := hS j hj
  refine two_le_card_tr (matchS_sperner hS) (mem_matchS.2 ⟨j, hj, rfl⟩) (lo_mem h) (hi_mem h)
    (lo_ne_hi h) fun f hf hlo => ?_
  rw [matchS_edge hf hlo]
  have := hi_mem h
  simp only [mem_blk, lo] at this ⊢
  omega

/-- The family `Q = {{y}} ∪ M(S')` of the right child, `y` outside the pairs of `S'`. -/
abbrev Qf (y : Fin n) (S' : Finset ℕ) : HG n := insert {y} (matchS S')

theorem Qf_sperner {y : Fin n} {S' : Finset ℕ} (hS : Fits n S') (hy : y.val / 2 ∉ S') :
    IsSperner (Qf y S') := by
  intro e he f hf hef
  rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
  · rfl
  · obtain ⟨j, hj, rfl⟩ := mem_matchS.1 hf
    have := hef (mem_singleton_self y)
    rw [mem_blk] at this
    exact absurd (this ▸ hj) hy
  · obtain ⟨j, hj, rfl⟩ := mem_matchS.1 he
    have h := hS j hj
    exact absurd ((subset_singleton_iff'.1 hef _ (lo_mem h)).trans
      (subset_singleton_iff'.1 hef _ (hi_mem h)).symm) (lo_ne_hi h)
  · exact matchS_sperner hS e he f hf hef

end Matching

section Matching

variable {S : Finset ℕ}

theorem del_Qf {y : Fin n} {S' : Finset ℕ} (hy : y.val / 2 ∉ S') :
    del (Qf y S') y = matchS S' := by
  ext e
  simp only [del, mem_filter, mem_insert]
  constructor
  · rintro ⟨rfl | he, hye⟩
    · exact absurd (mem_singleton_self y) hye
    · exact he
  · intro he
    refine ⟨Or.inr he, fun hye => hy ?_⟩
    obtain ⟨j, hj, rfl⟩ := mem_matchS.1 he
    rw [mem_blk] at hye
    exact hye ▸ hj

/-- **The right child.** At `(Tr Q, Q)`, `Q = {{y}} ∪ M(S')`, FK-A splits on `y`; its left child is
the leaf `(∅, {∅})` and its right child is `(M(S'), Tr M(S'))`. -/
theorem rnode {y : Fin n} {S' : Finset ℕ} (hS : Fits n S') (hy : y.val / 2 ∉ S')
    (hne : S'.Nonempty) (g : ℕ) :
    (fkA (g + 1) true (tr univ (Qf y S')) (Qf y S')).2 =
        2 + (fkA g true (matchS (n := n) S') (tr univ (matchS S'))).2 ∧
      fkADag (g + 1) true (tr univ (Qf y S')) (Qf y S') =
        insert (tr univ (Qf y S'), Qf y S')
          (insert ((∅ : HG n), ({∅} : HG n))
            (fkADag g true (matchS (n := n) S') (tr univ (matchS S')))) := by
  set Q := Qf y S'
  have sQ : IsSperner Q := Qf_sperner hS hy
  have sT := tr_isSperner univ Q
  have hd : Dual univ (tr univ Q) Q := dual_comm.1 (dual_tr Q)
  obtain ⟨j, hj⟩ := hne
  have hfj := hS j hj
  have hbj : blk j ∈ Q := mem_insert_of_mem (mem_matchS.2 ⟨j, hj, rfl⟩)
  have hyQ : ∀ T ∈ tr univ Q, y ∈ T := fun T hT => by
    obtain ⟨z, hz⟩ := (mem_tr.1 hT).2.1 {y} (mem_insert_self _ _)
    rw [mem_inter, mem_singleton] at hz
    exact hz.2 ▸ hz.1
  have hy_ne : ∀ {z : Fin n} {f : Finset (Fin n)}, f ∈ matchS S' → z ∈ f → z ≠ y := by
    intro z f hf hz hzy
    obtain ⟨i, hi, rfl⟩ := mem_matchS.1 hf
    rw [mem_blk] at hz
    exact hy (hzy ▸ hz ▸ hi)
  have hcardQ : 2 ≤ Q.card := by
    refine one_lt_card.2 ⟨{y}, mem_insert_self _ _, blk j, hbj, fun h => ?_⟩
    have h1 := lo_mem hfj
    have h2 := hi_mem hfj
    rw [← h, mem_singleton] at h1 h2
    exact lo_ne_hi hfj (h1.trans h2.symm)
  have hcardT : 2 ≤ (tr univ Q).card := by
    refine two_le_card_tr sQ hbj (lo_mem hfj) (hi_mem hfj) (lo_ne_hi hfj) fun f hf hlo => ?_
    rcases mem_insert.1 hf with rfl | hf
    · exact absurd (mem_singleton.1 hlo) (hy_ne (mem_matchS.2 ⟨j, hj, rfl⟩) (lo_mem hfj))
    · rw [matchS_edge hf hlo]
      have := hi_mem hfj
      simp only [mem_blk, lo] at this ⊢
      omega
  -- the split vertex is `y`
  have hkey_y : (tr univ Q).card + 1 ≤ key (tr univ Q) Q y := by
    have h1 : degree (tr univ Q) y = (tr univ Q).card := by
      rw [degree, filter_true_of_mem hyQ]
    have h2 : 0 < degree Q y := degree_pos_iff.2 ⟨{y}, mem_insert_self _ _, mem_singleton_self y⟩
    unfold key; omega
  have hkey_z : ∀ z, z ≠ y → key (tr univ Q) Q z ≤ (tr univ Q).card := by
    intro z hzy
    by_cases hz : ∃ e ∈ Q, z ∈ e
    · obtain ⟨e, he, hze⟩ := hz
      rcases mem_insert.1 he with rfl | he
      · exact absurd (mem_singleton.1 hze) hzy
      obtain ⟨i, hi, rfl⟩ := mem_matchS.1 he
      have hzi : z.val / 2 = i := mem_blk.1 hze
      have hfi : z.val / 2 * 2 + 1 < n := by have := hS i hi; omega
      have hQz : Q.filter (z ∈ ·) ⊆ {blk i} := by
        intro f hf
        rw [mem_filter] at hf
        rw [mem_singleton]
        rcases mem_insert.1 hf.1 with rfl | hf'
        · exact absurd (mem_singleton.1 hf.2) hzy
        · rw [matchS_edge hf' hf.2, hzi]
      have hdQ : degree Q z ≤ 1 := (card_le_card hQz).trans (card_singleton _).le
      have hmate : mate z hfi ∈ blk i := by rw [mem_blk, mate_div, hzi]
      obtain ⟨T, hT, hmT⟩ := exists_tr_mem sQ (mem_insert_of_mem he) hmate
      have hzT : z ∉ T := by
        refine not_both_of_isMinHit (mate_ne z hfi) (fun f hf hmf => ?_) (mem_tr.1 hT).2 hmT
        rcases mem_insert.1 hf with rfl | hf
        · have hmy : mate z hfi = y := mem_singleton.1 hmf
          exact absurd (by rw [← hmy, mate_div, hzi]; exact hi) hy
        · rw [matchS_edge hf hmf, mate_div]; exact mem_blk.2 rfl
      have hdT : degree (tr univ Q) z < (tr univ Q).card :=
        card_lt_card ⟨filter_subset _ _, fun h => hzT (mem_filter.1 (h hT)).2⟩
      unfold key; omega
    · push Not at hz
      have h1 : degree Q z = 0 := by
        rw [degree, card_eq_zero, filter_eq_empty_iff]; exact fun f hf => hz f hf
      have h2 : degree (tr univ Q) z = 0 := by
        rw [degree, card_eq_zero, filter_eq_empty_iff]
        intro T hT hzT
        obtain ⟨e, he, hze⟩ := exists_edge_of_mem_tr hT hzT
        exact hz e he hze
      unfold key; omega
  obtain ⟨x', hx', -, hmax⟩ := splitVar_spec (tr univ Q) Q (y₀ := y) (by omega)
  have hxy : x' = y := by
    by_contra h
    have := hmax y
    have := hkey_z x' h
    omega
  subst hxy
  -- the two children
  have hL : minimal (del (tr univ Q) x') = ∅ := by
    rw [show del (tr univ Q) x' = ∅ from filter_eq_empty_iff.2 fun T hT h => h (hyQ T hT)]
    rfl
  have hLD : minimal (con Q x') = {∅} :=
    minimal_of_empty_mem (mem_image.2 ⟨{x'}, mem_insert_self _ _, erase_singleton x'⟩)
  obtain ⟨hL1, hL2⟩ := fkA_empty (fuel := g) (b := true) (D := con Q x') hL
  have hR : fkA g true (del Q x') (con (tr univ Q) x') =
      fkA g true (matchS (n := n) S') (tr univ (matchS S')) := by
    rw [← fkA_minimal, minimal_con_tr (within_univ Q) (mem_univ x'), del_Qf hy,
      minimal_eq_self (matchS_sperner hS)]
  have hRD : fkADag g true (del Q x') (con (tr univ Q) x') =
      fkADag g true (matchS (n := n) S') (tr univ (matchS S')) := by
    rw [← fkADag_minimal, minimal_con_tr (within_univ Q) (mem_univ x'), del_Qf hy,
      minimal_eq_self (matchS_sperner hS)]
  refine ⟨?_, ?_⟩
  · rw [fkA_split sT sQ hd hcardT hcardQ hx', hL1, hR]
  · rw [fkADag_split sT sQ hd hcardT hcardQ hx', hL2, hLD, hRD, ← insert_eq]

end Matching

theorem root_mem_fkADag (fuel : ℕ) (b : Bool) (C D : HG n) :
    (minimal C, minimal D) ∈ fkADag fuel b C D := by
  cases fuel with
  | zero => simp [fkADag]
  | succ f =>
    simp only [fkADag]
    split_ifs
    · exact mem_singleton_self _
    · exact mem_singleton_self _
    · split
      · exact mem_singleton_self _
      · split_ifs <;> exact mem_insert_self _ _

section Matching

/-- The vertices of the pairs indexed by `S`. -/
def verts (S : Finset ℕ) : Finset (Fin n) := univ.filter fun z => z.val / 2 ∈ S

theorem matchS_within (S : Finset ℕ) : Within (verts S) (matchS (n := n) S) := by
  intro e he z hz
  obtain ⟨i, hi, rfl⟩ := mem_matchS.1 he
  rw [mem_blk] at hz
  simp [verts, hz, hi]

theorem tr_matchS_within (S : Finset ℕ) : Within (verts S) (tr univ (matchS (n := n) S)) := by
  intro T hT z hz
  obtain ⟨e, he, hze⟩ := exists_edge_of_mem_tr hT hz
  exact matchS_within S e he hze

/-- **Theorem C1 (matching).** Let `S` index `k + 1` disjoint pairs. With fuel at least
`2k + 1`, modified FK-A on `(M(S), Tr M(S))` has `2^(k+2) − 3` nodes and `1` (if `k = 0`) or
`2(k+1)` distinct subproblems, and the subproblem set does not depend on the fuel. -/
theorem matching_law : ∀ (k : ℕ) (S : Finset ℕ), S.card = k + 1 → Fits n S →
    ∀ fuel, 2 * k + 1 ≤ fuel →
      (fkA fuel true (matchS (n := n) S) (tr univ (matchS S))).2 = 2 ^ (k + 2) - 3 ∧
      (fkADag fuel true (matchS (n := n) S) (tr univ (matchS S))).card =
        (if k = 0 then 1 else 2 * (k + 1)) ∧
      (k ≠ 0 → ((∅ : HG n), ({∅} : HG n)) ∈
        fkADag fuel true (matchS (n := n) S) (tr univ (matchS S))) ∧
      fkADag fuel true (matchS (n := n) S) (tr univ (matchS S)) =
        fkADag (2 * k + 1) true (matchS (n := n) S) (tr univ (matchS S))
  | 0, S, hc, hS, fuel, _ => by
    have h1 : (matchS (n := n) S).card = 1 := by rw [card_matchS hS, hc]
    obtain ⟨a, b⟩ := fkA_single (fuel := fuel) (matchS_sperner hS) (tr_isSperner _ _)
      (dual_tr _) h1
    obtain ⟨-, b'⟩ := fkA_single (fuel := 1) (matchS_sperner hS) (tr_isSperner _ _)
      (dual_tr _) h1
    refine ⟨by rw [a]; rfl, by rw [b, card_singleton]; rfl, fun h => absurd rfl h, by rw [b, b']⟩
  | k + 1, S, hc, hS, fuel, hf => by
    set C := matchS (n := n) S with hCdef
    have sC := matchS_sperner (n := n) hS
    have hd := dual_tr C
    have hCc : 2 ≤ C.card := by rw [card_matchS hS, hc]; omega
    obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
    have hDc : 2 ≤ (tr univ C).card := two_le_card_tr_matchS hS hj
    have hpos : 0 < key C (tr univ C) (lo j (hS j hj)) := by
      have : 0 < degree C (lo j (hS j hj)) :=
        degree_pos_iff.2 ⟨blk j, mem_matchS.2 ⟨j, hj, rfl⟩, lo_mem _⟩
      unfold key; omega
    obtain ⟨x, hx, hxpos, -⟩ := splitVar_spec C (tr univ C) hpos
    have hxS : x.val / 2 ∈ S := by
      have : ∃ e ∈ C, x ∈ e := by
        unfold key at hxpos
        rcases Nat.eq_zero_or_pos (degree C x) with h0 | h0
        · obtain ⟨T, hT, hxT⟩ := degree_pos_iff.1 (show 0 < degree (tr univ C) x by omega)
          exact exists_edge_of_mem_tr hT hxT
        · exact degree_pos_iff.1 h0
      obtain ⟨e, he, hxe⟩ := this
      obtain ⟨i, hi, rfl⟩ := mem_matchS.1 he
      rw [mem_blk] at hxe
      rw [hxe]; exact hi
    set S' := S.erase (x.val / 2) with hS'def
    have hS' : Fits n S' := fits_erase hS _
    have hc' : S'.card = k + 1 := by rw [card_erase_of_mem hxS, hc]; rfl
    have hne' : S'.Nonempty := card_pos.1 (by omega)
    have hfit : x.val / 2 * 2 + 1 < n := by have := hS _ hxS; omega
    set y := mate x hfit
    have hy : y.val / 2 ∉ S' := by rw [mate_div]; exact notMem_erase _ _
    have hRC : con C x = Qf y S' := con_matchS hS hxS
    have hLeq : ∀ g, fkA g true (del C x) (con (tr univ C) x) =
        fkA g true (matchS S') (tr univ (matchS S')) := fun g => by
      rw [← fkA_minimal, minimal_con_tr (within_univ C) (mem_univ x), hCdef, del_matchS,
        minimal_eq_self (matchS_sperner hS')]
    have hLeqD : ∀ g, fkADag g true (del C x) (con (tr univ C) x) =
        fkADag g true (matchS S') (tr univ (matchS S')) := fun g => by
      rw [← fkADag_minimal, minimal_con_tr (within_univ C) (mem_univ x), hCdef, del_matchS,
        minimal_eq_self (matchS_sperner hS')]
    have hReq : del (tr univ C) x = tr univ (Qf y S') := by rw [← tr_con_eq, hRC]
    -- the DAG at any sufficient fuel
    set c : HG n × HG n := (∅, {∅}) with hcdef
    set D' := fkADag (2 * k + 1) true (matchS (n := n) S') (tr univ (matchS S')) with hD'def
    have hform : ∀ fuel', 2 * (k + 1) + 1 ≤ fuel' →
        fkADag fuel' true C (tr univ C) =
          insert (C, tr univ C) (insert (tr univ (Qf y S'), Qf y S') (insert c D')) := by
      intro fuel' hf'
      obtain ⟨g, rfl⟩ : ∃ g, fuel' = g + 2 := ⟨fuel' - 2, by omega⟩
      have e1 := (matching_law k S' hc' hS' (g + 1) (by omega)).2.2.2
      have e2 := (matching_law k S' hc' hS' g (by omega)).2.2.2
      rw [fkADag_split sC (tr_isSperner _ _) hd hCc hDc hx, hLeqD, hReq, hRC,
        (rnode hS' hy hne' g).2, e1, e2]
      ext p
      simp only [mem_insert, mem_union]
      tauto
    -- distinctness of the new subproblems
    have hD'w : ∀ p ∈ D', Within (verts S') p.1 ∧ Within (verts S') p.2 :=
      fkADag_within _ _ _ _ (matchS_within S') (tr_matchS_within S')
    have hxV : x ∉ (verts S' : Finset (Fin n)) := by simp [verts, S']
    have hbi : blk (x.val / 2) ∈ C := mem_matchS.2 ⟨_, hxS, rfl⟩
    have hxb : x ∈ (blk (x.val / 2) : Finset (Fin n)) := mem_blk.2 rfl
    have hroot : (C, tr univ C) ∉ insert (tr univ (Qf y S'), Qf y S') (insert c D') := by
      simp only [mem_insert, not_or]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have h1 : C = tr univ (Qf y S') := congrArg Prod.fst h
        have : blk (x.val / 2) ∈ tr univ (Qf y S') := h1 ▸ hbi
        obtain ⟨e, he, hxe⟩ := exists_edge_of_mem_tr this hxb
        rcases mem_insert.1 he with rfl | he
        · exact mate_ne x hfit (mem_singleton.1 hxe).symm
        · obtain ⟨i, hi, rfl⟩ := mem_matchS.1 he
          rw [mem_blk] at hxe
          exact notMem_erase _ _ (hxe ▸ hi : x.val / 2 ∈ S')
      · have h1 : C = ∅ := congrArg Prod.fst h
        rw [h1] at hbi; exact notMem_empty _ hbi
      · exact hxV ((hD'w _ h).1 _ hbi hxb)
    have hR : (tr univ (Qf y S'), Qf y S') ∉ insert c D' := by
      simp only [mem_insert, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h2 : Qf y S' = {∅} := congrArg Prod.snd h
        have : ({y} : Finset (Fin n)) ∈ ({∅} : HG n) := h2 ▸ mem_insert_self _ _
        exact singleton_ne_empty y (mem_singleton.1 this)
      · have := (hD'w _ h).2 {y} (mem_insert_self _ _) (mem_singleton_self y)
        simp only [verts, mem_filter, mem_univ, true_and] at this
        exact hy this
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by omega⟩
    have ihL := matching_law k S' hc' hS' (g + 1) (by omega)
    have ihR := matching_law k S' hc' hS' g (by omega)
    have ihD := matching_law k S' hc' hS' (2 * k + 1) le_rfl
    refine ⟨?_, ?_, fun _ => ?_, ?_⟩
    · rw [fkA_split sC (tr_isSperner _ _) hd hCc hDc hx, hLeq, hReq, hRC,
        (rnode hS' hy hne' g).1, ihL.1, ihR.1]
      have h4 : 4 ≤ 2 ^ (k + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : (2 : ℕ) ^ (k + 1 + 2) = 2 ^ (k + 2) * 2 := by rw [← pow_succ]
      rw [e]
      omega
    · rw [hform _ (by omega), card_insert_of_notMem hroot, card_insert_of_notMem hR]
      by_cases hk : k = 0
      · subst hk
        have hcD : c ∉ D' := by
          have hroot' := root_mem_fkADag (2 * 0 + 1) true (matchS (n := n) S')
            (tr univ (matchS S'))
          rw [minimal_eq_self (matchS_sperner hS'), minimal_eq_self (tr_isSperner _ _)]
            at hroot'
          have h1 : D'.card = 1 := by rw [hD'def, ihD.2.1]; rfl
          obtain ⟨q, hq⟩ := card_eq_one.1 h1
          intro hcq
          have e1 : c = q := mem_singleton.1 (hq ▸ hcq)
          have e2 : (matchS (n := n) S', tr univ (matchS S')) = q :=
            mem_singleton.1 (hq ▸ hroot')
          have e3 : matchS (n := n) S' = ∅ := by
            rw [← e1, hcdef] at e2; exact (Prod.mk.inj e2).1
          obtain ⟨j', hj'⟩ := hne'
          have h5 := mem_matchS (n := n) (S := S') (e := blk j') |>.2 ⟨j', hj', rfl⟩
          rw [e3] at h5
          exact notMem_empty _ h5
        rw [card_insert_of_notMem hcD, hD'def, ihD.2.1]
        rfl
      · rw [insert_eq_of_mem (ihD.2.2.1 hk), ihD.2.1, if_neg hk]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
        omega
    · rw [hform _ (by omega)]
      exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))
    · rw [hform _ (by omega), hform _ (by omega)]

/-- **Theorem C1 (matching(v)).** For the perfect matching on `v = 2m` points, `m ≥ 2`, the
modified FK-A tree has `τ = 2^(m+1) − 3` nodes and `δ = v` distinct subproblems. -/
theorem matching_tau_delta (m : ℕ) (hm : 2 ≤ m) :
    (runFKA true (matchS (n := 2 * m) (range m)) (tr univ (matchS (range m)))).2 =
        2 ^ (m + 1) - 3 ∧
      (fkADag (2 * m + 1) true (matchS (n := 2 * m) (range m))
        (tr univ (matchS (range m)))).card = 2 * m := by
  have hfit : Fits (2 * m) (range m) := fun i hi => by rw [mem_range] at hi; omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := matching_law k (range (k + 1)) (card_range _) hfit (2 * (k + 1) + 1) (by omega)
  refine ⟨h.1, ?_⟩
  rw [h.2.1, if_neg (by omega)]

/-- The law checked by evaluation against `fka.memo` on `matching(8)`: `τ = 29`, `δ = 8`. -/
theorem matching_eight :
    (runFKA true (matchS (n := 8) (range 4)) (tr univ (matchS (range 4)))).2 = 29 ∧
      (fkADag 9 true (matchS (n := 8) (range 4)) (tr univ (matchS (range 4)))).card = 8 := by
  native_decide

end Matching

end HD

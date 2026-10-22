/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A under an arbitrary split rule (research track C)

`fkAR r` is Algorithm 1 with the split vertex chosen by a rule `r : HG n → HG n → Option (Fin n)`
in place of the degree-sum rule `splitVar`; `fkADagR r` collects its distinct subproblems. The
degree-sum instance is the existing `fkA` (`fkAR_splitVar`, `fkADagR_splitVar`), and the verdict
is correct under every rule (`fkAR_correct`).

A family `𝒮` of Sperner hypergraphs is *`r`-closed* if every `H ∈ 𝒮` that `r` splits at `x` has
both restrictions `H − x = f|x=0` and `min(H / x) = f|x=1` in `𝒮`. For a symmetric rule every
subproblem of `(G, Tr G)`, `G ∈ 𝒮`, is `(H, Tr H)` or `(Tr H, H)` with `H ∈ 𝒮`
(`fkADagR_closed`), so `δ ≤ 2|𝒮|`. A closed family is a branching program whose nodes are named
by their own functions (`BranchingProgram`), so this is the bound `δ ≤ 2 · size`.

| Lean | Statement |
| --- | --- |
| `fkAR`, `fkADagR`, `fkAR_splitVar`, `fkADagR_splitVar` | FK-A with a split rule; the degree-sum instance is `fkA` |
| `fkAR_correct` | the verdict is `Dual` under every rule |
| `leftRule` | the least vertex of `support C ∪ support D` (Hertel's order) |
| `Closed`, `fkADagR_closed` | subproblems of `(G, Tr G)` lie over an `r`-closed family containing `G` |
-/
import HypergraphDualization.Blowup

namespace HD

open Finset

variable {n : ℕ}

/-- A split rule: the vertex on which to split the node `(C, D)`, or `none`. -/
abbrev Rule (n : ℕ) := HG n → HG n → Option (Fin n)

/-- Algorithm 1 with split rule `r`: the verdict and the number of nodes of the tree. -/
def fkAR (r : Rule n) : ℕ → Bool → HG n → HG n → Bool × ℕ
  | 0, _, C₀, D₀ => (decide (Dual univ (minimal C₀) (minimal D₀)), 1)
  | fuel + 1, modified, C₀, D₀ =>
    let C := minimal C₀
    let D := minimal D₀
    if !conds C D then (false, 1)
    else if C.card * D.card ≤ 1 || (modified && (C.card == 1 || D.card == 1)) then
      (decide (Dual univ C D), 1)
    else
      match r C D with
      | none => (decide (Dual univ C D), 1)
      | some x =>
        let l := fkAR r fuel modified (del C x) (con D x)
        if l.1 then
          let r' := fkAR r fuel modified (del D x) (con C x)
          (r'.1, 1 + l.2 + r'.2)
        else (false, 1 + l.2)

/-- The distinct Sperner-reduced pairs visited by `fkAR r`. -/
def fkADagR (r : Rule n) : ℕ → Bool → HG n → HG n → Finset (HG n × HG n)
  | 0, _, C₀, D₀ => {(minimal C₀, minimal D₀)}
  | fuel + 1, modified, C₀, D₀ =>
    let C := minimal C₀
    let D := minimal D₀
    if !conds C D then {(C, D)}
    else if C.card * D.card ≤ 1 || (modified && (C.card == 1 || D.card == 1)) then {(C, D)}
    else
      match r C D with
      | none => {(C, D)}
      | some x =>
        let l := fkADagR r fuel modified (del C x) (con D x)
        if (fkAR r fuel modified (del C x) (con D x)).1 then
          insert (C, D) (l ∪ fkADagR r fuel modified (del D x) (con C x))
        else insert (C, D) l

/-- The degree-sum instance is FK-A. -/
theorem fkAR_splitVar : fkAR (splitVar (n := n)) = fkA := by
  funext fuel b C D
  induction fuel generalizing C D with
  | zero => rfl
  | succ f ih => simp only [fkAR, fkA, ih]; rfl

theorem fkADagR_splitVar : fkADagR (splitVar (n := n)) = fkADag := by
  funext fuel b C D
  induction fuel generalizing C D with
  | zero => rfl
  | succ f ih => simp only [fkADagR, fkADag, ih, fkAR_splitVar]; rfl

theorem fkAR_minimal (r : Rule n) (fuel : ℕ) (b : Bool) (C D : HG n) :
    fkAR r fuel b (minimal C) (minimal D) = fkAR r fuel b C D := by
  cases fuel <;> simp only [fkAR, minimal_minimal]

theorem fkADagR_minimal (r : Rule n) (fuel : ℕ) (b : Bool) (C D : HG n) :
    fkADagR r fuel b (minimal C) (minimal D) = fkADagR r fuel b C D := by
  cases fuel <;> simp only [fkADagR, minimal_minimal]

/-- **Algorithm 1 is correct under every split rule.** -/
theorem fkAR_correct (r : Rule n) (fuel : ℕ) (modified : Bool) (C D : HG n) :
    (fkAR r fuel modified C D).1 = decide (Dual univ C D) := by
  induction fuel generalizing C D with
  | zero => simp [fkAR, dual_minimal]
  | succ fuel ih =>
    have hred : Dual univ (minimal C) (minimal D) ↔ Dual univ C D := dual_minimal
    simp only [fkAR]
    split_ifs with hc hleaf
    · have : ¬ Dual univ C D := fun h =>
        by simp [conds_of_dual (minimal_isSperner C) (minimal_isSperner D) (hred.2 h)] at hc
      simp [this]
    · simp [hred]
    · split
      · simp [hred]
      · rename_i x _
        have hD : Dual univ C D ↔ Dual univ (del (minimal C) x) (con (minimal D) x) ∧
            Dual univ (del (minimal D) x) (con (minimal C) x) :=
          hred.symm.trans ⟨fun h => dual_children h x, fun ⟨hL, hR⟩ => by
            have := (dual_split (within_univ (minimal C)) (within_univ (minimal D))
              (mem_univ x)).2
            refine this ⟨?_, ?_⟩
            · exact (dual_erase_of_notMem (fun e he => (mem_filter.1 he).2) (fun e he => by
                obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)).2 hL
            · exact (dual_erase_of_notMem (fun e he => (mem_filter.1 he).2) (fun e he => by
                obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)).2 hR⟩
        split_ifs with hl
        · rw [ih] at hl ⊢
          simp only [decide_eq_true_eq] at hl
          rw [decide_eq_decide]
          exact ⟨fun h => hD.2 ⟨hl, h⟩, fun h => (hD.1 h).2⟩
        · rw [ih] at hl
          simp only [decide_eq_true_eq] at hl
          simp [hD, hl]

/-- Every subproblem is the root or a subproblem of a child at the vertex the rule chose. -/
theorem mem_fkADagR_succ {r : Rule n} {f : ℕ} {b : Bool} {C D : HG n} {p : HG n × HG n}
    (hp : p ∈ fkADagR r (f + 1) b C D) : p = (minimal C, minimal D) ∨
      ∃ x, r (minimal C) (minimal D) = some x ∧
        (p ∈ fkADagR r f b (del (minimal C) x) (con (minimal D) x) ∨
          p ∈ fkADagR r f b (del (minimal D) x) (con (minimal C) x)) := by
  simp only [fkADagR] at hp
  split_ifs at hp
  · exact Or.inl (mem_singleton.1 hp)
  · exact Or.inl (mem_singleton.1 hp)
  · split at hp
    · exact Or.inl (mem_singleton.1 hp)
    · rename_i x hx
      split_ifs at hp
      · rcases mem_insert.1 hp with h | h
        · exact Or.inl h
        · rcases mem_union.1 h with h | h
          · exact Or.inr ⟨x, hx, Or.inl h⟩
          · exact Or.inr ⟨x, hx, Or.inr h⟩
      · rcases mem_insert.1 hp with h | h
        · exact Or.inl h
        · exact Or.inr ⟨x, hx, Or.inl h⟩

/-! ### Closed families -/

/-- `r` is symmetric: both orientations of a node split on the same vertex. -/
def Symm (r : Rule n) : Prop := ∀ C D, r C D = r D C

/-- `𝒮` is `r`-closed: its members are Sperner, and each `H ∈ 𝒮` that `r` splits at `x` has
`H − x` and `min(H / x)` in `𝒮`. -/
def Closed (r : Rule n) (𝒮 : Finset (HG n)) : Prop :=
  ∀ H ∈ 𝒮, IsSperner H ∧ ∀ x, r H (tr univ H) = some x → del H x ∈ 𝒮 ∧ minimal (con H x) ∈ 𝒮

/-- The pairs over `𝒮`: `(H, Tr H)` and `(Tr H, H)` for `H ∈ 𝒮`. -/
def pairs (𝒮 : Finset (HG n)) : Finset (HG n × HG n) :=
  𝒮.image (fun H => (H, tr univ H)) ∪ 𝒮.image (fun H => (tr univ H, H))

theorem card_pairs_le (𝒮 : Finset (HG n)) : (pairs 𝒮).card ≤ 2 * 𝒮.card := by
  unfold pairs
  calc _ ≤ _ := card_union_le _ _
    _ ≤ 𝒮.card + 𝒮.card := add_le_add card_image_le card_image_le
    _ = _ := by ring

/-- **Subproblems over a closed family.** For a symmetric rule `r`, an `r`-closed `𝒮` and
`G ∈ 𝒮`, every subproblem of FK-A on `(G, Tr G)` or `(Tr G, G)` is `(H, Tr H)` or `(Tr H, H)`
with `H ∈ 𝒮`. -/
theorem fkADagR_closed {r : Rule n} (hr : Symm r) {𝒮 : Finset (HG n)} (h𝒮 : Closed r 𝒮)
    (fuel : ℕ) (b : Bool) : ∀ G ∈ 𝒮,
      fkADagR r fuel b G (tr univ G) ⊆ pairs 𝒮 ∧ fkADagR r fuel b (tr univ G) G ⊆ pairs 𝒮 := by
  induction fuel with
  | zero =>
    intro G hG
    have sG := (h𝒮 G hG).1
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩ <;>
      simp only [fkADagR, mem_singleton, minimal_tr, minimal_eq_self sG] at hp <;> subst hp
    · exact mem_union_left _ (mem_image_of_mem _ hG)
    · exact mem_union_right _ (mem_image_of_mem _ hG)
  | succ f ih =>
    intro G hG
    obtain ⟨sG, hcl⟩ := h𝒮 G hG
    have mG : minimal G = G := minimal_eq_self sG
    -- the two children, as pairs over `𝒮`
    have hL : ∀ x, r G (tr univ G) = some x →
        fkADagR r f b (del G x) (con (tr univ G) x) ⊆ pairs 𝒮 := fun x hx p hp => by
      rw [← fkADagR_minimal, minimal_con_tr (within_univ G) (mem_univ x),
        ← minimal_tr (del G x), fkADagR_minimal] at hp
      exact (ih _ (hcl x hx).1).1 hp
    have hR : ∀ x, r G (tr univ G) = some x →
        fkADagR r f b (del (tr univ G) x) (con G x) ⊆ pairs 𝒮 := fun x hx p hp => by
      rw [← tr_con_eq, ← fkADagR_minimal, minimal_tr, ← tr_minimal univ (con G x)] at hp
      exact (ih _ (hcl x hx).2).2 hp
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩ <;>
      rcases mem_fkADagR_succ hp with rfl | ⟨x, hx, h | h⟩
    · rw [mG, minimal_tr]; exact mem_union_left _ (mem_image_of_mem _ hG)
    · rw [mG, minimal_tr] at hx h; exact hL x hx h
    · rw [mG, minimal_tr] at hx h; exact hR x hx h
    · rw [mG, minimal_tr]; exact mem_union_right _ (mem_image_of_mem _ hG)
    · rw [mG, minimal_tr, hr] at hx; rw [mG, minimal_tr] at h; exact hR x hx h
    · rw [mG, minimal_tr, hr] at hx; rw [mG, minimal_tr] at h; exact hL x hx h

/-- **`δ ≤ 2|𝒮|`** for a symmetric rule and an `r`-closed family containing `G`. -/
theorem card_fkADagR_le_closed {r : Rule n} (hr : Symm r) {𝒮 : Finset (HG n)}
    (h𝒮 : Closed r 𝒮) (fuel : ℕ) (b : Bool) {G : HG n} (hG : G ∈ 𝒮) :
    (fkADagR r fuel b G (tr univ G)).card ≤ 2 * 𝒮.card :=
  (card_le_card ((fkADagR_closed hr h𝒮 fuel b G hG).1)).trans (card_pairs_le 𝒮)

/-! ### The leftmost rule -/

/-- Hertel's order: the least vertex of `support C ∪ support D`. -/
def leftRule (C D : HG n) : Option (Fin n) :=
  if h : (support C ∪ support D).Nonempty then some ((support C ∪ support D).min' h) else none

theorem leftRule_symm : Symm (leftRule (n := n)) := by
  intro C D; simp only [leftRule, union_comm]

theorem splitVar_symm : Symm (splitVar (n := n)) := splitVar_comm

#print axioms fkAR_splitVar
#print axioms fkADagR_splitVar
#print axioms fkAR_correct
#print axioms fkADagR_closed
#print axioms card_fkADagR_le_closed

end HD

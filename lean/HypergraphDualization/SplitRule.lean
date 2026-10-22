/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A under an arbitrary split rule (research track C)

`fkAR r` (`Algorithm`) is Algorithm 1 with the split vertex chosen by a rule
`r : HG n → HG n → Option (Fin n)`; `fkADagR r` (`Dag`) collects its distinct subproblems. The
published FK-A is the degree-sum instance by definition (`fkAR_splitVar`, `fkADagR_splitVar`),
and the verdict is correct under every rule (`fkAR_correct`).

A family `𝒮` of Sperner hypergraphs is *`r`-closed* if every `H ∈ 𝒮` that `r` splits at `x` has
both restrictions `H − x = f|x=0` and `min(H / x) = f|x=1` in `𝒮`. For a symmetric rule every
subproblem of `(G, Tr G)`, `G ∈ 𝒮`, is `(H, Tr H)` or `(Tr H, H)` with `H ∈ 𝒮`
(`fkADagR_closed`), so `δ ≤ 2|𝒮|`. A closed family is a branching program whose nodes are named
by their own functions (`BranchingProgram`), so this is the bound `δ ≤ 2 · size`.

| Lean | Statement |
| --- | --- |
| `fkAR_splitVar`, `fkADagR_splitVar` | the degree-sum instance is `fkA` |
| `leftRule` | the least vertex of `support C ∪ support D` (Hertel's order) |
| `Closed`, `fkADagR_closed` | subproblems of `(G, Tr G)` lie over an `r`-closed family containing `G` |
-/
import HypergraphDualization.Blowup

namespace HD

open Finset

variable {n : ℕ}

/-- The degree-sum instance is FK-A. -/
theorem fkAR_splitVar : fkAR (splitVar (n := n)) = fkA := rfl

theorem fkADagR_splitVar : fkADagR (splitVar (n := n)) = fkADag := rfl

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

theorem mem_pairs_left {𝒮 : Finset (HG n)} {H : HG n} (h : H ∈ 𝒮) : (H, tr univ H) ∈ pairs 𝒮 :=
  mem_union_left _ (mem_image_of_mem _ h)

theorem mem_pairs_right {𝒮 : Finset (HG n)} {H : HG n} (h : H ∈ 𝒮) : (tr univ H, H) ∈ pairs 𝒮 :=
  mem_union_right _ (mem_image_of_mem _ h)

/-- If `K − x` and `min(K / x)` lie in `𝒮`, both reduced children of `(K, Tr K)` at `x` are
pairs over `𝒮`. -/
theorem kids_mem {𝒮 : Finset (HG n)} {K : HG n} (sK : IsSperner K) {x : Fin n}
    (h0 : del K x ∈ 𝒮) (h1 : minimal (con K x) ∈ 𝒮) :
    (minimal (del K x), minimal (con (tr univ K) x)) ∈ pairs 𝒮 ∧
      (minimal (del (tr univ K) x), minimal (con K x)) ∈ pairs 𝒮 := by
  obtain ⟨hl, hr⟩ := kids_eq sK x
  exact ⟨hl ▸ mem_pairs_left h0, hr ▸ mem_pairs_right h1⟩

/-- **Subproblems over a closed family.** For a symmetric rule `r`, an `r`-closed `𝒮` and
`G ∈ 𝒮`, every subproblem of FK-A on `(G, Tr G)` or `(Tr G, G)` is `(H, Tr H)` or `(Tr H, H)`
with `H ∈ 𝒮`. -/
theorem fkADagR_closed {r : Rule n} (hr : Symm r) {𝒮 : Finset (HG n)} (h𝒮 : Closed r 𝒮)
    (fuel : ℕ) (b : Bool) : ∀ G ∈ 𝒮,
      fkADagR r fuel b G (tr univ G) ⊆ pairs 𝒮 ∧ fkADagR r fuel b (tr univ G) G ⊆ pairs 𝒮 := by
  have hP : ∀ p ∈ (pairs 𝒮 : Set (HG n × HG n)), ∀ x, r p.1 p.2 = some x →
      (minimal (del p.1 x), minimal (con p.2 x)) ∈ (pairs 𝒮 : Set (HG n × HG n)) ∧
        (minimal (del p.2 x), minimal (con p.1 x)) ∈ (pairs 𝒮 : Set (HG n × HG n)) := by
    intro p hp x hx
    simp only [pairs, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hp
    rcases hp with ⟨H, hH, rfl⟩ | ⟨H, hH, rfl⟩
    · obtain ⟨sH, hcl⟩ := h𝒮 H hH
      exact kids_mem sH (hcl x hx).1 (hcl x hx).2
    · obtain ⟨sH, hcl⟩ := h𝒮 H hH
      obtain ⟨h1, h2⟩ := kids_mem sH (hcl x (by rw [hr]; exact hx)).1 (hcl x (by rw [hr]; exact hx)).2
      exact ⟨h2, h1⟩
  intro G hG
  have sG := (h𝒮 G hG).1
  refine ⟨fun p hp => fkADagR_sub hP fuel b _ _ ?_ p hp, fun p hp => fkADagR_sub hP fuel b _ _ ?_ p hp⟩
  · rw [minimal_eq_self sG, minimal_tr]; exact mem_pairs_left hG
  · rw [minimal_eq_self sG, minimal_tr]; exact mem_pairs_right hG

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

end HD

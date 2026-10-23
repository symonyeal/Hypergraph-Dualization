/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A, executable and verified

`fkAR r fuel modified C D` runs Algorithm 1 on hypergraphs over `Fin n` under the split rule
`r` and returns the verdict together with the number of nodes in its recursion tree; `fkA` is
the published degree-sum instance `fkAR splitVar`. Each node:

1. Sperner-reduces both sides (`minimal`);
2. checks conditions (i)-(iv) (`conds`); a failure is a leaf with verdict `false`;
3. stops at `|C|·|D| ≤ 1`, and under `modified` also at `|C| = 1` or `|D| = 1` (§5.1.1);
4. otherwise splits on the vertex maximising `deg_C + deg_D`, lowest index on ties, and
   recurses on `L = (C₁, D₀ ∨ D₁)` and then, only if `L` is dual, on `R = (D₁, C₀ ∨ C₁)`.

This is the configuration that produced the 2024 figures (`modified`, degree-sum rule) and
matches `fka.algorithm.fk_a` node for node. A leaf's verdict is computed from the definition
of duality, which is exact on any input; the polynomial leaf rules of the thesis are proved
equivalent separately (`dual_empty_left`, `dual_singleton_left`, `conds_of_dual`).

| Lean | Thesis |
| --- | --- |
| `fkAR_correct`, `fkA_correct` | Algorithm 1 decides `Trans-Hyp` under every split rule: the verdict is `Dual` |
| `conds_of_dual` | conditions (i)-(iv) hold for every dual pair (Props. 2.2.1-2.2.4) |
| `dual_singleton_left` | the `D₁,ₖ` rule of §5.1.1 |
-/
import HypergraphDualization.Decomposition
import HypergraphDualization.Symmetry

namespace HD

open Finset

variable {n : ℕ}

/-- Hypergraphs on the vertex set `Fin n`. -/
abbrev HG (n : ℕ) := Finset (Finset (Fin n))

/-- Conditions (i)-(iv) of Algorithm 1; (iv) is scaled by `2^n`. -/
def conds (C D : HG n) : Bool :=
  decide (support C = support D) &&
  decide (∀ c ∈ C, c.card ≤ D.card) && decide (∀ d ∈ D, d.card ≤ C.card) &&
  decide (∀ c ∈ C, ∀ d ∈ D, (c ∩ d).Nonempty) &&
  decide (2 ^ n ≤ ∑ c ∈ C, 2 ^ (n - c.card) + ∑ d ∈ D, 2 ^ (n - d.card))

/-- The degree-sum split rule: the vertex of largest `deg_C + deg_D`, lowest index on ties,
among vertices of positive degree. -/
def splitVar (C D : HG n) : Option (Fin n) :=
  ((List.finRange n).foldl (fun (acc : Option (Fin n × ℕ)) x =>
      let k := degree C x + degree D x
      if k = 0 then acc else
        match acc with
        | none => some (x, k)
        | some (y, k') => if k' < k then some (x, k) else some (y, k'))
    none).map Prod.fst

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

/-- Algorithm 1 as published: the degree-sum rule. -/
abbrev fkA : ℕ → Bool → HG n → HG n → Bool × ℕ := fkAR splitVar

/-- Run FK-A with enough fuel for every vertex to be split once. -/
def runFKA (modified : Bool) (C D : HG n) : Bool × ℕ := fkA (n + 1) modified C D

theorem within_univ (H : HG n) : Within univ H := fun _ _ => subset_univ _

/-- Conditions (i)-(iv) hold at every dual pair of Sperner-reduced families. -/
theorem conds_of_dual {C D : HG n} (sC : IsSperner C) (sD : IsSperner D)
    (h : Dual univ C D) : conds C D = true := by
  have hC : C = tr univ D := by
    rw [← minimal_eq_self sC]; exact (dual_iff_minimal_eq_tr (within_univ C) (within_univ D)).1 h
  have hk := kraft_sum (within_univ D) hC
  have hsz := card_le_card_tr (within_univ D) sD hC
  have hsup := support_eq (within_univ D) sD hC
  have hmeet := edges_meet hC
  simp only [conds, Bool.and_eq_true, decide_eq_true_eq, card_univ, Fintype.card_fin] at hk ⊢
  refine ⟨⟨⟨⟨hsup.symm, hsz.2⟩, hsz.1⟩, fun c hc d hd => ?_⟩, by omega⟩
  rw [inter_comm]; exact hmeet d hd c hc

/-- **Algorithm 1 is correct under every split rule.** For any fuel, the verdict is `Dual`. -/
theorem fkAR_correct (r : Rule n) (fuel : ℕ) (modified : Bool) (C D : HG n) :
    (fkAR r fuel modified C D).1 = decide (Dual univ C D) := by
  induction fuel generalizing C D with
  | zero => simp [fkAR, dual_minimal]
  | succ fuel ih =>
    have hred : Dual univ (minimal C) (minimal D) ↔ Dual univ C D := dual_minimal
    simp only [fkAR]
    split_ifs with hc hleaf
    · -- A failed condition: the pair cannot be dual.
      have : ¬ Dual univ C D := fun h =>
        by simp [conds_of_dual (minimal_isSperner C) (minimal_isSperner D) (hred.2 h)] at hc
      simp [this]
    · simp [hred]
    · split
      · simp [hred]
      · rename_i x _
        set C' := minimal C
        set D' := minimal D
        have hsplit := dual_split (G := C') (H := D') (mem_univ x)
        have hL := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
          (G := del C' x) (H := con D' x) (x := x)
          (fun e he => (mem_filter.1 he).2) (fun e he => by
            obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
        have hR := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
          (G := del D' x) (H := con C' x) (x := x)
          (fun e he => (mem_filter.1 he).2) (fun e he => by
            obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
        rw [hL, hR] at hsplit
        have hD : Dual univ C D ↔ Dual univ (del C' x) (con D' x) ∧
            Dual univ (del D' x) (con C' x) := hred.symm.trans hsplit
        split_ifs with hl
        · rw [ih] at hl ⊢
          simp only [decide_eq_true_eq] at hl
          rw [decide_eq_decide]
          exact ⟨fun h => hD.2 ⟨hl, h⟩, fun h => (hD.1 h).2⟩
        · rw [ih] at hl
          simp only [decide_eq_true_eq] at hl
          simp [hD, hl]

/-- **Algorithm 1 is correct.** For any fuel, the verdict of FK-A is exactly `Dual`. -/
theorem fkA_correct (fuel : ℕ) (modified : Bool) (C D : HG n) :
    (fkA fuel modified C D).1 = decide (Dual univ C D) :=
  fkAR_correct splitVar fuel modified C D

/-- Relabelling preserves the verdict under any two split rules; node counts may differ. -/
theorem fkAR_pimg (r s : Rule n) (fuel : ℕ) (modified : Bool)
    (σ : Equiv.Perm (Fin n)) (C D : HG n) :
    (fkAR r fuel modified (pimg σ C) (pimg σ D)).1 =
      (fkAR s fuel modified C D).1 := by
  rw [fkAR_correct, fkAR_correct, decide_eq_decide]
  exact dual_pimg σ C D

/-! ### The polynomial leaf rules -/

/-- `|C| = 0`: `(∅, D)` is dual iff `D` contains the empty edge. -/
theorem dual_empty_left {α : Type*} [DecidableEq α] {U : Finset α} {D : Finset (Finset α)} :
    Dual U ∅ D ↔ ∅ ∈ D := by
  rw [dual_iff]
  constructor
  · intro h
    have := (not_congr (h U subset_rfl)).1 (by rintro ⟨e, he, -⟩; exact notMem_empty e he)
    rw [not_not, sdiff_self] at this
    obtain ⟨e, he, hsub⟩ := this
    rwa [subset_empty.1 hsub] at he
  · intro h A _
    simp only [upHit, notMem_empty, false_and, exists_false, false_iff, not_not]
    exact ⟨∅, h, empty_subset _⟩

/-- The `D₁,ₖ` rule (§5.1.1): `({c}, D)` is dual iff `D` is the singletons of `c`. -/
theorem dual_singleton_left {α : Type*} [DecidableEq α] {U : Finset α} {c : Finset α}
    {D : Finset (Finset α)} (hc : c ⊆ U) (hD : Within U D) (sD : IsSperner D) :
    Dual U {c} D ↔ D = c.image ({·}) := by
  rw [dual_comm, dual_iff_minimal_eq_tr hD (fun e he => (mem_singleton.1 he) ▸ hc),
    minimal_eq_self sD, tr_singleton hc]

end HD

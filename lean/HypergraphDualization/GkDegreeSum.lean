/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The degree-sum growth question on GK

Index `k = 0` denotes `f₁`, on `2^(2k+1)` original vertices. `reach` uses modified FK-A,
the published degree-sum rule and fuel `n+1`. `isoDelta` takes the ordered-pair quotient
of that entire reach, not an isomorphism-keyed traversal. No growth conjecture is assumed.
-/
import HypergraphDualization.GkMemo
import HypergraphDualization.SymmetryDepth
import HypergraphDualization.RuleInstances
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace HD

open Finset

variable {n : ℕ}

/-- Once fuel exceeds the live support size, adding fuel changes no reached pair.
This holds even on nondual inputs; the short-circuit verdict is fuel-independent. -/
theorem fkADagR_stable {r : Rule n} (hv : Valid r) (b : Bool) :
    ∀ f (C D : HG n), (support C ∪ support D).card < f → ∀ t,
      fkADagR r (f + t) b C D = fkADagR r f b C D := by
  intro f
  induction f with
  | zero => intro C D hf; omega
  | succ f ih =>
    intro C D hf t
    let C' := minimal C
    let D' := minimal D
    have hsub : support C' ∪ support D' ⊆ support C ∪ support D :=
      union_subset_union (support_minimal_sub C) (support_minimal_sub D)
    have hc : ∀ x, r C' D' = some x → ∀ A B : HG n,
        support A ⊆ (support C').erase x → support B ⊆ (support D').erase x →
          (support A ∪ support B).card < f := by
      intro x hx A B hA hB
      have hxs := hsub ((hv C' D').1 x hx)
      have hs : support A ∪ support B ⊆ (support C ∪ support D).erase x := by
        have he : support A ∪ support B ⊆ (support C' ∪ support D').erase x := by
          rw [erase_union_distrib]
          exact union_subset_union hA hB
        exact he.trans (erase_subset_erase x hsub)
      have hcard := card_le_card hs
      rw [card_erase_of_mem hxs] at hcard
      have := card_pos.2 ⟨x, hxs⟩
      omega
    have hc' : ∀ x, r C' D' = some x → ∀ A B : HG n,
        support A ⊆ (support D').erase x → support B ⊆ (support C').erase x →
          (support A ∪ support B).card < f := by
      intro x hx A B hA hB
      rw [union_comm]
      exact hc x hx B A hB hA
    rw [Nat.succ_add]
    simp only [fkADagR]
    change (if !conds C' D' then _ else _) = (if !conds C' D' then _ else _)
    split_ifs with hconds hleaf
    · rfl
    · rfl
    · cases hx : r C' D' with
      | none => rfl
      | some x =>
        dsimp only
        rw [ih _ _ (hc x hx _ _ (support_del_sub C' x) (support_con_sub' D' x)) t,
          ih _ _ (hc' x hx _ _ (support_del_sub D' x) (support_con_sub' C' x)) t,
          fkAR_correct, fkAR_correct]

/-- The modified stop applies under every rule, including any choice of local weights. -/
theorem fkADagR_singleton (r : Rule n) (f : ℕ) (C D : HG n)
    (h : (minimal C).card = 1 ∨ (minimal D).card = 1) :
    fkADagR r f true C D = {(minimal C, minimal D)} := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [fkADagR]
    split_ifs
    · rfl
    · rfl
    · rename_i hstop
      exfalso
      apply hstop
      rcases h with h | h <;> simp [h]

/-- **Checked by evaluation.** The first zero child of GK f₂ is reached and its
first f₁ block has singleton support, although standalone f₁ is a modified leaf. -/
theorem gk2_embedded_singleton :
    let C := Fm.dnf gk2
    let D := Fm.dnf (Fm.dual gk2)
    splitVar C D = some 0 ∧
      (minimal (del C 0), minimal (con D 0)) ∈ fkADag 9 true C D ∧
      support (minimal (del C 0)) ∩ {0, 1} = {1} ∧
      (Fm.dnf (coFm 2 1 0)).card = 2 ∧
      (Fm.dnf (Fm.dual (coFm 2 1 0))).card = 1 := by
  native_decide

namespace GK

theorem map_gkH (i : ℕ) : mapH Fin.valEmbedding (gkH i) = coalt i := by
  unfold mapH gkH
  rw [image_image]
  have he : ∀ e ∈ coalt i,
      (univ.filter (fun v : Fin (2 ^ i) => v.val ∈ e)).map Fin.valEmbedding = e := by
    intro e he
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      have hlt := mem_range.1 ((alt_props i).2.1 e he hx)
      exact ⟨⟨x, hlt⟩, hx, rfl⟩
  change (coalt i).image (fun e =>
    (univ.filter (fun v : Fin (2 ^ i) => v.val ∈ e)).map Fin.valEmbedding) = coalt i
  rw [image_congr he]
  exact image_id

theorem card_gkH (i : ℕ) : (gkH i).card = (coalt i).card := by
  rw [← map_gkH i, card_mapH]

theorem card_tr_gkH (i : ℕ) : (tr univ (gkH i)).card = (alt i).card := by
  have hu : (univ : Finset (Fin (2 ^ i))).map Fin.valEmbedding = range (2 ^ i) := by
    ext x
    simp only [mem_map, mem_univ, true_and, mem_range, Fin.valEmbedding_apply]
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.isLt, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have ht := tr_mapH Fin.valEmbedding univ (gkH i)
  rw [hu, map_gkH, (alt_props i).2.2.2.2.2] at ht
  rw [← card_mapH Fin.valEmbedding (tr univ (gkH i)), ← ht]

/-- Full labelled reach on `f_{k+1}`, retaining its original ambient ground set. -/
def reach (k : ℕ) : Finset (HG (2 ^ (2 * k + 1)) × HG (2 ^ (2 * k + 1))) :=
  fkADag (2 ^ (2 * k + 1) + 1) true (gkH (2 * k + 1)) (tr univ (gkH (2 * k + 1)))

/-- Input size counts both edge families. -/
def edges (k : ℕ) : ℕ := (gkH (2 * k + 1)).card + (tr univ (gkH (2 * k + 1))).card

theorem edges_eq (k : ℕ) : edges k = 3 * 2 ^ (2 * 2 ^ k - 2) := by
  rw [edges, card_gkH, card_tr_gkH, (alt_counts k).2.2.1, (alt_counts k).2.2.2]
  have h := Nat.one_le_two_pow (n := k)
  rw [show 2 * 2 ^ k - 1 = (2 * 2 ^ k - 2) + 1 by omega, pow_succ]
  omega

theorem edges_pos (k : ℕ) : 0 < edges k := by
  rw [edges_eq]
  positivity

/-- Exact input-edge squaring, without rational division in the natural numbers. -/
theorem edges_succ (k : ℕ) : 3 * edges (k + 1) = 4 * edges k ^ 2 := by
  rw [edges_eq, edges_eq, pow_succ]
  have h := Nat.one_le_two_pow (n := k)
  have he : 2 * (2 ^ k * 2) - 2 = 2 * (2 * 2 ^ k - 2) + 2 := by omega
  rw [he, pow_add, mul_comm 2 (2 * 2 ^ k - 2), pow_mul]
  ring

def delta (k : ℕ) : ℕ := (reach k).card

noncomputable def isoDelta (k : ℕ) : ℕ := by
  classical
  exact ((reach k).image SD.isoKey).card

theorem reach_stable (k t : ℕ) :
    fkADag (2 ^ (2 * k + 1) + 1 + t) true (gkH (2 * k + 1))
      (tr univ (gkH (2 * k + 1))) = reach k := by
  apply fkADagR_stable valid_splitVar
  have h := card_le_univ
    (support (gkH (2 * k + 1)) ∪ support (tr univ (gkH (2 * k + 1))))
  simp only [Fintype.card_fin] at h
  omega

theorem isoDelta_le (k : ℕ) : isoDelta k ≤ delta k := by
  classical
  exact card_image_le

/-- Conjecture 4.30, with the zero-based index used in this namespace. -/
def IsoGrowth : Prop := ∀ M : ℝ, 0 < M → ∃ k, M * (edges k : ℝ) < (isoDelta k : ℝ)

/-- Conjecture 4.19, a separate weaker assertion. -/
def LabelledGrowth : Prop := ∀ M : ℝ, 0 < M → ∃ k, M * (edges k : ℝ) < (delta k : ℝ)

theorem labelledGrowth_of_isoGrowth (h : IsoGrowth) : LabelledGrowth := by
  intro M hM
  obtain ⟨k, hk⟩ := h M hM
  exact ⟨k, hk.trans_le (by exact_mod_cast isoDelta_le k)⟩

end GK

/-- A normalized squaring recurrence with a seed above one is unbounded. This is a
conditional arithmetic lemma; it asserts no recurrence for the GK reach. -/
theorem squaring_unbounded {u : ℕ → ℝ} (h0 : 1 < u 0)
    (hs : ∀ j, u j ^ 2 ≤ u (j + 1)) : ∀ M : ℝ, ∃ j, M < u j := by
  have hlin : ∀ j, 1 + (j + 1 : ℕ) * (u 0 - 1) ≤ u j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hpos : 0 < u 0 - 1 := by linarith
      have hu : 1 ≤ u j := by push_cast at ih; nlinarith
      have hsq := hs j
      push_cast at ih ⊢
      nlinarith [sq_nonneg (u j - 1)]
  intro M
  obtain ⟨j, hj⟩ := exists_nat_gt ((M - 1) / (u 0 - 1))
  refine ⟨j, lt_of_lt_of_le ?_ (hlin j)⟩
  have hpos : 0 < u 0 - 1 := by linarith
  have hm := (div_lt_iff₀ hpos).1 hj
  push_cast
  nlinarith

/-- If input sizes square by `a`, output counts square by at least `c`, and
`c D₀ > a N₀`, then the output/input ratio is unbounded. The GK value of `a` is `4/3`.
The recurrence and seed are hypotheses, not conclusions. -/
theorem squaring_ratio_unbounded {D N : ℕ → ℝ} {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hN : ∀ j, 0 < N j)
    (hsize : ∀ j, N (j + 1) = a * N j ^ 2)
    (hstep : ∀ j, c * D j ^ 2 ≤ D (j + 1))
    (hseed : a * N 0 < c * D 0) : ∀ M : ℝ, ∃ j, M * N j < D j := by
  let u := fun j => c * D j / (a * N j)
  have h0 : 1 < u 0 := (one_lt_div (mul_pos ha (hN 0))).2 hseed
  have hs : ∀ j, u j ^ 2 ≤ u (j + 1) := by
    intro j
    have he : u j ^ 2 = c * (c * D j ^ 2) / (a * N (j + 1)) := by
      dsimp [u]
      rw [hsize]
      field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hstep j) hc.le)
      (mul_pos ha (hN (j + 1))).le
  intro M
  obtain ⟨j, hj⟩ := squaring_unbounded h0 hs (c * M / a)
  have hj' := (lt_div_iff₀ (mul_pos ha (hN j))).1 hj
  have he : c * M / a * (a * N j) = c * (M * N j) := by
    field_simp
  rw [he] at hj'
  exact ⟨j, (mul_lt_mul_iff_right₀ hc).1 hj'⟩

namespace GK

/-- The arithmetic reduction with the actual GK edge counts. The uniform recurrence and
strict seed remain explicit hypotheses; this theorem supplies neither of them. -/
theorem growth_of_squaring (X : ℕ → ℕ) {c : ℝ} (hc : 0 < c) (k₀ : ℕ)
    (hstep : ∀ k, k₀ ≤ k → c * (X k : ℝ) ^ 2 ≤ (X (k + 1) : ℝ))
    (hseed : (4 / 3 : ℝ) * edges k₀ < c * X k₀) :
    ∀ M : ℝ, ∃ k, M * (edges k : ℝ) < (X k : ℝ) := by
  have hsize : ∀ j, (edges (k₀ + (j + 1)) : ℝ) =
      (4 / 3 : ℝ) * (edges (k₀ + j) : ℝ) ^ 2 := by
    intro j
    have he : (3 : ℝ) * edges (k₀ + j + 1) = 4 * (edges (k₀ + j) : ℝ) ^ 2 := by
      exact_mod_cast edges_succ (k₀ + j)
    simp only [← Nat.add_assoc]
    linarith
  have hs : ∀ j, c * (X (k₀ + j) : ℝ) ^ 2 ≤ (X (k₀ + (j + 1)) : ℝ) := by
    intro j
    simpa only [← Nat.add_assoc] using hstep (k₀ + j) (Nat.le_add_right k₀ j)
  intro M
  obtain ⟨j, hj⟩ := squaring_ratio_unbounded (D := fun j => (X (k₀ + j) : ℝ))
    (N := fun j => (edges (k₀ + j) : ℝ)) (a := 4 / 3) (by norm_num) hc
    (fun j => by exact_mod_cast edges_pos (k₀ + j)) hsize hs (by simpa using hseed) M
  exact ⟨k₀ + j, hj⟩

theorem isoGrowth_of_squaring {c : ℝ} (hc : 0 < c) (k₀ : ℕ)
    (hstep : ∀ k, k₀ ≤ k → c * (isoDelta k : ℝ) ^ 2 ≤ (isoDelta (k + 1) : ℝ))
    (hseed : (4 / 3 : ℝ) * edges k₀ < c * isoDelta k₀) : IsoGrowth := by
  intro M _
  exact growth_of_squaring isoDelta hc k₀ hstep hseed M

theorem labelledGrowth_of_squaring {c : ℝ} (hc : 0 < c) (k₀ : ℕ)
    (hstep : ∀ k, k₀ ≤ k → c * (delta k : ℝ) ^ 2 ≤ (delta (k + 1) : ℝ))
    (hseed : (4 / 3 : ℝ) * edges k₀ < c * delta k₀) : LabelledGrowth := by
  intro M _
  exact growth_of_squaring delta hc k₀ hstep hseed M

end GK

end HD

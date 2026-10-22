/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Which Steiner systems are self-transversal? (research track A, item A5)

A Steiner system `S(t, k, v)` on `U`, `|U| = v`, is a family of `k`-subsets of `U` such that
every `t`-subset of `U` lies in exactly one of them. A self-transversal family is intersecting
(Proposition A3), so a Steiner system with two disjoint blocks is not self-transversal.

| Lean | Statement |
| --- | --- |
| `card_between` | the `m`-sets between `S ⊆ X` number `C(|X| − |S|, m − |S|)` |
| `steiner_count` | `λ_i`: an `i`-set (`i ≤ t`) lies in `C(v−i, t−i) / C(k−i, t−i)` blocks |
| `card_disjoint_eq` | inclusion–exclusion: `#{f ∈ F : e ∩ f = ∅} = Σ_{S ⊆ e} (−1)^{|S|} #{f ∈ F : S ⊆ f}` |
| `steiner_disjoint` | **Theorem A5a.** every block is disjoint from exactly `n₀(t, k, v)` blocks |
| `steiner_n0_nonneg` | a Steiner system `S(t,k,v)` exists only if `n₀(t,k,v) ≥ 0` |
| `steiner_tr_ne` | `n₀ > 0`: no Steiner system `S(t,k,v)` is self-transversal |
-/
import HypergraphDualization.SelfTransversal
import Mathlib.Data.Nat.Choose.Sum

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-- `H` is a Steiner system `S(t, k, |U|)` on `U`. -/
structure IsSteiner (U : Finset α) (H : Finset (Finset α)) (t k : ℕ) : Prop where
  within : Within U H
  card_eq : ∀ e ∈ H, e.card = k
  unique : ∀ T ⊆ U, T.card = t → (H.filter (T ⊆ ·)).card = 1

/-! ### Counting -/

/-- The `m`-sets `T` with `S ⊆ T ⊆ X` number `C(|X| − |S|, m − |S|)` (`T ↦ T \ S`). -/
theorem card_between {S X : Finset α} (hSX : S ⊆ X) {m : ℕ} (hm : S.card ≤ m) :
    (X.powerset.filter fun T => S ⊆ T ∧ T.card = m).card =
      (X.card - S.card).choose (m - S.card) := by
  rw [← card_sdiff_of_subset hSX, ← card_powersetCard]
  refine card_nbij' (· \ S) (· ∪ S) ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_coe, mem_filter, mem_powerset] at hT
    rw [mem_coe, mem_powersetCard]
    exact ⟨sdiff_subset_sdiff hT.1 subset_rfl, by rw [card_sdiff_of_subset hT.2.1, hT.2.2]⟩
  · intro R hR
    rw [mem_coe, mem_powersetCard] at hR
    rw [mem_coe, mem_filter, mem_powerset]
    have hd : Disjoint R S := disjoint_of_subset_left hR.1 sdiff_disjoint
    refine ⟨union_subset (hR.1.trans sdiff_subset) hSX, subset_union_right, ?_⟩
    rw [card_union_of_disjoint hd, hR.2]
    omega
  · intro T hT
    rw [mem_coe, mem_filter, mem_powerset] at hT
    exact sdiff_union_of_subset hT.2.1
  · intro R hR
    rw [mem_coe, mem_powersetCard] at hR
    exact union_sdiff_cancel_right (disjoint_of_subset_left hR.1 sdiff_disjoint)

/-- **Lemma (`λ_i`).** In a Steiner system `S(t, k, v)` on `U`, an `i`-set `S ⊆ U` with `i ≤ t`
lies in `λ_i` blocks, where `λ_i · C(k−i, t−i) = C(v−i, t−i)`. (Double-count the pairs
`(T, e)` with `S ⊆ T ⊆ e`, `|T| = t`, `e ∈ H`.) -/
theorem steiner_count {U : Finset α} {H : Finset (Finset α)} {t k : ℕ} (hH : IsSteiner U H t k)
    {S : Finset α} (hSU : S ⊆ U) (hSt : S.card ≤ t) :
    (H.filter (S ⊆ ·)).card * (k - S.card).choose (t - S.card) =
      (U.card - S.card).choose (t - S.card) := by
  set Ts := U.powerset.filter fun T => S ⊆ T ∧ T.card = t
  have h1 : ∀ e ∈ H.filter (S ⊆ ·), (Ts.filter (· ⊆ e)).card =
      (k - S.card).choose (t - S.card) := by
    intro e he
    rw [mem_filter] at he
    have : Ts.filter (· ⊆ e) = e.powerset.filter fun T => S ⊆ T ∧ T.card = t := by
      ext T
      simp only [Ts, mem_filter, mem_powerset]
      exact ⟨fun ⟨⟨_, h⟩, hTe⟩ => ⟨hTe, h⟩,
        fun ⟨hTe, h⟩ => ⟨⟨hTe.trans (hH.within e he.1), h⟩, hTe⟩⟩
    rw [this, card_between he.2 hSt, hH.card_eq e he.1]
  have h2 : ∀ T ∈ Ts, ((H.filter (S ⊆ ·)).filter (T ⊆ ·)).card = 1 := by
    intro T hT
    simp only [Ts, mem_filter, mem_powerset] at hT
    rw [filter_filter, ← hH.unique T hT.1 hT.2.2]
    congr 1
    exact filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨hT.2.1.trans h, h⟩⟩
  have key : ∑ e ∈ H.filter (S ⊆ ·), (Ts.filter (· ⊆ e)).card =
      ∑ T ∈ Ts, ((H.filter (S ⊆ ·)).filter (T ⊆ ·)).card := by
    simp only [card_filter]
    exact sum_comm
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
    mul_one, card_between hSU hSt] at key
  exact key

/-- **Lemma (inclusion–exclusion).** For any family `F` and set `e`:
`#{f ∈ F : e ∩ f = ∅} = Σ_{S ⊆ e} (−1)^{|S|} #{f ∈ F : S ⊆ f}`. -/
theorem card_disjoint_eq (F : Finset (Finset α)) (e : Finset α) :
    ((F.filter fun f => Disjoint e f).card : ℤ) =
      ∑ S ∈ e.powerset, (-1) ^ S.card * ((F.filter (S ⊆ ·)).card : ℤ) := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have : e.powerset.filter (· ⊆ f) = (e ∩ f).powerset := by
    ext S
    simp [subset_inter_iff]
  rw [this, sum_powerset_neg_one_pow_card]
  simp only [disjoint_iff_inter_eq_empty]

/-! ### Theorem A5a -/

/-- `λ_i = C(v−i, t−i) / C(k−i, t−i)`, the number of blocks of `S(t,k,v)` through an `i`-set. -/
def lam (t k v i : ℕ) : ℕ := (v - i).choose (t - i) / (k - i).choose (t - i)

/-- `n₀(t,k,v) = Σ_{i<t} (−1)^i C(k,i) (λ_i − 1)`. -/
def n0 (t k v : ℕ) : ℤ := ∑ i ∈ range t, (-1) ^ i * (k.choose i : ℤ) * ((lam t k v i : ℤ) - 1)

/-- In `S(t,k,v)`, the blocks through a subset `S` of a block `e`: `λ_{|S|}` if `|S| < t`,
and only `e` if `|S| ≥ t`. -/
theorem steiner_through {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hH : IsSteiner U H t k) (htk : t ≤ k) {e S : Finset α} (he : e ∈ H) (hS : S ⊆ e) :
    (H.filter (S ⊆ ·)).card = if S.card < t then lam t k U.card S.card else 1 := by
  have hSU := hS.trans (hH.within e he)
  split_ifs with hlt
  · have hc := steiner_count hH hSU hlt.le
    have hpos : 0 < (k - S.card).choose (t - S.card) := Nat.choose_pos (by omega)
    unfold lam
    rw [← hc, Nat.mul_div_cancel _ hpos]
  · obtain ⟨T, hTS, hTc⟩ := exists_subset_card_eq (not_lt.1 hlt)
    have h1 := hH.unique T (hTS.trans hSU) hTc
    have hle : (H.filter (S ⊆ ·)).card ≤ 1 :=
      h1 ▸ card_le_card (monotone_filter_right _ fun f _ hf => hTS.trans hf)
    have hpos : 0 < (H.filter (S ⊆ ·)).card := card_pos.2 ⟨e, mem_filter.2 ⟨he, hS⟩⟩
    omega

/-- **Theorem A5a.** In a Steiner system `S(t, k, v)` with `1 ≤ t ≤ k`, every block is
disjoint from exactly `n₀(t, k, v) = Σ_{i<t} (−1)^i C(k,i)(λ_i − 1)` blocks. (Inclusion–exclusion
over the subsets of the block; a subset of size `≥ t` lies only in the block itself.) -/
theorem steiner_disjoint {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hH : IsSteiner U H t k) (ht : 1 ≤ t) (htk : t ≤ k) {e : Finset α} (he : e ∈ H) :
    ((H.filter fun f => Disjoint e f).card : ℤ) = n0 t k U.card := by
  set g : ℕ → ℤ := fun i => (-1) ^ i * if i < t then (lam t k U.card i : ℤ) else 1
  rw [card_disjoint_eq]
  have h1 : ∑ S ∈ e.powerset, (-1) ^ S.card * ((H.filter (S ⊆ ·)).card : ℤ) =
      ∑ S ∈ e.powerset, g S.card := by
    refine sum_congr rfl fun S hS => ?_
    rw [steiner_through hH htk he (mem_powerset.1 hS)]
    simp only [g]
    split_ifs <;> simp
  rw [h1, sum_powerset_apply_card g, hH.card_eq e he]
  have h2 : ∀ i ∈ range (k + 1), k.choose i • g i =
      (-1) ^ i * (k.choose i : ℤ) +
        if i < t then (-1) ^ i * (k.choose i : ℤ) * ((lam t k U.card i : ℤ) - 1) else 0 := by
    intro i _
    simp only [g, nsmul_eq_mul]
    split_ifs <;> ring
  rw [sum_congr rfl h2, sum_add_distrib, Int.alternating_sum_range_choose, if_neg (by omega),
    zero_add, ← sum_filter]
  have : (range (k + 1)).filter (· < t) = range t := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [this, n0]

/-- A Steiner system `S(t, k, v)` with `t ≤ v` has a block. -/
theorem IsSteiner.nonempty {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hH : IsSteiner U H t k) (htv : t ≤ U.card) : H.Nonempty := by
  obtain ⟨T, hTU, hT⟩ := exists_subset_card_eq htv
  have := hH.unique T hTU hT
  obtain ⟨e, he⟩ := card_pos.1 (this ▸ Nat.one_pos)
  exact ⟨e, (mem_filter.1 he).1⟩

/-- A Steiner system `S(t, k, v)`, `1 ≤ t ≤ k ≤ v`, exists only if `n₀(t, k, v) ≥ 0`. -/
theorem steiner_n0_nonneg {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hH : IsSteiner U H t k) (ht : 1 ≤ t) (htk : t ≤ k) (htv : t ≤ U.card) :
    0 ≤ n0 t k U.card := by
  obtain ⟨e, he⟩ := hH.nonempty htv
  rw [← steiner_disjoint hH ht htk he]
  positivity

omit [DecidableEq α] in
/-- A `k`-uniform family is Sperner. -/
theorem isSperner_of_uniform {H : Finset (Finset α)} {k : ℕ} (h : ∀ e ∈ H, e.card = k) :
    IsSperner H := fun e he f hf hef =>
  eq_of_subset_of_card_le hef (by rw [h e he, h f hf])

/-- If `n₀(t, k, v) > 0`, two blocks of `S(t, k, v)` are disjoint, so no Steiner system with
these parameters is self-transversal. -/
theorem steiner_tr_ne {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hH : IsSteiner U H t k) (ht : 1 ≤ t) (htk : t ≤ k) (htv : t ≤ U.card)
    (h0 : 0 < n0 t k U.card) : tr U H ≠ H := by
  intro htr
  have hI := ((tr_eq_self_iff hH.within (isSperner_of_uniform hH.card_eq)).1 htr).1
  obtain ⟨e, he⟩ := hH.nonempty htv
  have hd := steiner_disjoint hH ht htk he
  have : H.filter (fun f => Disjoint e f) = ∅ := by
    refine filter_eq_empty_iff.2 fun f hf hdis => ?_
    by_cases hef : e = f
    · subst hef
      have := hH.card_eq e he
      rw [(disjoint_self_iff_empty e).1 hdis, card_empty] at this
      omega
    · exact not_disjoint_iff_nonempty_inter.2 (hI e he f hf hef) hdis
  rw [this, card_empty, Nat.cast_zero] at hd
  omega

/-! ### Observation A5b: the parameter table -/

/-- Parameters `(t, k, v)` with `n₀ > 0`: no Steiner system with them is self-transversal. -/
def n0Positive : List (ℕ × ℕ × ℕ) :=
  [(2, 3, 9), (2, 3, 13), (2, 3, 15), (3, 4, 8), (3, 4, 10), (3, 4, 14), (3, 4, 16), (5, 6, 12),
    (5, 8, 24)]

/-- Parameters `(t, k, v)` with `n₀ < 0`: no Steiner system with them exists. -/
def n0Negative : List (ℕ × ℕ × ℕ) :=
  [(2, 6, 16), (2, 6, 21), (2, 12, 45), (2, 10, 46), (2, 10, 55), (4, 12, 57), (2, 15, 85),
    (2, 14, 92), (2, 20, 96), (2, 12, 100)]

/-- **Observation A5b.** The values of `n₀` (kernel `decide`). -/
theorem n0_table :
    (n0Positive.map fun p => n0 p.1 p.2.1 p.2.2) = [2, 10, 16, 1, 3, 20, 39, 1, 30] ∧
    (n0Negative.map fun p => n0 p.1 p.2.1 p.2.2) =
      [-5, -5, -22, -18, -18, -195, -42, -39, -57, -22] := by
  decide

/-- **Observation A5b.** No Steiner system with parameters in `n0Positive` (among them every
`S(2,3,15)`, every `S(3,4,16)` and the Witt design `S(5,8,24)`) is self-transversal. -/
theorem steiner_tr_ne_of_table {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hH : IsSteiner U H t k) (hp : (t, k, U.card) ∈ n0Positive) : tr U H ≠ H := by
  have h : ∀ p ∈ n0Positive, 1 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧ 0 < n0 p.1 p.2.1 p.2.2 := by
    decide
  obtain ⟨h1, h2, h3, h4⟩ := h _ hp
  exact steiner_tr_ne hH h1 h2 h3 h4

/-- **Observation A5b.** No Steiner system has parameters in `n0Negative`. -/
theorem not_steiner_of_table {U : Finset α} {H : Finset (Finset α)} {t k : ℕ}
    (hp : (t, k, U.card) ∈ n0Negative) : ¬ IsSteiner U H t k := by
  have h : ∀ p ∈ n0Negative, 1 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧ n0 p.1 p.2.1 p.2.2 < 0 := by
    decide
  obtain ⟨h1, h2, h3, h4⟩ := h _ hp
  exact fun hH => absurd (steiner_n0_nonneg hH h1 h2 h3) (not_le.2 h4)

/-! ### Theorem A5c: `S(t, t+1, 2t+3)` -/

section Witt

variable {U : Finset α} {H : Finset (Finset α)} {t : ℕ}

/-- In `S(t, t+1, 2t+3)`, an `i`-set (`i ≤ t`) lies in `N` blocks with
`(t+3)·N = C(2t+3−i, t+1−i)`. -/
theorem witt_count (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) {S : Finset α}
    (hSU : S ⊆ U) (hSt : S.card ≤ t) :
    (t + 3) * (H.filter (S ⊆ ·)).card = (2 * t + 3 - S.card).choose (t + 1 - S.card) := by
  have hc := steiner_count hH hSU hSt
  set m := t - S.card
  have e1 : t + 1 - S.card = m + 1 := by omega
  rw [e1, Nat.choose_succ_self_right, hv] at hc
  rw [e1]
  have e2 := Nat.choose_succ_right_eq (2 * t + 3 - S.card) m
  have e3 : 2 * t + 3 - S.card - m = t + 3 := by omega
  rw [e3] at e2
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m)
  rw [e2, ← hc, Nat.succ_eq_add_one]
  ring

/-- The `(t+1)`-subsets of `U`. -/
abbrev allK (U : Finset α) (t : ℕ) : Finset (Finset α) := U.powersetCard (t + 1)

theorem allK_through {S : Finset α} (hSU : S ⊆ U) (hS : S.card ≤ t + 1) :
    ((allK U t).filter (S ⊆ ·)).card = (U.card - S.card).choose (t + 1 - S.card) := by
  rw [← card_between hSU hS]
  congr 1
  ext T
  simp only [mem_filter, mem_powersetCard, mem_powerset]
  tauto

theorem allK_disjoint {B : Finset α} (hBU : B ⊆ U) :
    ((allK U t).filter fun f => Disjoint B f).card = (U.card - B.card).choose (t + 1) := by
  rw [← card_sdiff_of_subset hBU, ← card_powersetCard]
  congr 1
  ext T
  simp only [mem_filter, mem_powersetCard, subset_sdiff]
  constructor
  · rintro ⟨⟨hTU, hc⟩, hd⟩; exact ⟨⟨hTU, hd.symm⟩, hc⟩
  · rintro ⟨⟨hTU, hd⟩, hc⟩; exact ⟨⟨hTU, hc⟩, hd.symm⟩

/-- `(t+3) · #{blocks disjoint from B} = (t+2)(1 + (−1)^{t+1})`, by inclusion–exclusion against
the family of all `(t+1)`-sets. -/
theorem witt_disjoint (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) {B : Finset α}
    (hB : B ∈ H) :
    ((t + 3 : ℕ) : ℤ) * ((H.filter fun f => Disjoint B f).card : ℤ) =
      (t + 2) * (1 + (-1) ^ (t + 1)) := by
  have hBU := hH.within B hB
  have hBc := hH.card_eq B hB
  rw [card_disjoint_eq, mul_sum]
  have h1 : ∀ S ∈ B.powerset,
      ((t + 3 : ℕ) : ℤ) * ((-1) ^ S.card * ((H.filter (S ⊆ ·)).card : ℤ)) =
        (-1) ^ S.card * (((allK U t).filter (S ⊆ ·)).card : ℤ) +
          if S = B then (-1 : ℤ) ^ S.card * ((t : ℤ) + 2) else 0 := by
    intro S hS
    rw [mem_powerset] at hS
    have hSU := hS.trans hBU
    rw [allK_through hSU (hBc ▸ card_le_card hS), hv]
    by_cases hSB : S = B
    · subst hSB
      have hN : (H.filter (S ⊆ ·)).card = 1 := by
        rw [steiner_through hH (by omega) hB subset_rfl, if_neg (by omega)]
      rw [hN, hBc, if_pos rfl, show 2 * t + 3 - (t + 1) = t + 2 by omega, Nat.sub_self,
        Nat.choose_zero_right]
      push_cast
      ring
    · have hlt : S.card ≤ t := by
        have := card_lt_card (ssubset_of_subset_of_ne hS hSB)
        omega
      have := witt_count hH hv hSU hlt
      rw [if_neg hSB, add_zero, ← this]
      push_cast
      ring
  rw [sum_congr rfl h1, sum_add_distrib, ← card_disjoint_eq, allK_disjoint hBU, hv,
    hBc, show 2 * t + 3 - (t + 1) = t + 2 by omega, Nat.choose_succ_self_right,
    sum_ite_eq' B.powerset B, if_pos (mem_powerset_self B), hBc]
  push_cast
  ring

/-- No Steiner system `S(t, t+1, 2t+3)` exists for odd `t`. -/
theorem witt_even (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) : Even t := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨B, hB⟩ := hH.nonempty (by omega)
  have h := witt_disjoint hH hv hB
  rw [Even.neg_one_pow (by rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact hodd)] at h
  set D := (H.filter fun f => Disjoint B f).card
  have : (t + 3) * D = 2 * t + 4 := by
    have : ((t + 3 : ℕ) : ℤ) * (D : ℤ) = 2 * t + 4 := by rw [h]; ring
    exact_mod_cast this
  rcases Nat.lt_or_ge D 2 with hD | hD
  · rcases (show D = 0 ∨ D = 1 by omega) with h0 | h0 <;> rw [h0] at this <;> omega
  · have := Nat.mul_le_mul_left (t + 3) hD
    omega

/-- `S(t, t+1, 2t+3)` is intersecting. -/
theorem witt_intersecting (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) :
    OpenAI.Intersecting H := by
  intro e he f hf hef
  have h := witt_disjoint hH hv he
  rw [Odd.neg_one_pow (by rw [Nat.odd_add_one, Nat.not_odd_iff_even]; exact witt_even hH hv)]
    at h
  have hD : (H.filter fun f => Disjoint e f).card = 0 := by
    have : ((t + 3 : ℕ) : ℤ) * ((H.filter fun f => Disjoint e f).card : ℤ) = 0 := by
      rw [h]; ring
    rcases mul_eq_zero.1 this with h0 | h0
    · omega
    · exact_mod_cast h0
  rw [card_eq_zero, filter_eq_empty_iff] at hD
  exact not_disjoint_iff_nonempty_inter.1 (hD hf)

/-- Two blocks inside a `(t+2)`-set are equal: they share `t` points. -/
theorem witt_two_in (hH : IsSteiner U H t (t + 1)) {X e f : Finset α} (hX : X.card = t + 2)
    (he : e ∈ H) (hf : f ∈ H) (heX : e ⊆ X) (hfX : f ⊆ X) : e = f := by
  have hi : t ≤ (e ∩ f).card := by
    have h1 := card_union_add_card_inter e f
    have h2 := card_le_card (union_subset heX hfX)
    rw [hH.card_eq e he, hH.card_eq f hf] at h1
    omega
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hi
  have h1 := hH.unique T (hT.trans (inter_subset_left.trans (hH.within e he))) hTc
  exact card_le_one.1 h1.le e (mem_filter.2 ⟨he, hT.trans inter_subset_left⟩) f
    (mem_filter.2 ⟨hf, hT.trans inter_subset_right⟩)

/-- Every `(t+2)`-subset of `U` contains a block or is the complement of a block. (Count: the
`b(t+2)` sets containing a block and the `b` complements are disjoint, and
`b(t+3) = C(2t+3, t+2)`.) -/
theorem witt_cover (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) {X : Finset α}
    (hXU : X ⊆ U) (hX : X.card = t + 2) : upHit H X ∨ ∃ f ∈ H, X = U \ f := by
  have hI := witt_intersecting hH hv
  set C1 := H.biUnion fun e => (U \ e).image (insert · e)
  set C2 := H.image (U \ ·)
  have hC1 : C1.card = H.card * (t + 2) := by
    rw [card_biUnion]
    · have : ∀ e ∈ H, ((U \ e).image (insert · e)).card = t + 2 := by
        intro e he
        rw [card_image_of_injOn, card_sdiff_of_subset (hH.within e he), hv, hH.card_eq e he]
        · omega
        · intro y hy z hz hyz
          simp only [coe_sdiff, Set.mem_sdiff, mem_coe] at hy hz
          have hyz' : insert y e = insert z e := hyz
          have : y ∈ insert z e := hyz' ▸ mem_insert_self y e
          rcases mem_insert.1 this with h | h
          · exact h
          · exact absurd h hy.2
      rw [sum_congr rfl this, sum_const, smul_eq_mul]
    · intro e he f hf hef
      refine disjoint_left.2 fun X hXe hXf => hef ?_
      simp only [mem_image, mem_sdiff] at hXe hXf
      obtain ⟨y, ⟨hyU, hye⟩, rfl⟩ := hXe
      obtain ⟨z, ⟨hzU, hzf⟩, hz⟩ := hXf
      refine witt_two_in hH (X := insert y e) ?_ he hf (subset_insert y e)
        (hz ▸ subset_insert z f)
      rw [card_insert_of_notMem hye, hH.card_eq e he]
  have hC2 : C2.card = H.card := by
    refine card_image_of_injOn fun e he f hf hef => ?_
    simp only [mem_coe] at he hf
    rw [← Finset.sdiff_sdiff_eq_self (hH.within e he), ← Finset.sdiff_sdiff_eq_self (hH.within f hf)]
    exact congrArg (U \ ·) hef
  have hb : H.card * (t + 3) = (2 * t + 3).choose (t + 2) := by
    have := witt_count hH hv (empty_subset U) (Nat.zero_le t)
    rw [filter_true_of_mem fun e _ => empty_subset e, card_empty, Nat.sub_zero, Nat.sub_zero,
      mul_comm] at this
    rw [this, Nat.choose_symm_of_eq_add (by omega : 2 * t + 3 = (t + 1) + (t + 2))]
  have hsub : C1 ∪ C2 ⊆ U.powersetCard (t + 2) := by
    intro Y hY
    rw [mem_powersetCard]
    rcases mem_union.1 hY with hY | hY
    · obtain ⟨e, he, hY⟩ := mem_biUnion.1 hY
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hY
      rw [mem_sdiff] at hy
      exact ⟨insert_subset hy.1 (hH.within e he), by
        rw [card_insert_of_notMem hy.2, hH.card_eq e he]⟩
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hY
      refine ⟨sdiff_subset, ?_⟩
      rw [card_sdiff_of_subset (hH.within f hf), hv, hH.card_eq f hf]
      omega
  have hdisj : Disjoint C1 C2 := by
    refine disjoint_left.2 fun Y hY1 hY2 => ?_
    obtain ⟨e, he, hY⟩ := mem_biUnion.1 hY1
    obtain ⟨y, _, rfl⟩ := mem_image.1 hY
    obtain ⟨f, hf, hfY⟩ := mem_image.1 hY2
    have hef : Disjoint e f := by
      rw [disjoint_left]
      intro z hze hzf
      have : z ∈ U \ f := hfY ▸ mem_insert_of_mem hze
      exact (mem_sdiff.1 this).2 hzf
    by_cases h : e = f
    · subst h
      have := hH.card_eq e he
      rw [(disjoint_self_iff_empty e).1 hef, card_empty] at this
      omega
    · exact not_disjoint_iff_nonempty_inter.2 (hI e he f hf h) hef
  have heq : C1 ∪ C2 = U.powersetCard (t + 2) := by
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_union_of_disjoint hdisj, hC1, hC2, card_powersetCard, hv, ← hb]
    ring_nf
    rfl
  have hXm : X ∈ C1 ∪ C2 := heq ▸ mem_powersetCard.2 ⟨hXU, hX⟩
  rcases mem_union.1 hXm with h | h
  · obtain ⟨e, he, hY⟩ := mem_biUnion.1 h
    obtain ⟨y, _, rfl⟩ := mem_image.1 hY
    exact Or.inl ⟨e, he, subset_insert y e⟩
  · obtain ⟨f, hf, rfl⟩ := mem_image.1 h
    exact Or.inr ⟨f, hf, rfl⟩

/-- Every subset of `U` with at least `t+3` points contains a block. -/
theorem witt_large (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) {Y : Finset α}
    (hYU : Y ⊆ U) (hY : t + 3 ≤ Y.card) : upHit H Y := by
  by_contra hno
  have hno' : ∀ Z ⊆ Y, ¬ upHit H Z := fun Z hZ ⟨e, he, heZ⟩ => hno ⟨e, he, heZ.trans hZ⟩
  -- a block `B` whose complement `S` lies in `Y`
  obtain ⟨S, hSY, hSc⟩ := exists_subset_card_eq (show t + 2 ≤ Y.card by omega)
  obtain ⟨B, hB, hSB⟩ := (witt_cover hH hv (hSY.trans hYU) hSc).resolve_left (hno' S hSY)
  obtain ⟨x, hxY, hxS⟩ : ∃ x ∈ Y, x ∉ S := by
    by_contra h
    push Not at h
    have := card_le_card (show Y ⊆ S from h)
    omega
  have hxB : x ∈ B := by
    by_contra h
    exact hxS (hSB ▸ mem_sdiff.2 ⟨hYU hxY, h⟩)
  -- for `y ∈ S`, the set `S − y + x` is the complement of a block containing `(B − x) + y`
  have hblock : ∀ y ∈ S, ∃ B' ∈ H, B.erase x ⊆ B' ∧ y ∈ B' ∧ ∀ z ∈ S, z ≠ y → z ∉ B' := by
    intro y hy
    set S' := insert x (S.erase y)
    have hS'Y : S' ⊆ Y := insert_subset hxY ((erase_subset y S).trans hSY)
    have hS'c : S'.card = t + 2 := by
      rw [card_insert_of_notMem (fun h => hxS (mem_of_mem_erase h)), card_erase_of_mem hy, hSc]
      rfl
    obtain ⟨B', hB', hS'B'⟩ :=
      (witt_cover hH hv (hS'Y.trans hYU) hS'c).resolve_left (hno' S' hS'Y)
    have hmem : ∀ z ∈ U, z ∉ S' → z ∈ B' := fun z hz hzS => by
      by_contra h
      exact hzS (hS'B' ▸ mem_sdiff.2 ⟨hz, h⟩)
    refine ⟨B', hB', fun z hz => ?_, ?_, fun z hz hzy hzB => ?_⟩
    · obtain ⟨hzx, hzB⟩ := mem_erase.1 hz
      refine hmem z (hH.within B hB hzB) fun h => ?_
      rcases mem_insert.1 h with h | h
      · exact hzx h
      · have : z ∈ U \ B := hSB ▸ mem_of_mem_erase h
        exact (mem_sdiff.1 this).2 hzB
    · refine hmem y (hSY.trans hYU hy) fun h => ?_
      rcases mem_insert.1 h with h | h
      · exact hxS (h ▸ hy)
      · exact notMem_erase y S h
    · have : z ∈ S' := mem_insert_of_mem (mem_erase.2 ⟨hzy, hz⟩)
      rw [hS'B'] at this
      exact (mem_sdiff.1 this).2 hzB
  -- two of them contain the `t`-set `B − x`: contradiction
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := one_lt_card.1 (show 1 < S.card by omega)
  obtain ⟨B₁, hB₁, hx₁, hm₁, -⟩ := hblock y₁ hy₁
  obtain ⟨B₂, hB₂, hx₂, -, hn₂⟩ := hblock y₂ hy₂
  have hT : (B.erase x).card = t := by rw [card_erase_of_mem hxB, hH.card_eq B hB]; rfl
  have h1 := hH.unique (B.erase x) ((erase_subset x B).trans (hH.within B hB)) hT
  have : B₁ = B₂ :=
    card_le_one.1 h1.le B₁ (mem_filter.2 ⟨hB₁, hx₁⟩) B₂ (mem_filter.2 ⟨hB₂, hx₂⟩)
  exact hn₂ y₁ hy₁ hne (this ▸ hm₁)

/-- **Theorem A5c.** Let `H` be a Steiner system `S(t, t+1, 2t+3)` on `U`. Then `t` is even and
`Tr(H) = H`. (The Fano plane is `t = 2`, the Witt design `w11` is `t = 4`.)

Proof: inclusion–exclusion against all `(t+1)`-sets gives
`(t+3)·#{blocks disjoint from B} = (t+2)(1 + (−1)^{t+1})`, so `t` is even and `H` is
intersecting. Counting shows every `(t+2)`-set contains a block or is the complement of one;
then every set of `≥ t+3` points contains a block, so `H` is not 2-colourable. Proposition A3
concludes. -/
theorem witt_tr_eq (hH : IsSteiner U H t (t + 1)) (hv : U.card = 2 * t + 3) :
    Even t ∧ tr U H = H := by
  refine ⟨witt_even hH hv, (tr_eq_self_iff hH.within (isSperner_of_uniform hH.card_eq)).2
    ⟨witt_intersecting hH hv, fun h0 => by have := hH.card_eq ∅ h0; simp at this, ?_⟩⟩
  -- a set with at least `t+2` points, or its complement, contains a block
  have key : ∀ X ⊆ U, t + 2 ≤ X.card → upHit H X ∨ upHit H (U \ X) := by
    intro X hXU hX
    rcases Nat.lt_or_ge X.card (t + 3) with h | h
    · rcases witt_cover hH hv hXU (by omega) with h' | ⟨f, hf, rfl⟩
      · exact Or.inl h'
      · exact Or.inr ⟨f, hf, by rw [Finset.sdiff_sdiff_eq_self (hH.within f hf)]⟩
    · exact Or.inl (witt_large hH hv hXU h)
  rintro ⟨A, hAU, h1, h2⟩
  have hc := card_sdiff_add_card_eq_card hAU
  rcases Nat.lt_or_ge A.card (t + 2) with hA | hA
  · rcases key (U \ A) sdiff_subset (by omega) with h | h
    · exact h2 h
    · rw [Finset.sdiff_sdiff_eq_self hAU] at h; exact h1 h
  · rcases key A hAU hA with h | h
    · exact h1 h
    · exact h2 h

end Witt

end HD

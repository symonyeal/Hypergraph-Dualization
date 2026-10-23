/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Decision trees for the GK family are exponential

Jukna, Razborov, Savický and Wegener (*Comput. Complexity* 8, 1999, Lemma 2.2 and Theorem 2.4)
bound the size of a decision tree by the `ℓ₁` norm of the function's Fourier spectrum and show
that the iterated NAND needs `2(27/16)^{n/4}` leaves. The GK family `coalt (2k-1)` is the iterated
NAND with its inputs complemented. This module proves both steps for `coalt i`, `i ≥ 2`:
every decision tree computing `upHit (coalt i)` on the subsets of `range (2^i)` has at least
`2·(27/16)^(2^(i-2))` leaves (`gk_leaves`).

Legend
  DTree α     decision trees querying vertices of `α`; `eval t X` follows `x ∈ X`
  leaves t    number of leaves of `t`
  sg b        `±1` encoding of a Boolean, `true ↦ -1`
  chi S X     the character `χ_S(X) = (-1)^|S ∩ X|`
  wc U f S    `2^|U| · f̂(S)`: the unnormalised Fourier coefficient on the cube of subsets of `U`
  l1 U f      `Σ_{S ⊆ U} |wc U f S|` = `2^|U| · ‖f̂‖₁`
  gkF i       the function `X ↦ upHit (coalt i) X`
  R i, sh i   `range (2^i)` and the shift by `2^i` that places the second copy
  dense j     JRSW's dense supports at level `j + 2`: nonempty at level 2, then a union of a dense
              support of each copy
  dsum j      `Σ_{S ∈ dense j} |wc (R (j+2)) (gkF (j+2)) S|`

| Lean | Source |
| --- | --- |
| `l1_le_leaves` | JRSW Lemma 2.2 with `S = ∅`: `‖f̂‖₁ ≤ dt(f)` |
| `wc_gk_succ` | the product rule for a gate on disjoint inputs |
| `dsum_succ`, `dsum_zero`, `dsum_eq` | JRSW Theorem 2.4: `c_h = c_{h-1}²/2`, `c_2 = 27/8` |
| `gk_leaves` | `dt(coalt i) ≥ 2·(27/16)^(2^(i-2))` |
-/
import HypergraphDualization.Families
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace HD

open Finset

/-! ### Decision trees -/

/-- A decision tree querying the vertices of `α`. -/
inductive DTree (α : Type*) where
  | leaf : Bool → DTree α
  | node : α → DTree α → DTree α → DTree α

namespace DTree

variable {α : Type*} [DecidableEq α]

/-- The value on the input whose true variables are `X`: `node x lo hi` reads `x ∈ X`. -/
def eval : DTree α → Finset α → Bool
  | leaf b, _ => b
  | node x lo hi, X => if x ∈ X then eval hi X else eval lo X

/-- The number of leaves, the size measure of JRSW. -/
def leaves : DTree α → ℕ
  | leaf _ => 1
  | node _ lo hi => leaves lo + leaves hi

end DTree

/-! ### Fourier coefficients on the cube of subsets of `U` -/

section Fourier

variable {α : Type*} [DecidableEq α]

/-- `true ↦ -1`, `false ↦ 1`. -/
def sg (b : Bool) : ℤ := if b then -1 else 1

/-- The character `χ_S(X) = (-1)^|S ∩ X|`, as a product. -/
def chi (S X : Finset α) : ℤ := ∏ i ∈ S, if i ∈ X then -1 else 1

/-- The unnormalised Fourier coefficient `2^|U| f̂(S)`. -/
def wc (U : Finset α) (f : Finset α → Bool) (S : Finset α) : ℤ :=
  ∑ X ∈ U.powerset, sg (f X) * chi S X

/-- `2^|U|` times the `ℓ₁` norm of the spectrum. -/
def l1 (U : Finset α) (f : Finset α → Bool) : ℤ := ∑ S ∈ U.powerset, |wc U f S|

theorem chi_insert_right {S X : Finset α} {x : α} (hx : x ∉ X) :
    chi S (insert x X) = chi S X * (if x ∈ S then -1 else 1) := by
  by_cases hxS : x ∈ S
  · have key : ∀ i ∈ S.erase x, (if i ∈ insert x X then (-1 : ℤ) else 1) =
        if i ∈ X then -1 else 1 := fun i hi => by
      simp [ne_of_mem_erase hi]
    rw [chi, chi, ← mul_prod_erase S _ hxS, ← mul_prod_erase S _ hxS, prod_congr rfl key]
    simp [hx, hxS]
  · have key : ∀ i ∈ S, (if i ∈ insert x X then (-1 : ℤ) else 1) = if i ∈ X then -1 else 1 :=
      fun i hi => by simp [show i ≠ x from fun h => hxS (h ▸ hi)]
    rw [chi, chi, prod_congr rfl key]
    simp [hxS]

theorem chi_insert_left {S X : Finset α} {x : α} (hx : x ∉ S) :
    chi (insert x S) X = (if x ∈ X then -1 else 1) * chi S X := by
  simp only [chi, prod_insert hx]

/-- Orthogonality: the characters sum to `2^|U|` on `S` disjoint from `U`, else to `0`. -/
theorem sum_chi (U S : Finset α) :
    ∑ X ∈ U.powerset, chi S X = if Disjoint S U then 2 ^ U.card else 0 := by
  induction U using Finset.induction_on with
  | empty => simp [chi]
  | insert a U ha ih =>
    rw [sum_powerset_insert ha]
    have hsum : ∑ X ∈ U.powerset, chi S (insert a X) =
        (∑ X ∈ U.powerset, chi S X) * (if a ∈ S then -1 else 1) := by
      rw [sum_mul]
      exact sum_congr rfl fun X hX =>
        chi_insert_right (fun h => ha (mem_powerset.1 hX h))
    rw [hsum, ih, card_insert_of_notMem ha]
    by_cases haS : a ∈ S <;> by_cases hd : Disjoint S U <;>
      simp [haS, hd, disjoint_insert_right, pow_succ, mul_two]

theorem wc_congr {U : Finset α} {f g : Finset α → Bool} (h : ∀ X ⊆ U, f X = g X)
    (S : Finset α) : wc U f S = wc U g S :=
  sum_congr rfl fun X hX => by rw [h X (mem_powerset.1 hX)]

theorem l1_congr {U : Finset α} {f g : Finset α → Bool} (h : ∀ X ⊆ U, f X = g X) :
    l1 U f = l1 U g := sum_congr rfl fun S _ => by rw [wc_congr h]

theorem l1_const (U : Finset α) (b : Bool) : l1 U (fun _ => b) = 2 ^ U.card := by
  have hw : ∀ S ∈ U.powerset, |wc U (fun _ => b) S| = if S = ∅ then 2 ^ U.card else 0 := by
    intro S hS
    have hSU := mem_powerset.1 hS
    have hd : Disjoint S U ↔ S = ∅ :=
      ⟨fun h => disjoint_self.1 (h.mono_right hSU), fun h => h ▸ disjoint_empty_left _⟩
    rw [wc, ← mul_sum, sum_chi, abs_mul]
    by_cases h0 : S = ∅
    · simp [h0, sg, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) _)]
      cases b <;> simp
    · simp [h0, hd]
  rw [l1, sum_congr rfl hw, sum_ite_eq' _ _ _]
  simp

/-! ### `‖f̂‖₁ ≤ dt(f)` -/

/-- The half of a coefficient at `x` over the inputs without `x`. -/
def halfP (U : Finset α) (x : α) (f : Finset α → Bool) (S : Finset α) : ℤ :=
  ∑ X ∈ (U.erase x).powerset, sg (f X) * chi S X

/-- The half over the inputs with `x`. -/
def halfQ (U : Finset α) (x : α) (f : Finset α → Bool) (S : Finset α) : ℤ :=
  ∑ X ∈ (U.erase x).powerset, sg (f (insert x X)) * chi S X

/-- Splitting a coefficient at `x ∈ U` into its two halves. -/
theorem wc_split {U : Finset α} {x : α} (hx : x ∈ U) (f : Finset α → Bool) (S : Finset α) :
    wc U f S = halfP U x f S + (if x ∈ S then -1 else 1) * halfQ U x f S := by
  conv_lhs => rw [wc, ← insert_erase hx, sum_powerset_insert (notMem_erase x U)]
  rw [halfP, halfQ, mul_sum]
  congr 1
  refine sum_congr rfl fun X hX => ?_
  have : x ∉ X := fun h => notMem_erase x U (mem_powerset.1 hX h)
  rw [chi_insert_right this]; ring

theorem halfP_insert {U : Finset α} {x : α} (f : Finset α → Bool) {S : Finset α} (hS : x ∉ S) :
    halfP U x f (insert x S) = halfP U x f S := by
  refine sum_congr rfl fun X hX => ?_
  have : x ∉ X := fun h => notMem_erase x U (mem_powerset.1 hX h)
  rw [chi_insert_left hS, if_neg this, one_mul]

theorem halfQ_insert {U : Finset α} {x : α} (f : Finset α → Bool) {S : Finset α} (hS : x ∉ S) :
    halfQ U x f (insert x S) = halfQ U x f S := by
  refine sum_congr rfl fun X hX => ?_
  have : x ∉ X := fun h => notMem_erase x U (mem_powerset.1 hX h)
  rw [chi_insert_left hS, if_neg this, one_mul]

/-- For `x ∉ S`, the coefficients at `S` and `S + x` are the sum and difference of the halves. -/
theorem wc_pair {U : Finset α} {x : α} (hx : x ∈ U) (f : Finset α → Bool) {S : Finset α}
    (hS : x ∉ S) :
    wc U f S = halfP U x f S + halfQ U x f S ∧
      wc U f (insert x S) = halfP U x f S - halfQ U x f S := by
  rw [wc_split hx, wc_split hx, if_neg hS, if_pos (mem_insert_self x S), halfP_insert f hS,
    halfQ_insert f hS]
  constructor <;> ring

theorem sum_powerset_erase_insert {U : Finset α} {x : α} (hx : x ∈ U) (F : Finset α → ℤ) :
    ∑ S ∈ U.powerset, F S =
      ∑ S ∈ (U.erase x).powerset, (F S + F (insert x S)) := by
  conv_lhs => rw [← insert_erase hx, sum_powerset_insert (notMem_erase x U)]
  rw [sum_add_distrib]

/-- `|p + q| + |p - q|` is at most `2|p| + 2|q|` and at least `2|p|`. -/
theorem abs_pair_le (p q : ℤ) : |p + q| + |p - q| ≤ 2 * |p| + 2 * |q| := by
  have := abs_add_le p q; have := abs_sub p q; linarith

theorem two_abs_le (p q : ℤ) : 2 * |p| ≤ |p + q| + |p - q| := by
  have h := abs_add_le (p + q) (p - q)
  have e : p + q + (p - q) = 2 * p := by ring
  rw [e, abs_mul, abs_two] at h; exact h

theorem two_abs_le' (p q : ℤ) : 2 * |q| ≤ |p + q| + |p - q| := by
  have h := abs_sub (p + q) (p - q)
  have e : p + q - (p - q) = 2 * q := by ring
  rw [e, abs_mul, abs_two] at h; exact h

theorem l1_node_le (U : Finset α) (x : α) (lo hi : DTree α) :
    l1 U (DTree.node x lo hi).eval ≤ l1 U lo.eval + l1 U hi.eval := by
  by_cases hx : x ∈ U
  · have hP : ∀ S, halfP U x (DTree.node x lo hi).eval S = halfP U x lo.eval S := fun S =>
      sum_congr rfl fun X hX => by
        have : x ∉ X := fun h => notMem_erase x U (mem_powerset.1 hX h)
        simp [DTree.eval, this]
    have hQ : ∀ S, halfQ U x (DTree.node x lo hi).eval S = halfQ U x hi.eval S := fun S =>
      sum_congr rfl fun X _ => by simp [DTree.eval]
    rw [l1, l1, l1, sum_powerset_erase_insert hx, sum_powerset_erase_insert hx,
      sum_powerset_erase_insert hx, ← sum_add_distrib]
    refine sum_le_sum fun S hS => ?_
    have hxS : x ∉ S := fun h => notMem_erase x U (mem_powerset.1 hS h)
    obtain ⟨n1, n2⟩ := wc_pair hx (DTree.node x lo hi).eval hxS
    obtain ⟨l1', l2⟩ := wc_pair hx lo.eval hxS
    obtain ⟨h1, h2⟩ := wc_pair hx hi.eval hxS
    rw [n1, n2, hP, hQ, l1', l2, h1, h2]
    have a := abs_pair_le (halfP U x lo.eval S) (halfQ U x hi.eval S)
    have b := two_abs_le (halfP U x lo.eval S) (halfQ U x lo.eval S)
    have c := two_abs_le' (halfP U x hi.eval S) (halfQ U x hi.eval S)
    linarith
  · have h : ∀ X ⊆ U, (DTree.node x lo hi).eval X = lo.eval X := fun X hX => by
      have : x ∉ X := fun h => hx (hX h)
      simp [DTree.eval, this]
    rw [l1_congr h]
    have : 0 ≤ l1 U hi.eval := sum_nonneg fun _ _ => abs_nonneg _
    linarith

/-- **JRSW Lemma 2.2 (`S = ∅`).** A decision tree has at least `‖f̂‖₁` leaves:
`Σ_S |wc U f S| ≤ 2^|U| · leaves`. -/
theorem l1_le_leaves (U : Finset α) : ∀ t : DTree α, l1 U t.eval ≤ 2 ^ U.card * t.leaves
  | .leaf b => by
    have : (DTree.leaf b : DTree α).eval = fun _ => b := rfl
    rw [this, l1_const]; simp [DTree.leaves]
  | .node x lo hi => by
    have := l1_node_le U x lo hi
    have := l1_le_leaves U lo
    have := l1_le_leaves U hi
    simp only [DTree.leaves, Nat.cast_add, mul_add]
    linarith

/-- The same bound for any tree that agrees with `f` on the subsets of `U`. -/
theorem l1_le_leaves_of_eval {U : Finset α} {f : Finset α → Bool} (t : DTree α)
    (ht : ∀ X ⊆ U, t.eval X = f X) : l1 U f ≤ 2 ^ U.card * t.leaves := by
  rw [← l1_congr ht]; exact l1_le_leaves U t

end Fourier

/-! ### The GK family: JRSW's dense coefficients -/

section GK

/-- `X ↦ upHit (coalt i) X`; `coalt (2k-1)` is the GK function `f_k`. -/
def gkF (i : ℕ) (X : Finset ℕ) : Bool := decide (upHit (coalt i) X)

theorem range_split (i : ℕ) :
    range (2 ^ (i + 1)) = range (2 ^ i) ∪ (range (2 ^ i)).map (shift (2 ^ i)) := by
  rw [range_map_shift]; ext x; simp only [mem_range, mem_union, mem_filter, pow_succ]; omega

theorem le_of_mem_high {B : Finset ℕ} {i y : ℕ} (hy : y ∈ B.map (shift (2 ^ i))) :
    2 ^ i ≤ y := by
  obtain ⟨z, -, rfl⟩ := mem_map.1 hy; simp [shift]

theorem shift_mem_union {A B : Finset ℕ} {i z : ℕ} (hA : A ⊆ range (2 ^ i)) :
    shift (2 ^ i) z ∈ A ∪ B.map (shift (2 ^ i)) ↔ z ∈ B := by
  constructor
  · intro h
    rcases mem_union.1 h with h | h
    · have := mem_range.1 (hA h); simp [shift] at this
    · exact (mem_map' _).1 h
  · intro h; exact mem_union_right _ (mem_map_of_mem _ h)

theorem low_mem_union {A B : Finset ℕ} {i y : ℕ} (hy : y < 2 ^ i) :
    y ∈ A ∪ B.map (shift (2 ^ i)) ↔ y ∈ A := by
  constructor
  · intro h
    rcases mem_union.1 h with h | h
    · exact h
    · have := le_of_mem_high h; omega
  · exact fun h => mem_union_left _ h

/-- Sum over the subsets of a disjoint union. -/
theorem sum_powerset_union {β : Type*} [AddCommMonoid β] {U V : Finset ℕ} (h : Disjoint U V)
    (F : Finset ℕ → β) :
    ∑ X ∈ (U ∪ V).powerset, F X = ∑ A ∈ U.powerset, ∑ B ∈ V.powerset, F (A ∪ B) := by
  induction V using Finset.induction_on generalizing F with
  | empty => simp
  | insert b V hb ih =>
    have hbU : b ∉ U := fun hbU => disjoint_left.1 h hbU (mem_insert_self b V)
    have h' : Disjoint U V := h.mono_right (subset_insert b V)
    have hbUV : b ∉ U ∪ V := by simp [hbU, hb]
    rw [union_insert, sum_powerset_insert hbUV, ih h', ih h' (fun X => F (insert b X)),
      ← sum_add_distrib]
    refine sum_congr rfl fun A _ => ?_
    rw [sum_powerset_insert hb]
    simp only [union_insert]

theorem sum_powerset_map {β : Type*} [AddCommMonoid β] (φ : ℕ ↪ ℕ) (U : Finset ℕ)
    (F : Finset ℕ → β) :
    ∑ B ∈ (U.map φ).powerset, F B = ∑ B ∈ U.powerset, F (B.map φ) := by
  induction U using Finset.induction_on generalizing F with
  | empty => simp
  | insert a U ha ih =>
    have ha' : φ a ∉ U.map φ := by simpa using ha
    rw [map_insert, sum_powerset_insert ha', sum_powerset_insert ha, ih,
      ih (fun B => F (insert (φ a) B))]
    simp only [map_insert]

/-- The first copy ignores the shifted part of the input. -/
theorem upHit_low {H : Finset (Finset ℕ)} {A B : Finset ℕ} {i : ℕ}
    (hW : Within (range (2 ^ i)) H) :
    upHit H (A ∪ B.map (shift (2 ^ i))) ↔ upHit H A := by
  constructor
  · rintro ⟨e, he, heS⟩
    exact ⟨e, he, fun y hy => (low_mem_union (mem_range.1 (hW e he hy))).1 (heS hy)⟩
  · rintro ⟨e, he, heA⟩; exact ⟨e, he, heA.trans subset_union_left⟩

/-- The second copy `mapH sh H` sees `B.map sh` as `H` sees `B`. -/
theorem upHit_high {H : Finset (Finset ℕ)} {A B : Finset ℕ} {i : ℕ}
    (hA : A ⊆ range (2 ^ i)) :
    upHit (mapH (shift (2 ^ i)) H) (A ∪ B.map (shift (2 ^ i))) ↔ upHit H B := by
  constructor
  · rintro ⟨e', he', heS⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact ⟨e, he, fun z hz => (shift_mem_union hA).1 (heS (mem_map_of_mem _ hz))⟩
  · rintro ⟨e, he, heB⟩
    exact ⟨e.map (shift (2 ^ i)), mem_image_of_mem _ he,
      (map_subset_map.2 heB).trans subset_union_right⟩

/-- A gate on two disjoint copies: union at even `i`, join at odd `i`. -/
theorem gkF_succ (i : ℕ) {A B : Finset ℕ} (hA : A ⊆ range (2 ^ i)) :
    gkF (i + 1) (A ∪ B.map (shift (2 ^ i))) =
      if i % 2 = 0 then (gkF i A || gkF i B) else (gkF i A && gkF i B) := by
  have hW := (alt_props i).2.1
  by_cases hp : i % 2 = 0
  · rw [if_pos hp]
    simp only [gkF, coalt, if_pos hp, upHit_union, upHit_low hW, upHit_high hA]
    simp
  · rw [if_neg hp]
    simp only [gkF, coalt, if_neg hp, upHit_join, upHit_low hW, upHit_high hA]
    simp

theorem chi_split (i : ℕ) {S A T B : Finset ℕ} (hS : S ⊆ range (2 ^ i))
    (hA : A ⊆ range (2 ^ i)) :
    chi (S ∪ T.map (shift (2 ^ i))) (A ∪ B.map (shift (2 ^ i))) = chi S A * chi T B := by
  have hd : Disjoint S (T.map (shift (2 ^ i))) := disjoint_left.2 fun y hy hy' => by
    have := mem_range.1 (hS hy); have := le_of_mem_high hy'; omega
  rw [chi, prod_union hd, prod_map]
  congr 1
  · refine prod_congr rfl fun y hy => ?_
    simp only [low_mem_union (mem_range.1 (hS hy))]
  · refine prod_congr rfl fun z _ => ?_
    simp only [shift_mem_union hA]

theorem two_sg_or (a b : Bool) : 2 * sg (a || b) = -1 + sg a + sg b + sg a * sg b := by
  cases a <;> cases b <;> simp [sg]

theorem two_sg_and (a b : Bool) : 2 * sg (a && b) = 1 + sg a + sg b - sg a * sg b := by
  cases a <;> cases b <;> simp [sg]

/-- **The product rule.** For nonempty supports in both copies, a gate's coefficient is
`± ½` times the product of the copies' coefficients (JRSW eq. (2)). -/
theorem wc_gk_succ (i : ℕ) {S T : Finset ℕ} (hS : S ⊆ range (2 ^ i)) (hT : T ⊆ range (2 ^ i))
    (hS0 : S.Nonempty) (hT0 : T.Nonempty) :
    2 * wc (range (2 ^ (i + 1))) (gkF (i + 1)) (S ∪ T.map (shift (2 ^ i))) =
      (if i % 2 = 0 then 1 else -1) *
        (wc (range (2 ^ i)) (gkF i) S * wc (range (2 ^ i)) (gkF i) T) := by
  set R := range (2 ^ i)
  have hu : ∑ A ∈ R.powerset, chi S A = 0 := by
    rw [sum_chi, if_neg]; intro hd
    obtain ⟨y, hy⟩ := hS0; exact disjoint_left.1 hd hy (hS hy)
  have hv : ∑ B ∈ R.powerset, chi T B = 0 := by
    rw [sum_chi, if_neg]; intro hd
    obtain ⟨y, hy⟩ := hT0; exact disjoint_left.1 hd hy (hT hy)
  have hsum : wc (range (2 ^ (i + 1))) (gkF (i + 1)) (S ∪ T.map (shift (2 ^ i))) =
      ∑ A ∈ R.powerset, ∑ B ∈ R.powerset,
        sg (if i % 2 = 0 then (gkF i A || gkF i B) else (gkF i A && gkF i B)) *
          (chi S A * chi T B) := by
    rw [wc, range_split, sum_powerset_union (low_high i).1]
    refine sum_congr rfl fun A hA => ?_
    rw [sum_powerset_map]
    refine sum_congr rfl fun B _ => ?_
    rw [gkF_succ i (mem_powerset.1 hA), chi_split i hS (mem_powerset.1 hA)]
  rw [hsum, mul_sum]
  simp only [mul_sum]
  by_cases hp : i % 2 = 0
  · simp only [hp, if_true]
    have key : ∀ A B, 2 * (sg (gkF i A || gkF i B) * (chi S A * chi T B)) =
        -1 * (chi S A * chi T B) + (sg (gkF i A) * chi S A) * chi T B +
          chi S A * (sg (gkF i B) * chi T B) +
          (sg (gkF i A) * chi S A) * (sg (gkF i B) * chi T B) := by
      intro A B; rw [← mul_assoc, two_sg_or]; ring
    simp only [key, sum_add_distrib, ← mul_sum, ← sum_mul, hu, hv, mul_zero, zero_mul,
      add_zero, zero_add, wc, one_mul]
  · simp only [hp, if_false]
    have key : ∀ A B, 2 * (sg (gkF i A && gkF i B) * (chi S A * chi T B)) =
        1 * (chi S A * chi T B) + (sg (gkF i A) * chi S A) * chi T B +
          chi S A * (sg (gkF i B) * chi T B) +
          -1 * ((sg (gkF i A) * chi S A) * (sg (gkF i B) * chi T B)) := by
      intro A B; rw [← mul_assoc, two_sg_and]; ring
    simp only [key, sum_add_distrib, ← mul_sum, ← sum_mul, hu, hv, mul_zero, zero_mul,
      add_zero, zero_add, wc]

/-- JRSW's dense supports at level `j + 2`. -/
def dense : ℕ → Finset (Finset ℕ)
  | 0 => (range 4).powerset.erase ∅
  | j + 1 => ((dense j) ×ˢ (dense j)).image fun p => p.1 ∪ p.2.map (shift (2 ^ (j + 2)))

theorem dense_props : ∀ j, ∀ S ∈ dense j, S ⊆ range (2 ^ (j + 2)) ∧ S.Nonempty
  | 0, S, hS => by
    obtain ⟨hne, hS⟩ := mem_erase.1 hS
    exact ⟨mem_powerset.1 hS, nonempty_iff_ne_empty.2 hne⟩
  | j + 1, S, hS => by
    obtain ⟨⟨S₁, S₂⟩, hp, rfl⟩ := mem_image.1 hS
    obtain ⟨h₁, h₂⟩ := mem_product.1 hp
    obtain ⟨s₁, n₁⟩ := dense_props j S₁ h₁
    obtain ⟨s₂, -⟩ := dense_props j S₂ h₂
    refine ⟨?_, n₁.mono subset_union_left⟩
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, range_split]
    exact union_subset_union s₁ (map_subset_map.2 s₂)

/-- The dense part of the spectrum at level `j + 2`. -/
def dsum (j : ℕ) : ℤ := ∑ S ∈ dense j, |wc (range (2 ^ (j + 2))) (gkF (j + 2)) S|

/-- `c₂ = 27/8`, scaled by `2^4` (kernel evaluation, `decide`). -/
theorem dsum_zero : dsum 0 = 54 := by decide

theorem union_map_injOn (i : ℕ) {P : Finset (Finset ℕ × Finset ℕ)}
    (hP : ∀ p ∈ P, p.1 ⊆ range (2 ^ i)) :
    Set.InjOn (fun p : Finset ℕ × Finset ℕ => p.1 ∪ p.2.map (shift (2 ^ i))) P := by
  intro p hp q hq h
  simp only at h
  have h1 : p.1 = q.1 := by
    ext y; constructor
    · intro hy
      have hy' : y ∈ q.1 ∪ q.2.map (shift (2 ^ i)) := h ▸ mem_union_left _ hy
      exact (low_mem_union (mem_range.1 (hP p hp hy))).1 hy'
    · intro hy
      have hy' : y ∈ p.1 ∪ p.2.map (shift (2 ^ i)) := h.symm ▸ mem_union_left _ hy
      exact (low_mem_union (mem_range.1 (hP q hq hy))).1 hy'
  have h2 : p.2 = q.2 := by
    ext z; constructor
    · intro hz
      have : shift (2 ^ i) z ∈ q.1 ∪ q.2.map (shift (2 ^ i)) :=
        h ▸ mem_union_right _ (mem_map_of_mem _ hz)
      exact (shift_mem_union (hP q hq)).1 this
    · intro hz
      have : shift (2 ^ i) z ∈ p.1 ∪ p.2.map (shift (2 ^ i)) :=
        h.symm ▸ mem_union_right _ (mem_map_of_mem _ hz)
      exact (shift_mem_union (hP p hp)).1 this
  exact Prod.ext h1 h2

/-- **JRSW's recursion** `c_h = c_{h-1}² / 2`. -/
theorem dsum_succ (j : ℕ) : 2 * dsum (j + 1) = dsum j ^ 2 := by
  have hP : ∀ p ∈ dense j ×ˢ dense j, p.1 ⊆ range (2 ^ (j + 2)) := fun p hp =>
    (dense_props j p.1 (mem_product.1 hp).1).1
  rw [dsum, dense, sum_image (union_map_injOn (j + 2) hP), mul_sum, sq, dsum, sum_mul_sum,
    ← sum_product']
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h₁, h₂⟩ := mem_product.1 hp
  obtain ⟨s₁, n₁⟩ := dense_props j p.1 h₁
  obtain ⟨s₂, n₂⟩ := dense_props j p.2 h₂
  have e := wc_gk_succ (j + 2) s₁ s₂ n₁ n₂
  rw [show j + 1 + 2 = (j + 2) + 1 by omega]
  have : (2 : ℤ) * |wc (range (2 ^ (j + 2 + 1))) (gkF (j + 2 + 1))
      (p.1 ∪ p.2.map (shift (2 ^ (j + 2))))| =
      |2 * wc (range (2 ^ (j + 2 + 1))) (gkF (j + 2 + 1))
        (p.1 ∪ p.2.map (shift (2 ^ (j + 2))))| := by rw [abs_mul, abs_two]
  rw [this, e, abs_mul, abs_mul]
  split_ifs <;> simp

theorem dsum_eq (j : ℕ) : dsum j = 2 * 27 ^ (2 ^ j) := by
  induction j with
  | zero => rw [dsum_zero]; norm_num
  | succ j ih =>
    have h := dsum_succ j
    rw [ih] at h
    have e : ((2 : ℤ) * 27 ^ 2 ^ j) ^ 2 = 2 * (2 * 27 ^ 2 ^ (j + 1)) := by
      rw [pow_succ 2 j, pow_mul]; ring
    linarith

theorem dsum_le_l1 (j : ℕ) : dsum j ≤ l1 (range (2 ^ (j + 2))) (gkF (j + 2)) :=
  sum_le_sum_of_subset_of_nonneg
    (fun S hS => mem_powerset.2 (dense_props j S hS).1) (fun _ _ _ => abs_nonneg _)

/-- **JRSW Theorem 2.4 for GK.** Every decision tree that computes `coalt (j + 2)` on the
subsets of its `n = 2^(j+2)` vertices has at least `2·(27/16)^(n/4)` leaves. -/
theorem gk_leaves (j : ℕ) (t : DTree ℕ)
    (ht : ∀ X ⊆ range (2 ^ (j + 2)), t.eval X = gkF (j + 2) X) :
    2 * 27 ^ (2 ^ j) ≤ 16 ^ (2 ^ j) * t.leaves := by
  have h1 := dsum_le_l1 j
  have h2 := l1_le_leaves_of_eval t ht
  rw [dsum_eq] at h1
  rw [card_range] at h2
  have e : (2 : ℤ) ^ 2 ^ (j + 2) = 16 ^ 2 ^ j := by
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm, pow_mul]; norm_num
  rw [e] at h2
  exact_mod_cast h1.trans h2

end GK

end HD

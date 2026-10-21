/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Alternating trees (§4.2-4.3)

Hertel's combined alternating trees on the vertices `0 .. 2^i - 1`:
`alt 0 = coalt 0 = {{0}}`, and at level `i + 1` two vertex-disjoint copies (the second
shifted by `2^i`) are combined by join (`∧`) at odd levels and union (`∨`) at even levels
in `alt`, and the other way round in `coalt`.

* `alt (2k-1)` is `g_k` and `coalt (2k-1)` is `f_k` of the 𝒢𝒦-family (§4.2.1);
  `coalt 3` and `alt 3` are, edge for edge, the `f₂` and `g₂` printed on p.48.
* `alt (2k)` is `r_k` and `coalt (2k)` is `S_k` of the 𝒯𝒦-family (§4.2.2).

| Lean | Thesis |
| --- | --- |
| `tr_alt` | `Tr(Γᵢ) = Γ̄ᵢ`: `Tr(f_k) = g_k`, `Tr(S_k) = r_k` |
| `tr_union_disjoint`, `tr_join_disjoint` | §4.1, vertex-disjoint case |
| `card_alt_succ`, `card_coalt_succ` | §4.2.3, the edge-count recurrences **corrected** |
| `alt_counts` | §4.3, closed forms |
-/
import HypergraphDualization.Operations
import HypergraphDualization.Conditions

namespace HD

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### Transversals under injective relabelling and change of ground set -/

/-- Relabel every edge along `φ`. -/
def mapH (φ : α ↪ β) (H : Finset (Finset α)) : Finset (Finset β) := H.image (·.map φ)

theorem hits_mapH {φ : α ↪ β} {H : Finset (Finset α)} {T : Finset α} :
    Hits (mapH φ H) (T.map φ) ↔ Hits H T := by
  constructor
  · intro h e he
    have := h (e.map φ) (mem_image_of_mem _ he)
    rwa [← map_inter, map_nonempty] at this
  · intro h e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    rw [← map_inter, map_nonempty]; exact h e he

/-- `Tr` commutes with injective relabelling. -/
theorem tr_mapH (φ : α ↪ β) (V : Finset α) (H : Finset (Finset α)) :
    tr (V.map φ) (mapH φ H) = mapH φ (tr V H) := by
  ext T'
  constructor
  · intro hT'
    obtain ⟨hsub, hmin⟩ := mem_tr.1 hT'
    obtain ⟨T, hTV, rfl⟩ := subset_map_iff.1 hsub
    refine mem_image.2 ⟨T, mem_tr.2 ⟨hTV, hits_mapH.1 hmin.1, fun v hv hhit => ?_⟩, rfl⟩
    apply hmin.2 (φ v) (mem_map_of_mem φ hv)
    rw [← map_erase]; exact hits_mapH.2 hhit
  · intro hT'
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hT'
    obtain ⟨hTV, hmin⟩ := mem_tr.1 hT
    refine mem_tr.2 ⟨map_subset_map.2 hTV, hits_mapH.2 hmin.1, fun w hw hhit => ?_⟩
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hw
    rw [← map_erase, hits_mapH] at hhit
    exact hmin.2 v hv hhit

theorem mapH_within {φ : α ↪ β} {V : Finset α} {H : Finset (Finset α)} (h : Within V H) :
    Within (V.map φ) (mapH φ H) := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_image.1 he
  exact map_subset_map.2 (h f hf)

theorem card_mapH (φ : α ↪ β) (H : Finset (Finset α)) : (mapH φ H).card = H.card :=
  card_image_of_injective _ (map_injective φ)

/-- A minimal transversal lies in the union of the edges. -/
theorem tr_ground {U V : Finset α} {H : Finset (Finset α)} (hH : Within V H) (hVU : V ⊆ U) :
    tr U H = tr V H := by
  ext T
  simp only [mem_tr]
  constructor
  · rintro ⟨-, hmin⟩
    refine ⟨fun v hv => ?_, hmin⟩
    obtain ⟨f, hf, hTf⟩ := exists_private_edge hmin hv
    have : v ∈ T ∩ f := hTf ▸ mem_singleton_self v
    exact hH f hf (mem_inter.1 this).2
  · rintro ⟨hTV, hmin⟩; exact ⟨hTV.trans hVU, hmin⟩

theorem empty_mem_tr_iff {U : Finset α} {H : Finset (Finset α)} : ∅ ∈ tr U H ↔ H = ∅ := by
  rw [mem_tr]
  constructor
  · rintro ⟨-, hhit, -⟩
    exact eq_empty_of_forall_notMem fun e he => by simpa using hhit e he
  · rintro rfl
    exact ⟨empty_subset _, fun e he => absurd he (notMem_empty e),
      fun v hv => absurd hv (notMem_empty v)⟩

/-- **§4.1, disjoint union.** `Tr(A ∨ B) = Tr(A) ∧ Tr(B)` for vertex-disjoint `A`, `B`. -/
theorem tr_union_disjoint {U V W : Finset α} (hVW : Disjoint V W) (hVU : V ⊆ U) (hWU : W ⊆ U)
    {A B : Finset (Finset α)} (hA : Within V A) (hB : Within W B) :
    tr U (A ∪ B) = join (tr V A) (tr W B) := by
  rw [tr_union, tr_ground hA hVU, tr_ground hB hWU,
    minimal_eq_self (join_isSperner_of_disjoint hVW (tr_within V A) (tr_within W B)
      (tr_isSperner V A) (tr_isSperner W B))]

/-- **§4.1, disjoint join.** `Tr(A ∧ B) = Tr(A) ∨ Tr(B)` for nonempty vertex-disjoint `A`, `B`. -/
theorem tr_join_disjoint {U V W : Finset α} (hVW : Disjoint V W) (hVU : V ⊆ U) (hWU : W ⊆ U)
    {A B : Finset (Finset α)} (hA : Within V A) (hB : Within W B) (nA : A.Nonempty)
    (nB : B.Nonempty) : tr U (join A B) = tr V A ∪ tr W B := by
  rw [tr_join, tr_ground hA hVU, tr_ground hB hWU,
    minimal_eq_self (union_isSperner_of_disjoint hVW (tr_within V A) (tr_within W B)
      (tr_isSperner V A) (tr_isSperner W B) (fun h => nA.ne_empty (empty_mem_tr_iff.1 h))
      (fun h => nB.ne_empty (empty_mem_tr_iff.1 h)))]

/-! ### The alternating trees -/

/-- Shift by `m`. -/
def shift (m : ℕ) : ℕ ↪ ℕ := addRightEmbedding m

/-- Hertel's alternating tree `Γᵢ`: join at odd levels, union at even levels. -/
def alt : ℕ → Finset (Finset ℕ)
  | 0 => {{0}}
  | i + 1 => if i % 2 = 0 then join (alt i) (mapH (shift (2 ^ i)) (alt i))
             else alt i ∪ mapH (shift (2 ^ i)) (alt i)

/-- The dual tree `Γ̄ᵢ`: union at odd levels, join at even levels. -/
def coalt : ℕ → Finset (Finset ℕ)
  | 0 => {{0}}
  | i + 1 => if i % 2 = 0 then coalt i ∪ mapH (shift (2 ^ i)) (coalt i)
             else join (coalt i) (mapH (shift (2 ^ i)) (coalt i))

theorem range_map_shift (i : ℕ) : (range (2 ^ i)).map (shift (2 ^ i)) =
    (range (2 ^ (i + 1))).filter (2 ^ i ≤ ·) := by
  ext x; simp only [mem_map, mem_range, shift, addRightEmbedding_apply, mem_filter, pow_succ]
  constructor
  · rintro ⟨y, hy, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - 2 ^ i, by omega, by omega⟩

theorem low_high (i : ℕ) :
    Disjoint (range (2 ^ i)) ((range (2 ^ i)).map (shift (2 ^ i))) ∧
    range (2 ^ i) ⊆ range (2 ^ (i + 1)) ∧
    (range (2 ^ i)).map (shift (2 ^ i)) ⊆ range (2 ^ (i + 1)) := by
  rw [range_map_shift]
  refine ⟨disjoint_left.2 fun x hx hx' => ?_, range_subset_range.2 (Nat.pow_le_pow_right (by decide) (Nat.le_succ i)),
    filter_subset _ _⟩
  simp only [mem_range, mem_filter] at hx hx'; omega

/-- Both trees live on `0 .. 2^i - 1`, are nonempty, and are mutually transversal. -/
theorem alt_props (i : ℕ) :
    Within (range (2 ^ i)) (alt i) ∧ Within (range (2 ^ i)) (coalt i) ∧
    (alt i).Nonempty ∧ (coalt i).Nonempty ∧
    tr (range (2 ^ i)) (alt i) = coalt i ∧ tr (range (2 ^ i)) (coalt i) = alt i := by
  induction i with
  | zero =>
    refine ⟨by decide, by decide, by simp [alt], by simp [coalt], by decide, by decide⟩
  | succ i ih =>
    obtain ⟨wA, wC, nA, nC, tA, tC⟩ := ih
    obtain ⟨hd, hlo, hhi⟩ := low_high i
    set φ := shift (2 ^ i)
    have wA' := mapH_within (φ := φ) wA
    have wC' := mapH_within (φ := φ) wC
    have nA' : (mapH φ (alt i)).Nonempty := nA.image _
    have nC' : (mapH φ (coalt i)).Nonempty := nC.image _
    have tA' : tr ((range (2 ^ i)).map φ) (mapH φ (alt i)) = mapH φ (coalt i) := by
      rw [tr_mapH, tA]
    have tC' : tr ((range (2 ^ i)).map φ) (mapH φ (coalt i)) = mapH φ (alt i) := by
      rw [tr_mapH, tC]
    have wJ : ∀ {A B : Finset (Finset ℕ)}, Within (range (2 ^ i)) A →
        Within ((range (2 ^ i)).map φ) B → Within (range (2 ^ (i + 1))) (join A B) :=
      fun hA hB => join_within (fun e he => (hA e he).trans hlo) (fun e he => (hB e he).trans hhi)
    have wU : ∀ {A B : Finset (Finset ℕ)}, Within (range (2 ^ i)) A →
        Within ((range (2 ^ i)).map φ) B → Within (range (2 ^ (i + 1))) (A ∪ B) :=
      fun hA hB e he => (mem_union.1 he).elim (fun h => (hA e h).trans hlo)
        (fun h => (hB e h).trans hhi)
    simp only [alt, coalt]
    split_ifs
    · refine ⟨wJ wA wA', wU wC wC', ?_, nC.mono subset_union_left, ?_, ?_⟩
      · obtain ⟨e, he⟩ := nA; obtain ⟨f, hf⟩ := nA'
        exact ⟨e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩⟩
      · rw [tr_join_disjoint hd hlo hhi wA wA' nA nA', tA, tA']
      · rw [tr_union_disjoint hd hlo hhi wC wC', tC, tC']
    · refine ⟨wU wA wA', wJ wC wC', nA.mono subset_union_left, ?_, ?_, ?_⟩
      · obtain ⟨e, he⟩ := nC; obtain ⟨f, hf⟩ := nC'
        exact ⟨e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩⟩
      · rw [tr_union_disjoint hd hlo hhi wA wA', tA, tA']
      · rw [tr_join_disjoint hd hlo hhi wC wC' nC nC', tC, tC']

/-- **`Tr(Γᵢ) = Γ̄ᵢ`.** In particular `Tr(f_k) = g_k` and `Tr(S_k) = r_k`. -/
theorem tr_alt (i : ℕ) : tr (range (2 ^ i)) (coalt i) = alt i := (alt_props i).2.2.2.2.2

theorem tr_coalt (i : ℕ) : tr (range (2 ^ i)) (alt i) = coalt i := (alt_props i).2.2.2.2.1

/-! ### Edge counts -/

theorem card_union_disjoint_families {V W : Finset α} (hVW : Disjoint V W)
    {A B : Finset (Finset α)} (hA : Within V A) (hB : Within W B) (nA : ∅ ∉ A) :
    (A ∪ B).card = A.card + B.card := by
  refine card_union_of_disjoint (disjoint_left.2 fun e heA heB => nA ?_)
  have : e = ∅ := eq_empty_of_forall_notMem fun x hx =>
    disjoint_left.1 hVW (hA e heA hx) (hB e heB hx)
  exact this ▸ heA

theorem empty_notMem_alt (i : ℕ) : ∅ ∉ alt i ∧ ∅ ∉ coalt i := by
  have h := alt_props i
  constructor
  · intro he
    rw [← tr_alt] at he
    exact h.2.2.2.1.ne_empty (empty_mem_tr_iff.1 he)
  · intro he
    rw [← tr_coalt] at he
    exact h.2.2.1.ne_empty (empty_mem_tr_iff.1 he)

/-- **§4.2.3, corrected.** `|Γᵢ₊₁| = |Γᵢ|²` at odd levels (join) and `2|Γᵢ|` at even levels
(union). The thesis prints the two cases the other way round. -/
theorem card_alt_succ (i : ℕ) :
    (alt (i + 1)).card = if i % 2 = 0 then (alt i).card ^ 2 else 2 * (alt i).card := by
  obtain ⟨hd, -, -⟩ := low_high i
  have wA := (alt_props i).1
  simp only [alt]
  split_ifs
  · rw [card_join_of_disjoint hd wA (mapH_within wA), card_mapH, sq]
  · rw [card_union_disjoint_families hd wA (mapH_within wA) (empty_notMem_alt i).1, card_mapH,
      two_mul]

theorem card_coalt_succ (i : ℕ) :
    (coalt (i + 1)).card = if i % 2 = 0 then 2 * (coalt i).card else (coalt i).card ^ 2 := by
  obtain ⟨hd, -, -⟩ := low_high i
  have wC := (alt_props i).2.1
  simp only [coalt]
  split_ifs
  · rw [card_union_disjoint_families hd wC (mapH_within wC) (empty_notMem_alt i).2, card_mapH,
      two_mul]
  · rw [card_join_of_disjoint hd wC (mapH_within wC), card_mapH, sq]

/-- **§4.3, closed forms.** With `t = 2^k`:
`|r_k| = |Γ_{2k}| = 2^(t-1)`, `|S_k| = |Γ̄_{2k}| = 2^(2t-2)`,
`|g_{k+1}| = |Γ_{2k+1}| = 2^(2t-2)`, `|f_{k+1}| = |Γ̄_{2k+1}| = 2^(2t-1)`. -/
theorem alt_counts (k : ℕ) :
    (alt (2 * k)).card = 2 ^ (2 ^ k - 1) ∧ (coalt (2 * k)).card = 2 ^ (2 * 2 ^ k - 2) ∧
    (alt (2 * k + 1)).card = 2 ^ (2 * 2 ^ k - 2) ∧
    (coalt (2 * k + 1)).card = 2 ^ (2 * 2 ^ k - 1) := by
  induction k with
  | zero => simp [alt, coalt, mapH, shift, join]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have ht : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have e1 : (alt (2 * (k + 1))).card = 2 * (alt (2 * k + 1)).card := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, card_alt_succ]; simp [Nat.add_mod]
    have e2 : (coalt (2 * (k + 1))).card = (coalt (2 * k + 1)).card ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, card_coalt_succ]; simp [Nat.add_mod]
    have e3 : (alt (2 * (k + 1) + 1)).card = (alt (2 * (k + 1))).card ^ 2 := by
      rw [card_alt_succ]; simp [Nat.mul_mod_right]
    have e4 : (coalt (2 * (k + 1) + 1)).card = 2 * (coalt (2 * (k + 1))).card := by
      rw [card_coalt_succ]; simp [Nat.mul_mod_right]
    have p : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, h3, p, ← pow_succ']; congr 1 <;> omega
    · rw [e2, h4, ← pow_mul, p]; congr 1 <;> omega
    · rw [e3, e1, h3, p, ← pow_succ', ← pow_mul]; congr 1 <;> omega
    · rw [e4, e2, h4, ← pow_mul, ← pow_succ', p]; congr 1 <;> omega

/-- `coalt 3` and `alt 3` are the `f₂` and `g₂` printed in §5.2.1 (0-indexed). -/
theorem f2_g2_printed :
    coalt 3 = {{0, 2}, {0, 3}, {1, 2}, {1, 3}, {4, 6}, {4, 7}, {5, 6}, {5, 7}} ∧
    alt 3 = {{0, 1, 6, 7}, {2, 3, 4, 5}, {0, 1, 4, 5}, {2, 3, 6, 7}} := by decide

end HD

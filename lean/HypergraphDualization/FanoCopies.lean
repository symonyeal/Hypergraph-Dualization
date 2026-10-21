/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Disjoint copies of the Fano plane (Definition 5.2.1, corrected)

`kFano k` is `k` vertex-disjoint copies of the Fano plane on `0 .. 7k-1`. It has `7k` edges and
`7^k` minimal transversals; the printed count `(k-2)²/4 + k/2 + 1` is wrong for every `k ≥ 1`
(`two_fano_tr_card` checks `k = 2`).

| Lean | Thesis |
| --- | --- |
| `kFano_card`, `tr_kFano_card` | Def. 5.2.1 **corrected**: `7k` edges, `7^k` minimal transversals |
-/
import HypergraphDualization.Families

namespace HD

open Finset

/-- The Fano plane on `0 .. 6`. -/
def fanoN : Finset (Finset ℕ) :=
  {{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}}

/-- `k` disjoint copies of the Fano plane. -/
def kFano : ℕ → Finset (Finset ℕ)
  | 0 => ∅
  | k + 1 => kFano k ∪ mapH (shift (7 * k)) fanoN

theorem fanoN_within : Within (range 7) fanoN := by decide

theorem tr_fanoN_card : (tr (range 7) fanoN).card = 7 := by decide

theorem kFano_within (k : ℕ) : Within (range (7 * k)) (kFano k) := by
  induction k with
  | zero => intro e he; simp [kFano] at he
  | succ k ih =>
    intro e he
    rcases mem_union.1 he with he | he
    · exact (ih e he).trans (range_subset_range.2 (by omega))
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 he
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      have := mem_range.1 (fanoN_within f hf hy)
      simp only [shift, addRightEmbedding_apply, mem_range]; omega

theorem shift_range_disjoint (k : ℕ) :
    Disjoint (range (7 * k)) ((range 7).map (shift (7 * k))) := by
  refine disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨y, -, rfl⟩ := mem_map.1 hx'
  simp only [shift, addRightEmbedding_apply, mem_range] at hx; omega

theorem shift_range_subset (k : ℕ) : (range 7).map (shift (7 * k)) ⊆ range (7 * (k + 1)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  simp only [shift, addRightEmbedding_apply, mem_range] at hy ⊢; omega

theorem empty_notMem_kFano (k : ℕ) : ∅ ∉ kFano k := by
  induction k with
  | zero => simp [kFano]
  | succ k ih =>
    intro h
    rcases mem_union.1 h with h | h
    · exact ih h
    · obtain ⟨f, hf, hfe⟩ := mem_image.1 h
      have : f = ∅ := map_eq_empty.1 hfe
      exact absurd (this ▸ hf) (by decide)

/-- **Def. 5.2.1, corrected.** `k` disjoint Fano planes have `7k` edges. -/
theorem kFano_card (k : ℕ) : (kFano k).card = 7 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [kFano, card_union_disjoint_families (shift_range_disjoint k) (kFano_within k)
      (mapH_within fanoN_within) (empty_notMem_kFano k), card_mapH, ih]
    rfl

/-- **Def. 5.2.1, corrected.** `k` disjoint Fano planes have `7^k` minimal transversals. -/
theorem tr_kFano_card (k : ℕ) : (tr (range (7 * k)) (kFano k)).card = 7 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hd := shift_range_disjoint k
    have hlo : range (7 * k) ⊆ range (7 * (k + 1)) := range_subset_range.2 (by omega)
    have hhi := shift_range_subset k
    rw [kFano, tr_union_disjoint hd hlo hhi (kFano_within k) (mapH_within fanoN_within),
      tr_mapH, card_join_of_disjoint hd (tr_within _ _) (mapH_within (tr_within _ _)),
      card_mapH, ih, tr_fanoN_card, pow_succ]

end HD

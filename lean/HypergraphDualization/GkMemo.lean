/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Memoisation saves an exponential factor on GK and TK

`coFm m i b` is `coalt i` as a monotone formula on the vertices `b … b + 2^i − 1` of `Fin m`, with
its leaves in order. Its DNF is `gkH i` (`dnf_coFm_gkH`), so Theorem 4.16 (`Fm.leftmost_delta_le`)
and Theorem 4.25 (`fkA_gk_tree`) speak about the same pair. Under the leftmost rule FK-A on GK or
TK with `n = 2^(j+2)` vertices has at most `2n + 2` distinct subproblems and a recursion tree of
`τ ≥ 2·(27/16)^(n/4)/(n + 1)` nodes (`gk_memo_gap`).

Legend
  coFm m i b    `coalt i` shifted by `b`, as a formula over `Fin m`
  toFin m e     a set of naturals read as vertices of `Fin m`
-/
import HypergraphDualization.FkaTree

namespace HD

open Finset

/-- `coalt i` on the vertices `b, …, b + 2^i − 1` of `Fin m`, as a formula. -/
def coFm (m : ℕ) : ℕ → ℕ → Fm m
  | 0, b => if h : b < m then .var ⟨b, h⟩ else .ff
  | i + 1, b => if i % 2 = 0 then .or (coFm m i b) (coFm m i (b + 2 ^ i))
      else .and (coFm m i b) (coFm m i (b + 2 ^ i))

/-- A set of naturals read as vertices of `Fin m`. -/
def toFin (m : ℕ) (e : Finset ℕ) : Finset (Fin m) := univ.filter fun v => (v : ℕ) ∈ e

theorem bounds_succ {m i b : ℕ} (h : b + 2 ^ (i + 1) ≤ m) :
    b + 2 ^ i ≤ m ∧ b + 2 ^ i + 2 ^ i ≤ m := by
  rw [pow_succ] at h; constructor <;> omega

theorem vars_coFm (m : ℕ) : ∀ i b, b + 2 ^ i ≤ m → ∀ v ∈ (coFm m i b).vars,
    b ≤ (v : ℕ) ∧ (v : ℕ) < b + 2 ^ i
  | 0, b, h, v, hv => by
    have hb : b < m := by simp at h; omega
    simp only [coFm, dif_pos hb, Fm.vars, mem_singleton] at hv
    subst hv; simp
  | i + 1, b, h, v, hv => by
    obtain ⟨h1, h2⟩ := bounds_succ h
    have e : ∀ v ∈ (coFm m i b).vars ∪ (coFm m i (b + 2 ^ i)).vars,
        b ≤ (v : ℕ) ∧ (v : ℕ) < b + 2 ^ (i + 1) := by
      intro v hv
      rw [pow_succ]
      rcases mem_union.1 hv with hv | hv
      · have := vars_coFm m i b h1 v hv; omega
      · have := vars_coFm m i (b + 2 ^ i) h2 v hv; omega
    by_cases hp : i % 2 = 0
    · simp only [coFm, if_pos hp, Fm.vars] at hv; exact e v hv
    · simp only [coFm, if_neg hp, Fm.vars] at hv; exact e v hv

theorem ordered_coFm (m : ℕ) : ∀ i b, b + 2 ^ i ≤ m → (coFm m i b).Ordered
  | 0, b, h => by
    have hb : b < m := by simp at h; omega
    simp [coFm, dif_pos hb, Fm.Ordered]
  | i + 1, b, h => by
    obtain ⟨h1, h2⟩ := bounds_succ h
    have lt : ∀ a ∈ (coFm m i b).vars, ∀ c ∈ (coFm m i (b + 2 ^ i)).vars, a < c :=
      fun a ha c hc => by
        have := vars_coFm m i b h1 a ha
        have := vars_coFm m i (b + 2 ^ i) h2 c hc
        exact Fin.lt_def.2 (by omega)
    by_cases hp : i % 2 = 0
    · simp only [coFm, if_pos hp]
      exact ⟨ordered_coFm m i b h1, ordered_coFm m i _ h2, lt⟩
    · simp only [coFm, if_neg hp]
      exact ⟨ordered_coFm m i b h1, ordered_coFm m i _ h2, lt⟩

theorem image_join_of {α β : Type*} [DecidableEq α] [DecidableEq β] {f : Finset α → Finset β}
    (hf : ∀ e e', f (e ∪ e') = f e ∪ f e') (G H : Finset (Finset α)) :
    (join G H).image f = join (G.image f) (H.image f) := by
  ext s
  simp only [mem_image, mem_join]
  constructor
  · rintro ⟨_, ⟨e, he, e', he', rfl⟩, rfl⟩
    exact ⟨f e, ⟨e, he, rfl⟩, f e', ⟨e', he', rfl⟩, (hf e e').symm⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, _, ⟨e', he', rfl⟩, rfl⟩
    exact ⟨e ∪ e', ⟨e, he, e', he', rfl⟩, hf e e'⟩

theorem toFin_map_union (m b : ℕ) (e e' : Finset ℕ) :
    toFin m ((e ∪ e').map (shift b)) = toFin m (e.map (shift b)) ∪ toFin m (e'.map (shift b)) := by
  ext v; simp [toFin, map_union]

theorem map_shift_shift (b c : ℕ) (e : Finset ℕ) :
    (e.map (shift c)).map (shift b) = e.map (shift (b + c)) := by
  ext x; simp only [mem_map, shift, addRightEmbedding_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, by omega⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y + c, ⟨y, hy, rfl⟩, by omega⟩

theorem dnf_coFm (m : ℕ) : ∀ i b, b + 2 ^ i ≤ m →
    (coFm m i b).dnf = (coalt i).image fun e => toFin m (e.map (shift b))
  | 0, b, h => by
    have hb : b < m := by simp at h; omega
    simp only [coFm, dif_pos hb, Fm.dnf, coalt, image_singleton]
    congr 1; ext v
    simp only [mem_singleton, toFin, mem_filter, mem_univ, true_and, map_singleton, shift,
      addRightEmbedding_apply, zero_add]
    exact ⟨fun h => h ▸ rfl, fun h => Fin.ext h⟩
  | i + 1, b, h => by
    obtain ⟨h1, h2⟩ := bounds_succ h
    have ih1 := dnf_coFm m i b h1
    have ih2 := dnf_coFm m i (b + 2 ^ i) h2
    have himg : ((coalt i).image (·.map (shift (2 ^ i)))).image
        (fun e => toFin m (e.map (shift b))) =
        (coalt i).image fun e => toFin m (e.map (shift (b + 2 ^ i))) := by
      rw [image_image]; congr 1; funext e; simp only [Function.comp, map_shift_shift]
    by_cases hp : i % 2 = 0
    · simp only [coFm, if_pos hp, Fm.dnf, coalt, ih1, ih2, image_union, mapH, himg]
    · simp only [coFm, if_neg hp, Fm.dnf, coalt, ih1, ih2, mapH]
      rw [image_join_of (toFin_map_union m b), himg]

theorem dnf_coFm_gkH (i : ℕ) : (coFm (2 ^ i) i 0).dnf = gkH i := by
  rw [dnf_coFm _ i 0 (by simp), gkH]
  congr 1; funext e; ext v
  simp [toFin, shift]

/-- **Memoisation saves an exponential factor on GK and TK.** Under the leftmost rule, with fuel
`n + 1`, `n = 2^(j+2)`: at most `2n + 2` distinct subproblems, and a recursion tree of `τ` nodes
with `2·27^(n/4) ≤ 16^(n/4) (n + 1) τ`. -/
theorem gk_memo_gap (j : ℕ) (modified : Bool) :
    (fkADagR leftRule (2 ^ (j + 2) + 1) modified (gkH (j + 2)) (tr univ (gkH (j + 2)))).card ≤
        2 * 2 ^ (j + 2) + 2 ∧
      2 * 27 ^ (2 ^ j) ≤ 16 ^ (2 ^ j) *
        ((2 ^ (j + 2) + 1) *
          (fkAR leftRule (2 ^ (j + 2) + 1) modified (gkH (j + 2))
            (tr univ (gkH (j + 2)))).2) := by
  have hord := ordered_coFm (2 ^ (j + 2)) (j + 2) 0 (by simp)
  refine ⟨?_, fkA_gk_tree valid_leftRule modified⟩
  have := Fm.leftmost_delta_le hord (2 ^ (j + 2) + 1) modified
  rwa [← Fm.tr_dnf_readOnce hord.readOnce, dnf_coFm_gkH] at this

end HD

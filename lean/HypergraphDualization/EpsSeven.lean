/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# A lower bound on the most-frequent-vertex frequency (research track B)

For a non-trivial transversal pair `(G, Tr G)` on `n` points let `e = ε(G, Tr G)` and let `s` be
the size of a smallest edge of `G`. Every vertex has frequency at most `e` in `G`, so the average
edge size of `G` is at most `n·e`, and `s ≤ n·e`. Every minimal transversal meets the smallest
edge, so one of its `s` points lies in at least `|Tr G| / s` of them, and `s·e ≥ 1`. Hence
`n·e² ≥ 1`, and for small `n` the integrality of `s` settles `ε(n)`.

| Lean | Statement |
| --- | --- |
| `eps_bound` | **Theorem B.** some `s ∈ ℕ` has `s·ε ≥ 1` and `s ≤ n·ε` |
| `eps_sq` | **Corollary.** `n·ε² ≥ 1`, i.e. `ε(n) ≥ 1/√n` |
| `eps_seven` | **Theorem (Observation 5.2.3, `n = 7`).** `ε(7) = 3/7`, attained by the Fano plane |
| `eps_five`, `eps_six` | `ε(5) = ε(6) = 1/2` |
| `eps_nine` | `ε(9) = 1/3`, attained by three disjoint triples: the bound `1/√n` is attained |
-/
import HypergraphDualization.Frequency
import Mathlib.Tactic.Linarith

namespace HD.S32

open HD HD.Data Finset

variable {n : ℕ}

theorem foldl_max_ge (f : Fin n → ℚ) :
    ∀ (l : List (Fin n)) (m : ℚ), m ≤ l.foldl (fun m v => max m (f v)) m ∧
      ∀ v ∈ l, f v ≤ l.foldl (fun m v => max m (f v)) m
  | [], m => ⟨le_rfl, by simp⟩
  | a :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (max m (f a))
    refine ⟨(le_max_left _ _).trans h1, fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact (le_max_right _ _).trans h1
    · exact h2 v hv

/-- Every vertex's frequency is at most `ε`. -/
theorem freq_le_eps (C D : HG n) (v : Fin n) : freq C D v ≤ eps C D :=
  (foldl_max_ge (freq C D) _ 0).2 v (List.mem_finRange v)

theorem eps_nonneg (C D : HG n) : 0 ≤ eps C D := (foldl_max_ge (freq C D) _ 0).1

/-- `Σ_{v ∈ g} deg_H v = Σ_{h ∈ H} |g ∩ h|`. -/
theorem sum_degree_eq (H : HG n) (g : Finset (Fin n)) :
    ∑ v ∈ g, degree H v = ∑ h ∈ H, (g ∩ h).card := by
  simp only [degree, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  rw [← card_filter, filter_mem_eq_inter]

/-- **Theorem B.** For a non-trivial transversal pair on `n` points with `ε = ε(G, Tr G)`, some
natural number `s` (the size of a smallest edge of `G`) has `s·ε ≥ 1` and `s ≤ n·ε`. -/
theorem eps_bound (G : HG n) (hG : NonTrivial G) :
    ∃ s : ℕ, 1 ≤ (s : ℚ) * eps G (tr univ G) ∧ (s : ℚ) ≤ n * eps G (tr univ G) := by
  obtain ⟨hGne, -, hHne, -⟩ := hG
  set H := tr univ G
  set e := eps G H
  have hGpos : (0 : ℚ) < G.card := by exact_mod_cast card_pos.2 hGne
  have hHpos : (0 : ℚ) < H.card := by exact_mod_cast card_pos.2 hHne
  have hfG : ∀ v, (degree G v : ℚ) ≤ e * G.card := fun v =>
    (div_le_iff₀ hGpos).1 ((le_max_left _ _).trans (freq_le_eps G H v))
  have hfH : ∀ v, (degree H v : ℚ) ≤ e * H.card := fun v =>
    (div_le_iff₀ hHpos).1 ((le_max_right _ _).trans (freq_le_eps G H v))
  obtain ⟨g, hg, hmin⟩ := G.exists_min_image card hGne
  refine ⟨g.card, ?_, ?_⟩
  · -- every minimal transversal meets `g`
    have h1 : (H.card : ℚ) ≤ ∑ v ∈ g, (degree H v : ℚ) := by
      rw [← Nat.cast_sum, sum_degree_eq, card_eq_sum_ones, Nat.cast_le]
      refine sum_le_sum fun h hh => ?_
      obtain ⟨x, hx⟩ := (mem_tr.1 hh).2.1 g hg
      exact card_pos.2 ⟨x, by rw [mem_inter] at hx ⊢; exact ⟨hx.2, hx.1⟩⟩
    have h2 : ∑ v ∈ g, (degree H v : ℚ) ≤ g.card * (e * H.card) := by
      have := sum_le_sum fun v (_ : v ∈ g) => hfH v
      rwa [sum_const, nsmul_eq_mul] at this
    have : (H.card : ℚ) * 1 ≤ H.card * (g.card * e) := by nlinarith
    exact le_of_mul_le_mul_left this hHpos
  · -- the smallest edge is at most the average edge
    have h1 : (G.card : ℚ) * g.card ≤ ∑ f ∈ G, (f.card : ℚ) := by
      have := sum_le_sum fun f (hf : f ∈ G) => (Nat.cast_le (α := ℚ)).2 (hmin f hf)
      rwa [sum_const, nsmul_eq_mul] at this
    have h2 : ∑ f ∈ G, (f.card : ℚ) = ∑ v : Fin n, (degree G v : ℚ) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum, sum_degree_eq]
      simp
    have h3 : ∑ v : Fin n, (degree G v : ℚ) ≤ n * (e * G.card) := by
      have := sum_le_sum fun v (_ : v ∈ (univ : Finset (Fin n))) => hfG v
      rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have : (G.card : ℚ) * g.card ≤ G.card * (n * e) := by nlinarith
    exact le_of_mul_le_mul_left this hGpos

/-- **Corollary.** `n · ε² ≥ 1`: every non-trivial transversal pair on `n` points has a vertex
of frequency at least `1/√n`. -/
theorem eps_sq (G : HG n) (hG : NonTrivial G) : 1 ≤ n * eps G (tr univ G) ^ 2 := by
  obtain ⟨s, h1, h2⟩ := eps_bound G hG
  have he := eps_nonneg G (tr univ G)
  nlinarith

/-- If `ε < 1/m` then the smallest edge has more than `m` points. -/
theorem eps_bound_lt (G : HG n) (hG : NonTrivial G) {m : ℕ} (hm : 0 < m)
    (h : eps G (tr univ G) < 1 / m) : ∃ s : ℕ, m < s ∧ (s : ℚ) ≤ n * eps G (tr univ G) := by
  obtain ⟨s, h1, h2⟩ := eps_bound G hG
  refine ⟨s, ?_, h2⟩
  by_contra hs
  push Not at hs
  have hs' : (s : ℚ) ≤ m := by exact_mod_cast hs
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rw [lt_div_iff₀ hm'] at h
  have he := eps_nonneg G (tr univ G)
  nlinarith

/-- **Theorem (Observation 5.2.3, `n = 7`).** Every non-trivial transversal pair on seven points
has `ε ≥ 3/7`, and the Fano plane attains it: `ε(7) = 3/7`. -/
theorem eps_seven :
    (∀ G : HG 7, NonTrivial G → 3 / 7 ≤ eps G (tr univ G)) ∧ eps fanoC (tr univ fanoC) = 3 / 7 := by
  refine ⟨fun G hG => ?_, by native_decide⟩
  by_contra h
  push Not at h
  obtain ⟨s, hs, hsn⟩ := eps_bound_lt G hG (m := 2) (by norm_num) (by linarith)
  have : (3 : ℚ) ≤ s := by exact_mod_cast hs
  push_cast at hsn
  linarith

/-- `ε(5) = 1/2`. -/
theorem eps_five :
    (∀ G : HG 5, NonTrivial G → 1 / 2 ≤ eps G (tr univ G)) ∧
      eps ({{0, 3}, {1, 2}} : HG 5) (tr univ {{0, 3}, {1, 2}}) = 1 / 2 := by
  refine ⟨fun G hG => ?_, by native_decide⟩
  by_contra h
  push Not at h
  obtain ⟨s, hs, hsn⟩ := eps_bound_lt G hG (m := 2) (by norm_num) (by norm_num; linarith)
  have : (3 : ℚ) ≤ s := by exact_mod_cast hs
  push_cast at hsn
  linarith

/-- `ε(6) = 1/2`. -/
theorem eps_six :
    (∀ G : HG 6, NonTrivial G → 1 / 2 ≤ eps G (tr univ G)) ∧
      eps ({{0, 3}, {1, 2}} : HG 6) (tr univ {{0, 3}, {1, 2}}) = 1 / 2 := by
  refine ⟨fun G hG => ?_, by native_decide⟩
  by_contra h
  push Not at h
  obtain ⟨s, hs, hsn⟩ := eps_bound_lt G hG (m := 2) (by norm_num) (by norm_num; linarith)
  have : (3 : ℚ) ≤ s := by exact_mod_cast hs
  push_cast at hsn
  linarith

/-- `ε(9) = 1/3`, attained by three disjoint triples: the bound `ε ≥ 1/√n` is attained. -/
theorem eps_nine :
    (∀ G : HG 9, NonTrivial G → 1 / 3 ≤ eps G (tr univ G)) ∧
      eps ({{0, 1, 2}, {3, 4, 5}, {6, 7, 8}} : HG 9) (tr univ {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}}) =
        1 / 3 := by
  refine ⟨fun G hG => ?_, by native_decide⟩
  have := eps_sq G hG
  have he := eps_nonneg G (tr univ G)
  push_cast at this
  nlinarith

end HD.S32

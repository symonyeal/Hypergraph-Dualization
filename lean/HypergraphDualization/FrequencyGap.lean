/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Cross-intersection excess and frequency rigidity

Double-count incidences `(v, g, h)` with `v ∈ g ∩ h`. For cross-intersecting families,
`∑ v, deg_G v * deg_H v = |G| * |H| + ∑ g,h, (|g ∩ h| - 1)`.
The excess measures the gap in the frequency bound. No Sperner or duality assumption is
needed until specialising to transversal pairs. All general results are kernel proofs.
-/
import HypergraphDualization.EpsSeven
import Mathlib.Tactic.Ring

namespace HD.S32

open HD HD.Data Finset

variable {n : ℕ}

/-- The total cross-intersection size above the mandatory one point. -/
def crossExcess (G H : HG n) : ℕ := ∑ g ∈ G, ∑ h ∈ H, ((g ∩ h).card - 1)

/-- Count triples `(v,g,h)` with `v ∈ g ∩ h` in two orders. -/
theorem sum_degree_mul (G H : HG n) :
    ∑ v : Fin n, degree G v * degree H v = ∑ g ∈ G, ∑ h ∈ H, (g ∩ h).card := by
  have h : ∀ v, degree G v * degree H v = ∑ g ∈ G, if v ∈ g then degree H v else 0 := by
    intro v
    rw [← sum_filter]
    simp [degree, sum_const]
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun g _ => ?_
  rw [← sum_filter]
  simpa using sum_degree_eq H g

theorem sum_degree_mul_eq_excess (G H : HG n)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) :
    ∑ v : Fin n, degree G v * degree H v = G.card * H.card + crossExcess G H := by
  rw [sum_degree_mul]
  have hc : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).card = 1 + ((g ∩ h).card - 1) := by
    intro g hg h hh
    have := card_pos.2 (hGH g hg h hh)
    omega
  rw [sum_congr rfl fun g hg => sum_congr rfl fun h hh => hc g hg h hh]
  simp [sum_add_distrib, crossExcess, sum_const]

/-- Separate frequency caps `p,q` control the total cross-intersection excess. -/
theorem crossExcess_bound (G H : HG n)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) {p q : ℚ}
    (hG : ∀ v, (degree G v : ℚ) ≤ p * G.card)
    (hH : ∀ v, (degree H v : ℚ) ≤ q * H.card) :
    (G.card : ℚ) * H.card + crossExcess G H ≤
      n * (p * q) * ((G.card : ℚ) * H.card) := by
  have h : ∑ v : Fin n, (degree G v : ℚ) * degree H v ≤
      ∑ _v : Fin n, (p * G.card) * (q * H.card) :=
    sum_le_sum fun v _ => mul_le_mul (hG v) (hH v) (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans (hG v))
  have hc := sum_degree_mul_eq_excess G H hGH
  have hc' := congrArg (fun k : ℕ => (k : ℚ)) hc
  push_cast at hc'
  rw [hc'] at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Stability: total overlap excess is at most `(n ε² - 1)|G||H|`. -/
theorem eps_crossExcess (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) :
    (G.card : ℚ) * H.card + crossExcess G H ≤
      n * eps G H ^ 2 * ((G.card : ℚ) * H.card) := by
  simpa [pow_two] using crossExcess_bound G H hGH
    (degree_le_eps_left G H hG) (degree_le_eps_right G H hH)

/-- Equality in `n ε² ≥ 1` forces every cross intersection to be a singleton. -/
theorem eps_eq_cross_singleton (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) (he : n * eps G H ^ 2 = 1) :
    ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).card = 1 := by
  have h := eps_crossExcess G H hG hH hGH
  rw [he, one_mul] at h
  have h0 : crossExcess G H = 0 := by exact_mod_cast (show (crossExcess G H : ℚ) = 0 by
    have := Nat.cast_nonneg (α := ℚ) (crossExcess G H)
    linarith)
  have hz := sum_eq_zero_iff.1 h0
  intro g hg h hh
  have : (g ∩ h).card - 1 = 0 := sum_eq_zero_iff.1 (hz g hg) h hh
  have := card_pos.2 (hGH g hg h hh)
  omega

/-- Every vertex saturates both frequency caps at equality. -/
theorem eps_eq_degrees (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) (he : n * eps G H ^ 2 = 1) :
    ∀ v, (degree G v : ℚ) = eps G H * G.card ∧
      (degree H v : ℚ) = eps G H * H.card := by
  have hGp : (0 : ℚ) < G.card := by exact_mod_cast card_pos.2 hG
  have hHp : (0 : ℚ) < H.card := by exact_mod_cast card_pos.2 hH
  have hep : 0 < eps G H := by
    have := eps_nonneg G H
    by_contra hn
    have : eps G H = 0 := by linarith
    simp [this] at he
  have hgc := degree_le_eps_left G H hG
  have hhc := degree_le_eps_right G H hH
  have hle v (_ : v ∈ (univ : Finset (Fin n))) :
      (degree G v : ℚ) * degree H v ≤ (eps G H * G.card) * (eps G H * H.card) :=
    mul_le_mul (hgc v) (hhc v) (Nat.cast_nonneg _) (le_of_lt (mul_pos hep hGp))
  have hs : ∑ v : Fin n, (degree G v : ℚ) * degree H v =
      ∑ _v : Fin n, (eps G H * G.card) * (eps G H * H.card) := by
    have hnat := sum_degree_mul G H
    rw [sum_congr rfl fun g hg => sum_congr rfl fun h hh =>
      eps_eq_cross_singleton G H hG hH hGH he g hg h hh] at hnat
    simp only [sum_const, smul_eq_mul, mul_one] at hnat
    have hrat := congrArg (fun k : ℕ => (k : ℚ)) hnat
    push_cast at hrat
    rw [hrat]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (G.card : ℚ) * H.card = (n * eps G H ^ 2) * ((G.card : ℚ) * H.card) := by rw [he, one_mul]
      _ = _ := by ring
  intro v
  have hv := (sum_eq_sum_iff_of_le hle).1 hs v (mem_univ v)
  have h1 := mul_le_mul_of_nonneg_left (hhc v) (Nat.cast_nonneg (α := ℚ) (degree G v))
  have h2 := mul_le_mul_of_nonneg_right (hgc v) (Nat.cast_nonneg (α := ℚ) (degree H v))
  refine ⟨le_antisymm (hgc v) ?_, le_antisymm (hhc v) ?_⟩
  · exact (mul_le_mul_iff_left₀ (mul_pos hep hHp)).1 (hv ▸ h1)
  · exact (mul_le_mul_iff_right₀ (mul_pos hep hGp)).1 (hv ▸ h2)

/-- Rigidity of the square-root bound: square order, uniformity and regularity. -/
theorem eps_eq_rigid (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) (he : n * eps G H ^ 2 = 1) :
    ∃ m : ℕ, 0 < m ∧ n = m * m ∧ (m : ℚ) * eps G H = 1 ∧
      (∀ g ∈ G, g.card = m) ∧ (∀ h ∈ H, h.card = m) ∧
      (∀ v, (degree G v : ℚ) = eps G H * G.card ∧
        (degree H v : ℚ) = eps G H * H.card) := by
  have hd := eps_eq_degrees G H hG hH hGH he
  have hc := eps_eq_cross_singleton G H hG hH hGH he
  have key : ∀ {A B : HG n}, B.Nonempty →
      (∀ a ∈ A, ∀ b ∈ B, (a ∩ b).card = 1) →
      (∀ v, (degree B v : ℚ) = eps G H * B.card) →
      ∀ a ∈ A, (a.card : ℚ) * eps G H = 1 := by
    intro A B hB hAB hdeg a ha
    have hb : (0 : ℚ) < B.card := by exact_mod_cast card_pos.2 hB
    have h := sum_degree_eq B a
    rw [sum_congr rfl fun b hb => hAB a ha b hb] at h
    simp only [sum_const, smul_eq_mul, mul_one] at h
    have h' := congrArg (fun k : ℕ => (k : ℚ)) h
    push_cast at h'
    simp_rw [hdeg] at h'
    simp only [sum_const, nsmul_eq_mul] at h'
    exact (mul_right_cancel₀ (ne_of_gt hb) (by nlinarith :
      (a.card : ℚ) * eps G H * B.card = 1 * B.card))
  have hg := key hH hc (fun v => (hd v).2)
  have hh := key hG (fun h hh g hg => by rw [inter_comm]; exact hc g hg h hh)
    (fun v => (hd v).1)
  obtain ⟨g, hgG⟩ := hG
  have hm := hg g hgG
  have hmpos : 0 < g.card := by
    by_contra hn
    have : g.card = 0 := by omega
    simp [this] at hm
  have hep : 0 < eps G H := by
    have := eps_nonneg G H
    nlinarith
  refine ⟨g.card, hmpos, ?_, hm, ?_, ?_, hd⟩
  · have hm2 : (g.card : ℚ) * g.card * eps G H ^ 2 = 1 := by
      calc (g.card : ℚ) * g.card * eps G H ^ 2 = ((g.card : ℚ) * eps G H) ^ 2 := by ring
        _ = 1 := by rw [hm]; norm_num
    have h := mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt hep)) (he.trans hm2.symm)
    exact_mod_cast h
  · intro f hf
    have := hg f hf
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt hep) (this.trans hm.symm))
  · intro f hf
    have := hh f hf
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt hep) (this.trans hm.symm))

/-- Count cross pairs whose intersections contain at least two points. -/
def badCross (G H : HG n) : ℕ :=
  ((G ×ˢ H).filter fun gh => 1 < (gh.1 ∩ gh.2).card).card

theorem badCross_le_excess (G H : HG n) : badCross G H ≤ crossExcess G H := by
  rw [badCross, card_filter, sum_product]
  refine sum_le_sum fun g _ => sum_le_sum fun h _ => ?_
  split_ifs with hgh
  · change (1 : ℕ) ≤ (g ∩ h).card - 1
    change 1 < (g ∩ h).card at hgh
    omega
  · exact Nat.zero_le _

/-- At most `(n ε² - 1)|G||H|` cross pairs have a nonsingleton intersection. -/
theorem eps_badCross (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) :
    (G.card : ℚ) * H.card + badCross G H ≤
      n * eps G H ^ 2 * ((G.card : ℚ) * H.card) := by
  have := (Nat.cast_le (α := ℚ)).2 (badCross_le_excess G H)
  linarith [eps_crossExcess G H hG hH hGH]

/-- A single cross intersection of size at least two gives an explicit strict gap. -/
theorem eps_overlap_gap (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty)
    {g h : Finset (Fin n)} (hg : g ∈ G) (hh : h ∈ H) (hgh : 1 < (g ∩ h).card) :
    (G.card : ℚ) * H.card + 1 ≤ n * eps G H ^ 2 * ((G.card : ℚ) * H.card) := by
  have hpos : 0 < badCross G H := card_pos.2
    ⟨(g, h), mem_filter.2 ⟨mem_product.2 ⟨hg, hh⟩, hgh⟩⟩
  have : (1 : ℚ) ≤ badCross G H := by exact_mod_cast hpos
  linarith [eps_badCross G H hG hH hGH]

/-- Diagonal pairs alone account for `∑ g, (|g|-1)` units of excess. -/
theorem diagonal_le_excess (G : HG n) :
    ∑ g ∈ G, (g.card - 1) ≤ crossExcess G G := by
  refine sum_le_sum fun g hg => ?_
  simpa only [inter_self] using
    (single_le_sum (fun h (_ : h ∈ G) => Nat.zero_le ((g ∩ h).card - 1)) hg)

/-- The self-transversal frequency bound includes the diagonal correction. -/
theorem eps_self_diagonal (G : HG n) (hG : G.Nonempty) (hself : tr univ G = G) :
    (G.card : ℚ) ^ 2 + (∑ g ∈ G, (g.card - 1) : ℕ) ≤
      n * eps G G ^ 2 * (G.card : ℚ) ^ 2 := by
  have hGH : ∀ g ∈ G, ∀ h ∈ G, (g ∩ h).Nonempty := edges_meet hself.symm
  have := (Nat.cast_le (α := ℚ)).2 (diagonal_le_excess G)
  have := eps_crossExcess G G hG hG hGH
  nlinarith

/-- On more than one ambient vertex, a nonempty self-transversal family has strict gap. -/
theorem eps_self_strict (G : HG n) (hG : G.Nonempty) (hself : tr univ G = G) (hn : 1 < n) :
    1 < n * eps G G ^ 2 := by
  have hGH : ∀ g ∈ G, ∀ h ∈ G, (g ∩ h).Nonempty := edges_meet hself.symm
  have hGp : (0 : ℚ) < G.card := by exact_mod_cast card_pos.2 hG
  have hbound := eps_crossExcess G G hG hG hGH
  have hx := Nat.cast_nonneg (α := ℚ) (crossExcess G G)
  have hle : 1 ≤ n * eps G G ^ 2 := by
    nlinarith [mul_self_pos.2 (ne_of_gt hGp)]
  refine lt_of_le_of_ne hle ?_
  intro he
  obtain ⟨m, -, hnm, -, hmG, -, -⟩ := eps_eq_rigid G G hG hG hGH he.symm
  have hc := eps_eq_cross_singleton G G hG hG hGH he.symm
  obtain ⟨g, hg⟩ := hG
  have hm := hc g hg g hg
  rw [inter_self, hmG g hg] at hm
  rw [hm] at hnm
  norm_num at hnm
  omega

/-- A nonsquare ground-set size cannot attain the square-root bound. -/
theorem eps_strict_of_nonsquare (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) (hn : ∀ m : ℕ, n ≠ m * m) :
    1 < n * eps G H ^ 2 := by
  have hp : (0 : ℚ) < (G.card : ℚ) * H.card := mul_pos
    (by exact_mod_cast card_pos.2 hG) (by exact_mod_cast card_pos.2 hH)
  have hbound := eps_crossExcess G H hG hH hGH
  have hx := Nat.cast_nonneg (α := ℚ) (crossExcess G H)
  have hle : 1 ≤ n * eps G H ^ 2 := by nlinarith
  refine lt_of_le_of_ne hle ?_
  intro he
  obtain ⟨m, -, hnm, -⟩ := eps_eq_rigid G H hG hH hGH he.symm
  exact hn m hnm

/-- Equality already forces the antichain hypothesis needed for the minterm interpretation. -/
theorem eps_eq_sperner (G H : HG n) (hG : G.Nonempty) (hH : H.Nonempty)
    (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) (he : n * eps G H ^ 2 = 1) :
    IsSperner G ∧ IsSperner H := by
  obtain ⟨m, -, -, -, hmG, hmH, -⟩ := eps_eq_rigid G H hG hH hGH he
  exact ⟨fun g hg f hf hgf => eq_of_subset_of_card_le hgf (by rw [hmG g hg, hmG f hf]),
    fun h hh f hf hhf => eq_of_subset_of_card_le hhf (by rw [hmH h hh, hmH f hf])⟩

/-- On `r²` points with both sides `r`-uniform, regularity of just one side forces
singleton cross intersections. With Gurvich's cited theorem this excludes prime templates. -/
theorem uniform_regular_cross_singleton (G H : HG n) {r d : ℕ} (hr : 0 < r)
    (hn : n = r * r) (hGr : ∀ g ∈ G, g.card = r) (hHr : ∀ h ∈ H, h.card = r)
    (hHd : ∀ v, degree H v = d) (hGH : ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).Nonempty) :
    ∀ g ∈ G, ∀ h ∈ H, (g ∩ h).card = 1 := by
  have hi : n * d = H.card * r := by
    have := sum_degree_eq H univ
    simp only [univ_inter] at this
    rw [sum_congr rfl fun h hh => hHr h hh] at this
    simpa [hHd] using this
  have hrd : r * d = H.card := by
    apply Nat.eq_of_mul_eq_mul_left hr
    calc r * (r * d) = n * d := by rw [hn]; ring
      _ = H.card * r := hi
      _ = r * H.card := Nat.mul_comm _ _
  intro g hg
  have hs : ∑ h ∈ H, (g ∩ h).card = ∑ _h ∈ H, 1 := by
    rw [← sum_degree_eq, sum_congr rfl fun v _ => hHd v]
    simp [hGr g hg, hrd]
  have hle h (hh : h ∈ H) : 1 ≤ (g ∩ h).card := card_pos.2 (hGH g hg h hh)
  intro h hh
  exact ((sum_eq_sum_iff_of_le hle).1 hs.symm h hh).symm

/-- Uniformity of both sides on `r²` points does not imply frequency equality. -/
theorem path_four_not_extremal :
    let G : HG 4 := {{0, 1}, {1, 2}, {2, 3}}
    let H : HG 4 := {{0, 2}, {1, 2}, {1, 3}}
    tr univ G = H ∧ (∀ g ∈ G, g.card = 2) ∧ (∀ h ∈ H, h.card = 2) ∧
      eps G H = 2 / 3 ∧ crossExcess G H = 1 := by
  decide +kernel

/-- Fano attains the excess bound: its 14 units of excess are exactly the diagonal pairs. -/
theorem fano_crossExcess : crossExcess fanoC fanoC = 14 := by
  decide +kernel

end HD.S32

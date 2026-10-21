/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The thesis instances, checked

Every number the thesis reports about its instances, checked by evaluating the definitions
of `Basic`, `Symmetry` and `Algorithm` on the instance data. These proofs use
`native_decide`, so they trust the Lean compiler in addition to the kernel
(`#print axioms` lists `Lean.ofReduceBool`); the general theorems elsewhere do not.

| Lean | Thesis |
| --- | --- |
| `*_dual` | the instance pairs of §5.2.1 are transversal pairs |
| `sixA_printed_not_dual`, `eightVer_printed_not_dual` | 6-A and 8-Ver as printed are **not** |
| `*_nodes` | node counts of Figs. 5.1, 5.2, 5.4, 5, 6 |
| `*_eps` | the frequencies quoted in §5.2.2 |
| `*_aut` | the root groups of Figs. 5.1-5.4, 5, 6 (orders) |
| `k3_refutes_printed_cor_2_3_1` | Cor. 2.3.1 as printed is false |
| `pg23_not_self_dual` | §5.2.2: no projective plane of order 3 is self-transversal |
| `two_fano_tr_card` | Def. 5.2.1's transversal count fails at `k = 2` |
-/
import HypergraphDualization.Data
import HypergraphDualization.Symmetry

namespace HD.Data

open HD Finset

variable {n : ℕ}

/-- `max(deg_C v / |C|, deg_D v / |D|)` (§2.2.2). -/
def freq (C D : HG n) (v : Fin n) : ℚ :=
  max ((degree C v : ℚ) / C.card) ((degree D v : ℚ) / D.card)

/-- `ε(C, D)`: the frequency of the most frequent vertex. -/
def eps (C D : HG n) : ℚ := (List.finRange n).foldl (fun m v => max m (freq C D v)) 0

/-- `|Aut(H)|`. -/
def autOrder (H : HG n) : ℕ := ((univ : Finset (Equiv.Perm (Fin n))).filter (· ∈ aut H)).card

/-! ### Transversal pairs -/

theorem k3_dual : Dual univ k3C k3D := by native_decide
theorem fano_dual : Dual univ fanoC fanoD := by native_decide
theorem f2g2_dual : Dual univ f2g2C f2g2D := by native_decide
theorem sixA_dual : Dual univ sixAC sixAD := by native_decide
theorem sixB_dual : Dual univ sixBC sixBD := by native_decide
theorem sixC_dual : Dual univ sixCC sixCD := by native_decide
theorem sixD_dual : Dual univ sixDC sixDD := by native_decide
theorem sevenVer_dual : Dual univ sevenVerC sevenVerD := by native_decide
theorem eightVer_dual : Dual univ eightVerC eightVerD := by native_decide

/-- 6-A as printed on p.49 is not a transversal pair. -/
theorem sixA_printed_not_dual : ¬ Dual univ sixAPrintedC sixAPrintedD := by native_decide
/-- 8-Ver as printed on p.50 is not a transversal pair. -/
theorem eightVer_printed_not_dual : ¬ Dual univ eightVerPrintedC eightVerPrintedD := by
  native_decide

/-- The Fano plane is self-transversal. -/
theorem fano_self_tr : tr univ fanoC = fanoC := by native_decide
/-- `K₃` is self-transversal. -/
theorem k3_self_tr : tr univ k3C = k3C := by native_decide

/-! ### Recursion-tree sizes (FK-A, `modified`, degree-sum rule) -/

theorem k3_nodes : runFKA true k3C k3D = (true, 3) := by native_decide
theorem fano_nodes : runFKA true fanoC fanoD = (true, 35) := by native_decide
theorem f2g2_nodes : runFKA true f2g2C f2g2D = (true, 25) := by native_decide
theorem sixA_nodes : runFKA true sixAC sixAD = (true, 11) := by native_decide
theorem sixB_nodes : runFKA true sixBC sixBD = (true, 13) := by native_decide
theorem sixC_nodes : runFKA true sixCC sixCD = (true, 5) := by native_decide
theorem sixD_nodes : runFKA true sixDC sixDD = (true, 9) := by native_decide
theorem sevenVer_nodes : runFKA true sevenVerC sevenVerD = (true, 21) := by native_decide
theorem eightVer_nodes : runFKA true eightVerC eightVerD = (true, 21) := by native_decide

/-- Without the §5.1.1 single-edge rule the trees are larger: the modification saves nodes. -/
theorem faithful_nodes :
    (runFKA false k3C k3D).2 = 7 ∧ (runFKA false fanoC fanoD).2 = 59 ∧
    (runFKA false f2g2C f2g2D).2 = 37 ∧ (runFKA false sixAC sixAD).2 = 15 ∧
    (runFKA false sixBC sixBD).2 = 21 ∧ (runFKA false sixCC sixCD).2 = 17 ∧
    (runFKA false sixDC sixDD).2 = 15 ∧ (runFKA false sevenVerC sevenVerD).2 = 39 ∧
    (runFKA false eightVerC eightVerD).2 = 47 := by native_decide

/-! ### Frequencies (§5.2.2) -/

theorem k3_eps : eps k3C k3D = 2 / 3 := by native_decide
theorem fano_eps : eps fanoC fanoD = 3 / 7 := by native_decide
theorem f2g2_eps : eps f2g2C f2g2D = 1 / 2 := by native_decide
theorem six_eps : eps sixAC sixAD = 1 / 2 ∧ eps sixBC sixBD = 1 / 2 ∧
    eps sixCC sixCD = 1 / 2 ∧ eps sixDC sixDD = 1 / 2 := by native_decide
theorem sevenVer_eps : eps sevenVerC sevenVerD = 5 / 11 := by native_decide
theorem eightVer_eps : eps eightVerC eightVerD = 2 / 5 := by native_decide
/-- 8-Ver: every vertex has frequency exactly `2/5` on both sides (§5.2.2). -/
theorem eightVer_uniform : ∀ v, freq eightVerC eightVerD v = 2 / 5 := by native_decide

/-! ### Automorphism groups -/

theorem fano_aut : autOrder fanoC = 168 := by native_decide
theorem f2g2_aut : autOrder f2g2C = 128 ∧ autOrder f2g2D = 128 := by native_decide
theorem sixA_aut : autOrder sixAC = 4 := by native_decide
theorem sixBC_aut : autOrder sixBC = 48 := by native_decide
theorem sixCC_aut : autOrder sixCC = 48 := by native_decide
theorem sixD_aut : autOrder sixDC = 8 := by native_decide
theorem sevenVer_aut : autOrder sevenVerC = 2 := by native_decide
theorem eightVer_aut : autOrder eightVerC = 16 := by native_decide

/-! ### Refutations -/

/-- **Cor. 2.3.1 as printed is false.** For `K₃`, the shortest edge has `s = 2` vertices and
`n = |G| + |H| = 6`, so `s < log₂ n`; the corrected form `2^s ≤ n` holds. -/
theorem k3_refutes_printed_cor_2_3_1 :
    (∀ e ∈ k3C ∪ k3D, e.card = 2) ∧ 2 ^ 2 < k3C.card + k3D.card ∧
    2 ^ 2 ≤ k3C.card + k3D.card := by native_decide

/-- `PG(2,3)`: the 13 lines `{i, i+1, i+3, i+9} mod 13`. -/
def pg23 : HG 13 := (univ : Finset (Fin 13)).image fun i => {i, i + 1, i + 3, i + 9}

/-- A transversal of `H` containing no edge of `H` shows `Tr(H) ≠ H`. -/
theorem tr_ne_of_blocking {α : Type*} [DecidableEq α] {U : Finset α} {H : Finset (Finset α)}
    {B : Finset α} (hBU : B ⊆ U) (hB : Hits H B) (hno : ¬ upHit H B) : tr U H ≠ H := by
  intro h
  obtain ⟨T, hTB, hT⟩ := exists_isMinHit_subset _ B rfl hB
  have : T ∈ tr U H := mem_tr.2 ⟨hTB.trans hBU, hT⟩
  rw [h] at this
  exact hno ⟨T, this, hTB⟩

/-- **§5.2.2.** The projective plane of order 3 is not self-transversal: the six points
`0..5` meet every line and contain none. -/
theorem pg23_not_self_dual : tr univ pg23 ≠ pg23 :=
  tr_ne_of_blocking (B := {0, 1, 2, 3, 4, 5}) (subset_univ _) (by native_decide) (by native_decide)

/-- Two disjoint Fano planes: `14` edges and `49 = 7²` minimal transversals, where Def. 5.2.1's
formula `(k-2)²/4 + k/2 + 1` gives `2` at `k = 2`. -/
def twoFano : HG 14 :=
  (fanoC.image fun e => e.map (Fin.castLEEmb (by norm_num))) ∪
  (fanoC.image fun e => e.map ⟨fun v => ⟨v.1 + 7, by omega⟩, fun a b h => by
    simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩)

theorem two_fano_tr_card : twoFano.card = 14 ∧ (tr univ twoFano).card = 49 := by native_decide

end HD.Data

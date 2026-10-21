/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The base conditions of FK-A and the bounds of §2.3

For a transversal pair `H = Tr(G)` with `G` Sperner, all inside `U`:

| Lean | Thesis |
| --- | --- |
| `edges_meet` | Prop. 2.2.1, condition (iii) |
| `support_eq` | Prop. 2.2.2, condition (i) |
| `card_le_card_tr` | Prop. 2.2.3, condition (ii) |
| `kraft_sum` | Prop. 2.2.4, condition (iv), scaled by `2^|U|` |
| `two_pow_shortest_le` | Cor. 2.3.1 **corrected**: `2^s ≤ |G| + |H|`, i.e. `s ≤ log₂ n` |
| `exists_frequent_vertex` | Lemma 2.3.2: a vertex of frequency at least `1/s`, `2^s ≤ n` |

Cor. 2.3.1 as printed (`s ≥ log n`) is false; `k3_refutes_printed_cor_2_3_1` is the
counterexample. The proofs printed for Props. 2.2.3 and 2.2.4 do not establish them; the
proofs here are new.
-/
import HypergraphDualization.Duality
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

section Pair

variable {U : Finset α} {G H : Finset (Finset α)}

/-- **Proposition 2.2.1.** Every edge of `G` meets every edge of `Tr(G)`. -/
theorem edges_meet (hH : H = tr U G) : ∀ e ∈ G, ∀ f ∈ H, (e ∩ f).Nonempty := by
  subst hH
  intro e he f hf
  obtain ⟨x, hx⟩ := (mem_tr.1 hf).2.1 e he
  exact ⟨x, by rw [mem_inter] at hx ⊢; exact ⟨hx.2, hx.1⟩⟩

/-- Every vertex of a minimal transversal has a private edge: one it alone hits. -/
theorem exists_private_edge {T : Finset α} (hT : IsMinHit H T) {v : α} (hv : v ∈ T) :
    ∃ f ∈ H, T ∩ f = {v} := by
  have hnot := hT.2 v hv
  unfold Hits at hnot
  push Not at hnot
  obtain ⟨f, hf, hempty⟩ := hnot
  refine ⟨f, hf, ?_⟩
  obtain ⟨y, hy⟩ := hT.1 f hf
  ext x
  simp only [mem_inter, mem_singleton]
  constructor
  · rintro ⟨hxT, hxf⟩
    by_contra hxv
    exact (not_nonempty_iff_eq_empty.2 hempty) ⟨x, mem_inter.2 ⟨mem_erase.2 ⟨hxv, hxT⟩, hxf⟩⟩
  · intro hxv
    rw [hxv]
    rw [mem_inter] at hy
    refine ⟨hv, ?_⟩
    by_cases hyv : y = v
    · exact hyv ▸ hy.2
    · exact absurd (⟨y, mem_inter.2 ⟨mem_erase.2 ⟨hyv, hy.1⟩, hy.2⟩⟩ : (T.erase v ∩ f).Nonempty)
        (by rw [hempty]; exact not_nonempty_empty)

/-- **Proposition 2.2.2.** A transversal pair has a common support. -/
theorem support_eq (hG : Within U G) (sG : IsSperner G) (hH : H = tr U G) :
    support G = support H := by
  have hG' : G = tr U H := (eq_tr_comm hG (hH ▸ tr_within U G) sG (hH ▸ tr_isSperner U G)).1 hH
  have key : ∀ {X Y : Finset (Finset α)}, X = tr U Y → support X ⊆ support Y := by
    intro X Y hXY v hv
    simp only [support, mem_biUnion, id] at hv ⊢
    obtain ⟨T, hT, hvT⟩ := hv
    rw [hXY] at hT
    obtain ⟨f, hf, hTf⟩ := exists_private_edge (mem_tr.1 hT).2 hvT
    exact ⟨f, hf, (mem_inter.1 (hTf ▸ mem_singleton_self v : v ∈ T ∩ f)).2⟩
  exact Subset.antisymm (key hG') (key hH)

/-- **Proposition 2.2.3.** An edge of `Tr(H)` has at most `|H|` vertices. -/
theorem card_le_card_of_mem_tr {T : Finset α} (hT : T ∈ tr U H) : T.card ≤ H.card := by
  classical
  have hmin := (mem_tr.1 hT).2
  choose! f hf hTf using fun v (hv : v ∈ T) => exists_private_edge hmin hv
  refine card_le_card_of_injOn f (fun v hv => hf v hv) ?_
  intro v hv w hw hvw
  have h1 := hTf v hv
  have h2 := hTf w hw
  rw [hvw] at h1
  exact singleton_injective (h1.symm.trans h2)

/-- **Proposition 2.2.3**, both halves, for a transversal pair. -/
theorem card_le_card_tr (hG : Within U G) (sG : IsSperner G) (hH : H = tr U G) :
    (∀ e ∈ G, e.card ≤ H.card) ∧ (∀ f ∈ H, f.card ≤ G.card) := by
  have hG' : G = tr U H := (eq_tr_comm hG (hH ▸ tr_within U G) sG (hH ▸ tr_isSperner U G)).1 hH
  exact ⟨fun e he => card_le_card_of_mem_tr (hG' ▸ he),
    fun f hf => card_le_card_of_mem_tr (hH ▸ hf)⟩

/-- The subsets of `U` containing `e` number `2^(|U| - |e|)`. -/
theorem card_supersets {e : Finset α} (he : e ⊆ U) :
    (U.powerset.filter (e ⊆ ·)).card = 2 ^ (U.card - e.card) := by
  rw [← card_sdiff_of_subset he, ← card_powerset]
  refine card_bij (fun A _ => A \ e) ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_powerset] at hA
    exact mem_powerset.2 (sdiff_subset_sdiff hA.1 subset_rfl)
  · intro A hA B hB hAB
    simp only [mem_filter, mem_powerset] at hA hB
    rw [← sdiff_union_of_subset hA.2, ← sdiff_union_of_subset hB.2, hAB]
  · intro B hB
    rw [mem_powerset] at hB
    refine ⟨B ∪ e, ?_, ?_⟩
    · simp only [mem_filter, mem_powerset]
      exact ⟨union_subset (hB.trans sdiff_subset) he, subset_union_right⟩
    · ext x; simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx | hx, hxe⟩; exact hx; exact absurd hx hxe
      · intro hx; exact ⟨Or.inl hx, (mem_sdiff.1 (hB hx)).2⟩

/-- **Proposition 2.2.4**, scaled by `2^|U|`:
`∑_{e ∈ G} 2^(|U|-|e|) + ∑_{f ∈ H} 2^(|U|-|f|) ≥ 2^|U|`. -/
theorem kraft_sum (hG : Within U G) (sG : IsSperner G) (hH : H = tr U G) :
    2 ^ U.card ≤ ∑ e ∈ G, 2 ^ (U.card - e.card) + ∑ f ∈ H, 2 ^ (U.card - f.card) := by
  have hHw : Within U H := hH ▸ tr_within U G
  have hdual : Dual U H G := (eq_tr_iff_partition hG hHw sG (hH ▸ tr_isSperner U G)).1 hH
  rw [dual_iff] at hdual
  -- Every `A ⊆ U` contains an edge of `H`, or its complement contains an edge of `G`.
  have cover : U.powerset ⊆ G.biUnion (fun e => U.powerset.filter (fun A => e ⊆ U \ A))
      ∪ H.biUnion (fun f => U.powerset.filter (f ⊆ ·)) := by
    intro A hA
    have hAU := mem_powerset.1 hA
    by_cases hHA : upHit H A
    · obtain ⟨f, hf, hfA⟩ := hHA
      exact mem_union_right _ (mem_biUnion.2 ⟨f, hf, mem_filter.2 ⟨hA, hfA⟩⟩)
    · have := (not_congr (hdual A hAU)).1 hHA
      rw [not_not] at this
      obtain ⟨e, he, heA⟩ := this
      exact mem_union_left _ (mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨hA, heA⟩⟩)
  have hcompl : ∀ e ⊆ U,
      (U.powerset.filter (fun A => e ⊆ U \ A)).card = 2 ^ (U.card - e.card) := by
    intro e he
    rw [← card_supersets he]
    refine card_bij (fun A _ => U \ A) ?_ ?_ ?_
    · intro A hA
      simp only [mem_filter, mem_powerset] at hA ⊢
      exact ⟨sdiff_subset, hA.2⟩
    · intro A hA B hB hAB
      simp only [mem_filter, mem_powerset] at hA hB
      rw [← Finset.sdiff_sdiff_eq_self hA.1, ← Finset.sdiff_sdiff_eq_self hB.1, hAB]
    · intro B hB
      simp only [mem_filter, mem_powerset] at hB
      exact ⟨U \ B, by simp only [mem_filter, mem_powerset]; exact ⟨sdiff_subset,
        by rw [Finset.sdiff_sdiff_eq_self hB.1]; exact hB.2⟩, Finset.sdiff_sdiff_eq_self hB.1⟩
  calc 2 ^ U.card = U.powerset.card := (card_powerset U).symm
    _ ≤ _ := card_le_card cover
    _ ≤ _ := card_union_le _ _
    _ ≤ ∑ e ∈ G, (U.powerset.filter (fun A => e ⊆ U \ A)).card
        + ∑ f ∈ H, (U.powerset.filter (f ⊆ ·)).card :=
          add_le_add card_biUnion_le card_biUnion_le
    _ = _ := by
      rw [sum_congr rfl fun e he => hcompl e (hG e he),
        sum_congr rfl fun f hf => card_supersets (hHw f hf)]

/-- **Corollary 2.3.1, corrected.** If every edge of a transversal pair has at least `s`
vertices, then `2^s ≤ |G| + |H|`; the shortest edge has at most `log₂ (|G|+|H|)` vertices. -/
theorem two_pow_shortest_le (hG : Within U G) (sG : IsSperner G) (hH : H = tr U G) (s : ℕ)
    (hs : ∀ e ∈ G ∪ H, s ≤ e.card) : 2 ^ s ≤ G.card + H.card := by
  have hHw : Within U H := hH ▸ tr_within U G
  have hk := kraft_sum hG sG hH
  by_cases hsU : s ≤ U.card
  · have bound : ∀ X : Finset (Finset α), Within U X → (∀ e ∈ X, s ≤ e.card) →
        ∑ e ∈ X, 2 ^ (U.card - e.card) ≤ X.card * 2 ^ (U.card - s) := by
      intro X _ hX
      rw [← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun e he => Nat.pow_le_pow_right (by norm_num) (by have := hX e he; omega)
    have hb := add_le_add (bound G hG fun e he => hs e (mem_union_left _ he))
      (bound H hHw fun e he => hs e (mem_union_right _ he))
    rw [← add_mul] at hb
    have : 2 ^ s * 2 ^ (U.card - s) ≤ (G.card + H.card) * 2 ^ (U.card - s) := by
      rw [← pow_add, Nat.add_sub_cancel' hsU]; exact hk.trans hb
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  · -- No edge can have more than `|U|` vertices, so both families are empty, which the
    -- duality of the pair rules out.
    push Not at hsU
    have hGe : G = ∅ := eq_empty_of_forall_notMem fun e he =>
      absurd (card_le_card (hG e he)) (by have := hs e (mem_union_left _ he); omega)
    have hHe : H = ∅ := eq_empty_of_forall_notMem fun f hf =>
      absurd (card_le_card (hHw f hf)) (by have := hs f (mem_union_right _ hf); omega)
    rw [hGe] at hH
    have : (∅ : Finset α) ∈ tr U (∅ : Finset (Finset α)) :=
      mem_tr.2 ⟨empty_subset _, fun e he => absurd he (notMem_empty e), fun v hv => absurd hv
        (notMem_empty v)⟩
    rw [← hH, hHe] at this
    exact absurd this (notMem_empty _)

/-- **Lemma 2.3.2.** If `G` and `H` are both nonempty, some vertex lies in at least a
`1/s` fraction of the edges of `G` or of `H`, where `2^s ≤ |G| + |H|`. In real terms its
frequency is at least `1/s ≥ 1/log₂(|G|+|H|)`. -/
theorem exists_frequent_vertex (hG : Within U G) (sG : IsSperner G) (hH : H = tr U G)
    (hGne : G.Nonempty) (hHne : H.Nonempty) :
    ∃ s v, 1 ≤ s ∧ 2 ^ s ≤ G.card + H.card ∧
      (G.card ≤ s * degree G v ∨ H.card ≤ s * degree H v) := by
  have hHw : Within U H := hH ▸ tr_within U G
  have hG' : G = tr U H := (eq_tr_comm hG hHw sG (hH ▸ tr_isSperner U G)).1 hH
  -- A shortest edge of `G ∪ H`.
  obtain ⟨e, he, hmin⟩ := (G ∪ H).exists_min_image card (hGne.mono subset_union_left)
  have hs := two_pow_shortest_le hG sG hH e.card hmin
  have meet := edges_meet hH
  -- Every edge on the other side meets `e`, so the degrees over `e` sum to at least that
  -- side's size, and one of the `|e|` summands carries a `1/|e|` share.
  have share : ∀ X : Finset (Finset α), e.Nonempty → (∀ f ∈ X, (e ∩ f).Nonempty) →
      ∃ v ∈ e, X.card ≤ e.card * degree X v := by
    intro X hne hX
    have hsum : X.card ≤ ∑ v ∈ e, degree X v := by
      unfold degree
      calc X.card ≤ (e.biUnion fun v => X.filter (v ∈ ·)).card := by
              refine card_le_card fun f hf => ?_
              obtain ⟨v, hv⟩ := hX f hf
              rw [mem_inter] at hv
              exact mem_biUnion.2 ⟨v, hv.1, mem_filter.2 ⟨hf, hv.2⟩⟩
        _ ≤ _ := card_biUnion_le
    by_contra hno
    push Not at hno
    have h1 := sum_lt_sum_of_nonempty hne hno
    rw [← mul_sum, sum_const, smul_eq_mul] at h1
    have h2 := Nat.mul_le_mul_left e.card hsum
    omega
  rcases mem_union.1 he with heG | heH
  · obtain ⟨f, hf⟩ := hHne
    have hne : e.Nonempty := (meet e heG f hf).mono inter_subset_left
    obtain ⟨v, -, hv⟩ := share H hne fun f hf => meet e heG f hf
    exact ⟨e.card, v, card_pos.2 hne, hs, Or.inr hv⟩
  · obtain ⟨g, hg⟩ := hGne
    have hne : e.Nonempty := (meet g hg e heH).mono inter_subset_right
    obtain ⟨v, -, hv⟩ := share G hne fun g hg => by rw [inter_comm]; exact meet g hg e heH
    exact ⟨e.card, v, card_pos.2 hne, hs, Or.inl hv⟩

end Pair

end HD

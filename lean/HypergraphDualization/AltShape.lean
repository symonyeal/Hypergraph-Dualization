/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Edge sizes and vertex frequencies of the alternating trees (§4.3)

Every edge of `Γᵢ` has `2^⌈i/2⌉` vertices and every edge of `Γ̄ᵢ` has `2^⌊i/2⌋`; every vertex has
frequency `2^-⌊i/2⌋` in `Γᵢ` and `2^-⌈i/2⌉` in `Γ̄ᵢ`. With `f_k = Γ̄_{2k-1}`, `g_k = Γ_{2k-1}`,
`S_k = Γ̄_{2k}`, `r_k = Γ_{2k}` these are the values of §4.3: edges of `f_k`, `g_k`, `S_k`, `r_k`
have `2^(k-1)`, `2^k`, `2^k`, `2^k` vertices, and the frequencies are `2^-k`, `2^(1-k)`, `2^-k`,
`2^-k`.

| Lean | Thesis |
| --- | --- |
| `alt_shape` | §4.3: uniform edge sizes and uniform vertex frequencies, for every level |
| `degree_join_left`, `degree_union_left`, `degree_mapH_shift` | degrees under the operations of §4.1 |
-/
import HypergraphDualization.Cotree

namespace HD

open Finset

section Degrees

variable {α : Type*} [DecidableEq α]

theorem degree_union_left {A B : Finset (Finset α)} {v : α} (h : ∀ e ∈ B, v ∉ e) :
    degree (A ∪ B) v = degree A v := by
  unfold degree
  rw [filter_union, filter_false_of_mem (fun e he => h e he), union_empty]

theorem degree_union_right {A B : Finset (Finset α)} {v : α} (h : ∀ e ∈ A, v ∉ e) :
    degree (A ∪ B) v = degree B v := by
  rw [union_comm]; exact degree_union_left h

theorem degree_join_left {V W : Finset α} (hVW : Disjoint V W) {A B : Finset (Finset α)}
    (hA : Within V A) (hB : Within W B) {v : α} (hv : v ∈ V) :
    degree (join A B) v = degree A v * B.card := by
  unfold degree
  have key : (join A B).filter (v ∈ ·) = ((A.filter (v ∈ ·)) ×ˢ B).image fun p => p.1 ∪ p.2 := by
    ext s
    simp only [mem_filter, join, mem_image, mem_product, Prod.exists]
    constructor
    · rintro ⟨⟨e, f, ⟨he, hf⟩, rfl⟩, hvs⟩
      rcases mem_union.1 hvs with hve | hvf
      · exact ⟨e, f, ⟨⟨he, hve⟩, hf⟩, rfl⟩
      · exact absurd (hB f hf hvf) (disjoint_left.1 hVW hv)
    · rintro ⟨e, f, ⟨⟨he, hve⟩, hf⟩, rfl⟩
      exact ⟨⟨e, f, ⟨he, hf⟩, rfl⟩, mem_union_left _ hve⟩
  rw [key, card_image_of_injOn (union_injOn hVW (fun e he => hA e (mem_filter.1 he).1) hB),
    card_product]

theorem degree_join_right {V W : Finset α} (hVW : Disjoint V W) {A B : Finset (Finset α)}
    (hA : Within V A) (hB : Within W B) {v : α} (hv : v ∈ W) :
    degree (join A B) v = degree B v * A.card := by
  have hcomm : join A B = join B A := by
    ext s; simp only [mem_join]
    constructor
    · rintro ⟨e, he, f, hf, rfl⟩; exact ⟨f, hf, e, he, union_comm _ _⟩
    · rintro ⟨f, hf, e, he, rfl⟩; exact ⟨e, he, f, hf, union_comm _ _⟩
  rw [hcomm]; exact degree_join_left hVW.symm hB hA hv

end Degrees

theorem degree_mapH_shift (m w : ℕ) (A : Finset (Finset ℕ)) :
    degree (mapH (shift m) A) (w + m) = degree A w := by
  unfold degree mapH
  rw [filter_image, card_image_of_injective _ (map_injective (shift m))]
  congr 1
  refine filter_congr fun e _ => ?_
  show w + m ∈ e.map (shift m) ↔ w ∈ e
  exact mem_map' (shift m)

theorem notMem_of_within_range {A : Finset (Finset ℕ)} {k v : ℕ} (hA : Within (range k) A)
    (hv : k ≤ v) : ∀ e ∈ A, v ∉ e := fun e he hve => by
  have := mem_range.1 (hA e he hve); omega

theorem notMem_mapH_shift {A : Finset (Finset ℕ)} {m v : ℕ} (hv : v < m) :
    ∀ e ∈ mapH (shift m) A, v ∉ e := by
  intro e he hve
  obtain ⟨f, -, rfl⟩ := mem_image.1 he
  obtain ⟨w, -, hw⟩ := mem_map.1 hve
  simp only [shift, addRightEmbedding_apply] at hw; omega

/-- **§4.3, for every level.** Uniform edge sizes, and the frequency identity
`deg(v) · 2^⌊i/2⌋ = |Γᵢ|`, `deg(v) · 2^⌈i/2⌉ = |Γ̄ᵢ|` for every vertex `v < 2^i`. -/
theorem alt_shape (i : ℕ) :
    (∀ e ∈ alt i, e.card = 2 ^ ((i + 1) / 2)) ∧ (∀ e ∈ coalt i, e.card = 2 ^ (i / 2)) ∧
    (∀ v < 2 ^ i, degree (alt i) v * 2 ^ (i / 2) = (alt i).card) ∧
    (∀ v < 2 ^ i, degree (coalt i) v * 2 ^ ((i + 1) / 2) = (coalt i).card) := by
  induction i with
  | zero =>
    refine ⟨by decide, by decide, fun v hv => ?_, fun v hv => ?_⟩ <;>
    · obtain rfl : v = 0 := by simpa using hv
      decide
  | succ i ih =>
    obtain ⟨sA, sC, dA, dC⟩ := ih
    obtain ⟨hd, hlo, hhi⟩ := low_high i
    obtain ⟨wA, wC, -, -, -, -⟩ := alt_props i
    have wA' := mapH_within (φ := shift (2 ^ i)) wA
    have wC' := mapH_within (φ := shift (2 ^ i)) wC
    have nA := (empty_notMem_alt i).1
    have nC := (empty_notMem_alt i).2
    have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; omega
    -- sizes of shifted edges
    have sMap : ∀ {A : Finset (Finset ℕ)} {c : ℕ}, (∀ e ∈ A, e.card = c) →
        ∀ e ∈ mapH (shift (2 ^ i)) A, e.card = c := by
      intro A c h e he
      obtain ⟨f, hf, rfl⟩ := mem_image.1 he
      rw [card_map]; exact h f hf
    -- sizes of a disjoint join
    have sJoin : ∀ {A B : Finset (Finset ℕ)} {c : ℕ}, Within (range (2 ^ i)) A →
        Within ((range (2 ^ i)).map (shift (2 ^ i))) B → (∀ e ∈ A, e.card = c) →
        (∀ e ∈ B, e.card = c) → ∀ e ∈ join A B, e.card = 2 * c := by
      intro A B c hA hB h1 h2 s hs
      obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hs
      rw [card_union_of_disjoint (disjoint_of_subset_left (hA e he)
        (disjoint_of_subset_right (hB f hf) hd)), h1 e he, h2 f hf, two_mul]
    -- a vertex is either low or a shifted low vertex
    have split : ∀ v < 2 ^ (i + 1), v < 2 ^ i ∨ ∃ w < 2 ^ i, v = w + 2 ^ i := by
      intro v hv
      by_cases h : v < 2 ^ i
      · exact Or.inl h
      · exact Or.inr ⟨v - 2 ^ i, by omega, by omega⟩
    have memHi : ∀ w < 2 ^ i, w + 2 ^ i ∈ (range (2 ^ i)).map (shift (2 ^ i)) := fun w hw =>
      mem_map.2 ⟨w, mem_range.2 hw, rfl⟩
    have jl : ∀ {A : Finset (Finset ℕ)} {t : ℕ}, Within (range (2 ^ i)) A →
        (∀ v < 2 ^ i, degree A v * 2 ^ t = A.card) →
        ∀ v < 2 ^ (i + 1),
          degree (join A (mapH (shift (2 ^ i)) A)) v * 2 ^ t =
            (join A (mapH (shift (2 ^ i)) A)).card := by
      intro A t wX dX v hv
      have wX' := mapH_within (φ := shift (2 ^ i)) wX
      rw [card_join_of_disjoint hd wX wX', card_mapH]
      rcases split v hv with hv | ⟨w, hw, rfl⟩
      · rw [degree_join_left hd wX wX' (mem_range.2 hv), card_mapH, mul_right_comm, dX v hv]
      · rw [degree_join_right hd wX wX' (memHi w hw), degree_mapH_shift, mul_right_comm, dX w hw]
    have un : ∀ {A : Finset (Finset ℕ)} {t : ℕ}, Within (range (2 ^ i)) A → ∅ ∉ A →
        (∀ v < 2 ^ i, degree A v * 2 ^ t = A.card) →
        ∀ v < 2 ^ (i + 1),
          degree (A ∪ mapH (shift (2 ^ i)) A) v * 2 ^ (t + 1) =
            (A ∪ mapH (shift (2 ^ i)) A).card := by
      intro A t wX nX dX v hv
      have wX' := mapH_within (φ := shift (2 ^ i)) wX
      rw [card_union_disjoint_families hd wX wX' nX, card_mapH, pow_succ, ← mul_assoc]
      rcases split v hv with hv | ⟨w, hw, rfl⟩
      · rw [degree_union_left (notMem_mapH_shift hv), dX v hv, mul_two]
      · rw [degree_union_right (notMem_of_within_range wX (by omega)), degree_mapH_shift,
          dX w hw, mul_two]
    have uS : ∀ {A : Finset (Finset ℕ)} {c : ℕ}, (∀ e ∈ A, e.card = c) →
        ∀ e ∈ A ∪ mapH (shift (2 ^ i)) A, e.card = c := fun h e he =>
      (mem_union.1 he).elim (h e) (sMap h e)
    have jS : ∀ {A : Finset (Finset ℕ)} {t : ℕ}, Within (range (2 ^ i)) A →
        (∀ e ∈ A, e.card = 2 ^ t) → ∀ e ∈ join A (mapH (shift (2 ^ i)) A), e.card = 2 ^ (t + 1) :=
      fun wX h e he => by
        rw [sJoin wX (mapH_within wX) h (sMap h) e he, pow_succ, mul_comm]
    by_cases hp : i % 2 = 0
    · -- `alt` joins, `coalt` unions
      have e1 : (i + 1) / 2 = i / 2 := by omega
      have e2 : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
      rw [show alt (i + 1) = join (alt i) (mapH (shift (2 ^ i)) (alt i)) by rw [alt, if_pos hp],
        show coalt (i + 1) = coalt i ∪ mapH (shift (2 ^ i)) (coalt i) by rw [coalt, if_pos hp],
        e1, e2]
      rw [e1] at sA dC
      exact ⟨jS wA sA, uS sC, jl wA dA, un wC nC dC⟩
    · -- `alt` unions, `coalt` joins
      have e1 : (i + 1) / 2 = i / 2 + 1 := by omega
      have e2 : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
      rw [show alt (i + 1) = alt i ∪ mapH (shift (2 ^ i)) (alt i) by rw [alt, if_neg hp],
        show coalt (i + 1) = join (coalt i) (mapH (shift (2 ^ i)) (coalt i)) by
          rw [coalt, if_neg hp], e1, e2]
      rw [e1] at sA dC
      exact ⟨uS sA, jS wC sC, un wA nA dA, jl wC dC⟩

end HD

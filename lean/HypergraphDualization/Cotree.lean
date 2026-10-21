/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The alternating tree is a cotree (Observation 4.4.9)

A cotree has vertex leaves and internal nodes labelled union (`∨`, no new adjacencies) or
join (`∧`, every vertex on the left adjacent to every vertex on the right); its graph is a
cograph (Thm. 4.4.8, cited). `altTree i` is Hertel's alternating tree with the labels of
`alt i`, and `coaltTree i` with those of `coalt i`.

| Lean | Thesis |
| --- | --- |
| `primalAdj_alt`, `primalAdj_coalt` | Observation 4.4.9: the primal graph of every `Γᵢ` and `Γ̄ᵢ` (so of every `f_k`, `g_k`, `r_k`, `S_k`) is the graph of the alternating tree |
| `support_alt`, `support_coalt` | both families use all `2^i` vertices |
-/
import HypergraphDualization.Families
import HypergraphDualization.Recursion

namespace HD

open Finset

/-- Cotrees on `ℕ`-labelled leaves. -/
inductive Cotree
  | leaf (v : ℕ)
  | union (l r : Cotree)
  | join (l r : Cotree)

namespace Cotree

/-- The leaves. -/
def verts : Cotree → Finset ℕ
  | leaf v => {v}
  | union l r => l.verts ∪ r.verts
  | join l r => l.verts ∪ r.verts

/-- Adjacency in the cograph of the cotree. -/
def Adj : Cotree → ℕ → ℕ → Prop
  | leaf _, _, _ => False
  | union l r, u, v => l.Adj u v ∨ r.Adj u v
  | join l r, u, v => l.Adj u v ∨ r.Adj u v ∨ (u ∈ l.verts ∧ v ∈ r.verts) ∨
      (v ∈ l.verts ∧ u ∈ r.verts)

/-- Add `m` to every leaf. -/
def shift (m : ℕ) : Cotree → Cotree
  | leaf v => leaf (v + m)
  | union l r => union (l.shift m) (r.shift m)
  | join l r => join (l.shift m) (r.shift m)

theorem verts_shift (m : ℕ) (t : Cotree) : (t.shift m).verts = t.verts.map (HD.shift m) := by
  induction t with
  | leaf v => simp [shift, verts, HD.shift]
  | union l r hl hr => simp [shift, verts, hl, hr, map_union]
  | join l r hl hr => simp [shift, verts, hl, hr, map_union]

theorem mem_verts_shift {m u : ℕ} {t : Cotree} :
    u ∈ (t.shift m).verts ↔ m ≤ u ∧ u - m ∈ t.verts := by
  rw [verts_shift, mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; simp [HD.shift] at hw ⊢; exact hw
  · rintro ⟨hm, hu⟩; exact ⟨u - m, hu, by simp [HD.shift]; omega⟩

theorem adj_shift {m u v : ℕ} (t : Cotree) :
    (t.shift m).Adj u v ↔ m ≤ u ∧ m ≤ v ∧ t.Adj (u - m) (v - m) := by
  induction t with
  | leaf w => simp [shift, Adj]
  | union l r hl hr => simp only [shift, Adj, hl, hr]; tauto
  | join l r hl hr =>
    simp only [shift, Adj, hl, hr, mem_verts_shift]; tauto

end Cotree

/-- Hertel's alternating tree, labelled as `alt`: join at odd levels, union at even levels. -/
def altTree : ℕ → Cotree
  | 0 => .leaf 0
  | i + 1 => if i % 2 = 0 then .join (altTree i) ((altTree i).shift (2 ^ i))
             else .union (altTree i) ((altTree i).shift (2 ^ i))

/-- The same tree labelled as `coalt`. -/
def coaltTree : ℕ → Cotree
  | 0 => .leaf 0
  | i + 1 => if i % 2 = 0 then .union (coaltTree i) ((coaltTree i).shift (2 ^ i))
             else .join (coaltTree i) ((coaltTree i).shift (2 ^ i))

/-! ### Primal graphs of unions, joins and shifts -/

section Primal

variable {α : Type*} [DecidableEq α]

theorem mem_support {H : Finset (Finset α)} {u : α} : u ∈ support H ↔ ∃ e ∈ H, u ∈ e := by
  simp [support]

theorem primalAdj_union {A B : Finset (Finset α)} {u v : α} :
    primalAdj (A ∪ B) u v ↔ primalAdj A u v ∨ primalAdj B u v := by
  simp only [primalAdj, mem_union]
  constructor
  · rintro ⟨h, e, he | he, hu, hv⟩
    · exact Or.inl ⟨h, e, he, hu, hv⟩
    · exact Or.inr ⟨h, e, he, hu, hv⟩
  · rintro (⟨h, e, he, hu, hv⟩ | ⟨h, e, he, hu, hv⟩)
    · exact ⟨h, e, Or.inl he, hu, hv⟩
    · exact ⟨h, e, Or.inr he, hu, hv⟩

theorem primalAdj_join {V W : Finset α} (hVW : Disjoint V W) {A B : Finset (Finset α)}
    (hA : Within V A) (hB : Within W B) (nA : A.Nonempty) (nB : B.Nonempty) {u v : α} :
    primalAdj (join A B) u v ↔ primalAdj A u v ∨ primalAdj B u v ∨
      (u ∈ support A ∧ v ∈ support B) ∨ (v ∈ support A ∧ u ∈ support B) := by
  have sep : ∀ {a b : α} {e f : Finset α}, e ∈ A → f ∈ B → a ∈ e → b ∈ f → a ≠ b :=
    fun he hf ha hb hab => disjoint_left.1 hVW (hA _ he ha) (hab ▸ hB _ hf hb)
  constructor
  · rintro ⟨huv, g, hg, hu, hv⟩
    obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hg
    rcases mem_union.1 hu with hu | hu <;> rcases mem_union.1 hv with hv | hv
    · exact Or.inl ⟨huv, e, he, hu, hv⟩
    · exact Or.inr (Or.inr (Or.inl ⟨mem_support.2 ⟨e, he, hu⟩, mem_support.2 ⟨f, hf, hv⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨mem_support.2 ⟨e, he, hv⟩, mem_support.2 ⟨f, hf, hu⟩⟩))
    · exact Or.inr (Or.inl ⟨huv, f, hf, hu, hv⟩)
  · rintro (⟨huv, e, he, hu, hv⟩ | ⟨huv, f, hf, hu, hv⟩ | ⟨hu, hv⟩ | ⟨hv, hu⟩)
    · obtain ⟨f, hf⟩ := nB
      exact ⟨huv, e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩, mem_union_left _ hu,
        mem_union_left _ hv⟩
    · obtain ⟨e, he⟩ := nA
      exact ⟨huv, e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩, mem_union_right _ hu,
        mem_union_right _ hv⟩
    · obtain ⟨e, he, hue⟩ := mem_support.1 hu
      obtain ⟨f, hf, hvf⟩ := mem_support.1 hv
      exact ⟨sep he hf hue hvf, e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩, mem_union_left _ hue,
        mem_union_right _ hvf⟩
    · obtain ⟨e, he, hve⟩ := mem_support.1 hv
      obtain ⟨f, hf, huf⟩ := mem_support.1 hu
      exact ⟨(sep he hf hve huf).symm, e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩,
        mem_union_right _ huf, mem_union_left _ hve⟩

theorem support_union (A B : Finset (Finset α)) : support (A ∪ B) = support A ∪ support B := by
  ext u; simp only [mem_support, mem_union]
  constructor
  · rintro ⟨e, he | he, hu⟩
    · exact Or.inl ⟨e, he, hu⟩
    · exact Or.inr ⟨e, he, hu⟩
  · rintro (⟨e, he, hu⟩ | ⟨e, he, hu⟩)
    · exact ⟨e, Or.inl he, hu⟩
    · exact ⟨e, Or.inr he, hu⟩

theorem support_join {A B : Finset (Finset α)} (nA : A.Nonempty) (nB : B.Nonempty) :
    support (join A B) = support A ∪ support B := by
  ext u; simp only [mem_support, mem_union]
  constructor
  · rintro ⟨g, hg, hu⟩
    obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hg
    rcases mem_union.1 hu with hu | hu
    · exact Or.inl ⟨e, he, hu⟩
    · exact Or.inr ⟨f, hf, hu⟩
  · rintro (⟨e, he, hu⟩ | ⟨f, hf, hu⟩)
    · obtain ⟨f, hf⟩ := nB; exact ⟨e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩, mem_union_left _ hu⟩
    · obtain ⟨e, he⟩ := nA; exact ⟨e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩, mem_union_right _ hu⟩

end Primal

theorem mem_support_mapH_shift {m u : ℕ} {A : Finset (Finset ℕ)} :
    u ∈ support (mapH (shift m) A) ↔ m ≤ u ∧ u - m ∈ support A := by
  rw [mem_support]
  unfold mapH
  constructor
  · rintro ⟨g, hg, hu⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hg
    obtain ⟨w, hw, rfl⟩ := mem_map.1 hu
    simp only [shift, addRightEmbedding_apply, Nat.add_sub_cancel]
    exact ⟨by omega, mem_support.2 ⟨e, he, hw⟩⟩
  · rintro ⟨hm, hu⟩
    obtain ⟨e, he, hue⟩ := mem_support.1 hu
    refine ⟨e.map (shift m), mem_image_of_mem _ he, mem_map.2 ⟨u - m, hue, ?_⟩⟩
    simp only [shift, addRightEmbedding_apply]; omega

theorem primalAdj_mapH_shift {m u v : ℕ} {A : Finset (Finset ℕ)} :
    primalAdj (mapH (shift m) A) u v ↔ m ≤ u ∧ m ≤ v ∧ primalAdj A (u - m) (v - m) := by
  unfold primalAdj mapH
  constructor
  · rintro ⟨huv, g, hg, hu, hv⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hg
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_map.1 hv
    simp only [shift, addRightEmbedding_apply, Nat.add_sub_cancel] at huv ⊢
    exact ⟨by omega, by omega, fun h => huv (by rw [h]), e, he, ha, hb⟩
  · rintro ⟨hu, hv, huv, e, he, ha, hb⟩
    refine ⟨fun h => huv (by rw [h]), e.map (shift m), mem_image_of_mem _ he,
      mem_map.2 ⟨u - m, ha, ?_⟩, mem_map.2 ⟨v - m, hb, ?_⟩⟩ <;>
      simp only [shift, addRightEmbedding_apply] <;> omega

/-! ### The alternating trees -/

theorem support_alt (i : ℕ) : support (alt i) = range (2 ^ i) ∧ support (coalt i) = range (2 ^ i) := by
  induction i with
  | zero => exact ⟨by decide, by decide⟩
  | succ i ih =>
    obtain ⟨sA, sC⟩ := ih
    have nA := (alt_props i).2.2.1
    have nC := (alt_props i).2.2.2.1
    have nA' : (mapH (shift (2 ^ i)) (alt i)).Nonempty := nA.image _
    have nC' : (mapH (shift (2 ^ i)) (coalt i)).Nonempty := nC.image _
    have split : range (2 ^ (i + 1)) = range (2 ^ i) ∪ (range (2 ^ i)).map (shift (2 ^ i)) := by
      rw [range_map_shift]; ext x; simp only [mem_range, mem_union, mem_filter, pow_succ]; omega
    have sm : ∀ {A : Finset (Finset ℕ)}, support A = range (2 ^ i) →
        support (mapH (shift (2 ^ i)) A) = (range (2 ^ i)).map (shift (2 ^ i)) := by
      intro A hA; ext u
      rw [mem_support_mapH_shift, hA, mem_map]
      simp only [mem_range, shift, addRightEmbedding_apply]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨u - 2 ^ i, h2, by omega⟩
      · rintro ⟨w, hw, rfl⟩; omega
    simp only [alt, coalt]
    split_ifs
    · rw [support_join nA nA', support_union, sA, sC, sm sA, sm sC, split]; exact ⟨rfl, rfl⟩
    · rw [support_union, support_join nC nC', sA, sC, sm sA, sm sC, split]; exact ⟨rfl, rfl⟩

theorem verts_altTree (i : ℕ) : (altTree i).verts = range (2 ^ i) ∧
    (coaltTree i).verts = range (2 ^ i) := by
  induction i with
  | zero => exact ⟨by decide, by decide⟩
  | succ i ih =>
    have split : range (2 ^ (i + 1)) = range (2 ^ i) ∪ (range (2 ^ i)).map (shift (2 ^ i)) := by
      rw [range_map_shift]; ext x; simp only [mem_range, mem_union, mem_filter, pow_succ]; omega
    simp only [altTree, coaltTree]
    split_ifs <;> simp [Cotree.verts, Cotree.verts_shift, ih.1, ih.2, split]

/-- **Observation 4.4.9.** For every `i`, two vertices are adjacent in the primal graph of
`Γᵢ` (resp. `Γ̄ᵢ`) exactly when they are adjacent in the cograph of the alternating tree.
`Γ_{2k-1}, Γ̄_{2k-1}` are `g_k, f_k` and `Γ_{2k}, Γ̄_{2k}` are `r_k, S_k`. -/
theorem primalAdj_alt (i : ℕ) (u v : ℕ) :
    (primalAdj (alt i) u v ↔ (altTree i).Adj u v) ∧
    (primalAdj (coalt i) u v ↔ (coaltTree i).Adj u v) := by
  induction i generalizing u v with
  | zero =>
    constructor
    · simp only [alt, altTree, Cotree.Adj, iff_false, primalAdj, mem_singleton]
      rintro ⟨huv, e, rfl, hu, hv⟩; simp at hu hv; exact huv (hu.trans hv.symm)
    · simp only [coalt, coaltTree, Cotree.Adj, iff_false, primalAdj, mem_singleton]
      rintro ⟨huv, e, rfl, hu, hv⟩; simp at hu hv; exact huv (hu.trans hv.symm)
  | succ i ih =>
    obtain ⟨hd, hlo, hhi⟩ := low_high i
    obtain ⟨wA, wC, nA, nC, -, -⟩ := alt_props i
    obtain ⟨sA, sC⟩ := support_alt i
    obtain ⟨vA, vC⟩ := verts_altTree i
    have wA' := mapH_within (φ := shift (2 ^ i)) wA
    have wC' := mapH_within (φ := shift (2 ^ i)) wC
    have memS : ∀ {A : Finset (Finset ℕ)} {t : Cotree}, support A = range (2 ^ i) →
        t.verts = range (2 ^ i) → ∀ w,
        (w ∈ support (mapH (shift (2 ^ i)) A) ↔ w ∈ (t.shift (2 ^ i)).verts) := by
      intro A t hA ht w
      rw [mem_support_mapH_shift, Cotree.mem_verts_shift, hA, ht]
    simp only [alt, coalt, altTree, coaltTree]
    split_ifs
    · constructor
      · rw [primalAdj_join hd wA wA' nA (nA.image _), primalAdj_mapH_shift, Cotree.Adj,
          Cotree.adj_shift, (ih u v).1, (ih _ _).1, memS sA vA, memS sA vA, sA, vA]
      · rw [primalAdj_union, primalAdj_mapH_shift, Cotree.Adj, Cotree.adj_shift, (ih u v).2,
          (ih _ _).2]
    · constructor
      · rw [primalAdj_union, primalAdj_mapH_shift, Cotree.Adj, Cotree.adj_shift, (ih u v).1,
          (ih _ _).1]
      · rw [primalAdj_join hd wC wC' nC (nC.image _), primalAdj_mapH_shift, Cotree.Adj,
          Cotree.adj_shift, (ih u v).2, (ih _ _).2, memS sC vC, memS sC vC, sC, vC]

end HD

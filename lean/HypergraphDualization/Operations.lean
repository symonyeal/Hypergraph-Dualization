/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Union and join of hypergraphs (§4.1)

`G ∨ H` is the union of the edge families; `G ∧ H` is `{e ∪ f : e ∈ G, f ∈ H}`.

| Lean | Thesis |
| --- | --- |
| `tr_union` | §4.1: `Tr(G ∨ H) = min(Tr(G) ∧ Tr(H))` |
| `tr_join` | §4.1: `Tr(G ∧ H) = min(Tr(G) ∨ Tr(H))` |
| `card_join_of_disjoint` | §4.1, vertex-disjoint case: `|Tr(G ∨ H)| = |Tr G|·|Tr H|` |
| `join_isSperner_of_disjoint` | the `min` is unnecessary for vertex-disjoint Sperner families |
-/
import HypergraphDualization.Duality

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-- `G ∧ H = {e ∪ f : e ∈ G, f ∈ H}`. -/
def join (G H : Finset (Finset α)) : Finset (Finset α) := (G ×ˢ H).image fun p => p.1 ∪ p.2

theorem mem_join {G H : Finset (Finset α)} {s : Finset α} :
    s ∈ join G H ↔ ∃ e ∈ G, ∃ f ∈ H, e ∪ f = s := by
  simp [join, and_assoc]

theorem hits_union {G H : Finset (Finset α)} {T : Finset α} :
    Hits (G ∪ H) T ↔ Hits G T ∧ Hits H T := by
  simp only [Hits, mem_union]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem hits_join {G H : Finset (Finset α)} {T : Finset α} :
    Hits (join G H) T ↔ Hits G T ∨ Hits H T := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    unfold Hits at hno
    push Not at hno
    obtain ⟨⟨e, he, hTe⟩, ⟨f, hf, hTf⟩⟩ := hno
    obtain ⟨x, hx⟩ := h (e ∪ f) (mem_join.2 ⟨e, he, f, hf, rfl⟩)
    rw [inter_union_distrib_left, mem_union] at hx
    rcases hx with hx | hx
    · exact (not_nonempty_iff_eq_empty.2 hTe) ⟨x, hx⟩
    · exact (not_nonempty_iff_eq_empty.2 hTf) ⟨x, hx⟩
  · rintro (h | h) s hs
    all_goals obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hs
    · exact (h e he).mono (inter_subset_inter_left subset_union_left)
    · exact (h f hf).mono (inter_subset_inter_left subset_union_right)

/-- Inside `U`, a set contains a minimal transversal iff it is a transversal. -/
theorem upHit_tr_iff {U : Finset α} {H : Finset (Finset α)} {A : Finset α} (hA : A ⊆ U) :
    upHit (tr U H) A ↔ Hits H A := by
  constructor
  · rintro ⟨T, hT, hTA⟩; exact hits_mono (mem_tr.1 hT).2.1 hTA
  · intro h
    obtain ⟨T, hTA, hT⟩ := exists_isMinHit_subset _ A rfl h
    exact ⟨T, mem_tr.2 ⟨hTA.trans hA, hT⟩, hTA⟩

theorem upHit_join {G H : Finset (Finset α)} {A : Finset α} :
    upHit (join G H) A ↔ upHit G A ∧ upHit H A := by
  constructor
  · rintro ⟨s, hs, hsA⟩
    obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hs
    exact ⟨⟨e, he, subset_union_left.trans hsA⟩, ⟨f, hf, subset_union_right.trans hsA⟩⟩
  · rintro ⟨⟨e, he, heA⟩, ⟨f, hf, hfA⟩⟩
    exact ⟨e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩, union_subset heA hfA⟩

theorem upHit_union {G H : Finset (Finset α)} {A : Finset α} :
    upHit (G ∪ H) A ↔ upHit G A ∨ upHit H A := by
  simp only [upHit, mem_union]
  constructor
  · rintro ⟨e, he | he, h⟩; exact Or.inl ⟨e, he, h⟩; exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩); exact ⟨e, Or.inl he, h⟩; exact ⟨e, Or.inr he, h⟩

theorem join_within {U : Finset α} {G H : Finset (Finset α)} (hG : Within U G)
    (hH : Within U H) : Within U (join G H) := by
  intro s hs
  obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hs
  exact union_subset (hG e he) (hH f hf)

/-- **§4.1.** `Tr(G ∨ H) = min(Tr(G) ∧ Tr(H))`. -/
theorem tr_union {U : Finset α} (G H : Finset (Finset α)) :
    tr U (G ∪ H) = minimal (join (tr U G) (tr U H)) := by
  refine eq_of_upHit_iff (tr_within U _)
    (fun e he => join_within (tr_within U G) (tr_within U H) e (minimal_subset _ he))
    (tr_isSperner U _) (minimal_isSperner _) fun A hA => ?_
  rw [upHit_minimal, upHit_join, upHit_tr_iff hA, upHit_tr_iff hA, upHit_tr_iff hA, hits_union]

/-- **§4.1.** `Tr(G ∧ H) = min(Tr(G) ∨ Tr(H))`. -/
theorem tr_join {U : Finset α} (G H : Finset (Finset α)) :
    tr U (join G H) = minimal (tr U G ∪ tr U H) := by
  refine eq_of_upHit_iff (tr_within U _)
    (fun e he => by
      rcases mem_union.1 (minimal_subset _ he) with h | h
      exacts [tr_within U G e h, tr_within U H e h])
    (tr_isSperner U _) (minimal_isSperner _) fun A hA => ?_
  rw [upHit_minimal, upHit_union, upHit_tr_iff hA, upHit_tr_iff hA, upHit_tr_iff hA, hits_join]

/-! ### Vertex-disjoint families -/

/-- For families inside disjoint sets, `(e, f) ↦ e ∪ f` is injective. -/
theorem union_injOn {V W : Finset α} (hVW : Disjoint V W) {G H : Finset (Finset α)}
    (hG : Within V G) (hH : Within W H) :
    Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2) (G ×ˢ H : Finset _) := by
  rintro ⟨e, f⟩ hp ⟨e', f'⟩ hp' heq
  simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
  simp only at heq
  have hl : ∀ {a b c d : Finset α}, a ⊆ V → b ⊆ W → c ⊆ V → d ⊆ W → a ∪ b = c ∪ d → a = c := by
    intro a b c d ha hb hc hd h
    ext x; constructor
    · intro hx
      have : x ∈ c ∪ d := h ▸ mem_union_left _ hx
      rcases mem_union.1 this with h' | h'
      · exact h'
      · exact absurd (hd h') (disjoint_left.1 hVW (ha hx))
    · intro hx
      have : x ∈ a ∪ b := h.symm ▸ mem_union_left _ hx
      rcases mem_union.1 this with h' | h'
      · exact h'
      · exact absurd (hb h') (disjoint_left.1 hVW (hc hx))
  have he := hl (hG e hp.1) (hH f hp.2) (hG e' hp'.1) (hH f' hp'.2) heq
  exact Prod.ext he (by
    ext x; constructor
    · intro hx
      have : x ∈ e' ∪ f' := heq ▸ mem_union_right _ hx
      rcases mem_union.1 this with h' | h'
      · exact absurd (hG e' hp'.1 h') (disjoint_right.1 hVW (hH f hp.2 hx))
      · exact h'
    · intro hx
      have : x ∈ e ∪ f := heq.symm ▸ mem_union_right _ hx
      rcases mem_union.1 this with h' | h'
      · exact absurd (hG e hp.1 h') (disjoint_right.1 hVW (hH f' hp'.2 hx))
      · exact h')

/-- **§4.1**, vertex-disjoint case: the join of `G` and `H` has `|G|·|H|` edges. -/
theorem card_join_of_disjoint {V W : Finset α} (hVW : Disjoint V W) {G H : Finset (Finset α)}
    (hG : Within V G) (hH : Within W H) : (join G H).card = G.card * H.card := by
  rw [join, card_image_of_injOn (union_injOn hVW hG hH), card_product]

/-- The join of Sperner families on disjoint sets is Sperner. -/
theorem join_isSperner_of_disjoint {V W : Finset α} (hVW : Disjoint V W)
    {G H : Finset (Finset α)} (hG : Within V G) (hH : Within W H) (sG : IsSperner G)
    (sH : IsSperner H) : IsSperner (join G H) := by
  intro s hs t ht hst
  obtain ⟨e, he, f, hf, rfl⟩ := mem_join.1 hs
  obtain ⟨e', he', f', hf', rfl⟩ := mem_join.1 ht
  have h1 : e ⊆ e' := fun x hx => by
    rcases mem_union.1 (hst (mem_union_left _ hx)) with h | h
    · exact h
    · exact absurd (hH f' hf' h) (disjoint_left.1 hVW (hG e he hx))
  have h2 : f ⊆ f' := fun x hx => by
    rcases mem_union.1 (hst (mem_union_right _ hx)) with h | h
    · exact absurd (hG e' he' h) (disjoint_right.1 hVW (hH f hf hx))
    · exact h
  rw [sG e he e' he' h1, sH f hf f' hf' h2]

/-- Families with no empty edge, on disjoint sets, have a Sperner union of disjoint parts. -/
theorem union_isSperner_of_disjoint {V W : Finset α} (hVW : Disjoint V W)
    {G H : Finset (Finset α)} (hG : Within V G) (hH : Within W H) (sG : IsSperner G)
    (sH : IsSperner H) (nG : ∅ ∉ G) (nH : ∅ ∉ H) : IsSperner (G ∪ H) := by
  have cross : ∀ {P Q : Finset α}, Disjoint P Q → ∀ {e f : Finset α}, e ⊆ P → f ⊆ Q → e ⊆ f →
      e = ∅ := fun hPQ _ _ he hf hef =>
    eq_empty_of_forall_notMem fun x hx => disjoint_left.1 hPQ (he hx) (hf (hef hx))
  intro e he f hf hef
  rcases mem_union.1 he with he | he <;> rcases mem_union.1 hf with hf | hf
  · exact sG e he f hf hef
  · exact absurd (cross hVW (hG e he) (hH f hf) hef ▸ he) nG
  · exact absurd (cross hVW.symm (hH e he) (hG f hf) hef ▸ he) nH
  · exact sH e he f hf hef

end HD

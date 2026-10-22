/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Substitution (research track D, item D1)

Let `T` be a hypergraph on an index type `ι` (the template) and `Γ i` a hypergraph for each
`i : ι`. The substitution `T[Γ]` replaces each point `i` of an edge `t ∈ T` by an edge of `Γ i`:
`T[Γ] = {⋃_{i∈t} g_i : t ∈ T, g_i ∈ Γ i}`. As monotone functions it is the composition
`f_T(f_{Γ 1}, …, f_{Γ m})`. Union (`T = {{0}, {1}}`) and join (`T = {{0, 1}}`) are the two
smallest cases.

| Lean | Statement |
| --- | --- |
| `upHit_subst` | `X ⊇` an edge of `T[Γ]` iff `{i : X ⊇` an edge of `Γ i}` `⊇` an edge of `T` |
| `hits_subst` | `X` hits `T[Γ]` iff `{i : X` hits `Γ i}` hits `T` |
| `tr_subst` | **Theorem D1.** `Tr(T[Γ]) = min(Tr(T)[Tr Γ])` |
| `subst_isSperner` | on disjoint supports, without empty edges, `T[Γ]` is Sperner when `T` and every `Γ i` are |
| `tr_subst_of_disjoint` | on disjoint supports, `Tr(T[Γ]) = Tr(T)[Tr Γ]`: no reduction needed |
| `card_subst` | on disjoint supports, `|T[Γ]| = Σ_{t∈T} Π_{i∈t} |Γ i|` |
| `card_subst_uniform` | `r`-uniform `T`, `|Γ i| = l`: `|T[Γ]| = |T|·l^r` |
| `prop_P_comp` | **Proposition D2.** `(P)`: `k·k* ≥ 8^{r−1}` passes from two templates to their composite |
| `template_rank_two` | **D3 at `r = 2`.** every 2-uniform template on 4 points with 2-uniform dual satisfies `(P)` |
-/
import HypergraphDualization.Operations
import HypergraphDualization.Conditions
import Mathlib.Tactic.Ring

namespace HD

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- `⋃_{i∈t} g_i` for a choice `g` of one set per point of `t`. -/
def glue (t : Finset ι) (g : ∀ i ∈ t, Finset α) : Finset α := t.attach.biUnion fun i => g i.1 i.2

/-- The substitution `T[Γ] = {⋃_{i∈t} g_i : t ∈ T, g_i ∈ Γ i}`. -/
def subst (T : Finset (Finset ι)) (Γ : ι → Finset (Finset α)) : Finset (Finset α) :=
  T.biUnion fun t => (t.pi Γ).image (glue t)

omit [DecidableEq ι] in
theorem mem_glue {t : Finset ι} {g : ∀ i ∈ t, Finset α} {x : α} :
    x ∈ glue t g ↔ ∃ i, ∃ hi : i ∈ t, x ∈ g i hi := by
  simp [glue]

theorem mem_subst {T : Finset (Finset ι)} {Γ : ι → Finset (Finset α)} {s : Finset α} :
    s ∈ subst T Γ ↔ ∃ t ∈ T, ∃ g ∈ t.pi Γ, glue t g = s := by
  simp [subst]

theorem subst_within {U : Finset α} {T : Finset (Finset ι)} {Γ : ι → Finset (Finset α)}
    (hΓ : ∀ i, Within U (Γ i)) : Within U (subst T Γ) := by
  intro s hs x hx
  obtain ⟨t, -, g, hg, rfl⟩ := mem_subst.1 hs
  obtain ⟨i, hi, hx⟩ := mem_glue.1 hx
  exact hΓ i (g i hi) (mem_pi.1 hg i hi) hx

variable [Fintype ι]

theorem upHit_subst {T : Finset (Finset ι)} {Γ : ι → Finset (Finset α)} {X : Finset α} :
    upHit (subst T Γ) X ↔ upHit T (univ.filter fun i => upHit (Γ i) X) := by
  constructor
  · rintro ⟨s, hs, hsX⟩
    obtain ⟨t, ht, g, hg, rfl⟩ := mem_subst.1 hs
    exact ⟨t, ht, fun i hi => mem_filter.2 ⟨mem_univ i, g i hi, mem_pi.1 hg i hi,
      fun x hx => hsX (mem_glue.2 ⟨i, hi, hx⟩)⟩⟩
  · rintro ⟨t, ht, htS⟩
    have h : ∀ i ∈ t, ∃ e ∈ Γ i, e ⊆ X := fun i hi => (mem_filter.1 (htS hi)).2
    choose g hg hgX using h
    exact ⟨glue t g, mem_subst.2 ⟨t, ht, g, mem_pi.2 hg, rfl⟩, fun x hx => by
      obtain ⟨i, hi, hx⟩ := mem_glue.1 hx; exact hgX i hi hx⟩

theorem hits_subst {T : Finset (Finset ι)} {Γ : ι → Finset (Finset α)} {X : Finset α} :
    Hits (subst T Γ) X ↔ Hits T (univ.filter fun i => Hits (Γ i) X) := by
  constructor
  · intro h t ht
    by_contra hn
    have h' : ∀ i ∈ t, ∃ e ∈ Γ i, ¬ (X ∩ e).Nonempty := fun i hi => by
      by_contra hc
      push Not at hc
      exact hn ⟨i, mem_inter.2 ⟨mem_filter.2 ⟨mem_univ i, hc⟩, hi⟩⟩
    choose g hg hgX using h'
    obtain ⟨x, hx⟩ := h (glue t g) (mem_subst.2 ⟨t, ht, g, mem_pi.2 hg, rfl⟩)
    obtain ⟨i, hi, hxi⟩ := mem_glue.1 (mem_inter.1 hx).2
    exact hgX i hi ⟨x, mem_inter.2 ⟨(mem_inter.1 hx).1, hxi⟩⟩
  · intro h s hs
    obtain ⟨t, ht, g, hg, rfl⟩ := mem_subst.1 hs
    obtain ⟨i, hi⟩ := h t ht
    obtain ⟨hiS, hit⟩ := mem_inter.1 hi
    obtain ⟨x, hx⟩ := (mem_filter.1 hiS).2 (g i hit) (mem_pi.1 hg i hit)
    exact ⟨x, mem_inter.2 ⟨(mem_inter.1 hx).1, mem_glue.2 ⟨i, hit, (mem_inter.1 hx).2⟩⟩⟩

/-- **Theorem D1.** `Tr(T[Γ]) = min(Tr(T)[Tr Γ])`: a set hits `T[Γ]` iff the points `i` whose
`Γ i` it hits form a transversal of `T`. No hypothesis on `T` or `Γ`. -/
theorem tr_subst {U : Finset α} (T : Finset (Finset ι)) (Γ : ι → Finset (Finset α)) :
    tr U (subst T Γ) = minimal (subst (tr univ T) fun i => tr U (Γ i)) := by
  refine eq_of_upHit_iff (tr_within U _)
    (fun e he => subst_within (fun i => tr_within U (Γ i)) e (minimal_subset _ he))
    (tr_isSperner U _) (minimal_isSperner _) fun A hA => ?_
  rw [upHit_minimal, upHit_subst, upHit_tr_iff (subset_univ _), upHit_tr_iff hA, hits_subst]
  simp only [upHit_tr_iff hA]

/-! ### Disjoint supports -/

variable {V : ι → Finset α}

omit [Fintype ι] in
/-- On disjoint supports without empty edges, `⋃_{i∈t} g_i ⊆ ⋃_{i∈t'} g'_i` forces `t ⊆ t'`
and `g_i ⊆ g'_i`: the part of a glued set inside `V i` is `g_i`. -/
theorem glue_subset_glue (hV : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    {Γ : ι → Finset (Finset α)} (hΓ : ∀ i, Within (V i) (Γ i)) (h0 : ∀ i, ∅ ∉ Γ i)
    {t t' : Finset ι} {g : ∀ i ∈ t, Finset α} {g' : ∀ i ∈ t', Finset α} (hg : g ∈ t.pi Γ)
    (hg' : g' ∈ t'.pi Γ) (h : glue t g ⊆ glue t' g') :
    t ⊆ t' ∧ ∀ i (hi : i ∈ t) (hi' : i ∈ t'), g i hi ⊆ g' i hi' := by
  -- a point of `g_i` lying in `g'_j` forces `j = i`
  have key : ∀ i (hi : i ∈ t) x, x ∈ g i hi → ∃ hi' : i ∈ t', x ∈ g' i hi' := by
    intro i hi x hx
    obtain ⟨j, hj, hxj⟩ := mem_glue.1 (h (mem_glue.2 ⟨i, hi, hx⟩))
    have hij : j = i := by
      by_contra hne
      exact disjoint_left.1 (hV j i hne) (hΓ j _ (mem_pi.1 hg' j hj) hxj)
        (hΓ i _ (mem_pi.1 hg i hi) hx)
    subst hij
    exact ⟨hj, hxj⟩
  refine ⟨fun i hi => ?_, fun i hi hi' x hx => (key i hi x hx).2⟩
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 fun he => h0 i (he ▸ mem_pi.1 hg i hi)
  exact (key i hi x hx).1

omit [Fintype ι] in
theorem subst_isSperner (hV : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    {T : Finset (Finset ι)} {Γ : ι → Finset (Finset α)} (hΓ : ∀ i, Within (V i) (Γ i))
    (h0 : ∀ i, ∅ ∉ Γ i) (sT : IsSperner T) (sΓ : ∀ i, IsSperner (Γ i)) :
    IsSperner (subst T Γ) := by
  intro s hs s' hs' hss'
  obtain ⟨t, ht, g, hg, rfl⟩ := mem_subst.1 hs
  obtain ⟨t', ht', g', hg', rfl⟩ := mem_subst.1 hs'
  obtain ⟨htt', hgg'⟩ := glue_subset_glue hV hΓ h0 hg hg' hss'
  have := sT t ht t' ht' htt'
  subst this
  have : g = g' := funext fun i => funext fun hi =>
    sΓ i _ (mem_pi.1 hg i hi) _ (mem_pi.1 hg' i hi) (hgg' i hi hi)
  rw [this]

/-- A minimal transversal lies in the support of the hypergraph. -/
theorem isMinHit_subset {H : Finset (Finset α)} {W : Finset α} (hH : Within W H) {X : Finset α}
    (hX : IsMinHit H X) : X ⊆ W := fun v hv => by
  obtain ⟨f, hf, hXf⟩ := exists_private_edge hX hv
  exact hH f hf (mem_of_mem_inter_right (hXf ▸ mem_singleton_self v : v ∈ X ∩ f))

/-- **Theorem D1, disjoint case.** On disjoint supports with every `Γ i` nonempty,
`Tr(T[Γ]) = Tr(T)[Tr Γ]`: the substituted family is already Sperner. -/
theorem tr_subst_of_disjoint {U : Finset α} (hV : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (T : Finset (Finset ι)) {Γ : ι → Finset (Finset α)} (hΓ : ∀ i, Within (V i) (Γ i))
    (hne : ∀ i, (Γ i).Nonempty) :
    tr U (subst T Γ) = subst (tr univ T) fun i => tr U (Γ i) := by
  rw [tr_subst, minimal_eq_self]
  refine subst_isSperner hV (fun i e he => isMinHit_subset (hΓ i) (mem_tr.1 he).2)
    (fun i h => ?_) (tr_isSperner _ _) fun i => tr_isSperner _ _
  obtain ⟨e, he⟩ := hne i
  obtain ⟨x, hx⟩ := (mem_tr.1 h).2.1 e he
  simp at hx

omit [Fintype ι] in
/-- On disjoint supports without empty edges, `|T[Γ]| = Σ_{t∈T} Π_{i∈t} |Γ i|`. -/
theorem card_subst (hV : ∀ i j, i ≠ j → Disjoint (V i) (V j)) {T : Finset (Finset ι)}
    {Γ : ι → Finset (Finset α)} (hΓ : ∀ i, Within (V i) (Γ i)) (h0 : ∀ i, ∅ ∉ Γ i) :
    (subst T Γ).card = ∑ t ∈ T, ∏ i ∈ t, (Γ i).card := by
  have inj : ∀ {t t'} {g : ∀ i ∈ t, Finset α} {g' : ∀ i ∈ t', Finset α}, g ∈ t.pi Γ →
      g' ∈ t'.pi Γ → glue t g = glue t' g' → t = t' ∧ HEq g g' := by
    intro t t' g g' hg hg' h
    obtain ⟨h1, k1⟩ := glue_subset_glue hV hΓ h0 hg hg' h.le
    obtain ⟨h2, k2⟩ := glue_subset_glue hV hΓ h0 hg' hg h.ge
    have htt := Subset.antisymm h1 h2
    subst htt
    exact ⟨rfl, heq_of_eq (funext fun i => funext fun hi => Subset.antisymm (k1 i hi hi)
      (k2 i hi hi))⟩
  rw [subst, card_biUnion]
  · refine sum_congr rfl fun t _ => ?_
    rw [card_image_of_injOn, card_pi]
    intro g hg g' hg' h
    exact eq_of_heq (inj hg hg' h).2
  · intro t _ t' _ htt'
    refine disjoint_left.2 fun s hs hs' => htt' ?_
    obtain ⟨g, hg, rfl⟩ := mem_image.1 hs
    obtain ⟨g', hg', h⟩ := mem_image.1 hs'
    exact (inj hg hg' h.symm).1

omit [Fintype ι] in
/-- On disjoint supports without empty edges, an `r`-uniform `T` with `|Γ i| = l` for every `i`
has `|T[Γ]| = |T|·l^r`. -/
theorem card_subst_uniform (hV : ∀ i j, i ≠ j → Disjoint (V i) (V j)) {T : Finset (Finset ι)}
    {Γ : ι → Finset (Finset α)} (hΓ : ∀ i, Within (V i) (Γ i)) (h0 : ∀ i, ∅ ∉ Γ i) {r l : ℕ}
    (hr : ∀ t ∈ T, t.card = r) (hl : ∀ i, (Γ i).card = l) :
    (subst T Γ).card = T.card * l ^ r := by
  rw [card_subst hV hΓ h0, sum_congr rfl fun t ht => by rw [prod_congr rfl fun i _ => hl i,
    prod_const, hr t ht], sum_const, smul_eq_mul]

/-- **Proposition D2.** Let a template be `r`-uniform with `k` edges and `k*` minimal
transversals, both `r`-uniform, and satisfy `(P)`: `k·k* ≥ 8^{r−1}`. Substituting into each point
a copy of an `s`-template with `(l, l*)` satisfying `(P)` gives an `rs`-template with
`(k·l^r, k*·l*^r)` (`card_subst_uniform`, `tr_subst_of_disjoint`), and it satisfies `(P)`.
Under `(P)`, `c_∞ = max(log₂ k, log₂ k*)/(r − 1) ≥ 3/2`. -/
theorem prop_P_comp {r s k k' l l' : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hT : 8 ^ (r - 1) ≤ k * k')
    (hS : 8 ^ (s - 1) ≤ l * l') : 8 ^ (r * s - 1) ≤ (k * l ^ r) * (k' * l' ^ r) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hs
  simp only [Nat.add_sub_cancel] at hT hS
  have h : (r + 1) * (s + 1) = r + s * (r + 1) + 1 := by ring
  rw [h, Nat.add_sub_cancel, pow_add, pow_mul]
  calc 8 ^ r * (8 ^ s) ^ (r + 1) ≤ (k * k') * (l * l') ^ (r + 1) :=
        Nat.mul_le_mul hT (Nat.pow_le_pow_left hS _)
    _ = (k * l ^ (r + 1)) * (k' * l' ^ (r + 1)) := by ring

/-- Every family of pairs of `Fin 4` with a nonempty 2-uniform transversal family has
`(|G|, |Tr G|)` equal to `(2, 4)`, `(4, 2)` or `(3, 3)` (evaluation, `native_decide`, over the 64
families). -/
theorem template_rank_two_check : ∀ G ∈ ((univ : Finset (Fin 4)).powersetCard 2).powerset,
    G.Nonempty → (∀ t ∈ tr univ G, t.card = 2) →
      (G.card, (tr univ G).card) ∈ ({(2, 4), (4, 2), (3, 3)} : Finset (ℕ × ℕ)) := by
  native_decide

/-- **Open problem D3 at `r = 2`.** A nonempty 2-uniform template on 4 points whose minimal
transversals are 2-uniform satisfies `(P)`: `k·k* ≥ 8`. The counts `(k, k*)` are `(2, 4)`,
`(4, 2)` or `(3, 3)`: the matching, the 4-cycle and the path `P₄` up to relabelling. `P₄`, the
only one that is not read-once, exceeds the bound. -/
theorem template_rank_two {G : Finset (Finset (Fin 4))} (hG : ∀ g ∈ G, g.card = 2)
    (hne : G.Nonempty) (hT : ∀ t ∈ tr univ G, t.card = 2) : 8 ≤ G.card * (tr univ G).card := by
  have h := template_rank_two_check G
    (mem_powerset.2 fun g hg => mem_powersetCard.2 ⟨subset_univ _, hG g hg⟩) hne hT
  simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

end HD

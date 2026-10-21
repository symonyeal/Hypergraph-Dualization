/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Hypergraphs, transversals and the transversal hypergraph

A hypergraph on a ground set `U : Finset α` is a family `H : Finset (Finset α)`.
Edges are not required to lie in `U` or to be nonempty; each result states what it needs.

| Symbol | Meaning | Thesis |
| --- | --- | --- |
| `Hits H T` | `T` meets every edge of `H` | Def. 1.1.4 |
| `upHit H S` | some edge of `H` lies inside `S`: the monotone function with DNF `H` | §1.1.2 |
| `IsMinHit H T` | `T` hits `H`, and no `T.erase v` does | Def. 1.1.4 |
| `tr U H` | minimal transversals of `H` inside `U` | `Tr(H)` |
| `minimal H` | inclusion-minimal edges of `H` | Def. 1.1.3, `min(H)` |
| `IsSperner H` | no edge is contained in another edge | Def. 1.1.2 |
| `Within U H` | every edge of `H` lies in `U` | |
| `degree H v` | number of edges containing `v` | Def. 1.1.6 |
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Antichain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

/-- `T` meets every edge of `H`. -/
def Hits (H : Finset (Finset α)) (T : Finset α) : Prop := ∀ e ∈ H, (T ∩ e).Nonempty

instance (H : Finset (Finset α)) (T : Finset α) : Decidable (Hits H T) := by
  unfold Hits; infer_instance

/-- Some edge of `H` lies inside `S`. -/
def upHit (H : Finset (Finset α)) (S : Finset α) : Prop := ∃ e ∈ H, e ⊆ S

instance (H : Finset (Finset α)) (S : Finset α) : Decidable (upHit H S) := by
  unfold upHit; infer_instance

/-- `T` is a minimal transversal: it hits `H` and no one-point deletion does. -/
def IsMinHit (H : Finset (Finset α)) (T : Finset α) : Prop :=
  Hits H T ∧ ∀ v ∈ T, ¬ Hits H (T.erase v)

instance (H : Finset (Finset α)) (T : Finset α) : Decidable (IsMinHit H T) := by
  unfold IsMinHit; infer_instance

/-- The transversal hypergraph of `H` on the ground set `U`. -/
def tr (U : Finset α) (H : Finset (Finset α)) : Finset (Finset α) :=
  U.powerset.filter (IsMinHit H)

/-- The inclusion-minimal edges of `H`. -/
def minimal (H : Finset (Finset α)) : Finset (Finset α) :=
  H.filter (fun e => ∀ f ∈ H, f ⊆ e → f = e)

/-- No edge of `H` is contained in another. -/
def IsSperner (H : Finset (Finset α)) : Prop := ∀ e ∈ H, ∀ f ∈ H, e ⊆ f → e = f

instance (H : Finset (Finset α)) : Decidable (IsSperner H) := by
  unfold IsSperner; infer_instance

/-- Every edge of `H` lies in `U`. -/
def Within (U : Finset α) (H : Finset (Finset α)) : Prop := ∀ e ∈ H, e ⊆ U

instance (U : Finset α) (H : Finset (Finset α)) : Decidable (Within U H) := by
  unfold Within; infer_instance

/-- The number of edges containing `v`. -/
def degree (H : Finset (Finset α)) (v : α) : ℕ := (H.filter (v ∈ ·)).card

/-- The union of the edges. -/
def support (H : Finset (Finset α)) : Finset α := H.biUnion id

/-! ### Transversals -/

theorem hits_mono {H : Finset (Finset α)} {T T' : Finset α} (h : Hits H T) (hT : T ⊆ T') :
    Hits H T' := fun e he =>
  (h e he).mono (inter_subset_inter_right hT)

theorem not_hits_of_mem_empty {H : Finset (Finset α)} (h : ∅ ∈ H) (T : Finset α) :
    ¬ Hits H T := fun hT => by simpa using hT ∅ h

theorem isMinHit_iff {H : Finset (Finset α)} {T : Finset α} :
    IsMinHit H T ↔ Hits H T ∧ ∀ T' ⊆ T, Hits H T' → T' = T := by
  constructor
  · rintro ⟨hT, hmin⟩
    refine ⟨hT, fun T' hT' hhit => ?_⟩
    by_contra hne
    obtain ⟨v, hvT, hvT'⟩ := exists_of_ssubset (_root_.ssubset_iff_subset_ne.2 ⟨hT', hne⟩)
    exact hmin v hvT (hits_mono hhit (fun x hx => mem_erase.2 ⟨fun h => hvT' (h ▸ hx), hT' hx⟩))
  · rintro ⟨hT, hmin⟩
    refine ⟨hT, fun v hv hhit => ?_⟩
    have := hmin _ (erase_subset v T) hhit
    exact notMem_erase v T (by rw [this]; exact hv)

/-- Every transversal contains a minimal one. -/
theorem exists_isMinHit_subset {H : Finset (Finset α)} :
    ∀ (n : ℕ) (T : Finset α), T.card = n → Hits H T → ∃ T' ⊆ T, IsMinHit H T' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hT
    by_cases hmin : ∀ v ∈ T, ¬ Hits H (T.erase v)
    · exact ⟨T, subset_rfl, hT, hmin⟩
    · push Not at hmin
      obtain ⟨v, hv, hhit⟩ := hmin
      obtain ⟨T', hT'sub, hT'⟩ :=
        ih _ (hn ▸ card_erase_lt_of_mem hv) (T.erase v) rfl hhit
      exact ⟨T', hT'sub.trans (erase_subset v T), hT'⟩

theorem mem_tr {U : Finset α} {H : Finset (Finset α)} {T : Finset α} :
    T ∈ tr U H ↔ T ⊆ U ∧ IsMinHit H T := by
  simp [tr]

theorem tr_within (U : Finset α) (H : Finset (Finset α)) : Within U (tr U H) :=
  fun _ hT => (mem_tr.1 hT).1

/-- `Tr(H)` is Sperner (Def. 1.1.4). -/
theorem tr_isSperner (U : Finset α) (H : Finset (Finset α)) : IsSperner (tr U H) := by
  intro e he f hf hef
  have hf' := (isMinHit_iff.1 (mem_tr.1 hf).2).2
  exact hf' e hef (mem_tr.1 he).2.1

/-! ### Minimal edges -/

theorem mem_minimal {H : Finset (Finset α)} {e : Finset α} :
    e ∈ minimal H ↔ e ∈ H ∧ ∀ f ∈ H, f ⊆ e → f = e := mem_filter

theorem minimal_subset (H : Finset (Finset α)) : minimal H ⊆ H := filter_subset _ _

theorem exists_minimal_subset {H : Finset (Finset α)} :
    ∀ (n : ℕ) (e : Finset α), e.card = n → e ∈ H → ∃ f ∈ minimal H, f ⊆ e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e hn he
    by_cases hmin : ∀ f ∈ H, f ⊆ e → f = e
    · exact ⟨e, mem_filter.2 ⟨he, hmin⟩, subset_rfl⟩
    · push Not at hmin
      obtain ⟨f, hf, hfe, hne⟩ := hmin
      obtain ⟨g, hg, hgf⟩ :=
        ih _ (hn ▸ card_lt_card (_root_.ssubset_iff_subset_ne.2 ⟨hfe, hne⟩)) f rfl hf
      exact ⟨g, hg, hgf.trans hfe⟩

theorem upHit_minimal {H : Finset (Finset α)} {S : Finset α} :
    upHit (minimal H) S ↔ upHit H S := by
  constructor
  · rintro ⟨e, he, heS⟩; exact ⟨e, minimal_subset H he, heS⟩
  · rintro ⟨e, he, heS⟩
    obtain ⟨f, hf, hfe⟩ := exists_minimal_subset _ e rfl he
    exact ⟨f, hf, hfe.trans heS⟩

theorem hits_minimal {H : Finset (Finset α)} {T : Finset α} :
    Hits (minimal H) T ↔ Hits H T := by
  constructor
  · intro h e he
    obtain ⟨f, hf, hfe⟩ := exists_minimal_subset _ e rfl he
    exact (h f hf).mono (inter_subset_inter_left hfe)
  · intro h e he; exact h e (minimal_subset H he)

theorem minimal_isSperner (H : Finset (Finset α)) : IsSperner (minimal H) := by
  intro e he f hf hef
  exact ((mem_filter.1 hf).2 e (minimal_subset H he) hef)

theorem minimal_eq_self {H : Finset (Finset α)} (h : IsSperner H) : minimal H = H := by
  ext e
  refine ⟨fun he => minimal_subset H he, fun he => mem_filter.2 ⟨he, fun f hf hfe => ?_⟩⟩
  exact h f hf e he hfe

theorem isSperner_iff_minimal_eq {H : Finset (Finset α)} : IsSperner H ↔ minimal H = H :=
  ⟨minimal_eq_self, fun h => h ▸ minimal_isSperner H⟩

/-- **Proposition 1.1.5.** The transversal hypergraph is unchanged by Sperner reduction. -/
theorem tr_minimal (U : Finset α) (H : Finset (Finset α)) : tr U (minimal H) = tr U H := by
  ext T; simp only [tr, mem_filter, IsMinHit, hits_minimal]

end HD

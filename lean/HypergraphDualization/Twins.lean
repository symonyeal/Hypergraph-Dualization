/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Twins and the clique hypergraph (§4.4.2)

For a simple graph `G` on a finite type, `nbhd G u` is the open neighbourhood `N(u)` and
`cliques G` the clique hypergraph (Def. 1.1.15). `u, v` are false twins when
`N(u) = N(v)` and true twins when `N[u] = N[v]` (Def. 4.4.11).

| Lean | Thesis |
| --- | --- |
| `swap_isAut_of_twins` | swapping twins is a graph automorphism |
| `twins_mem_aut_cliques` | Lemma 4.4.13 **generalised**: twins permute in `H` and in `Tr(H)`, for every graph |
| `twins_map` | Lemma 4.4.14: automorphisms map true twins to true twins, false to false |
| `not_trueTwin_and_falseTwin` | §4.4.2: a vertex cannot have both a true twin and a false twin, so "twin" is an equivalence relation |
-/
import HypergraphDualization.Symmetry

namespace HD

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The open neighbourhood `N(u)`. -/
def nbhd (u : α) : Finset α := univ.filter (G.Adj u)

/-- The closed neighbourhood `N[u]`. -/
def cnbhd (u : α) : Finset α := insert u (nbhd G u)

/-- False twins: distinct, `N(u) = N(v)`. -/
def FalseTwin (u v : α) : Prop := u ≠ v ∧ nbhd G u = nbhd G v

/-- True twins: distinct, `N[u] = N[v]`. -/
def TrueTwin (u v : α) : Prop := u ≠ v ∧ cnbhd G u = cnbhd G v

/-- `σ` preserves adjacency in both directions. -/
def IsGraphAut (σ : Equiv.Perm α) : Prop := ∀ a b, G.Adj (σ a) (σ b) ↔ G.Adj a b

theorem falseTwin_not_adj {u v : α} (h : FalseTwin G u v) : ¬ G.Adj u v := by
  intro huv
  have : v ∈ nbhd G u := by simp [nbhd, huv]
  rw [h.2] at this
  simp [nbhd] at this

theorem trueTwin_adj {u v : α} (h : TrueTwin G u v) : G.Adj u v := by
  have : v ∈ cnbhd G u := by rw [h.2]; exact mem_insert_self v _
  rcases mem_insert.1 this with h' | h'
  · exact absurd h'.symm h.1
  · simpa [nbhd] using h'

/-- Outside `{u, v}`, twins have the same neighbours. -/
theorem twin_adj_iff {u v w : α} (h : FalseTwin G u v ∨ TrueTwin G u v) (hwu : w ≠ u)
    (hwv : w ≠ v) : G.Adj u w ↔ G.Adj v w := by
  rcases h with h | h
  · have := congrArg (w ∈ ·) h.2
    simpa [nbhd] using this
  · have := congrArg (w ∈ ·) h.2
    simpa [cnbhd, nbhd, hwu, hwv] using this

/-- Swapping twins is an automorphism of the graph. -/
theorem swap_isAut_of_twins {u v : α} (h : FalseTwin G u v ∨ TrueTwin G u v) :
    IsGraphAut G (Equiv.swap u v) := by
  have key : ∀ w, w ≠ u → w ≠ v → (G.Adj u w ↔ G.Adj v w) := fun w => twin_adj_iff G h
  -- One endpoint outside `{u, v}`: it is fixed, and the other endpoint is moved to a twin.
  have side : ∀ a b, a ≠ u → a ≠ v →
      (G.Adj (Equiv.swap u v a) (Equiv.swap u v b) ↔ G.Adj a b) := by
    intro a b hau hav
    rw [Equiv.swap_apply_of_ne_of_ne hau hav]
    by_cases hbu : b = u
    · rw [hbu, Equiv.swap_apply_left, G.adj_comm a v, G.adj_comm a u]
      exact (key a hau hav).symm
    by_cases hbv : b = v
    · rw [hbv, Equiv.swap_apply_right, G.adj_comm a u, G.adj_comm a v]
      exact key a hau hav
    rw [Equiv.swap_apply_of_ne_of_ne hbu hbv]
  intro a b
  by_cases ha : a ≠ u ∧ a ≠ v
  · exact side a b ha.1 ha.2
  by_cases hb : b ≠ u ∧ b ≠ v
  · rw [G.adj_comm, G.adj_comm a]; exact side b a hb.1 hb.2
  -- Both endpoints in `{u, v}`.
  have ha' : a = u ∨ a = v := by by_contra hc; push Not at hc; exact ha hc
  have hb' : b = u ∨ b = v := by by_contra hc; push Not at hc; exact hb hc
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha', hb'] <;>
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right, G.adj_comm]

/-- `s` is a clique. -/
def IsCliqueF (s : Finset α) : Prop := ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b

instance (s : Finset α) : Decidable (IsCliqueF G s) := by unfold IsCliqueF; infer_instance

/-- The clique hypergraph: the maximal cliques (Def. 1.1.15). -/
def cliques : Finset (Finset α) :=
  univ.filter fun s => IsCliqueF G s ∧ ∀ v ∉ s, ¬ IsCliqueF G (insert v s)

theorem isCliqueF_pmap {σ : Equiv.Perm α} (hσ : IsGraphAut G σ) {s : Finset α} :
    IsCliqueF G (pmap σ s) ↔ IsCliqueF G s := by
  constructor
  · intro h a ha b hb hab
    have := h (σ a) (by simpa [mem_pmap]) (σ b) (by simpa [mem_pmap]) (σ.injective.ne hab)
    exact (hσ a b).1 this
  · intro h a ha b hb hab
    rw [mem_pmap] at ha hb
    have := h _ ha _ hb (σ.symm.injective.ne hab)
    rw [← hσ] at this
    simpa using this

/-- A graph automorphism is an automorphism of the clique hypergraph. -/
theorem graphAut_mem_aut_cliques {σ : Equiv.Perm α} (hσ : IsGraphAut G σ) :
    σ ∈ aut (cliques G) := by
  refine mem_aut_of_subset fun s' hs' => ?_
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
  simp only [cliques, mem_filter, mem_univ, true_and] at hs ⊢
  refine ⟨(isCliqueF_pmap G hσ).2 hs.1, fun v hv hcl => ?_⟩
  have hv' : σ.symm v ∉ s := fun h => hv (by simpa [mem_pmap] using h)
  apply hs.2 _ hv'
  have : insert v (pmap σ s) = pmap σ (insert (σ.symm v) s) := by
    ext w; simp [mem_pmap, Equiv.symm_apply_eq]
  rw [this, isCliqueF_pmap G hσ] at hcl
  exact hcl

/-- **Lemma 4.4.13, generalised.** In any graph, twins `u, v` permute in the clique
hypergraph `H` and in `Tr(H)`: the transposition `(u v)` lies in both automorphism groups.
No distance-hereditary or conformality hypothesis is needed. -/
theorem twins_mem_aut_cliques {u v : α} (h : FalseTwin G u v ∨ TrueTwin G u v) :
    Equiv.swap u v ∈ aut (cliques G) ∧ Equiv.swap u v ∈ aut (tr univ (cliques G)) :=
  ⟨graphAut_mem_aut_cliques G (swap_isAut_of_twins G h),
    aut_le_aut_tr _ (graphAut_mem_aut_cliques G (swap_isAut_of_twins G h))⟩

theorem nbhd_map {σ : Equiv.Perm α} (hσ : IsGraphAut G σ) (u : α) :
    nbhd G (σ u) = pmap σ (nbhd G u) := by
  ext w
  simp only [nbhd, mem_filter, mem_univ, true_and, mem_pmap]
  rw [← hσ u (σ.symm w), Equiv.apply_symm_apply]

/-- **Lemma 4.4.14.** Graph automorphisms map false twins to false twins and true twins to
true twins. -/
theorem twins_map {σ : Equiv.Perm α} (hσ : IsGraphAut G σ) {u v : α} :
    (FalseTwin G u v → FalseTwin G (σ u) (σ v)) ∧ (TrueTwin G u v → TrueTwin G (σ u) (σ v)) := by
  refine ⟨fun h => ⟨σ.injective.ne h.1, by rw [nbhd_map G hσ, nbhd_map G hσ, h.2]⟩,
    fun h => ⟨σ.injective.ne h.1, ?_⟩⟩
  have : ∀ x, cnbhd G (σ x) = pmap σ (cnbhd G x) := by
    intro x; ext w; simp only [cnbhd, mem_insert, nbhd_map G hσ, mem_pmap]
    constructor
    · rintro (rfl | hw); exact Or.inl (by simp); exact Or.inr hw
    · rintro (hw | hw)
      · exact Or.inl (by rw [← hw]; simp)
      · exact Or.inr hw
  rw [this, this, h.2]

/-- **§4.4.2.** No vertex has both a true twin and a false twin; hence the twin relation is
an equivalence relation whose classes are all true-twin classes or all false-twin classes. -/
theorem not_trueTwin_and_falseTwin {u v w : α} (h1 : TrueTwin G u v) (h2 : FalseTwin G v w) :
    False := by
  have huv := trueTwin_adj G h1
  have hvw := falseTwin_not_adj G h2
  -- `u ∈ N(v) = N(w)`, so `w ∈ N(u) ⊆ N[u] = N[v]`, so `w ~ v`.
  have hu : u ∈ nbhd G w := by rw [← h2.2]; simp [nbhd, G.adj_comm, huv]
  have hw : w ∈ cnbhd G v := by
    rw [← h1.2]; exact mem_insert_of_mem (by simpa [nbhd, G.adj_comm] using hu)
  rcases mem_insert.1 hw with h | h
  · exact h2.1 h.symm
  · exact hvw (by simpa [nbhd, G.adj_comm] using h)

end HD

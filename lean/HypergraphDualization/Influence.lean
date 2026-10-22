/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Influences under automorphisms (research track E, item E2)

The influence of `v` on the monotone property "contains an edge of `G`" at density `p` is the
probability, under the product measure `bernoulliProbability` of `Connections`, that `v` is
pivotal: adding `v` creates an edge and removing it destroys every edge. An automorphism moves
influences along with points, so a transitive `Aut(G)` gives every point the same influence at
every `p`. With `bernoulli_self_dual` this settles item E2 for the Fano plane: `P_{1/2} = 1/2`
and all seven influences agree.

| Lean | Statement |
| --- | --- |
| `upHit_pimg` | `σ(A)` contains an edge of `σ(G)` iff `A` contains an edge of `G` |
| `bernoulliWeight_pmap` | the product measure is invariant under relabelling |
| `influence_aut` | `σ ∈ Aut(G)`: `I_p(σ v) = I_p(v)` |
| `influence_eq_of_transitive` | a transitive `Aut(G)` gives equal influences |
| `fano_influence_eq` | the Fano plane: all influences equal at every `p` |
-/
import HypergraphDualization.Connections
import HypergraphDualization.Symmetry
import Mathlib.Logic.Equiv.Fin.Rotate

namespace HD

open Finset OpenAI

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem upHit_pimg (σ : Equiv.Perm V) {G : Finset (Finset V)} {A : Finset V} :
    upHit (pimg σ G) (pmap σ A) ↔ upHit G A := by
  constructor
  · rintro ⟨e', he', h⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact ⟨e, he, (pmap_subset_iff σ).1 h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨pmap σ e, mem_image_of_mem _ he, (pmap_subset_iff σ).2 h⟩

omit [Fintype V] in
theorem pmap_insert (σ : Equiv.Perm V) (W : Finset V) (v : V) :
    pmap σ (insert v W) = insert (σ v) (pmap σ W) := by
  ext x
  simp only [mem_pmap, mem_insert]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [← h]; simp)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr h

theorem bernoulliWeight_pmap (p : ℝ) (σ : Equiv.Perm V) (W : Finset V) :
    bernoulliWeight p (pmap σ W) = bernoulliWeight p W := by
  unfold bernoulliWeight
  simp only [mem_pmap]
  exact Equiv.prod_comp σ.symm fun y => if y ∈ W then p else 1 - p

/-- The influence of `v` at density `p`: the probability that `v` is pivotal for "contains an
edge of `G`". -/
noncomputable def influence (p : ℝ) (G : Finset (Finset V)) (v : V) : ℝ :=
  bernoulliProbability p fun W => upHit G (insert v W) ∧ ¬ upHit G (W.erase v)

/-- An automorphism carries influences with points: `I_p(σ v) = I_p(v)`. -/
theorem influence_aut {G : Finset (Finset V)} {σ : Equiv.Perm V} (hσ : σ ∈ aut G) (p : ℝ)
    (v : V) : influence p G (σ v) = influence p G v := by
  unfold influence bernoulliProbability
  rw [← Equiv.sum_comp σ.finsetCongr]
  refine sum_congr rfl fun W _ => ?_
  have e : ∀ A, σ.finsetCongr A = pmap σ A := fun _ => rfl
  have key : ∀ A, upHit G (pmap σ A) ↔ upHit G A := fun A => by
    conv_lhs => rw [← mem_aut.1 hσ]
    exact upHit_pimg σ
  simp only [e, ← pmap_insert, ← pmap_erase, bernoulliWeight_pmap, key]
  by_cases h : upHit G (insert v W) ∧ ¬ upHit G (W.erase v) <;> simp [h]

/-- If `Aut(G)` is transitive, every point has the same influence at every density. -/
theorem influence_eq_of_transitive {G : Finset (Finset V)}
    (hT : ∀ u v : V, ∃ σ ∈ aut G, σ u = v) (p : ℝ) (u v : V) :
    influence p G u = influence p G v := by
  obtain ⟨σ, hσ, rfl⟩ := hT u v
  exact (influence_aut hσ p u).symm

/-- **E2 for the Fano plane.** The rotation `x ↦ x + 1` preserves `fanoC`, so all seven points have
the same influence at every `p`; `fano_k3_balanced` gives `P_{1/2} = 1/2`. The automorphism
check is by `decide`. -/
theorem fano_influence_eq (p : ℝ) (u v : Fin 7) :
    influence p Data.fanoC u = influence p Data.fanoC v := by
  have hρ : finRotate 7 ∈ aut Data.fanoC := by decide
  refine influence_eq_of_transitive (fun u v => ⟨finRotate 7 ^ (v - u : Fin 7).val,
    pow_mem hρ _, ?_⟩) p u v
  revert u v; decide

end HD

/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The smallest most-frequent-vertex frequency (Observation 5.2.3)

`ε(n)` is the least value of `eps C D` over transversal pairs on `n` vertices with both sides
nonempty and free of the empty edge. Observation 5.2.3 claims `ε(3) = 2/3` and `ε(7) = 3/7`.

| Lean | Thesis |
| --- | --- |
| `eps_three` | `ε(3) = 2/3`, attained only by `K₃` (exhaustive) |
| `eps_four` | `ε(4) = 1/2`, so `ε` is not determined by projective planes |
| `fano_eps` (in `Instances`) | the Fano plane has `eps = 3/7`; that `3/7` is the minimum on seven vertices is **not** established |
-/
import HypergraphDualization.Section32

namespace HD.S32

open HD HD.Data Finset

/-- The non-trivial transversal pairs: both sides nonempty and without the empty edge. -/
def NonTrivial {n : ℕ} (G : HG n) : Prop :=
  G.Nonempty ∧ ∅ ∉ G ∧ (tr univ G).Nonempty ∧ ∅ ∉ tr univ G

instance {n : ℕ} (G : HG n) : Decidable (NonTrivial G) := by unfold NonTrivial; infer_instance

/-- **Observation 5.2.3, `n = 3`.** Every non-trivial transversal pair on three vertices has
`eps ≥ 2/3`, with equality only for `K₃`. -/
theorem eps_three :
    ∀ G ∈ sperner 3, NonTrivial G →
      2 / 3 ≤ eps G (tr univ G) ∧ (eps G (tr univ G) = 2 / 3 → G = k3C) := by
  native_decide

/-- On four vertices the minimum is `1/2`, attained by `{{v₁,v₄},{v₂,v₃}}`. -/
theorem eps_four :
    (∀ G ∈ sperner 4, NonTrivial G → 1 / 2 ≤ eps G (tr univ G)) ∧
    eps ({{0, 3}, {1, 2}} : HG 4) (tr univ {{0, 3}, {1, 2}}) = 1 / 2 := by
  native_decide

end HD.S32

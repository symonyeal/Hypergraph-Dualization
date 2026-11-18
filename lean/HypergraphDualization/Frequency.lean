/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The smallest most-frequent-vertex frequency (Observation 5.2.3)

`ε(n)` is the least value of `eps C D` over transversal pairs on `n` vertices with both sides
nonempty and free of the empty edge. Observation 5.2.3 claims `ε(3) = 2/3` and `ε(7) = 3/7`.

| Lean | Thesis |
| --- | --- |
| `eps_three` | `ε(3) = 2/3`, attained only by `K₃` (exhaustive) |
| `eps_seven` (in `EpsSeven`) | `ε(7) = 3/7`; the lower bound is general and the Fano plane attains it |
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

end HD.S32

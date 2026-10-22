/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The three split rules on small read-once pairs (evaluation)

Modified FK-A's subproblem count `δ` under the degree-sum rule (`splitVar`), the leftmost rule
(`leftRule`) and the guarded rule (`guardRule`) on GK `f₂` and `ro12`. GK `f₂` is an ordered
read-once formula, so `leftmost_delta` bounds its leftmost count by `2n + 2`; `ro12` interleaves
its two copies, and on it the leftmost order is worse than FK-A's own rule. Larger pairs (TK
`S₂` and up) are measured in `results/split-rules.md`: a leaf here decides duality over all
`2ⁿ` subsets.
The values agree with `fka.memo.fk_a_memo` (`split_rule = degree_sum | leftmost | guarded`).
Every fact here is an *Observation (evaluation)*, proved by `native_decide`.

| pair | `n` | `N` | degree-sum | leftmost | guarded |
| --- | --- | --- | --- | --- | --- |
| GK `f₂` | 8 | 12 | 8 | 8 | 8 |
| `ro12` | 12 | 21 | 43 | 91 | 91 |
-/
import HypergraphDualization.BranchingProgram

namespace HD

open Fm

/-- GK `f₂ = ((x₀ ∨ x₁) ∧ (x₂ ∨ x₃)) ∨ ((x₄ ∨ x₅) ∧ (x₆ ∨ x₇))`, leaves in order. -/
def gk2 : Fm 8 :=
  or (and (or (var 0) (var 1)) (or (var 2) (var 3))) (and (or (var 4) (var 5)) (or (var 6) (var 7)))

theorem gk2_ordered : gk2.Ordered := by
  simp [gk2, Ordered, vars]

/-- **Observation (evaluation).** `δ` of modified FK-A on GK `f₂`: 8 under every rule. -/
theorem gk2_rules :
    (fkADagR splitVar 9 true (dnf gk2) (dnf (dual gk2))).card = 8 ∧
      (fkADagR leftRule 9 true (dnf gk2) (dnf (dual gk2))).card = 8 ∧
      (fkADagR guardRule 9 true (dnf gk2) (dnf (dual gk2))).card = 8 := by
  native_decide

/-- **Observation (evaluation).** On `ro12`, whose labels interleave the two copies, the leftmost
and guarded rules give `δ = 91`, against 43 under the degree-sum rule: a static order is only as
good as its labelling. -/
theorem ro12_rules :
    (fkADagR leftRule 13 true ro12 ro12d).card = 91 ∧
      (fkADagR guardRule 13 true ro12 ro12d).card = 91 := by
  native_decide

#print axioms gk2_ordered
#print axioms gk2_rules
#print axioms ro12_rules

end HD

/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Counterexamples to statements as printed in 2024

Each corrected statement elsewhere in the library is paired here with a concrete instance on
which the printed form fails. Vertices are 0-indexed.

| Lean | Printed statement that fails |
| --- | --- |
| `lemma_3_3_1_needs_sperner` | Lemma 3.3.1 without the Sperner hypothesis: `Aut(Tr H) = Aut(H)` |
| `cor_3_3_4_not_iso` | Cor. 3.3.4: `Aut(H) ≅ Aut(min H)` |
| `claim_3_1_6_counterexample` | Claim 3.1.6: invariant vertex sets are *precisely* the orbits |
| `printed_recurrence_fails` | §4.2.3 as printed: `|Γᵢ₊₁| = 2|Γᵢ|` at the first (join) level |
| `gem_chordal_four`, `gem_chordal_five`, `gem_not_distance_hereditary` | §4.4.2: chordal graphs are distance-hereditary |
-/
import HypergraphDualization.Families
import HypergraphDualization.Recursion

namespace HD.Fix

open HD HD.Data Finset

/-- `H = {{v₁}, {v₁, v₂}}` on three vertices: not Sperner, `min(H) = {{v₁}}`. -/
def nonSperner : HG 3 := {{0}, {0, 1}}

/-- **Lemma 3.3.1 needs `H` Sperner.** `(v₂ v₃)` is an automorphism of `Tr(H) = {{v₁}}` but
not of `H`. -/
theorem lemma_3_3_1_needs_sperner :
    tr univ nonSperner = {{0}} ∧ Equiv.swap 1 2 ∈ aut (tr univ nonSperner) ∧
    Equiv.swap 1 2 ∉ aut nonSperner := by native_decide

/-- **Cor. 3.3.4 fails.** `|Aut(H)| = 1` while `|Aut(min H)| = 2`, so the groups are not
isomorphic. What holds is `Aut(H) ≤ Aut(min H)` (`aut_le_aut_minimal`). -/
theorem cor_3_3_4_not_iso :
    minimal nonSperner = {{0}} ∧ autOrder nonSperner = 1 ∧ autOrder (minimal nonSperner) = 2 :=
  by native_decide

/-- **Claim 3.1.6 fails.** For `St₂ = {{v₁}, {v₂, v₃}}` the whole vertex set is invariant under
`Aut(St₂)`, yet it is not an orbit: `v₁` is fixed by every automorphism. -/
theorem claim_3_1_6_counterexample :
    (∀ σ ∈ aut S32.st2, σ 0 = 0) ∧ Equiv.swap 1 2 ∈ aut S32.st2 := by native_decide

/-- **§4.2.3 as printed fails.** At the first level the tree is a join, so
`|Γ₁| = |Γ₀|² = 1`, not `2|Γ₀| = 2`; at the second (union) level `|Γ₂| = 2|Γ₁| = 2`, not
`|Γ₁|² = 1`. -/
theorem printed_recurrence_fails :
    (alt 0).card = 1 ∧ (alt 1).card = 1 ∧ (alt 2).card = 2 := by decide

/-- The gem: the path `0-1-2-3` with a vertex `4` adjacent to all four. -/
def gemAdj (a b : Fin 5) : Bool :=
  let E : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 3), (4, 0), (4, 1), (4, 2), (4, 3)]
  E.contains (a, b) || E.contains (b, a)

/-- The entries of `l` are pairwise distinct. -/
def distinct (l : List (Fin 5)) : Bool := l.all fun x => l.count x == 1

/-- **§4.4.2, "chordal graphs are distance-hereditary", is false**, by the gem. It is chordal:
every cycle on four or five vertices has a chord. -/
theorem gem_chordal_four : ∀ a b c d : Fin 5, distinct [a, b, c, d] = true →
    (gemAdj a b && gemAdj b c && gemAdj c d && gemAdj d a) = true →
    (gemAdj a c || gemAdj b d) = true := by decide

theorem gem_chordal_five : ∀ a b c d e : Fin 5, distinct [a, b, c, d, e] = true →
    (gemAdj a b && gemAdj b c && gemAdj c d && gemAdj d e && gemAdj e a) = true →
    (gemAdj a c || gemAdj a d || gemAdj b d || gemAdj b e || gemAdj c e) = true := by decide

/-- The gem is not distance-hereditary: `v₀` and `v₃` are at distance 2 (through `4`), but in
the connected induced path `0-1-2-3` (delete `4`) no path of length at most 2 joins them, so
their distance there is 3. -/
theorem gem_not_distance_hereditary :
    (gemAdj 0 4 && gemAdj 4 3 && !gemAdj 0 3) = true ∧
    (gemAdj 0 1 && gemAdj 1 2 && gemAdj 2 3) = true ∧
    ∀ w : Fin 5, w ≠ 4 → (gemAdj 0 w && gemAdj w 3) = false := by decide

end HD.Fix

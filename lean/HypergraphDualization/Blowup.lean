/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Why FK-A's subproblems multiply (research track C)

On a dual pair `(G, Tr G)` FK-A is a decision tree of the monotone function `f` whose DNF is
`G`: deletion `G − x` is `f|x=0`, contraction `G / x` is `f|x=1`. This module proves the three
facts that account for the size of its recursion tree `τ` and of its subproblem set `δ`.

1. *Normal form.* Under any split rule every subproblem is `(H, Tr H)` or `(Tr H, H)` for a minor
   `H` of `G` (`fkADag_minor`); the two orientations have the same children (`fkA_comm`). Hence
   `δ ≤ 2 · #minors` (`card_fkADag_le_minors`).
2. *Repetition.* `δ ≤ τ` under any rule (`card_fkADag_le`).

Finally an explicit read-once pair on 12 points has `δ = 43 > 2N = 42` (`ro12_delta`), which
refutes Conjecture 4.5 of `docs/research-2026-10.md` (`δ ≤ 2N` on read-once pairs).

| Lean | Statement |
| --- | --- |
| `Minor`, `fkADag_minor` | subproblems are minors of `G` or their transversals |
| `fkA_comm` | `τ(C, D) = τ(D, C)` on dual pairs |
| `card_fkADag_le` | `δ ≤ τ` |
| `ro12_readOnce`, `ro12_delta` | the read-once counterexample to `δ ≤ 2N` (evaluation) |
-/
import HypergraphDualization.Dag
import HypergraphDualization.Primitive

namespace HD

open Finset

variable {n : ℕ}

/-! ### One step of the recursion -/

theorem splitVar_comm (C D : HG n) : splitVar C D = splitVar D C := by
  simp only [splitVar, Nat.add_comm (degree C _)]

theorem fkA_pos (fuel : ℕ) (b : Bool) (C D : HG n) : 1 ≤ (fkA fuel b C D).2 := by
  cases fuel with
  | zero => simp [fkAR]
  | succ f =>
    simp only [fkA, fkAR]
    split_ifs <;> try simp
    split <;> try simp
    split_ifs <;> dsimp only <;> omega

/-- **The two orientations of a dual pair have the same tree size**: their children coincide. -/
theorem fkA_comm (fuel : ℕ) (b : Bool) {C D : HG n} (h : Dual univ C D) :
    (fkA fuel b C D).2 = (fkA fuel b D C).2 := by
  cases fuel with
  | zero => simp [fkAR]
  | succ f =>
    have hm : Dual univ (minimal C) (minimal D) := dual_minimal.2 h
    have h1 := conds_of_dual (minimal_isSperner C) (minimal_isSperner D) hm
    have h2 := conds_of_dual (minimal_isSperner D) (minimal_isSperner C) (dual_comm.1 hm)
    have hl := fun x => (dual_children hm x).1
    have hr := fun x => (dual_children hm x).2
    simp only [fkA, fkAR, h1, h2, Bool.not_true, Bool.false_eq_true, ite_false, splitVar_comm (minimal D),
      Nat.mul_comm (minimal D).card, Bool.or_comm ((minimal D).card == 1)]
    split_ifs <;> try rfl
    split <;> try rfl
    rename_i x _
    simp only [fkAR_correct, decide_eq_true (hl x), decide_eq_true (hr x), ite_true]
    omega

/-! ### Minors -/

/-- `Minor G k H`: `H` arises from `G` by `k` deletions `· − x` and contractions `· / x`, with
Sperner reductions between them. On functions these are the restrictions `f|ρ`, `|ρ| = k`. -/
inductive Minor (G : HG n) : ℕ → HG n → Prop
  | refl : Minor G 0 G
  | del {k : ℕ} {H : HG n} (x : Fin n) : Minor G k H → Minor G (k + 1) (del H x)
  | con {k : ℕ} {H : HG n} (x : Fin n) : Minor G k H → Minor G (k + 1) (con H x)
  | min {k : ℕ} {H : HG n} : Minor G k H → Minor G k (minimal H)

theorem Minor.trans {G H K : HG n} {j k : ℕ} (hK : Minor H j K) (hH : Minor G k H) :
    Minor G (k + j) K := by
  induction hK with
  | refl => exact hH
  | del x _ ih => exact .del x ih
  | con x _ ih => exact .con x ih
  | min _ ih => exact .min ih

/-- `p` is `(H, Tr H)` or `(Tr H, H)` for a Sperner-reduced minor `H` of `G`. -/
def IsMinorPair (G : HG n) (p : HG n × HG n) : Prop :=
  ∃ k H, Minor G k H ∧ (p = (minimal H, tr univ H) ∨ p = (tr univ H, minimal H))

theorem IsMinorPair.lift {G H : HG n} {k : ℕ} {p : HG n × HG n} (hp : IsMinorPair H p)
    (hH : Minor G k H) : IsMinorPair G p := by
  obtain ⟨j, K, hK, h⟩ := hp
  exact ⟨k + j, K, hK.trans hH, h⟩

/-- **Normal form.** Under any rule, every subproblem of FK-A on `(G, Tr G)` or on `(Tr G, G)` is
`(H, Tr H)` or `(Tr H, H)` for a Sperner-reduced minor `H` of `G`: a subfunction `f|ρ` of the
input or its dual. -/
theorem fkADag_minor (r : Rule n) (fuel : ℕ) (b : Bool) (G : HG n) :
    (∀ p ∈ fkADagR r fuel b G (tr univ G), IsMinorPair G p) ∧
      ∀ p ∈ fkADagR r fuel b (tr univ G) G, IsMinorPair G p := by
  -- minors are closed under both children at every vertex, so any rule stays inside them
  have hP : ∀ p ∈ {p | IsMinorPair G p}, ∀ x, r p.1 p.2 = some x →
      (minimal (del p.1 x), minimal (con p.2 x)) ∈ {p | IsMinorPair G p} ∧
        (minimal (del p.2 x), minimal (con p.1 x)) ∈ {p | IsMinorPair G p} := by
    rintro p ⟨k, H, hH, hp⟩ x -
    have hm : Minor G k (minimal H) := .min hH
    obtain ⟨hl, hr⟩ := kids_eq (minimal_isSperner H) x
    rw [tr_minimal] at hl hr
    have L : IsMinorPair G (del (minimal H) x, tr univ (del (minimal H) x)) :=
      ⟨k + 1, _, .del x hm, Or.inl (by rw [minimal_eq_self (del_isSperner (minimal_isSperner H) x)])⟩
    have R : IsMinorPair G (tr univ (minimal (con (minimal H) x)), minimal (con (minimal H) x)) :=
      ⟨k + 1, _, .con x hm, Or.inr (by rw [tr_minimal])⟩
    rcases hp with rfl | rfl
    · exact ⟨hl ▸ L, hr ▸ R⟩
    · exact ⟨hr ▸ R, hl ▸ L⟩
  refine ⟨fkADagR_sub hP fuel b _ _ ⟨0, G, .refl, Or.inl (by rw [minimal_tr])⟩,
    fkADagR_sub hP fuel b _ _ ⟨0, G, .refl, Or.inr (by rw [minimal_tr])⟩⟩

open Classical in
/-- The Sperner-reduced minors of `G`: the distinct subfunctions `f|ρ`. -/
noncomputable def minors (G : HG n) : Finset (HG n) :=
  univ.filter fun H => ∃ k K, Minor G k K ∧ minimal K = H

/-- **`δ ≤ 2 · #minors`.** A memoised FK-A solves at most two subproblems per subfunction. -/
theorem card_fkADag_le_minors (r : Rule n) (fuel : ℕ) (b : Bool) (G : HG n) :
    (fkADagR r fuel b G (tr univ G)).card ≤ 2 * (minors G).card := by
  classical
  have hsub : fkADagR r fuel b G (tr univ G) ⊆
      (minors G).image (fun H => (H, tr univ H)) ∪ (minors G).image (fun H => (tr univ H, H)) := by
    intro p hp
    have hK : ∀ k K, Minor G k K → minimal K ∈ minors G := fun k K hK => by
      simp only [minors, mem_filter, mem_univ, true_and]; exact ⟨k, K, hK, rfl⟩
    obtain ⟨k, K, hk, h | h⟩ := (fkADag_minor r fuel b G).1 p hp
    · exact mem_union_left _ (mem_image.2 ⟨minimal K, hK k K hk, by rw [h, tr_minimal]⟩)
    · exact mem_union_right _ (mem_image.2 ⟨minimal K, hK k K hk, by rw [h, tr_minimal]⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ (minors G).card + (minors G).card := add_le_add card_image_le card_image_le
    _ = _ := by ring

/-! ### Repeated work -/

/-- `δ ≤ τ` under any rule: the subproblems are among the tree's nodes. -/
theorem card_fkADag_le (r : Rule n) (fuel : ℕ) (b : Bool) (C D : HG n) :
    (fkADagR r fuel b C D).card ≤ (fkAR r fuel b C D).2 := by
  induction fuel generalizing C D with
  | zero => simp [fkAR, fkADagR]
  | succ f ih =>
    simp only [fkAR, fkADagR]
    split_ifs <;> try simp
    rcases hs : r (minimal C) (minimal D) with _ | x
    · simp
    simp only
    have hL := ih (del (minimal C) x) (con (minimal D) x)
    have hR := ih (del (minimal D) x) (con (minimal C) x)
    split_ifs
    · have := card_insert_le (minimal C, minimal D) (fkADagR r f b (del (minimal C) x)
        (con (minimal D) x) ∪ fkADagR r f b (del (minimal D) x) (con (minimal C) x))
      have := card_union_le (fkADagR r f b (del (minimal C) x) (con (minimal D) x))
        (fkADagR r f b (del (minimal D) x) (con (minimal C) x))
      dsimp only; omega
    · have := card_insert_le (minimal C, minimal D) (fkADagR r f b (del (minimal C) x)
        (con (minimal D) x))
      dsimp only; omega

/-! ### A read-once pair with `δ > 2N`

`ro12` is the DNF of `g(0,6,4,8,2,9) ∨ g(1,7,5,11,10,3)` with
`g(a,b,c,d,e,f) = (a ∨ b) ∧ (c ∨ (d ∧ (e ∨ f)))`: two disjoint copies of a six-variable formula,
labelled so that the lowest-index tie-break alternates between them. Found by
`experiments/readonce_dag`; the facts below are evaluated (`native_decide`). -/

/-- The DNF, 12 edges. -/
def ro12 : HG 12 :=
  {{0, 2, 8}, {0, 4}, {0, 8, 9}, {1, 3, 11}, {1, 5}, {1, 10, 11}, {2, 6, 8}, {3, 7, 11}, {4, 6},
    {5, 7}, {6, 8, 9}, {7, 10, 11}}

/-- The dual's DNF, 9 edges. -/
def ro12d : HG 12 :=
  {{0, 1, 6, 7}, {0, 3, 5, 6, 10}, {0, 5, 6, 11}, {1, 2, 4, 7, 9}, {1, 4, 7, 8},
    {2, 3, 4, 5, 9, 10}, {2, 4, 5, 9, 11}, {3, 4, 5, 8, 10}, {4, 5, 8, 11}}

/-- The cotree of `ro12`'s primal graph: OR gates are unions, AND gates joins. -/
theorem ro12_cograph : IsCograph (primalAdj ro12) univ := by
  have s : ∀ v, IsCograph (primalAdj ro12) {v} := .single
  have u : ∀ A B, IsCograph (primalAdj ro12) A → IsCograph (primalAdj ro12) B →
      Disjoint A B → (∀ a ∈ A, ∀ b ∈ B, ¬ primalAdj ro12 a b) → IsCograph (primalAdj ro12) (A ∪ B) :=
    fun A B hA hB h hn => .union A B h hA hB hn
  have j : ∀ A B, IsCograph (primalAdj ro12) A → IsCograph (primalAdj ro12) B →
      Disjoint A B → (∀ a ∈ A, ∀ b ∈ B, primalAdj ro12 a b) → IsCograph (primalAdj ro12) (A ∪ B) :=
    fun A B hA hB h hj => .join A B h hA hB hj
  -- g(a,b,c,d,e,f) = (a ∨ b) ∧ (c ∨ (d ∧ (e ∨ f)))
  have g : ∀ a b c d e f : Fin 12,
      Disjoint ({a} ∪ {b} : Finset (Fin 12)) ({c} ∪ ({d} ∪ ({e} ∪ {f}))) →
      Disjoint ({a} : Finset (Fin 12)) {b} → Disjoint ({c} : Finset (Fin 12)) ({d} ∪ ({e} ∪ {f})) →
      Disjoint ({d} : Finset (Fin 12)) ({e} ∪ {f}) → Disjoint ({e} : Finset (Fin 12)) {f} →
      (∀ x ∈ ({a} ∪ {b} : Finset (Fin 12)), ∀ y ∈ ({c} ∪ ({d} ∪ ({e} ∪ {f})) : Finset (Fin 12)),
        primalAdj ro12 x y) →
      (¬ primalAdj ro12 a b) → (∀ y ∈ ({d} ∪ ({e} ∪ {f}) : Finset (Fin 12)), ¬ primalAdj ro12 c y) →
      (∀ y ∈ ({e} ∪ {f} : Finset (Fin 12)), primalAdj ro12 d y) → (¬ primalAdj ro12 e f) →
      IsCograph (primalAdj ro12) (({a} ∪ {b}) ∪ ({c} ∪ ({d} ∪ ({e} ∪ {f})))) :=
    fun a b c d e f h1 h2 h3 h4 h5 k1 k2 k3 k4 k5 =>
      j _ _ (u _ _ (s a) (s b) h2 (by simpa using k2))
        (u _ _ (s c) (j _ _ (s d) (u _ _ (s e) (s f) h5 (by simpa using k5)) h4
          (by simpa using k4)) h3 (by simpa using k3)) h1 k1
  have hg1 := g 0 6 4 8 2 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold primalAdj; decide) (by unfold primalAdj; decide) (by unfold primalAdj; decide)
    (by unfold primalAdj; decide) (by unfold primalAdj; decide)
  have hg2 := g 1 7 5 11 10 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold primalAdj; decide) (by unfold primalAdj; decide) (by unfold primalAdj; decide)
    (by unfold primalAdj; decide) (by unfold primalAdj; decide)
  have := u _ _ hg1 hg2 (by decide) (by unfold primalAdj; decide)
  convert this using 1
  decide

/-- `ro12` is read-once and `(ro12, ro12d)` is a dual pair with `N = 21`. -/
theorem ro12_readOnce :
    ReadOnce ro12 ∧ tr univ ro12 = ro12d ∧ ro12.card + ro12d.card = 21 := by
  refine ⟨⟨by decide, ?_, ro12_cograph⟩, by native_decide, by decide⟩
  unfold Conformal primalAdj
  native_decide

/-- **Conjecture 4.5 fails.** Modified FK-A on the read-once pair `(ro12, Tr ro12)` has
`τ = 59` and `δ = 43 > 2N = 42` (evaluation). -/
theorem ro12_delta :
    (runFKA true ro12 ro12d).2 = 59 ∧ (fkADag 13 true ro12 ro12d).card = 43 := by
  native_decide

end HD

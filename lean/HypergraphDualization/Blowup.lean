/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Why FK-A's subproblems multiply (research track C)

On a dual pair `(G, Tr G)` FK-A is a decision tree of the monotone function `f` whose DNF is
`G`: deletion `G − x` is `f|x=0`, contraction `G / x` is `f|x=1`. This module proves the three
facts that account for the size of its recursion tree `τ` and of its subproblem set `δ`.

1. *Normal form.* Every subproblem is `(H, Tr H)` or `(Tr H, H)` for a minor `H` of `G`
   (`fkADag_minor`); the two orientations have the same children (`fkA_comm`). Hence
   `δ ≤ 2 · #minors` (`card_fkADag_le_minors`).
2. *Resilience.* A dual node is never pruned, so if every minor of `G` by fewer than `d`
   deletions and contractions keeps two edges and two minimal transversals, then
   `τ ≥ 2^(d+1) − 1` (`tau_ge_of_resilient`).
3. *Overlap.* The repeated work `τ − δ` is superadditive over a split, with the overlap of the
   children's subproblem sets as surplus (`excess_split`).

Finally an explicit read-once pair on 12 points has `δ = 43 > 2N = 42` (`ro12_delta`), which
refutes Conjecture 4.5 of `docs/research-2026-10.md` (`δ ≤ 2N` on read-once pairs).

| Lean | Statement |
| --- | --- |
| `Minor`, `fkADag_minor` | subproblems are minors of `G` or their transversals |
| `fkA_comm` | `τ(C, D) = τ(D, C)` on dual pairs |
| `tau_ge_of_resilient` | `τ ≥ 2^(d+1) − 1` for `d`-resilient `G` |
| `card_fkADag_le`, `excess_split` | `δ ≤ τ`; `τ − δ ≥ (τ_L − δ_L) + (τ_R − δ_R) + |Δ_L ∩ Δ_R|` |
| `ro12_readOnce`, `ro12_delta` | the read-once counterexample to `δ ≤ 2N` (evaluation) |
-/
import HypergraphDualization.Dag
import HypergraphDualization.Primitive

namespace HD

open Finset

variable {n : ℕ}

/-! ### One step of the recursion -/

theorem minimal_tr (H : HG n) : minimal (tr univ H) = tr univ H :=
  minimal_eq_self (tr_isSperner _ _)

theorem splitVar_comm (C D : HG n) : splitVar C D = splitVar D C := by
  simp only [splitVar, Nat.add_comm (degree C _)]

theorem fkA_pos (fuel : ℕ) (b : Bool) (C D : HG n) : 1 ≤ (fkA fuel b C D).2 := by
  cases fuel with
  | zero => simp [fkA]
  | succ f =>
    simp only [fkA]
    split_ifs <;> try simp
    split <;> try simp
    split_ifs <;> dsimp only <;> omega

/-- Every subproblem of `(C, D)` is the root or a subproblem of a child. -/
theorem mem_fkADag_succ {f : ℕ} {b : Bool} {C D : HG n} {p : HG n × HG n}
    (hp : p ∈ fkADag (f + 1) b C D) : p = (minimal C, minimal D) ∨ ∃ x,
      p ∈ fkADag f b (del (minimal C) x) (con (minimal D) x) ∨
        p ∈ fkADag f b (del (minimal D) x) (con (minimal C) x) := by
  simp only [fkADag] at hp
  split_ifs at hp
  · exact Or.inl (mem_singleton.1 hp)
  · exact Or.inl (mem_singleton.1 hp)
  · split at hp
    · exact Or.inl (mem_singleton.1 hp)
    · rename_i x _
      split_ifs at hp
      · rcases mem_insert.1 hp with h | h
        · exact Or.inl h
        · rcases mem_union.1 h with h | h
          · exact Or.inr ⟨x, Or.inl h⟩
          · exact Or.inr ⟨x, Or.inr h⟩
      · rcases mem_insert.1 hp with h | h
        · exact Or.inl h
        · exact Or.inr ⟨x, Or.inl h⟩

/-- One split at a dual Sperner node with both sides of size at least 2, either variant. -/
theorem fkA_split' {fuel : ℕ} {b : Bool} {C D : HG n} (sC : IsSperner C) (sD : IsSperner D)
    (h : Dual univ C D) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) {x : Fin n}
    (hx : splitVar C D = some x) :
    (fkA (fuel + 1) b C D).2 =
        1 + (fkA fuel b (del C x) (con D x)).2 + (fkA fuel b (del D x) (con C x)).2 ∧
      fkADag (fuel + 1) b C D =
        insert (C, D) (fkADag fuel b (del C x) (con D x) ∪ fkADag fuel b (del D x) (con C x)) := by
  have hl : (fkA fuel b (del C x) (con D x)).1 = true := by
    rw [fkA_correct]; exact decide_eq_true (dual_children h x).1
  have hsize : ¬ (C.card * D.card ≤ 1) := by nlinarith
  constructor <;>
  simp [fkA, fkADag, minimal_eq_self sC, minimal_eq_self sD, conds_of_dual sC sD h, hx, hl, hsize,
    show C.card ≠ 1 by omega, show D.card ≠ 1 by omega]

/-- **The two orientations of a dual pair have the same tree size**: their children coincide. -/
theorem fkA_comm (fuel : ℕ) (b : Bool) {C D : HG n} (h : Dual univ C D) :
    (fkA fuel b C D).2 = (fkA fuel b D C).2 := by
  cases fuel with
  | zero => simp [fkA]
  | succ f =>
    have hm : Dual univ (minimal C) (minimal D) := dual_minimal.2 h
    have h1 := conds_of_dual (minimal_isSperner C) (minimal_isSperner D) hm
    have h2 := conds_of_dual (minimal_isSperner D) (minimal_isSperner C) (dual_comm.1 hm)
    have hl := fun x => (dual_children hm x).1
    have hr := fun x => (dual_children hm x).2
    simp only [fkA, h1, h2, Bool.not_true, Bool.false_eq_true, ite_false, splitVar_comm (minimal D),
      Nat.mul_comm (minimal D).card, Bool.or_comm ((minimal D).card == 1)]
    split_ifs <;> try rfl
    split <;> try rfl
    rename_i x _
    simp only [fkA_correct, decide_eq_true (hl x), decide_eq_true (hr x), ite_true]
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

/-- The left child of `(G, Tr G)` at `x` is `(G' − x, Tr(G' − x))`, `G' = min G`. -/
theorem fkADag_left (f : ℕ) (b : Bool) (G : HG n) (x : Fin n) :
    fkADag f b (del (minimal G) x) (con (minimal (tr univ G)) x) =
      fkADag f b (del (minimal G) x) (tr univ (del (minimal G) x)) := by
  rw [← fkADag_minimal f b _ (con _ x), minimal_tr, ← tr_minimal univ G,
    minimal_con_tr (within_univ _) (mem_univ x), ← fkADag_minimal f b (del (minimal G) x) (tr univ _),
    minimal_tr]

/-- The right child of `(G, Tr G)` at `x` is `(Tr(G'/x), G'/x)`, `G' = min G`. -/
theorem del_tr_eq (G : HG n) (x : Fin n) :
    del (minimal (tr univ G)) x = tr univ (con (minimal G) x) := by
  rw [minimal_tr, ← tr_minimal univ G, tr_con_eq]

theorem fkA_left (f : ℕ) (b : Bool) (G : HG n) (x : Fin n) :
    fkA f b (del (minimal G) x) (con (minimal (tr univ G)) x) =
      fkA f b (del (minimal G) x) (tr univ (del (minimal G) x)) := by
  rw [← fkA_minimal f b _ (con _ x), minimal_tr, ← tr_minimal univ G,
    minimal_con_tr (within_univ _) (mem_univ x), ← fkA_minimal f b (del (minimal G) x) (tr univ _),
    minimal_tr]

/-- **Normal form.** Every subproblem of FK-A on `(G, Tr G)` or on `(Tr G, G)` is `(H, Tr H)` or
`(Tr H, H)` for a Sperner-reduced minor `H` of `G`: a subfunction `f|ρ` of the input or its
dual. -/
theorem fkADag_minor (fuel : ℕ) (b : Bool) (G : HG n) :
    (∀ p ∈ fkADag fuel b G (tr univ G), IsMinorPair G p) ∧
      ∀ p ∈ fkADag fuel b (tr univ G) G, IsMinorPair G p := by
  induction fuel generalizing G with
  | zero =>
    refine ⟨fun p hp => ⟨0, G, .refl, Or.inl ?_⟩, fun p hp => ⟨0, G, .refl, Or.inr ?_⟩⟩ <;>
      simpa [fkADag, minimal_tr] using hp
  | succ f ih =>
    have hm : Minor G 0 (minimal G) := .min .refl
    -- the two children, whichever orientation the parent has
    have hL : ∀ x, ∀ p ∈ fkADag f b (del (minimal G) x) (con (minimal (tr univ G)) x),
        IsMinorPair G p := fun x p hp => by
      rw [fkADag_left] at hp
      exact ((ih _).1 p hp).lift (.del x hm)
    have hR : ∀ x, ∀ p ∈ fkADag f b (del (minimal (tr univ G)) x) (con (minimal G) x),
        IsMinorPair G p := fun x p hp => by
      rw [del_tr_eq] at hp
      exact ((ih _).2 p hp).lift (.con x hm)
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩ <;> rcases mem_fkADag_succ hp with rfl | ⟨x, h | h⟩
    · exact ⟨0, G, .refl, Or.inl (by rw [minimal_tr])⟩
    · exact hL x p h
    · exact hR x p h
    · exact ⟨0, G, .refl, Or.inr (by rw [minimal_tr])⟩
    · exact hR x p h
    · exact hL x p h

open Classical in
/-- The Sperner-reduced minors of `G`: the distinct subfunctions `f|ρ`. -/
noncomputable def minors (G : HG n) : Finset (HG n) :=
  univ.filter fun H => ∃ k K, Minor G k K ∧ minimal K = H

/-- **`δ ≤ 2 · #minors`.** A memoised FK-A solves at most two subproblems per subfunction. -/
theorem card_fkADag_le_minors (fuel : ℕ) (b : Bool) (G : HG n) :
    (fkADag fuel b G (tr univ G)).card ≤ 2 * (minors G).card := by
  classical
  have hsub : fkADag fuel b G (tr univ G) ⊆
      (minors G).image (fun H => (H, tr univ H)) ∪ (minors G).image (fun H => (tr univ H, H)) := by
    intro p hp
    have hK : ∀ k K, Minor G k K → minimal K ∈ minors G := fun k K hK => by
      simp only [minors, mem_filter, mem_univ, true_and]; exact ⟨k, K, hK, rfl⟩
    obtain ⟨k, K, hk, h | h⟩ := (fkADag_minor fuel b G).1 p hp
    · exact mem_union_left _ (mem_image.2 ⟨minimal K, hK k K hk, by rw [h, tr_minimal]⟩)
    · exact mem_union_right _ (mem_image.2 ⟨minimal K, hK k K hk, by rw [h, tr_minimal]⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ (minors G).card + (minors G).card := add_le_add card_image_le card_image_le
    _ = _ := by ring

/-! ### Resilience: the tree is a full binary tree to depth `d` -/

/-- A Sperner family with two edges has a vertex of positive degree. -/
theorem exists_degree_pos {C : HG n} (sC : IsSperner C) (hC : 2 ≤ C.card) :
    ∃ y, 0 < degree C y := by
  obtain ⟨e, he, f, hf, hef⟩ := one_lt_card.1 hC
  have : e.Nonempty := by
    rw [nonempty_iff_ne_empty]; rintro rfl
    exact hef (sC _ he f hf (empty_subset f))
  obtain ⟨y, hy⟩ := this
  exact ⟨y, card_pos.2 ⟨e, mem_filter.2 ⟨he, hy⟩⟩⟩

/-- **Resilience bound.** Suppose every minor of `G` by `k < d` deletions and contractions keeps
at least two edges and two minimal transversals. Then FK-A's tree on `(G, Tr G)` (either variant,
fuel at least `d`) has at least `2^(d+1) − 1` nodes: a dual node is never pruned, so the tree is
full to depth `d`. -/
theorem tau_ge_of_resilient (b : Bool) (d : ℕ) : ∀ (G : HG n) (fuel : ℕ), d ≤ fuel →
    (∀ k < d, ∀ H, Minor G k H → 2 ≤ (minimal H).card ∧ 2 ≤ (tr univ H).card) →
    2 ^ (d + 1) - 1 ≤ (fkA fuel b G (tr univ G)).2 := by
  induction d with
  | zero => intro G fuel _ _; simpa using fkA_pos fuel b G (tr univ G)
  | succ d ih =>
    intro G fuel hfuel hres
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    set G' := minimal G
    have sG := minimal_isSperner G
    obtain ⟨hC, hD⟩ := hres 0 (by omega) G' (.min .refl)
    rw [minimal_eq_self sG] at hC
    obtain ⟨y, hy⟩ := exists_degree_pos sG hC
    obtain ⟨x, hx, -⟩ := splitVar_spec G' (tr univ G') (y₀ := y) (by unfold key; exact Nat.add_pos_left hy _)
    have hroot : fkA (f + 1) b G (tr univ G) = fkA (f + 1) b G' (tr univ G') := by
      rw [← fkA_minimal, minimal_tr, tr_minimal]
    have hstep := (fkA_split' (fuel := f) (b := b) sG (tr_isSperner _ _) (dual_tr G')
      hC hD hx).1
    -- the children are `(G' − x, Tr)` and, up to orientation, `(G'/x, Tr)`
    have hL : (fkA f b (del G' x) (con (tr univ G') x)).2 =
        (fkA f b (del G' x) (tr univ (del G' x))).2 := by
      have := fkA_left f b G x; rw [minimal_tr, ← tr_minimal univ G] at this; rw [this]
    have hR : (fkA f b (del (tr univ G') x) (con G' x)).2 =
        (fkA f b (con G' x) (tr univ (con G' x))).2 := by
      rw [← tr_con_eq]; exact (fkA_comm f b (dual_tr _)).symm
    have lift : ∀ (op : HG n → Fin n → HG n), (∀ H, Minor G 0 H → Minor G 1 (op H x)) →
        ∀ k < d, ∀ H, Minor (op G' x) k H → 2 ≤ (minimal H).card ∧ 2 ≤ (tr univ H).card :=
      fun op hop k hk H hH => hres (1 + k) (by omega) H (hH.trans (hop G' (.min .refl)))
    have iL := ih (del G' x) f (by omega) (lift del fun H h => .del x h)
    have iR := ih (con G' x) f (by omega) (lift con fun H h => .con x h)
    rw [hroot, hstep, hL, hR]
    have : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    omega

/-! ### Overlap: repeated work is superadditive -/

/-- `δ ≤ τ`: the subproblems are among the tree's nodes. -/
theorem card_fkADag_le (fuel : ℕ) (b : Bool) (C D : HG n) :
    (fkADag fuel b C D).card ≤ (fkA fuel b C D).2 := by
  induction fuel generalizing C D with
  | zero => simp [fkA, fkADag]
  | succ f ih =>
    simp only [fkA, fkADag]
    split_ifs <;> try simp
    rcases hs : splitVar (minimal C) (minimal D) with _ | x
    · simp
    simp only
    have hL := ih (del (minimal C) x) (con (minimal D) x)
    have hR := ih (del (minimal D) x) (con (minimal C) x)
    split_ifs
    · have := card_insert_le (minimal C, minimal D) (fkADag f b (del (minimal C) x)
        (con (minimal D) x) ∪ fkADag f b (del (minimal D) x) (con (minimal C) x))
      have := card_union_le (fkADag f b (del (minimal C) x) (con (minimal D) x))
        (fkADag f b (del (minimal D) x) (con (minimal C) x))
      dsimp only; omega
    · have := card_insert_le (minimal C, minimal D) (fkADag f b (del (minimal C) x)
        (con (minimal D) x))
      dsimp only; omega

/-- **Overlap excess.** At a split of a dual Sperner node, the repeated work `τ − δ` is at least
that of the two children plus the number of subproblems they share:
`τ − δ ≥ (τ_L − δ_L) + (τ_R − δ_R) + |Δ_L ∩ Δ_R|`. A memo removes exactly this surplus, and
iterating it along a chain of overlapping splits doubles `τ` while `δ` grows additively. -/
theorem excess_split {fuel : ℕ} {b : Bool} {C D : HG n} (sC : IsSperner C) (sD : IsSperner D)
    (h : Dual univ C D) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) {x : Fin n}
    (hx : splitVar C D = some x) :
    let L := (del C x, con D x)
    let R := (del D x, con C x)
    let ΔL := fkADag fuel b L.1 L.2
    let ΔR := fkADag fuel b R.1 R.2
    ((fkA fuel b L.1 L.2).2 - ΔL.card) + ((fkA fuel b R.1 R.2).2 - ΔR.card) + (ΔL ∩ ΔR).card ≤
      (fkA (fuel + 1) b C D).2 - (fkADag (fuel + 1) b C D).card := by
  intro L R ΔL ΔR
  obtain ⟨hτ, hδ⟩ := fkA_split' (fuel := fuel) (b := b) sC sD h hC hD hx
  have h1 := card_insert_le (C, D) (ΔL ∪ ΔR)
  have h2 := card_union_add_card_inter ΔL ΔR
  have h3 := card_fkADag_le fuel b L.1 L.2
  have h4 := card_fkADag_le fuel b R.1 R.2
  simp only [L, R, ΔL, ΔR] at *
  rw [hτ, hδ]
  omega

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

#print axioms fkADag_minor
#print axioms card_fkADag_le_minors
#print axioms fkA_comm
#print axioms tau_ge_of_resilient
#print axioms excess_split
#print axioms ro12_cograph
#print axioms ro12_readOnce
#print axioms ro12_delta

end HD

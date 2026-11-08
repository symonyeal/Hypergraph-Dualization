/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-B, executable and verified

`fkBR r mf fuel C D` is the verdict of Algorithm FK-B on hypergraphs over `Fin n`. With `C` the
clauses of a CNF and `D` the monomials of a DNF, the pair is dual exactly when the two
formulas agree on every assignment. At a node whose split variable is `x`:

* if `x` is `mf`-rare in `D`: the `x = 0` pair `(con C x, del D x)` is solved, then one
  subproblem per clause `c` of `C₀` (the clauses holding `x`, minus `x`), with the variables
  of `c` set false in `(del C x, D₀)`;
* else if `x` is `mf`-rare in `C`: the mirror image (`x = 1`, then one subproblem per
  monomial of `D₀`, set true);
* else the two-way split of FK-A.

What is mechanised: the verdict is `Dual` for every split rule `r`, every `mu`-frequency test
`mf` and every fuel (`fkBR_correct`). Not modelled: the arithmetic of `mu(n) = log n / log log n`
(`mf` is a parameter), the node count, and the polynomial checks of Check_Conditions and
Easy_case: as in `fkAR`, a leaf (the two small-side easy case, a split rule returning `none`,
fuel zero) is decided by `Dual` itself, and the conditions are those of `conds`, which
`conds_of_dual` proves necessary.

| Lean | Thesis / Python |
| --- | --- |
| `cx` | `phi_x_0`: the edges holding `x`, with `x` removed |
| `setF` | `A_c_x`: the variables of `c` set false |
| `dual_muD` | FK-B's per-clause branch (lines 8-12 of the listing) is exact |
| `fkBR_correct`, `fkB_correct` | `fkb.algorithm.fk_b` decides `C = Tr(D)` |
-/
import HypergraphDualization.Algorithm

namespace HD

open Finset

variable {n : ℕ}

/-- The edges of `H` holding `x`, with `x` removed. -/
def cx (H : HG n) (x : Fin n) : HG n := (H.filter (x ∈ ·)).image (·.erase x)

/-- `(C, D)` with the variables of `c` set false: `C` loses them, `D` loses the edges meeting them. -/
def setF (C D : HG n) (c : Finset (Fin n)) : HG n × HG n :=
  (C.image (· \ c), D.filter (Disjoint · c))

/-- The CNF with clauses `C` is true at `S`: every clause meets `S`. -/
def cnfv (C : HG n) (S : Finset (Fin n)) : Prop := ∀ c ∈ C, (c ∩ S).Nonempty

theorem cnfv_iff {C : HG n} {S : Finset (Fin n)} : cnfv C S ↔ ¬ upHit C (univ \ S) := by
  constructor
  · rintro h ⟨e, he, hs⟩
    obtain ⟨y, hy⟩ := h e he
    rw [mem_inter] at hy
    exact (mem_sdiff.1 (hs hy.1)).2 hy.2
  · intro h e he
    by_contra hne
    exact h ⟨e, he, fun y hy => mem_sdiff.2 ⟨mem_univ _, fun hS => hne ⟨y, mem_inter.2 ⟨hy, hS⟩⟩⟩⟩

/-- `C` and `D` are dual iff the CNF `C` and the DNF `D` are the same function. -/
theorem dual_iff_fun {C D : HG n} : Dual univ C D ↔ ∀ S, cnfv C S ↔ upHit D S := by
  rw [dual_iff]
  constructor
  · intro h S
    have := h (univ \ S) (subset_univ _)
    rw [Finset.sdiff_sdiff_eq_self (subset_univ S)] at this
    rw [cnfv_iff]
    tauto
  · intro h A hA
    have := h (univ \ A)
    rw [cnfv_iff, Finset.sdiff_sdiff_eq_self hA] at this
    tauto

/-- The FK-A decomposition at any vertex, for arbitrary hypergraphs. -/
theorem dual_split_univ (C D : HG n) (x : Fin n) :
    Dual univ C D ↔ Dual univ (del C x) (con D x) ∧ Dual univ (del D x) (con C x) := by
  have hsplit := dual_split (G := C) (H := D) (mem_univ x)
  have hL := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
    (G := del C x) (H := con D x) (x := x)
    (fun e he => (mem_filter.1 he).2) (fun e he => by
      obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
  have hR := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
    (G := del D x) (H := con C x) (x := x)
    (fun e he => (mem_filter.1 he).2) (fun e he => by
      obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
  rw [hL, hR] at hsplit
  exact hsplit

theorem meets_of_conds {C D : HG n} (h : conds C D = true) : ∀ c ∈ C, ∀ d ∈ D, (c ∩ d).Nonempty := by
  simp only [conds, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- The `x = 0` pair is dual iff the two functions agree off `x`. -/
theorem dual_zero_iff {C D : HG n} {x : Fin n} :
    Dual univ (con C x) (del D x) ↔ ∀ S, x ∉ S → (cnfv C S ↔ upHit D S) := by
  rw [dual_iff_fun]
  have hc : ∀ S, cnfv (con C x) S ↔ cnfv C (S.erase x) := by
    intro S
    simp only [cnfv, con, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine forall₂_congr fun c _ => ?_
    constructor <;> rintro ⟨y, hy⟩ <;> refine ⟨y, ?_⟩ <;> simp only [mem_inter, mem_erase] at hy ⊢ <;> tauto
  constructor
  · intro h S hS
    have := h S
    rwa [hc, upHit_del, erase_eq_of_notMem hS] at this
  · intro h S
    rw [hc, upHit_del]
    exact h _ (notMem_erase x S)

theorem cnfv_del {C : HG n} {x : Fin n} {T : Finset (Fin n)} :
    cnfv (del C x) T ↔ cnfv C (insert x T) := by
  simp only [cnfv, del, mem_filter, and_imp]
  constructor
  · intro h c hc
    by_cases hx : x ∈ c
    · exact ⟨x, mem_inter.2 ⟨hx, mem_insert_self x T⟩⟩
    · obtain ⟨y, hy⟩ := h c hc hx
      exact ⟨y, mem_inter.2 ⟨(mem_inter.1 hy).1, mem_insert_of_mem (mem_inter.1 hy).2⟩⟩
  · intro h c hc hx
    obtain ⟨y, hy⟩ := h c hc
    rw [mem_inter] at hy
    refine ⟨y, mem_inter.2 ⟨hy.1, ?_⟩⟩
    rcases mem_insert.1 hy.2 with rfl | h'
    · exact absurd hy.1 hx
    · exact h'

theorem upHit_con_split {D : HG n} {x : Fin n} {T : Finset (Fin n)} :
    upHit (con D x) T ↔ upHit (cx D x) T ∨ upHit (del D x) T := by
  simp only [upHit, con, cx, del, mem_image, mem_filter]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, hT⟩
    by_cases hx : x ∈ m
    · exact Or.inl ⟨_, ⟨m, ⟨hm, hx⟩, rfl⟩, hT⟩
    · refine Or.inr ⟨m, ⟨hm, hx⟩, ?_⟩
      rwa [erase_eq_of_notMem hx] at hT
  · rintro (⟨_, ⟨m, ⟨hm, hx⟩, rfl⟩, hT⟩ | ⟨m, ⟨hm, hx⟩, hT⟩)
    · exact ⟨_, ⟨m, hm, rfl⟩, hT⟩
    · exact ⟨m.erase x, ⟨m, hm, rfl⟩, (erase_subset x m).trans hT⟩

theorem cnfv_image_sdiff {A : HG n} {c S : Finset (Fin n)} :
    cnfv (A.image (· \ c)) S ↔ cnfv A (S \ c) := by
  simp only [cnfv, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun e _ => ?_
  constructor <;> rintro ⟨y, hy⟩ <;> refine ⟨y, ?_⟩ <;>
    simp only [mem_inter, mem_sdiff] at hy ⊢ <;> tauto

theorem upHit_filter_disjoint {B : HG n} {c S : Finset (Fin n)} :
    upHit (B.filter (Disjoint · c)) S ↔ upHit B (S \ c) := by
  simp only [upHit, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hd⟩, hS⟩
    refine ⟨e, he, fun y hy => mem_sdiff.2 ⟨hS hy, fun hc => ?_⟩⟩
    exact (disjoint_left.1 hd) hy hc
  · rintro ⟨e, he, hS⟩
    refine ⟨e, ⟨he, disjoint_left.2 fun y hy hc => (mem_sdiff.1 (hS hy)).2 hc⟩,
      fun y hy => (mem_sdiff.1 (hS hy)).1⟩

/-- **FK-B's per-clause branch is exact.** If every clause meets every monomial and the
`x = 0` pair is dual, then `(C, D)` is dual iff, for each clause `c` of `C₀`, the pair
`(del C x, D₀)` with the variables of `c` set false is dual. -/
theorem dual_muD {C D : HG n} (x : Fin n) (hM : ∀ c ∈ C, ∀ d ∈ D, (c ∩ d).Nonempty)
    (h0 : Dual univ (con C x) (del D x)) :
    Dual univ C D ↔ ∀ c ∈ cx C x,
      Dual univ (setF (del C x) (cx D x) c).1 (setF (del C x) (cx D x) c).2 := by
  rw [dual_zero_iff] at h0
  simp only [setF, dual_iff_fun, cnfv_image_sdiff, upHit_filter_disjoint]
  constructor
  · intro h c hc S
    obtain ⟨t, htf, rfl⟩ := mem_image.1 hc
    obtain ⟨ht, hxt⟩ := mem_filter.1 htf
    set T := S \ t.erase x with hT
    have hdis : Disjoint T (t.erase x) := sdiff_disjoint
    rw [cnfv_del]
    have h1 := h (insert x T)
    rw [← upHit_con, upHit_con_split] at h1
    have hno : ¬ upHit (del D x) T := by
      rintro ⟨m, hm, hmT⟩
      obtain ⟨hmD, hxm⟩ := mem_filter.1 hm
      obtain ⟨y, hy⟩ := hM t ht m hmD
      rw [mem_inter] at hy
      have hyx : y ≠ x := fun e => hxm (e ▸ hy.2)
      exact (disjoint_left.1 hdis) (hmT hy.2) (mem_erase.2 ⟨hyx, hy.1⟩)
    rw [h1]
    tauto
  · intro h S
    constructor
    · intro hS
      by_cases hx : x ∈ S
      · set T := S.erase x with hT
        have hS' : S = insert x T := (insert_erase hx).symm
        by_cases hCT : cnfv C T
        · obtain ⟨m, hm, hmT⟩ := ((h0 T (notMem_erase x S)).1 hCT)
          exact ⟨m, hm, hmT.trans (erase_subset x S)⟩
        · obtain ⟨t, ht, hte⟩ : ∃ t ∈ C, ¬ (t ∩ T).Nonempty := by
            simp only [cnfv, not_forall] at hCT
            obtain ⟨t, ht, h'⟩ := hCT
            exact ⟨t, ht, h'⟩
          have hxt : x ∈ t := by
            obtain ⟨y, hy⟩ := hS t ht
            rw [mem_inter] at hy
            by_contra hxt
            rw [hS'] at hy
            rcases mem_insert.1 hy.2 with rfl | hyT
            · exact hxt hy.1
            · exact hte ⟨y, mem_inter.2 ⟨hy.1, hyT⟩⟩
          have hc : t.erase x ∈ cx C x :=
            mem_image.2 ⟨t, mem_filter.2 ⟨ht, hxt⟩, rfl⟩
          have hdis : Disjoint T (t.erase x) := by
            rw [disjoint_left]
            intro y hyT hyc
            exact hte ⟨y, mem_inter.2 ⟨(mem_erase.1 hyc).2, hyT⟩⟩
          have h2 := h _ hc T
          rw [sdiff_eq_self_of_disjoint hdis, cnfv_del, ← hS'] at h2
          obtain ⟨m', hm', hm'T⟩ := h2.1 hS
          obtain ⟨m, hmf, rfl⟩ := mem_image.1 hm'
          obtain ⟨hmD, hxm⟩ := mem_filter.1 hmf
          refine ⟨m, hmD, fun y hy => ?_⟩
          by_cases hyx : y = x
          · rw [hS']; exact hyx ▸ mem_insert_self x T
          · rw [hS']; exact mem_insert_of_mem (hm'T (mem_erase.2 ⟨hyx, hy⟩))
      · exact (h0 S hx).1 hS
    · rintro ⟨d, hd, hdS⟩ c hc
      obtain ⟨y, hy⟩ := hM c hc d hd
      rw [mem_inter] at hy
      exact ⟨y, mem_inter.2 ⟨hy.1, hdS hy.2⟩⟩

/-- FK-B: the verdict with split rule `r` and `mu`-frequency test `mf`. -/
def fkBR (r : Rule n) (mf : Fin n → HG n → HG n → Bool) : ℕ → HG n → HG n → Bool
  | 0, C₀, D₀ => decide (Dual univ (minimal C₀) (minimal D₀))
  | fuel + 1, C₀, D₀ =>
    let C := minimal C₀
    let D := minimal D₀
    if !conds C D then false
    else if C.card ≤ 2 || D.card ≤ 2 then decide (Dual univ C D)
    else
      match r C D with
      | none => decide (Dual univ C D)
      | some x =>
        if mf x D C then
          fkBR r mf fuel (con C x) (del D x) &&
            decide (∀ c ∈ cx C x, fkBR r mf fuel (setF (del C x) (cx D x) c).1
              (setF (del C x) (cx D x) c).2 = true)
        else if mf x C D then
          fkBR r mf fuel (del C x) (con D x) &&
            decide (∀ m ∈ cx D x, fkBR r mf fuel (setF (del D x) (cx C x) m).2
              (setF (del D x) (cx C x) m).1 = true)
        else
          fkBR r mf fuel (con C x) (del D x) && fkBR r mf fuel (del C x) (con D x)

/-- **FK-B is correct** under every split rule, every `mu`-frequency test and every fuel. -/
theorem fkBR_correct (r : Rule n) (mf : Fin n → HG n → HG n → Bool) (fuel : ℕ) (C D : HG n) :
    fkBR r mf fuel C D = decide (Dual univ C D) := by
  induction fuel generalizing C D with
  | zero => simp [fkBR, dual_minimal]
  | succ fuel ih =>
    have hred : Dual univ (minimal C) (minimal D) ↔ Dual univ C D := dual_minimal
    simp only [fkBR]
    set C' := minimal C
    set D' := minimal D
    by_cases hc : conds C' D' = true
    · have hM := meets_of_conds hc
      simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hleaf
      · simp [hred]
      · split
        · simp [hred]
        · rename_i x _
          have hsp := dual_split_univ C' D' x
          -- the `x = 0` pair, written both ways
          have h0 : Dual univ (con C' x) (del D' x) ↔ Dual univ (del D' x) (con C' x) := dual_comm
          have h1 : Dual univ (del C' x) (con D' x) ↔ Dual univ (con D' x) (del C' x) := dual_comm
          have hD : Dual univ C D ↔ Dual univ (del C' x) (con D' x) ∧
              Dual univ (con C' x) (del D' x) := by
            rw [← hred, hsp, h0, and_comm]
          by_cases hmD : mf x D' C' = true
          · simp only [hmD, ↓reduceIte]
            rw [Bool.eq_iff_iff]
            simp only [ih, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨h0', hch⟩
              exact hred.1 ((dual_muD x hM h0').2 hch)
            · intro h
              have hd := hred.2 h
              have h0' : Dual univ (con C' x) (del D' x) :=
                dual_comm.1 ((dual_split_univ C' D' x).1 hd).2
              exact ⟨h0', (dual_muD x hM h0').1 hd⟩
          · have hmD' : mf x D' C' = false := by simpa using hmD
            simp only [hmD', Bool.false_eq_true, ↓reduceIte]
            by_cases hmC : mf x C' D' = true
            · simp only [hmC, ↓reduceIte]
              rw [Bool.eq_iff_iff]
              simp only [ih, Bool.and_eq_true, decide_eq_true_eq]
              have hM' : ∀ d ∈ D', ∀ c ∈ C', (d ∩ c).Nonempty := fun d hd c hc => by
                rw [inter_comm]; exact hM c hc d hd
              have hd' : Dual univ C D ↔ Dual univ D' C' := hred.symm.trans dual_comm
              constructor
              · rintro ⟨hL, hch⟩
                refine hred.1 (dual_comm.1 ((dual_muD x hM' (dual_comm.1 hL)).2 fun m hm => ?_))
                exact dual_comm.1 (hch m hm)
              · intro h
                have hd := dual_comm.1 (hred.2 h)
                have hL : Dual univ (del C' x) (con D' x) := ((dual_split_univ C' D' x).1 (hred.2 h)).1
                refine ⟨hL, fun m hm => dual_comm.1 ((dual_muD x hM' (dual_comm.1 hL)).1 hd m hm)⟩
            · have hmC' : mf x C' D' = false := by simpa using hmC
              simp only [hmC', Bool.false_eq_true, ↓reduceIte]
              rw [Bool.eq_iff_iff]
              simp only [ih, Bool.and_eq_true, decide_eq_true_eq]
              rw [← hred, dual_split_univ C' D' x, and_comm, dual_comm (G := del D' x)]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, ↓reduceIte]
      have : ¬ Dual univ C D := fun h => by
        have hct : conds C' D' = true :=
          conds_of_dual (minimal_isSperner C) (minimal_isSperner D) (hred.2 h)
        exact absurd (hc.symm.trans hct) (by decide)
      simp [this]

/-- FK-B with the degree-sum split rule. -/
abbrev fkB (mf : Fin n → HG n → HG n → Bool) : ℕ → HG n → HG n → Bool := fkBR splitVar mf

/-- **FK-B is correct.** For any `mu`-frequency test and any fuel, the verdict is exactly `Dual`. -/
theorem fkB_correct (mf : Fin n → HG n → HG n → Bool) (fuel : ℕ) (C D : HG n) :
    fkB mf fuel C D = decide (Dual univ C D) :=
  fkBR_correct splitVar mf fuel C D

end HD

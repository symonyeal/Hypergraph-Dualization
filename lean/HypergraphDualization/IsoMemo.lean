/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A with a memo keyed by isomorphism class (research prompt, Track S, S1)

`fkAI r κ` is FK-A under the rule `r` with a memo of verdicts keyed by `κ (C, D)`, threaded
through the recursion. The key function only has to send each pair to an isomorphic pair
(`Canon κ`): it need not be a canonical labelling, and it need not be compatible with the rule.
A hit returns the verdict stored under an equal key, which belongs to an isomorphic pair, so it
is the right verdict because duality is invariant under relabelling (`dual_pimg`). The memo's
length is the number of nodes the algorithm expands: `d_iso` of `experiments/iso_memo.py` and
`readonce_dag --iso` when `κ` is the shape key.

| Lean | Research |
| --- | --- |
| `Canon` | `κ p` is a relabelling of `p` |
| `Sound` | every stored verdict is `Dual` of some pair with that key |
| `fkAI` | iso-memoised FK-A |
| `fkAI_correct` | S1: the verdict is `Dual` and the memo stays sound, for every rule and fuel |
| `fkAI_eq_fkAR` | from an empty memo, the verdict of FK-A without a memo |
-/
import HypergraphDualization.Algorithm

namespace HD

open Finset

variable {n : ℕ}

/-- Memo entries: a key pair and the verdict stored under it. -/
abbrev Memo (n : ℕ) := List ((HG n × HG n) × Bool)

/-- `κ` sends every pair to a relabelling of it. -/
def Canon (κ : HG n × HG n → HG n × HG n) : Prop :=
  ∀ p, ∃ σ : Equiv.Perm (Fin n), κ p = (pimg σ p.1, pimg σ p.2)

/-- Every stored verdict is the verdict of some pair with that key. -/
def Sound (κ : HG n × HG n → HG n × HG n) (m : Memo n) : Prop :=
  ∀ e ∈ m, ∃ p, κ p = e.1 ∧ e.2 = decide (Dual univ p.1 p.2)

/-- FK-A under `r` with the memo keyed by `κ`: the verdict and the memo after the call. -/
def fkAI (r : Rule n) (κ : HG n × HG n → HG n × HG n) :
    ℕ → Bool → HG n → HG n → Memo n → Bool × Memo n
  | 0, _, C₀, D₀, m => (decide (Dual univ (minimal C₀) (minimal D₀)), m)
  | fuel + 1, modified, C₀, D₀, m =>
    let C := minimal C₀
    let D := minimal D₀
    match m.find? (fun e => decide (e.1 = κ (C, D))) with
    | some e => (e.2, m)
    | none =>
      let res : Bool × Memo n :=
        if !conds C D then (false, m)
        else if C.card * D.card ≤ 1 || (modified && (C.card == 1 || D.card == 1)) then
          (decide (Dual univ C D), m)
        else
          match r C D with
          | none => (decide (Dual univ C D), m)
          | some x =>
            let l := fkAI r κ fuel modified (del C x) (con D x) m
            if l.1 then fkAI r κ fuel modified (del D x) (con C x) l.2 else (false, l.2)
      (res.1, (κ (C, D), res.1) :: res.2)

/-- Equal keys belong to pairs with the same verdict. -/
theorem dual_of_key_eq {κ : HG n × HG n → HG n × HG n} (hκ : Canon κ) {p q : HG n × HG n}
    (h : κ p = κ q) : Dual univ p.1 p.2 ↔ Dual univ q.1 q.2 := by
  obtain ⟨σ, hσ⟩ := hκ p
  obtain ⟨τ, hτ⟩ := hκ q
  rw [← dual_pimg σ, ← dual_pimg τ q.1 q.2]
  rw [hσ, hτ] at h
  simp only [Prod.mk.injEq] at h
  rw [h.1, h.2]

theorem sound_cons {κ : HG n × HG n → HG n × HG n} {m : Memo n} (C D : HG n) (hm : Sound κ m) :
    Sound κ ((κ (C, D), decide (Dual univ C D)) :: m) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨(C, D), rfl, rfl⟩
  · exact hm e he

/-- **S1.** Iso-memoised FK-A is correct under every rule, for every fuel and every sound memo,
and leaves the memo sound. -/
theorem fkAI_correct (r : Rule n) {κ : HG n × HG n → HG n × HG n} (hκ : Canon κ)
    (fuel : ℕ) (modified : Bool) :
    ∀ (C D : HG n) (m : Memo n), Sound κ m →
      (fkAI r κ fuel modified C D m).1 = decide (Dual univ C D) ∧
        Sound κ (fkAI r κ fuel modified C D m).2 := by
  induction fuel with
  | zero => intro C D m hm; exact ⟨by simp [fkAI, dual_minimal], hm⟩
  | succ fuel ih =>
    intro C D m hm
    have hred : Dual univ (minimal C) (minimal D) ↔ Dual univ C D := dual_minimal
    simp only [fkAI]
    split
    · rename_i e he
      obtain ⟨p, hp, hv⟩ := hm e (List.mem_of_find?_eq_some he)
      have hk : e.1 = κ (minimal C, minimal D) := by simpa using List.find?_some he
      refine ⟨?_, hm⟩
      rw [hv, decide_eq_decide, dual_of_key_eq hκ (hp.trans hk)]
      exact hred
    · -- The body: the verdict is `Dual` of the reduced pair, and its memo is sound.
      have body : ∀ res : Bool × Memo n, res.1 = decide (Dual univ (minimal C) (minimal D)) →
          Sound κ res.2 →
          ((res.1, (κ (minimal C, minimal D), res.1) :: res.2) : Bool × Memo n).1 =
              decide (Dual univ C D) ∧
            Sound κ ((res.1, (κ (minimal C, minimal D), res.1) :: res.2) : Bool × Memo n).2 := by
        intro res h1 h2
        refine ⟨by rw [h1, decide_eq_decide]; exact hred, ?_⟩
        rw [h1]
        exact sound_cons _ _ h2
      apply body
      · split_ifs with hc hleaf
        · have : ¬ Dual univ (minimal C) (minimal D) := fun h => by
            simp [conds_of_dual (minimal_isSperner C) (minimal_isSperner D) h] at hc
          simp [this]
        · rfl
        · split
          · rfl
          · rename_i x _
            set C' := minimal C
            set D' := minimal D
            have hsplit := dual_split (G := C') (H := D') (mem_univ x)
            have hL := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
              (G := del C' x) (H := con D' x) (x := x)
              (fun e he => (mem_filter.1 he).2) (fun e he => by
                obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
            have hR := dual_erase_of_notMem (U := (univ : Finset (Fin n)))
              (G := del D' x) (H := con C' x) (x := x)
              (fun e he => (mem_filter.1 he).2) (fun e he => by
                obtain ⟨f, -, rfl⟩ := mem_image.1 he; exact notMem_erase x f)
            rw [hL, hR] at hsplit
            obtain ⟨hl1, hl2⟩ := ih (del C' x) (con D' x) m hm
            split_ifs with hl
            · obtain ⟨hr1, -⟩ := ih (del D' x) (con C' x) _ hl2
              rw [hl1] at hl
              simp only [decide_eq_true_eq] at hl
              rw [hr1, decide_eq_decide]
              exact ⟨fun h => hsplit.2 ⟨hl, h⟩, fun h => (hsplit.1 h).2⟩
            · rw [hl1] at hl
              simp only [decide_eq_true_eq] at hl
              simp [hsplit, hl]
      · split_ifs with hc hleaf
        · exact hm
        · exact hm
        · split
          · exact hm
          · rename_i x _
            obtain ⟨hl1, hl2⟩ := ih (del (minimal C) x) (con (minimal D) x) m hm
            split_ifs with hl
            · exact (ih _ _ _ hl2).2
            · exact hl2

/-- From an empty memo the verdict is that of FK-A without a memo, under any two rules. -/
theorem fkAI_eq_fkAR (r s : Rule n) {κ : HG n × HG n → HG n × HG n} (hκ : Canon κ)
    (fuel : ℕ) (modified : Bool) (C D : HG n) :
    (fkAI r κ fuel modified C D []).1 = (fkAR s fuel modified C D).1 := by
  rw [(fkAI_correct r hκ fuel modified C D [] (by simp [Sound])).1, fkAR_correct]

end HD

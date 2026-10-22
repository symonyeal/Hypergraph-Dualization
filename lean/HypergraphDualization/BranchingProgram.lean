/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A's memo DAG is a free binary decision diagram (research track C, §4)

Let `f` be the monotone function with DNF `G`. A *branching program named by its functions* is a
set `𝒮` of Sperner hypergraphs (functions) with a label `ℓ H` for each non-leaf `H ∈ 𝒮`: the
node `H` tests `x = ℓ H ∈ support H`, its 0-successor is `H − x = H|x=0` and its 1-successor is
`min(H / x) = H|x=1`, both in `𝒮`. Leaves are the constants `∅` (false) and `{∅}` (true). Its
size is `|𝒮|`. Such an `𝒮` is a read-once branching program (an FBDD) computing every `H ∈ 𝒮`:
`run` follows the labels and returns `H(S)` (`run_correct`), and the variables tested on any path
are distinct (`path_nodup`).

1. *The memo DAG is an FBDD.* For a valid symmetric split rule (`splitVar`, `leftRule`,
   `guardRule`), the two sides of the subproblems of the unmodified FK-A on `(G, Tr G)`, together
   with the constants, form an FBDD named by its functions for `f`, labelled by the rule, of
   size at most `2δ + 2` (`memo_fbdd`). Under the modified variant the same family is a branching
   program with single-term and single-clause leaves (`memo_bp`). Hence every valid symmetric
   rule has `δ ≥ (s − 2)/2` on unmodified FK-A, `s` the least size of an FBDD named by its
   functions.
2. *Conversely* an FBDD `𝒮` named by its functions gives a valid symmetric rule (`fbddRule`)
   with `δ ≤ 2|𝒮|`, either variant (`rule_of_fbdd`). So on unmodified FK-A the least `δ` over
   valid symmetric rules and the least FBDD named by its functions agree within a factor 2.

A family closed under a valid rule is an FBDD labelled by it (`isFBDD_of_closed`). Under the
leftmost rule on a read-once formula with leaves in order, the states of `ReadOnceFormula` and
the constants form an FBDD with at most `|vars f| + 2` nodes (`Fm.leftmost_fbdd`).

| Lean | Statement |
| --- | --- |
| `IsBP`, `IsFBDD`, `run`, `path` | branching programs named by their functions |
| `run_correct`, `path_nodup` | an FBDD computes each node's function, reading each variable at most once |
| `Valid`, `valid_splitVar`, `valid_leftRule` | a rule returns a vertex of the support, whenever there is one |
| `memo_good` | every memo node is a leaf of the variant or has both children in the memo |
| `memo_bp`, `memo_fbdd` | the memo DAG is a BP (term/clause leaves) / an FBDD of size `≤ 2δ + 2` |
| `fbddRule`, `rule_of_fbdd` | an FBDD of size `s` gives a valid symmetric rule with `δ ≤ 2s` |
| `isFBDD_of_closed`, `Fm.leftmost_fbdd` | a rule-closed family is an FBDD; the leftmost FBDD has `≤ \|vars f\| + 2` nodes |
-/
import HypergraphDualization.ReadOnceFormula

namespace HD

open Finset

variable {n : ℕ}

/-! ### Branching programs named by their functions -/

/-- `𝒮` with labels `ℓ` is a branching program with leaves in `L`: each `H ∈ 𝒮` is Sperner and is
a leaf, or tests `x = ℓ H ∈ support H` with successors `H − x` and `min(H / x)` in `𝒮`. -/
def IsBP (L : HG n → Prop) (𝒮 : Finset (HG n)) (ℓ : HG n → Option (Fin n)) : Prop :=
  ∀ H ∈ 𝒮, IsSperner H ∧ (L H ∨ ∃ x, ℓ H = some x ∧ x ∈ support H ∧ del H x ∈ 𝒮 ∧
    minimal (con H x) ∈ 𝒮)

/-- A free BDD: the leaves are the constants `∅` and `{∅}`, the functions with empty support. -/
def IsFBDD (𝒮 : Finset (HG n)) (ℓ : HG n → Option (Fin n)) : Prop :=
  IsBP (fun H => support H = ∅) 𝒮 ℓ

/-- Evaluate at `S` by following the labels from `H`; a leaf `K` answers `∅ ∈ K`. -/
def run (ℓ : HG n → Option (Fin n)) : ℕ → HG n → Finset (Fin n) → Bool
  | 0, H, _ => decide (∅ ∈ H)
  | k + 1, H, S =>
    if support H = ∅ then decide (∅ ∈ H) else
      match ℓ H with
      | none => decide (∅ ∈ H)
      | some x => if x ∈ S then run ℓ k (minimal (con H x)) S else run ℓ k (del H x) S

/-- The variables tested on the path of `S` from `H`. -/
def path (ℓ : HG n → Option (Fin n)) : ℕ → HG n → Finset (Fin n) → List (Fin n)
  | 0, _, _ => []
  | k + 1, H, S =>
    if support H = ∅ then [] else
      match ℓ H with
      | none => []
      | some x => x :: if x ∈ S then path ℓ k (minimal (con H x)) S else path ℓ k (del H x) S

theorem support_del_sub (H : HG n) (x : Fin n) : support (del H x) ⊆ (support H).erase x :=
  fun y hy => by
    obtain ⟨e, he, hye⟩ := mem_support.1 hy
    obtain ⟨he, hxe⟩ := mem_filter.1 he
    exact mem_erase.2 ⟨fun h => hxe (h ▸ hye), mem_support.2 ⟨e, he, hye⟩⟩

theorem support_con_sub (H : HG n) (x : Fin n) :
    support (minimal (con H x)) ⊆ (support H).erase x := fun y hy => by
  obtain ⟨e, he, hye⟩ := mem_support.1 hy
  obtain ⟨f, hf, rfl⟩ := mem_image.1 (minimal_subset _ he)
  obtain ⟨hyx, hyf⟩ := mem_erase.1 hye
  exact mem_erase.2 ⟨hyx, mem_support.2 ⟨f, hf, hyf⟩⟩

theorem upHit_of_support_empty {H : HG n} (h : support H = ∅) (S : Finset (Fin n)) :
    upHit H S ↔ ∅ ∈ H := by
  rcases Fm.const_of_support_empty h with rfl | rfl <;> simp [upHit]

/-- **An FBDD computes its functions**: from `H ∈ 𝒮`, with enough steps, `run` returns `H(S)`. -/
theorem run_correct {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} (h : IsFBDD 𝒮 ℓ)
    (S : Finset (Fin n)) : ∀ k, ∀ H ∈ 𝒮, (support H).card < k →
      run ℓ k H S = decide (upHit H S) := by
  intro k
  induction k with
  | zero => intro H _ hk; omega
  | succ k ih =>
    intro H hH hk
    by_cases hs : support H = ∅
    · simp [run, hs, upHit_of_support_empty hs]
    obtain ⟨-, hl | ⟨x, hx, hxs, h0, h1⟩⟩ := h H hH
    · exact absurd hl hs
    have hc : ∀ K, support K ⊆ (support H).erase x → (support K).card < k := fun K hK => by
      have := card_le_card hK; have := card_pos.2 ⟨x, hxs⟩; rw [card_erase_of_mem hxs] at *; omega
    simp only [run, hs, if_false, hx]
    by_cases hxS : x ∈ S
    · rw [if_pos hxS, ih _ h1 (hc _ (support_con_sub H x))]
      simp only [upHit_minimal, upHit_con, insert_eq_of_mem hxS]
    · rw [if_neg hxS, ih _ h0 (hc _ (support_del_sub H x))]
      simp only [upHit_del, erase_eq_of_notMem hxS]

/-- **Read-once.** The variables tested on any path of an FBDD lie in the support and are
distinct. -/
theorem path_nodup {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} (h : IsFBDD 𝒮 ℓ)
    (S : Finset (Fin n)) : ∀ k, ∀ H ∈ 𝒮,
      (∀ y ∈ path ℓ k H S, y ∈ support H) ∧ (path ℓ k H S).Nodup := by
  intro k
  induction k with
  | zero => intro H _; simp [path]
  | succ k ih =>
    intro H hH
    by_cases hs : support H = ∅
    · simp [path, hs]
    obtain ⟨-, hl | ⟨x, hx, hxs, h0, h1⟩⟩ := h H hH
    · exact absurd hl hs
    have step : ∀ K ∈ 𝒮, support K ⊆ (support H).erase x →
        (∀ y ∈ x :: path ℓ k K S, y ∈ support H) ∧ (x :: path ℓ k K S).Nodup := fun K hK hsub => by
      obtain ⟨hin, hnd⟩ := ih K hK
      refine ⟨fun y hy => ?_, List.nodup_cons.2 ⟨fun hxp => ?_, hnd⟩⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hxs
        · exact (mem_erase.1 (hsub (hin y hy))).2
      · exact (mem_erase.1 (hsub (hin x hxp))).1 rfl
    simp only [path, hs, if_false, hx]
    split_ifs
    · exact step _ h1 (support_con_sub H x)
    · exact step _ h0 (support_del_sub H x)

/-! ### Valid rules -/

/-- A rule is valid if it returns a vertex of `support C ∪ support D`, and some vertex whenever
that set is nonempty. -/
def Valid (r : Rule n) : Prop :=
  ∀ C D, (∀ x, r C D = some x → x ∈ support C ∪ support D) ∧
    ((support C ∪ support D).Nonempty → (r C D).isSome)

theorem valid_leftRule : Valid (leftRule (n := n)) := by
  intro C D
  refine ⟨fun x hx => ?_, fun h => by simp [leftRule, h]⟩
  simp only [leftRule] at hx
  split_ifs at hx with h
  cases hx; exact min'_mem _ h

theorem mem_support_of_key {C D : HG n} {x : Fin n} (h : 0 < key C D x) :
    x ∈ support C ∪ support D := by
  unfold key at h
  rcases Nat.eq_zero_or_pos (degree C x) with h0 | h0
  · obtain ⟨e, he, hx⟩ := degree_pos_iff.1 (show 0 < degree D x by omega)
    exact mem_union_right _ (mem_support.2 ⟨e, he, hx⟩)
  · obtain ⟨e, he, hx⟩ := degree_pos_iff.1 h0
    exact mem_union_left _ (mem_support.2 ⟨e, he, hx⟩)

theorem key_pos_of_mem {C D : HG n} {x : Fin n} (h : x ∈ support C ∪ support D) :
    0 < key C D x := by
  unfold key
  rcases mem_union.1 h with h | h <;> obtain ⟨e, he, hx⟩ := mem_support.1 h
  · have := degree_pos_iff.2 ⟨e, he, hx⟩; omega
  · have := degree_pos_iff.2 ⟨e, he, hx⟩; omega

theorem valid_splitVar : Valid (splitVar (n := n)) := by
  intro C D
  refine ⟨fun x hx => ?_, fun ⟨y, hy⟩ => ?_⟩
  · by_cases hall : ∀ y, key C D y = 0
    · have := (splitStep_fold C D (List.finRange n) none).1 rfl fun y _ => hall y
      rw [splitVar_eq, this] at hx; cases hx
    · push Not at hall
      obtain ⟨y, hy⟩ := hall
      obtain ⟨z, hz, hpos, -⟩ := splitVar_spec C D (y₀ := y) (Nat.pos_of_ne_zero hy)
      rw [hx] at hz; cases hz
      exact mem_support_of_key hpos
  · obtain ⟨z, hz, -, -⟩ := splitVar_spec C D (key_pos_of_mem hy)
    rw [hz]; rfl

/-! ### The memo DAG -/

/-- `p` is a dual pair over a Sperner family. -/
def DualNode (p : HG n × HG n) : Prop :=
  ∃ K, IsSperner K ∧ (p = (K, tr univ K) ∨ p = (tr univ K, K))

/-- The leaf test of FK-A's variant `b`. -/
def LeafCond (b : Bool) (p : HG n × HG n) : Prop :=
  p.1.card * p.2.card ≤ 1 ∨ (b = true ∧ (p.1.card = 1 ∨ p.2.card = 1))

/-- A memo node is good in `Δ`: a dual pair that is a leaf, or whose two children are in `Δ`. -/
def Good (r : Rule n) (b : Bool) (Δ : Finset (HG n × HG n)) (p : HG n × HG n) : Prop :=
  DualNode p ∧ (LeafCond b p ∨ ∃ x, r p.1 p.2 = some x ∧
    (minimal (del p.1 x), minimal (con p.2 x)) ∈ Δ ∧ (minimal (del p.2 x), minimal (con p.1 x)) ∈ Δ)

theorem Good.mono {r : Rule n} {b : Bool} {Δ Δ' : Finset (HG n × HG n)} {p : HG n × HG n}
    (h : Good r b Δ p) (hΔ : Δ ⊆ Δ') : Good r b Δ' p :=
  ⟨h.1, h.2.imp id fun ⟨x, hx, h1, h2⟩ => ⟨x, hx, hΔ h1, hΔ h2⟩⟩

theorem card_le_one_of_support_empty {H : HG n} (h : support H = ∅) : H.card ≤ 1 := by
  rcases Fm.const_of_support_empty h with rfl | rfl <;> simp

/-- **Every memo node is good.** With fuel above the support size, every subproblem of FK-A on
`(K, Tr K)` or `(Tr K, K)` under a valid rule is a leaf of the variant, or has both children
among the subproblems. -/
theorem memo_good {r : Rule n} (hv : Valid r) (b : Bool) : ∀ fuel (K : HG n), IsSperner K →
    (support K).card < fuel →
      (∀ p ∈ fkADagR r fuel b K (tr univ K), Good r b (fkADagR r fuel b K (tr univ K)) p) ∧
      (∀ p ∈ fkADagR r fuel b (tr univ K) K, Good r b (fkADagR r fuel b (tr univ K) K) p) := by
  intro fuel
  induction fuel with
  | zero => intro K _ hk; omega
  | succ f ih =>
    intro K sK hk
    have sT := tr_isSperner univ K
    have hsT : support (tr univ K) = support K := (support_eq (within_univ K) sK rfl).symm
    -- the children of a split at `x ∈ support K` satisfy the hypothesis at fuel `f`
    have hcard : ∀ x ∈ support K, ∀ K', support K' ⊆ (support K).erase x →
        (support K').card < f := fun x hx K' hK' => by
      have := card_le_card hK'; have := card_pos.2 ⟨x, hx⟩; rw [card_erase_of_mem hx] at *; omega
    have iL : ∀ x ∈ support K, ∀ p ∈ fkADagR r f b (del K x) (tr univ (del K x)),
        Good r b (fkADagR r f b (del K x) (tr univ (del K x))) p := fun x hx =>
      (ih _ (del_isSperner sK x) (hcard x hx _ (support_del_sub K x))).1
    have iR : ∀ x ∈ support K, ∀ p ∈ fkADagR r f b (tr univ (minimal (con K x))) (minimal (con K x)),
        Good r b (fkADagR r f b (tr univ (minimal (con K x))) (minimal (con K x))) p := fun x hx =>
      (ih _ (minimal_isSperner _) (hcard x hx _ (support_con_sub K x))).2
    -- one step at a root `(C, D)`, `{C, D} = {K, Tr K}`
    have step : ∀ C D, (C = K ∧ D = tr univ K) ∨ (C = tr univ K ∧ D = K) →
        ∀ p ∈ fkADagR r (f + 1) b C D, Good r b (fkADagR r (f + 1) b C D) p := by
      intro C D hCD
      have sC : IsSperner C := by rcases hCD with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
      have sD : IsSperner D := by rcases hCD with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
      have hdual : Dual univ C D := by
        rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact dual_tr _
        · exact dual_comm.1 (dual_tr _)
      have hnode : DualNode (C, D) := ⟨K, sK, by rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
      have hsupp : support C ∪ support D = support K := by
        rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hsT]
      have hconds := conds_of_dual sC sD hdual
      -- the subproblem sets of the two children
      have hΔ : ∀ x, x ∈ support K →
          (∀ p ∈ fkADagR r f b (del C x) (con D x),
            Good r b (fkADagR r f b (del C x) (con D x)) p) ∧
          (∀ p ∈ fkADagR r f b (del D x) (con C x),
            Good r b (fkADagR r f b (del D x) (con C x)) p) := fun x hx => by
        rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [fkADagR_left, fkADagR_right]; exact ⟨iL x hx, iR x hx⟩
        · rw [fkADagR_left, fkADagR_right]; exact ⟨iR x hx, iL x hx⟩
      intro p hp
      by_cases hleaf : C.card * D.card ≤ 1 ∨ (b = true ∧ (C.card = 1 ∨ D.card = 1))
      · have : fkADagR r (f + 1) b C D = {(C, D)} := by
          have hb : (decide (C.card * D.card ≤ 1) || (b && (C.card == 1 || D.card == 1))) = true := by
            rcases hleaf with h | ⟨rfl, h⟩ <;> simp [h]
          simp [fkADagR, minimal_eq_self sC, minimal_eq_self sD, hconds, hb]
        rw [this] at hp ⊢; rw [mem_singleton] at hp; subst hp
        exact ⟨hnode, Or.inl hleaf⟩
      · have hb : (decide (C.card * D.card ≤ 1) || (b && (C.card == 1 || D.card == 1))) = false := by
          push Not at hleaf
          cases b <;> simp_all
        have hne : (support C ∪ support D).Nonempty := by
          by_contra h0
          rw [not_nonempty_iff_eq_empty, union_eq_empty] at h0
          have := card_le_one_of_support_empty h0.1
          have := card_le_one_of_support_empty h0.2
          exact hleaf (Or.inl (by nlinarith))
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((hv C D).2 hne)
        have hxK : x ∈ support K := hsupp ▸ (hv C D).1 x hx
        have hl : (fkAR r f b (del C x) (con D x)).1 = true := by
          rw [fkAR_correct]; exact decide_eq_true (dual_children hdual x).1
        have hD : fkADagR r (f + 1) b C D =
            insert (C, D) (fkADagR r f b (del C x) (con D x) ∪ fkADagR r f b (del D x) (con C x)) := by
          simp only [fkADagR, minimal_eq_self sC, minimal_eq_self sD, hconds, Bool.not_true,
            Bool.false_eq_true, if_false, hb, hx, hl, if_true]
        have sub1 : fkADagR r f b (del C x) (con D x) ⊆ fkADagR r (f + 1) b C D :=
          by rw [hD]; exact subset_union_left.trans (subset_insert _ _)
        have sub2 : fkADagR r f b (del D x) (con C x) ⊆ fkADagR r (f + 1) b C D :=
          by rw [hD]; exact subset_union_right.trans (subset_insert _ _)
        rw [hD] at hp
        rcases mem_insert.1 hp with rfl | hp
        · refine ⟨hnode, Or.inr ⟨x, hx, sub1 (root_mem_fkADagR _ _ _ _ _), ?_⟩⟩
          exact sub2 (root_mem_fkADagR _ _ _ _ _)
        rcases mem_union.1 hp with hp | hp
        · exact ((hΔ x hxK).1 p hp).mono sub1
        · exact ((hΔ x hxK).2 p hp).mono sub2
    exact ⟨step K _ (Or.inl ⟨rfl, rfl⟩), step _ K (Or.inr ⟨rfl, rfl⟩)⟩

/-- The leaves of the memo BP of variant `b`: a constant, a literal (`b = false`), or a single
term or clause (`b = true`). -/
def LeafB (b : Bool) (H : HG n) : Prop :=
  support H = ∅ ∨ (H.card = 1 ∧ (tr univ H).card = 1) ∨ (b = true ∧ (H.card = 1 ∨ (tr univ H).card = 1))

/-- The functions of the memo DAG: both sides of every subproblem, and the constants. -/
def memoSet (Δ : Finset (HG n × HG n)) : Finset (HG n) :=
  Δ.image Prod.fst ∪ Δ.image Prod.snd ∪ {∅, {∅}}

theorem card_memoSet_le (Δ : Finset (HG n × HG n)) : (memoSet Δ).card ≤ 2 * Δ.card + 2 := by
  unfold memoSet
  have h1 := card_union_le (Δ.image Prod.fst ∪ Δ.image Prod.snd) ({∅, {∅}} : Finset (HG n))
  have h2 := card_union_le (Δ.image Prod.fst) (Δ.image Prod.snd)
  have h3 : (Δ.image Prod.fst).card ≤ Δ.card := card_image_le
  have h4 : (Δ.image Prod.snd).card ≤ Δ.card := card_image_le
  have h5 : ({∅, {∅}} : Finset (HG n)).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  omega

theorem tr_eq_empty {H : HG n} (sH : IsSperner H) (h : tr univ H = ∅) : support H = ∅ := by
  have : H = {∅} := by
    rw [← tr_tr_of_sperner (within_univ H) sH, h, tr_empty_hg]
  rw [this]; simp [support]

/-- **The memo DAG is a branching program.** For a valid symmetric rule, a Sperner `G` and fuel
above `|support G|`, the functions of the subproblems of FK-A (variant `b`) on `(G, Tr G)` form a
branching program for `G`, labelled by the rule, with leaves `LeafB b` and at most `2δ + 2`
nodes. -/
theorem memo_bp {r : Rule n} (hv : Valid r) (hs : Symm r) (b : Bool) {G : HG n}
    (sG : IsSperner G) {fuel : ℕ} (hf : (support G).card < fuel) :
    let Δ := fkADagR r fuel b G (tr univ G)
    IsBP (LeafB b) (memoSet Δ) (fun H => r H (tr univ H)) ∧ G ∈ memoSet Δ ∧
      (memoSet Δ).card ≤ 2 * Δ.card + 2 := by
  intro Δ
  have hgood := (memo_good hv b fuel G sG hf).1
  refine ⟨fun H hH => ?_, ?_, card_memoSet_le Δ⟩
  · simp only [memoSet, mem_union, mem_image] at hH
    rcases hH with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | hc
    rotate_left 2
    · -- a constant
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ⟨isSperner_empty, Or.inl (Or.inl (by simp [support]))⟩
      · exact ⟨isSperner_unit, Or.inl (Or.inl (by simp [support]))⟩
    all_goals
      obtain ⟨⟨K, sK, hpK⟩, hcase⟩ := hgood p hp
      have sT := tr_isSperner univ K
      have ttK := tr_tr_of_sperner (within_univ K) sK
      have hsT : support (tr univ K) = support K := (support_eq (within_univ K) sK rfl).symm
    -- `H` is one side of `p`, and the other side is `Tr H`
    · obtain ⟨H', sH, hH', hp2, hsupp⟩ : ∃ H', IsSperner p.1 ∧ H' = tr univ p.1 ∧ p.2 = H' ∧
          support p.2 = support p.1 := by
        rcases hpK with rfl | rfl
        · exact ⟨_, sK, rfl, rfl, hsT⟩
        · exact ⟨_, sT, rfl, ttK.symm, hsT.symm⟩
      refine ⟨sH, ?_⟩
      rcases hcase with hl | ⟨x, hx, h1, h2⟩
      · left
        rw [LeafCond, hp2, hH'] at hl
        rcases hl with hl | hl
        · rcases Nat.eq_zero_or_pos p.1.card with h0 | h0
          · exact Or.inl (by rw [card_eq_zero.1 h0]; simp [support])
          rcases Nat.eq_zero_or_pos (tr univ p.1).card with h0' | h0'
          · exact Or.inl (tr_eq_empty sH (card_eq_zero.1 h0'))
          · exact Or.inr (Or.inl ⟨by nlinarith, by nlinarith⟩)
        · exact Or.inr (Or.inr hl)
      · right
        have hxs : x ∈ support p.1 := by
          have := (hv p.1 p.2).1 x hx; rwa [hsupp, union_self] at this
        refine ⟨x, by show r p.1 (tr univ p.1) = some x; rw [← hH', ← hp2]; exact hx, hxs, ?_, ?_⟩
        · rw [← minimal_eq_self (del_isSperner sH x)]
          exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ h1))
        · exact mem_union_left _ (mem_union_right _ (mem_image_of_mem Prod.snd h2))
    · obtain ⟨sH, hp1, hsupp⟩ : IsSperner p.2 ∧ p.1 = tr univ p.2 ∧ support p.1 = support p.2 := by
        rcases hpK with rfl | rfl
        · exact ⟨sT, ttK.symm, hsT.symm⟩
        · exact ⟨sK, rfl, hsT⟩
      refine ⟨sH, ?_⟩
      rcases hcase with hl | ⟨x, hx, h1, h2⟩
      · left
        rw [LeafCond, hp1] at hl
        rcases hl with hl | hl
        · rcases Nat.eq_zero_or_pos p.2.card with h0 | h0
          · exact Or.inl (by rw [card_eq_zero.1 h0]; simp [support])
          rcases Nat.eq_zero_or_pos (tr univ p.2).card with h0' | h0'
          · exact Or.inl (tr_eq_empty sH (card_eq_zero.1 h0'))
          · exact Or.inr (Or.inl ⟨by nlinarith, by nlinarith⟩)
        · exact Or.inr (Or.inr ⟨hl.1, hl.2.symm⟩)
      · right
        have hxs : x ∈ support p.2 := by
          have := (hv p.1 p.2).1 x hx; rwa [hsupp, union_self] at this
        refine ⟨x, by show r p.2 (tr univ p.2) = some x; rw [← hp1, hs]; exact hx, hxs, ?_, ?_⟩
        · rw [← minimal_eq_self (del_isSperner sH x)]
          exact mem_union_left _ (mem_union_left _ (mem_image_of_mem Prod.fst h2))
        · exact mem_union_left _ (mem_union_right _ (mem_image_of_mem Prod.snd h1))
  · have := root_mem_fkADagR r fuel b G (tr univ G)
    rw [minimal_eq_self sG, minimal_tr] at this
    exact mem_union_left _ (mem_union_left _ (mem_image_of_mem Prod.fst this))

/-- A Sperner family with one edge and one minimal transversal is a literal `{{y}}`. -/
theorem literal_of_card {H : HG n} (hH : H.card = 1) (hT : (tr univ H).card = 1) :
    ∃ y, H = {{y}} := by
  obtain ⟨c, rfl⟩ := card_eq_one.1 hH
  rw [tr_singleton (subset_univ c), card_image_of_injective _ singleton_injective] at hT
  obtain ⟨y, rfl⟩ := card_eq_one.1 hT
  exact ⟨y, rfl⟩

/-- **The memo DAG is an FBDD.** Under the unmodified variant, the functions of the subproblems
of FK-A on `(G, Tr G)` form an FBDD for `G` of size at most `2δ + 2`, for every valid symmetric
rule. Hence `δ ≥ (FBDD(f) − 2)/2` under every such rule. -/
theorem memo_fbdd {r : Rule n} (hv : Valid r) (hs : Symm r) {G : HG n} (sG : IsSperner G)
    {fuel : ℕ} (hf : (support G).card < fuel) :
    let Δ := fkADagR r fuel false G (tr univ G)
    IsFBDD (memoSet Δ) (fun H => r H (tr univ H)) ∧ G ∈ memoSet Δ ∧
      (memoSet Δ).card ≤ 2 * Δ.card + 2 := by
  intro Δ
  obtain ⟨hbp, hG, hc⟩ := memo_bp hv hs false sG hf
  refine ⟨fun H hH => ?_, hG, hc⟩
  obtain ⟨sH, hl | hsplit⟩ := hbp H hH
  · rcases hl with hl | ⟨h1, h2⟩ | ⟨h, -⟩
    · exact ⟨sH, Or.inl hl⟩
    · -- a literal `{{y}}` tests `y` and goes to the constants
      obtain ⟨y, rfl⟩ := literal_of_card h1 h2
      refine ⟨sH, Or.inr ⟨y, ?_, by simp [support], ?_, ?_⟩⟩
      · have hne : (support ({{y}} : HG n) ∪ support (tr univ {{y}})).Nonempty :=
          ⟨y, mem_union_left _ (by simp [support])⟩
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 ((hv _ _).2 hne)
        have := (hv _ _).1 z hz
        rw [tr_singleton (subset_univ _)] at this
        simp [support] at this
        show r {{y}} (tr univ {{y}}) = some y
        rw [hz, this]
      · rw [show del ({{y}} : HG n) y = ∅ by simp [del]]
        exact mem_union_right _ (by simp)
      · rw [show minimal (con ({{y}} : HG n) y) = {∅} by
          simp [con, minimal_eq_self isSperner_unit]]
        exact mem_union_right _ (by simp)
    · cases h
  · exact ⟨sH, Or.inr hsplit⟩

/-! ### Conversely: a rule from an FBDD -/

/-- The label of `H` if `H` is a test node of `(𝒮, ℓ)`. -/
def lab (𝒮 : Finset (HG n)) (ℓ : HG n → Option (Fin n)) (H : HG n) : Option (Fin n) :=
  if H ∈ 𝒮 ∧ (support H).Nonempty then ℓ H else none

/-- The rule of an FBDD: the label of whichever side is a test node, the lesser label if both
are, and the degree-sum vertex if neither is. -/
def fbddRule (𝒮 : Finset (HG n)) (ℓ : HG n → Option (Fin n)) : Rule n := fun C D =>
  match lab 𝒮 ℓ C, lab 𝒮 ℓ D with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => splitVar C D

theorem lab_spec {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} (h : IsFBDD 𝒮 ℓ) {H : HG n}
    {x : Fin n} (hx : lab 𝒮 ℓ H = some x) :
    x ∈ support H ∧ del H x ∈ 𝒮 ∧ minimal (con H x) ∈ 𝒮 := by
  unfold lab at hx
  split_ifs at hx with hH
  obtain ⟨-, hl | ⟨y, hy, hys, h0, h1⟩⟩ := h H hH.1
  · exact absurd hl (nonempty_iff_ne_empty.1 hH.2)
  · rw [hy] at hx; cases hx; exact ⟨hys, h0, h1⟩

theorem support_of_lab_none {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} (h : IsFBDD 𝒮 ℓ)
    {H : HG n} (hH : H ∈ 𝒮) (hx : lab 𝒮 ℓ H = none) : support H = ∅ := by
  by_contra h0
  obtain ⟨-, hl | ⟨y, hy, -⟩⟩ := h H hH
  · exact h0 hl
  · simp [lab, hH, nonempty_iff_ne_empty.2 h0, hy] at hx

theorem fbddRule_symm (𝒮 : Finset (HG n)) (ℓ : HG n → Option (Fin n)) : Symm (fbddRule 𝒮 ℓ) := by
  intro C D
  unfold fbddRule
  cases lab 𝒮 ℓ C <;> cases lab 𝒮 ℓ D <;> simp [min_comm, splitVar_comm]

/-- The vertex chosen is the label of a test node, or the degree-sum vertex if there is none. -/
theorem fbddRule_spec {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} {C D : HG n} {x : Fin n}
    (hx : fbddRule 𝒮 ℓ C D = some x) : lab 𝒮 ℓ C = some x ∨ lab 𝒮 ℓ D = some x ∨
      (lab 𝒮 ℓ C = none ∧ lab 𝒮 ℓ D = none ∧ splitVar C D = some x) := by
  unfold fbddRule at hx
  rcases h1 : lab 𝒮 ℓ C with _ | a <;> rcases h2 : lab 𝒮 ℓ D with _ | b <;>
    simp only [h1, h2, Option.some.injEq] at hx
  · exact Or.inr (Or.inr ⟨rfl, rfl, hx⟩)
  · exact Or.inr (Or.inl (hx ▸ rfl))
  · exact Or.inl (hx ▸ rfl)
  · rcases min_choice a b with h | h <;> rw [h] at hx <;> subst hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem valid_fbddRule {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} (h : IsFBDD 𝒮 ℓ) :
    Valid (fbddRule 𝒮 ℓ) := by
  intro C D
  refine ⟨fun x hx => ?_, fun hne => ?_⟩
  · rcases fbddRule_spec hx with h1 | h1 | ⟨-, -, h1⟩
    · exact mem_union_left _ (lab_spec h h1).1
    · exact mem_union_right _ (lab_spec h h1).1
    · exact (valid_splitVar C D).1 x h1
  · unfold fbddRule
    cases lab 𝒮 ℓ C <;> cases lab 𝒮 ℓ D <;> simp [(valid_splitVar C D).2 hne]

/-- **An FBDD gives a valid symmetric rule.** For an FBDD `𝒮` named by its functions and
containing `G`, the rule `fbddRule 𝒮 ℓ` is valid and symmetric, and FK-A under it has at most
`2|𝒮|` subproblems on `(G, Tr G)`, either variant and any fuel. -/
theorem rule_of_fbdd {𝒮 : Finset (HG n)} {ℓ : HG n → Option (Fin n)} (h : IsFBDD 𝒮 ℓ) {G : HG n}
    (hG : G ∈ 𝒮) : Symm (fbddRule 𝒮 ℓ) ∧ Valid (fbddRule 𝒮 ℓ) ∧ ∀ fuel b,
      (fkADagR (fbddRule 𝒮 ℓ) fuel b G (tr univ G)).card ≤ 2 * 𝒮.card := by
  refine ⟨fbddRule_symm 𝒮 ℓ, valid_fbddRule h, fun fuel b => ?_⟩
  -- a labelled side `K` has both children over `𝒮`
  have key : ∀ K : HG n, IsSperner K → ∀ x, lab 𝒮 ℓ K = some x →
      (minimal (del K x), minimal (con (tr univ K) x)) ∈ pairs 𝒮 ∧
        (minimal (del (tr univ K) x), minimal (con K x)) ∈ pairs 𝒮 := fun K sK x hx =>
    kids_mem sK (lab_spec h hx).2.1 (lab_spec h hx).2.2
  -- either orientation `(C, D)` of the pair of `K ∈ 𝒮`
  have node : ∀ K ∈ 𝒮, ∀ C D, (C = K ∧ D = tr univ K) ∨ (C = tr univ K ∧ D = K) →
      ∀ x, fbddRule 𝒮 ℓ C D = some x →
        (minimal (del C x), minimal (con D x)) ∈ pairs 𝒮 ∧
          (minimal (del D x), minimal (con C x)) ∈ pairs 𝒮 := by
    intro K hK C D hCD x hx
    have sK := (h K hK).1
    have sT := tr_isSperner univ K
    have ttK := tr_tr_of_sperner (within_univ K) sK
    have hs : support (tr univ K) = support K := (support_eq (within_univ K) sK rfl).symm
    rcases fbddRule_spec hx with h1 | h1 | ⟨h1, h2, h3⟩
    · rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact key _ sK x h1
      · have := key _ sT x h1; rw [ttK] at this; exact this
    · rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have := key _ sT x h1; rw [ttK] at this; exact ⟨this.2, this.1⟩
      · have := key _ sK x h1; exact ⟨this.2, this.1⟩
    · have h0 : support K = ∅ := by
        rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact support_of_lab_none h hK h1
        · exact support_of_lab_none h hK h2
      have := (valid_splitVar C D).1 x h3
      rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hs, h0] at this
  have hP : ∀ p ∈ (pairs 𝒮 : Set (HG n × HG n)), ∀ x, fbddRule 𝒮 ℓ p.1 p.2 = some x →
      (minimal (del p.1 x), minimal (con p.2 x)) ∈ (pairs 𝒮 : Set (HG n × HG n)) ∧
        (minimal (del p.2 x), minimal (con p.1 x)) ∈ (pairs 𝒮 : Set (HG n × HG n)) := by
    intro p hp x hx
    simp only [pairs, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hp
    rcases hp with ⟨K, hK, rfl⟩ | ⟨K, hK, rfl⟩
    · exact node K hK _ _ (Or.inl ⟨rfl, rfl⟩) x hx
    · exact node K hK _ _ (Or.inr ⟨rfl, rfl⟩) x hx
  have hroot : (minimal G, minimal (tr univ G)) ∈ (pairs 𝒮 : Set (HG n × HG n)) := by
    rw [minimal_eq_self (h G hG).1, minimal_tr]; exact mem_pairs_left hG
  exact (card_le_card fun p hp => fkADagR_sub hP fuel b _ _ hroot p hp).trans (card_pairs_le 𝒮)

/-- A family closed under a valid rule is an FBDD labelled by the rule. -/
theorem isFBDD_of_closed {r : Rule n} (hv : Valid r) {𝒮 : Finset (HG n)} (h : Closed r 𝒮) :
    IsFBDD 𝒮 (fun H => r H (tr univ H)) := by
  intro H hH
  obtain ⟨sH, hcl⟩ := h H hH
  refine ⟨sH, ?_⟩
  by_cases h0 : support H = ∅
  · exact Or.inl h0
  have hs : support (tr univ H) = support H := (support_eq (within_univ H) sH rfl).symm
  have hne : (support H ∪ support (tr univ H)).Nonempty := by
    rw [hs, union_self]; exact nonempty_iff_ne_empty.2 h0
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((hv H _).2 hne)
  have hxs : x ∈ support H := by have := (hv H _).1 x hx; rwa [hs, union_self] at this
  exact Or.inr ⟨x, hx, hxs, (hcl x hx).1, (hcl x hx).2⟩

/-- **The leftmost FBDD.** For a read-once formula with leaves in order, the states and the two
constants, labelled by the leftmost rule, form an FBDD for `f` with at most `|vars f| + 2` nodes
(Theorem 4.16). -/
theorem Fm.leftmost_fbdd {f : Fm n} (hf : Fm.Ordered f) :
    IsFBDD (Fm.Kst f) (fun H => leftRule H (tr univ H)) ∧ Fm.dnf f ∈ Fm.Kst f ∧
      (Fm.Kst f).card ≤ (Fm.vars f).card + 2 := by
  refine ⟨isFBDD_of_closed valid_leftRule (Fm.leftRule_closed hf),
    Fm.St_sub_Kst (Fm.dnf_mem_St hf), ?_⟩
  have h1 := card_union_le (Fm.St f) ({∅, {∅}} : Finset (HG n))
  have h2 : ({∅, {∅}} : Finset (HG n)).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have h3 := Fm.card_St_le hf
  unfold Fm.Kst
  omega

/-! ### A memo-friendly rule with FK96's guarantee (track 3) -/

/-- `x` is frequent at `(C, D)`: `|C| ≤ s·deg_C x` or `|D| ≤ s·deg_D x`, `s = ⌊log₂(|C| + |D|)⌋`,
i.e. frequency at least `1/log₂ N` on one side, and `x` is live. -/
def frequent (C D : HG n) (x : Fin n) : Bool :=
  decide (0 < key C D x) && (decide (C.card ≤ Nat.log 2 (C.card + D.card) * degree C x) ||
    decide (D.card ≤ Nat.log 2 (C.card + D.card) * degree D x))

/-- The guarded rule: the least frequent vertex, else the degree-sum vertex. Within the frequent
vertices it follows a fixed order, as an OBDD does. -/
def guardRule (C D : HG n) : Option (Fin n) :=
  match (List.finRange n).find? (frequent C D) with
  | some x => some x
  | none => splitVar C D

theorem frequent_comm (C D : HG n) : frequent C D = frequent D C := by
  funext x
  unfold frequent key
  rw [Nat.add_comm (degree D x) (degree C x), Nat.add_comm D.card C.card,
    Bool.or_comm (decide (D.card ≤ _))]

theorem guardRule_symm : Symm (guardRule (n := n)) := by
  intro C D; simp only [guardRule, frequent_comm C D, splitVar_comm C D]

theorem valid_guardRule : Valid (guardRule (n := n)) := by
  intro C D
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [guardRule] at hx
    split at hx
    · rename_i y hy
      cases hx
      have := List.find?_some hy
      simp only [frequent, Bool.and_eq_true, decide_eq_true_eq] at this
      exact mem_support_of_key this.1
    · exact (valid_splitVar C D).1 x hx
  · simp only [guardRule]
    split
    · rfl
    · exact (valid_splitVar C D).2 h

/-- **FK96's guarantee.** On a dual pair `(G, Tr G)` with both sides nonempty the guarded rule
splits on a vertex of frequency at least `1/⌊log₂ N⌋` on one side: the least such vertex, which
exists by FK96 Lemma 2.3.2 (`exists_frequent_vertex`). -/
theorem guardRule_frequent {G : HG n} (sG : IsSperner G) (hG : G.Nonempty)
    (hH : (tr univ G).Nonempty) : ∃ x, guardRule G (tr univ G) = some x ∧
      (G.card ≤ Nat.log 2 (G.card + (tr univ G).card) * degree G x ∨
        (tr univ G).card ≤ Nat.log 2 (G.card + (tr univ G).card) * degree (tr univ G) x) := by
  obtain ⟨s, v, hs, hpow, hv⟩ := exists_frequent_vertex (within_univ G) sG rfl hG hH
  have hsl : s ≤ Nat.log 2 (G.card + (tr univ G).card) := Nat.le_log_of_pow_le (by norm_num) hpow
  have hfv : frequent G (tr univ G) v = true := by
    have cG := card_pos.2 hG; have cH := card_pos.2 hH
    simp only [frequent, key, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff]
    rcases hv with hv | hv
    · have : G.card ≤ Nat.log 2 (G.card + (tr univ G).card) * degree G v :=
        hv.trans (Nat.mul_le_mul_right _ hsl)
      have dpos : 0 < degree G v := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at this; omega
      exact ⟨by simpa using Nat.add_pos_left dpos (degree (tr univ G) v), Or.inl this⟩
    · have : (tr univ G).card ≤ Nat.log 2 (G.card + (tr univ G).card) * degree (tr univ G) v :=
        hv.trans (Nat.mul_le_mul_right _ hsl)
      have dpos : 0 < degree (tr univ G) v := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at this; omega
      exact ⟨by simpa using Nat.add_pos_right (degree G v) dpos, Or.inr this⟩
  have hsome : ((List.finRange n).find? (frequent G (tr univ G))).isSome := by
    rcases h : (List.finRange n).find? (frequent G (tr univ G)) with _ | x
    · exact absurd hfv ((List.find?_eq_none.1 h) v (List.mem_finRange v))
    · rfl
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
  have hfx := List.find?_some hx
  simp only [frequent, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff] at hfx
  exact ⟨x, by simp only [guardRule, hx], hfx.2⟩

end HD

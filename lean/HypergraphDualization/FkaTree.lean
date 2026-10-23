/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# FK-A's recursion tree is a decision tree, so it is exponential on GK

On a dual pair, FK-A's recursion tree under any valid split rule unfolds into a decision tree
for `f_C` (`fkDT`): a split of `(C, D)` at `x` reads `x`, the left child `(C - x, D/x)` carries
`f_C|x=0` on its first side and the right child `(D - x, C/x)` carries `f_C|x=1` on its second.
Each leaf of the recursion is a constant, a single term or a single clause, which costs at most
`n + 1` leaves (`leaves_fkDT`). With `gk_leaves` this gives the bound on the GK and TK families
under every valid rule (`fkA_gk_tree`):

  `2·(27/16)^(n/4) ≤ (n + 1) · τ`,   `n = 2^i` vertices of `coalt i`, `i ≥ 2`.

Legend
  vl e          the vertices of `e` in increasing order
  chainAnd l    decision tree for `∀ v ∈ l, v ∈ X`; `chainOr l` for `∃ v ∈ l, v ∈ X`
  brute f l S   the complete tree over the vertices of `l`, a fallback that is always correct
  leafDT H      decision tree for `upHit H`, small when `H` is `Simple`
  fkDT r ... s  the unfolded recursion, computing the first side if `s`, else the second
  gkH i         `coalt i` on `Fin (2^i)`
-/
import HypergraphDualization.DecisionTree
import HypergraphDualization.BranchingProgram

namespace HD

open Finset

variable {n : ℕ}

/-! ### Small decision trees for the leaves -/

/-- The vertices of `e`, in increasing order. -/
def vl (e : Finset (Fin n)) : List (Fin n) := (List.finRange n).filter (· ∈ e)

theorem mem_vl {e : Finset (Fin n)} {v : Fin n} : v ∈ vl e ↔ v ∈ e := by simp [vl]

theorem length_vl_le (e : Finset (Fin n)) : (vl e).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

def chainAnd : List (Fin n) → DTree (Fin n)
  | [] => .leaf true
  | x :: l => .node x (.leaf false) (chainAnd l)

def chainOr : List (Fin n) → DTree (Fin n)
  | [] => .leaf false
  | x :: l => .node x (chainOr l) (.leaf true)

def brute (f : Finset (Fin n) → Bool) : List (Fin n) → Finset (Fin n) → DTree (Fin n)
  | [], S => .leaf (f S)
  | x :: l, S => .node x (brute f l S) (brute f l (insert x S))

theorem eval_chainAnd (X : Finset (Fin n)) :
    ∀ l, (chainAnd l).eval X = decide (∀ v ∈ l, v ∈ X)
  | [] => by simp [chainAnd, DTree.eval]
  | x :: l => by
    by_cases hx : x ∈ X <;> simp [chainAnd, DTree.eval, hx, eval_chainAnd X l]

theorem eval_chainOr (X : Finset (Fin n)) :
    ∀ l, (chainOr l).eval X = decide (∃ v ∈ l, v ∈ X)
  | [] => by simp [chainOr, DTree.eval]
  | x :: l => by
    by_cases hx : x ∈ X <;> simp [chainOr, DTree.eval, hx, eval_chainOr X l]

theorem leaves_chainAnd : ∀ l : List (Fin n), (chainAnd l).leaves = l.length + 1
  | [] => rfl
  | x :: l => by simp [chainAnd, DTree.leaves, leaves_chainAnd l]; omega

theorem leaves_chainOr : ∀ l : List (Fin n), (chainOr l).leaves = l.length + 1
  | [] => rfl
  | x :: l => by simp [chainOr, DTree.leaves, leaves_chainOr l]

theorem eval_brute (f : Finset (Fin n) → Bool) (X : Finset (Fin n)) :
    ∀ l S, (brute f l S).eval X = f (S ∪ X.filter (· ∈ l))
  | [], S => by simp [brute, DTree.eval]
  | x :: l, S => by
    by_cases hx : x ∈ X
    · simp only [brute, DTree.eval, if_pos hx, eval_brute f X l]
      congr 1; ext v
      simp only [mem_union, mem_insert, mem_filter, List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h1, h2⟩)
        · exact Or.inr ⟨hx, Or.inl rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inr h2⟩
      · rintro (h | ⟨h1, rfl | h2⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨h1, h2⟩
    · simp only [brute, DTree.eval, if_neg hx, eval_brute f X l]
      congr 1; ext v
      simp only [mem_union, mem_filter, List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inr h2⟩
      · rintro (h | ⟨h1, rfl | h2⟩)
        · exact Or.inl h
        · exact absurd h1 hx
        · exact Or.inr ⟨h1, h2⟩

theorem eval_brute_univ (f : Finset (Fin n) → Bool) (X : Finset (Fin n)) :
    (brute f (List.finRange n) ∅).eval X = f X := by
  rw [eval_brute]; congr 1; ext v; simp

/-- A decision tree for `upHit H`; short when `H` is a constant, one edge or singletons. -/
def leafDT (H : HG n) : DTree (Fin n) :=
  if ∅ ∈ H then .leaf true
  else if H = ∅ then .leaf false
  else if H.card = 1 then chainAnd (vl (support H))
  else if ∀ e ∈ H, e.card = 1 then chainOr (vl (support H))
  else brute (fun X => decide (upHit H X)) (List.finRange n) ∅

theorem eval_leafDT (H : HG n) (X : Finset (Fin n)) :
    (leafDT H).eval X = decide (upHit H X) := by
  unfold leafDT
  split_ifs with h0 h1 h2 h3
  · simp only [DTree.eval]; exact (decide_eq_true ⟨∅, h0, empty_subset _⟩).symm
  · subst h1; simp [DTree.eval, upHit]
  · obtain ⟨e, rfl⟩ := card_eq_one.1 h2
    rw [eval_chainAnd]
    simp only [mem_vl, support, singleton_biUnion, id, upHit, mem_singleton, exists_eq_left]
    rw [decide_eq_decide]; exact ⟨fun h v hv => h v hv, fun h v hv => h hv⟩
  · rw [eval_chainOr]
    simp only [mem_vl, mem_support, upHit, decide_eq_decide]
    constructor
    · rintro ⟨v, ⟨e, he, hv⟩, hvX⟩
      obtain ⟨w, rfl⟩ := card_eq_one.1 (h3 e he)
      exact ⟨{w}, he, by simpa [mem_singleton.1 hv] using hvX⟩
    · rintro ⟨e, he, heX⟩
      obtain ⟨w, rfl⟩ := card_eq_one.1 (h3 e he)
      exact ⟨w, ⟨{w}, he, mem_singleton_self w⟩, heX (mem_singleton_self w)⟩
  · exact eval_brute_univ _ _

/-- The leaf shapes of FK-A on a dual pair. -/
def Simple (H : HG n) : Prop := ∅ ∈ H ∨ H = ∅ ∨ H.card = 1 ∨ ∀ e ∈ H, e.card = 1

theorem leaves_leafDT {H : HG n} (h : Simple H) : (leafDT H).leaves ≤ n + 1 := by
  unfold leafDT
  split_ifs with h0 h1 h2 h3
  · simp [DTree.leaves]
  · simp [DTree.leaves]
  · rw [leaves_chainAnd]; have := length_vl_le (support H); omega
  · rw [leaves_chainOr]; have := length_vl_le (support H); omega
  · rcases h with h | h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3

theorem simple_of_card_le_one {C D : HG n} (sD : IsSperner D) (hd : Dual univ C D)
    (h : C.card ≤ 1) : Simple C ∧ Simple D := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · have hC : C = ∅ := card_eq_zero.1 h0
    subst hC
    exact ⟨Or.inr (Or.inl rfl), Or.inl (dual_empty_left.1 hd)⟩
  · obtain ⟨c, rfl⟩ := card_eq_one.1 h1
    refine ⟨Or.inr (Or.inr (Or.inl (card_singleton c))), Or.inr (Or.inr (Or.inr ?_))⟩
    rw [(dual_singleton_left (subset_univ c) (within_univ D) sD).1 hd]
    intro e he
    obtain ⟨v, -, rfl⟩ := mem_image.1 he
    exact card_singleton v

/-- At a leaf of FK-A on a dual pair, both sides are simple. -/
theorem simple_of_leaf {C D : HG n} (sC : IsSperner C) (sD : IsSperner D) (hd : Dual univ C D)
    (h : C.card ≤ 1 ∨ D.card ≤ 1) : Simple C ∧ Simple D := by
  rcases h with h | h
  · exact simple_of_card_le_one sD hd h
  · exact (simple_of_card_le_one sC (dual_comm.1 hd) h).symm

/-! ### The unfolded recursion -/

/-- FK-A's recursion tree as a decision tree for the first side (`s`) or the second. -/
def fkDT (r : Rule n) : ℕ → Bool → HG n → HG n → Bool → DTree (Fin n)
  | 0, _, C₀, D₀, s => leafDT (if s then minimal C₀ else minimal D₀)
  | fuel + 1, modified, C₀, D₀, s =>
    let C := minimal C₀
    let D := minimal D₀
    if !conds C D then leafDT (if s then C else D)
    else if C.card * D.card ≤ 1 || (modified && (C.card == 1 || D.card == 1)) then
      leafDT (if s then C else D)
    else
      match r C D with
      | none => leafDT (if s then C else D)
      | some x =>
        if s then .node x (fkDT r fuel modified (del C x) (con D x) true)
          (fkDT r fuel modified (del D x) (con C x) false)
        else .node x (fkDT r fuel modified (del D x) (con C x) true)
          (fkDT r fuel modified (del C x) (con D x) false)

theorem upHit_ite_minimal (s : Bool) (C D : HG n) (X : Finset (Fin n)) :
    upHit (if s then minimal C else minimal D) X ↔ upHit (if s then C else D) X := by
  cases s <;> simp [upHit_minimal]

/-- **The unfolded recursion computes the side it is asked for**, on every input and rule. -/
theorem eval_fkDT (r : Rule n) : ∀ fuel (modified : Bool) (C D : HG n) (s : Bool)
    (X : Finset (Fin n)),
    (fkDT r fuel modified C D s).eval X = decide (upHit (if s then C else D) X) := by
  intro fuel
  induction fuel with
  | zero =>
    intro modified C D s X
    simp only [fkDT, eval_leafDT, upHit_ite_minimal]
  | succ fuel ih =>
    intro modified C D s X
    cases s
    · simp only [fkDT, Bool.false_eq_true, if_false]
      split_ifs
      · rw [eval_leafDT, decide_eq_decide, upHit_minimal]
      · rw [eval_leafDT, decide_eq_decide, upHit_minimal]
      · split
        · rw [eval_leafDT, decide_eq_decide, upHit_minimal]
        · rename_i x _
          by_cases hx : x ∈ X
          · simp only [DTree.eval, if_pos hx, ih, Bool.false_eq_true, if_false, decide_eq_decide]
            rw [upHit_con, insert_eq_of_mem hx, upHit_minimal]
          · simp only [DTree.eval, if_neg hx, ih, if_true, decide_eq_decide]
            rw [upHit_del, erase_eq_of_notMem hx, upHit_minimal]
    · simp only [fkDT, if_true]
      split_ifs
      · rw [eval_leafDT, decide_eq_decide, upHit_minimal]
      · rw [eval_leafDT, decide_eq_decide, upHit_minimal]
      · split
        · rw [eval_leafDT, decide_eq_decide, upHit_minimal]
        · rename_i x _
          by_cases hx : x ∈ X
          · simp only [DTree.eval, if_pos hx, ih, Bool.false_eq_true, if_false, decide_eq_decide]
            rw [upHit_con, insert_eq_of_mem hx, upHit_minimal]
          · simp only [DTree.eval, if_neg hx, ih, if_true, decide_eq_decide]
            rw [upHit_del, erase_eq_of_notMem hx, upHit_minimal]

theorem support_con_sub' (H : HG n) (x : Fin n) : support (con H x) ⊆ (support H).erase x := by
  intro v hv
  obtain ⟨e', he', hve⟩ := mem_biUnion.1 hv
  obtain ⟨e, he, rfl⟩ := mem_image.1 he'
  obtain ⟨hvx, hve⟩ := mem_erase.1 hve
  exact mem_erase.2 ⟨hvx, mem_biUnion.2 ⟨e, he, hve⟩⟩

theorem support_minimal_sub (H : HG n) : support (minimal H) ⊆ support H :=
  biUnion_subset_biUnion_of_subset_left _ (minimal_subset H)

/-- **The size bound.** On a dual pair with enough fuel, under a valid rule, the unfolded tree
has at most `n + 1` leaves per node of FK-A's recursion tree. -/
theorem leaves_fkDT {r : Rule n} (hv : Valid r) (modified : Bool) : ∀ fuel (C D : HG n),
    Dual univ C D → (support C ∪ support D).card < fuel → ∀ s,
      (fkDT r fuel modified C D s).leaves ≤ (n + 1) * (fkAR r fuel modified C D).2 := by
  intro fuel
  induction fuel with
  | zero => intro C D _ h; omega
  | succ f ih =>
    intro C D hd hcard s
    set C' := minimal C with hC'
    set D' := minimal D with hD'
    have sC : IsSperner C' := minimal_isSperner C
    have sD : IsSperner D' := minimal_isSperner D
    have hd' : Dual univ C' D' := dual_minimal.2 hd
    have hconds : conds C' D' = true := conds_of_dual sC sD hd'
    have hsimple : C'.card ≤ 1 ∨ D'.card ≤ 1 → (leafDT (if s then C' else D')).leaves ≤ n + 1 :=
      fun h => by
        obtain ⟨h1, h2⟩ := simple_of_leaf sC sD hd' h
        cases s
        · exact leaves_leafDT h2
        · exact leaves_leafDT h1
    simp only [fkDT, fkAR, ← hC', ← hD', hconds, Bool.not_true, Bool.false_eq_true, if_false]
    by_cases hleaf : (C'.card * D'.card ≤ 1 || (modified && (C'.card == 1 || D'.card == 1))) = true
    · rw [if_pos hleaf, if_pos hleaf]
      have : C'.card ≤ 1 ∨ D'.card ≤ 1 := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hleaf
        rcases hleaf with h | ⟨-, h | h⟩
        · by_contra hc; push Not at hc; nlinarith
        · exact Or.inl h.le
        · exact Or.inr h.le
      have := hsimple this; simpa using this
    · rw [if_neg hleaf, if_neg hleaf]
      have hne : (support C' ∪ support D').Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty, union_eq_empty] at hemp
        have hsub : ∀ H : HG n, support H = ∅ → H.card ≤ 1 := fun H hH => by
          refine card_le_one.2 fun a ha b hb => ?_
          have ha' : a = ∅ := eq_empty_of_forall_notMem fun v hv => by
            have : v ∈ support H := mem_biUnion.2 ⟨a, ha, hv⟩
            rw [hH] at this; exact notMem_empty v this
          have hb' : b = ∅ := eq_empty_of_forall_notMem fun v hv => by
            have : v ∈ support H := mem_biUnion.2 ⟨b, hb, hv⟩
            rw [hH] at this; exact notMem_empty v this
          rw [ha', hb']
        have h1 := hsub C' hemp.1
        have h2 := hsub D' hemp.2
        apply hleaf
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (by nlinarith)
      obtain ⟨x, hxr⟩ := Option.isSome_iff_exists.1 ((hv C' D').2 hne)
      have hxs : x ∈ support C' ∪ support D' := (hv C' D').1 x hxr
      rw [hxr]
      simp only
      -- the two children are dual
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
      obtain ⟨dL, dR⟩ := hsplit.1 hd'
      have hsupp : support C' ∪ support D' ⊆ support C ∪ support D :=
        union_subset_union (support_minimal_sub C) (support_minimal_sub D)
      have hlt : ∀ A B : HG n, support A ⊆ (support C').erase x →
          support B ⊆ (support D').erase x → (support A ∪ support B).card < f := by
        intro A B hA hB
        have h1 : support A ∪ support B ⊆ (support C ∪ support D).erase x :=
          union_subset ((hA.trans (erase_subset_erase x (support_minimal_sub C))).trans
              (erase_subset_erase x subset_union_left))
            ((hB.trans (erase_subset_erase x (support_minimal_sub D))).trans
              (erase_subset_erase x subset_union_right))
        have := card_le_card h1
        rw [card_erase_of_mem (hsupp hxs)] at this
        have := card_pos.2 ⟨x, hsupp hxs⟩
        omega
      have hlt' : ∀ A B : HG n, support A ⊆ (support D').erase x →
          support B ⊆ (support C').erase x → (support A ∪ support B).card < f := by
        intro A B hA hB; rw [union_comm]; exact hlt B A hB hA
      have cL := hlt _ _ (support_del_sub C' x) (support_con_sub' D' x)
      have cR := hlt' _ _ (support_del_sub D' x) (support_con_sub' C' x)
      have l1 : (fkAR r f modified (del C' x) (con D' x)).1 = true := by
        rw [fkAR_correct]; exact decide_eq_true dL
      rw [if_pos l1]
      have iL := ih _ _ dL cL
      have iR := ih _ _ dR cR
      cases s
      · simp only [Bool.false_eq_true, if_false, DTree.leaves]
        have := iR true; have := iL false; nlinarith
      · simp only [if_true, DTree.leaves]
        have := iL true; have := iR false; nlinarith

/-- **FK-A's tree is a decision tree.** For a valid rule and a dual pair, some decision tree
for `f_C` has at most `(n + 1) τ` leaves, `τ` the nodes of FK-A's recursion tree. -/
theorem fkA_tree_dt {r : Rule n} (hv : Valid r) (modified : Bool) {C D : HG n}
    (hd : Dual univ C D) :
    ∃ t : DTree (Fin n), (∀ X, t.eval X = decide (upHit C X)) ∧
      t.leaves ≤ (n + 1) * (fkAR r (n + 1) modified C D).2 := by
  refine ⟨fkDT r (n + 1) modified C D true, fun X => by rw [eval_fkDT]; rfl, ?_⟩
  refine leaves_fkDT hv modified (n + 1) C D hd ?_ true
  have := card_le_univ (support C ∪ support D)
  simp only [Fintype.card_fin] at this
  omega

/-! ### The GK family on `Fin (2^i)` -/

/-- `coalt i` on the vertex type `Fin (2^i)`. -/
def gkH (i : ℕ) : HG (2 ^ i) :=
  (coalt i).image fun e => univ.filter fun v : Fin (2 ^ i) => (v : ℕ) ∈ e

theorem upHit_gkH (i : ℕ) (X : Finset (Fin (2 ^ i))) :
    upHit (gkH i) X ↔ upHit (coalt i) (X.map Fin.valEmbedding) := by
  have hW := (alt_props i).2.1
  constructor
  · rintro ⟨e', he', heX⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    refine ⟨e, he, fun u hu => ?_⟩
    have hu' : u < 2 ^ i := mem_range.1 (hW e he hu)
    have : (⟨u, hu'⟩ : Fin (2 ^ i)) ∈ X := heX (mem_filter.2 ⟨mem_univ _, hu⟩)
    exact mem_map.2 ⟨_, this, rfl⟩
  · rintro ⟨e, he, heX⟩
    refine ⟨_, mem_image_of_mem _ he, fun v hv => ?_⟩
    obtain ⟨w, hw, hwv⟩ := mem_map.1 (heX (mem_filter.1 hv).2)
    rw [Fin.valEmbedding_apply] at hwv
    rwa [← Fin.ext hwv]

/-- Relabel a decision tree. -/
def DTree.map {α β : Type*} (φ : α → β) : DTree α → DTree β
  | .leaf b => .leaf b
  | .node x lo hi => .node (φ x) (lo.map φ) (hi.map φ)

theorem eval_map_val {m : ℕ} (Y : Finset ℕ) :
    ∀ t : DTree (Fin m), (t.map Fin.val).eval Y = t.eval (univ.filter fun v => (v : ℕ) ∈ Y)
  | .leaf b => rfl
  | .node x lo hi => by
    simp only [DTree.map, DTree.eval, mem_filter, mem_univ, true_and, eval_map_val Y lo,
      eval_map_val Y hi]

theorem leaves_map {α β : Type*} (φ : α → β) : ∀ t : DTree α, (t.map φ).leaves = t.leaves
  | .leaf _ => rfl
  | .node _ lo hi => by simp [DTree.map, DTree.leaves, leaves_map φ lo, leaves_map φ hi]

/-- **FK-A is exponential on GK and TK under every valid split rule.** On `coalt (j + 2)`,
`n = 2^(j+2)` vertices, FK-A's recursion tree has `τ` nodes with
`2·27^(n/4) ≤ 16^(n/4) (n + 1) τ`, that is `τ ≥ 2·(27/16)^(n/4) / (n + 1)`. -/
theorem fkA_gk_tree {j : ℕ} {r : Rule (2 ^ (j + 2))} (hv : Valid r) (modified : Bool) :
    2 * 27 ^ (2 ^ j) ≤ 16 ^ (2 ^ j) *
      ((2 ^ (j + 2) + 1) *
        (fkAR r (2 ^ (j + 2) + 1) modified (gkH (j + 2)) (tr univ (gkH (j + 2)))).2) := by
  obtain ⟨t, ht, hl⟩ := fkA_tree_dt hv modified (dual_tr (gkH (j + 2)))
  have hgk : ∀ Y ⊆ range (2 ^ (j + 2)), (t.map Fin.val).eval Y = gkF (j + 2) Y := by
    intro Y hY
    rw [eval_map_val, ht, gkF, decide_eq_decide, upHit_gkH]
    have : (univ.filter fun v : Fin (2 ^ (j + 2)) => (v : ℕ) ∈ Y).map Fin.valEmbedding = Y := by
      ext u; constructor
      · intro hu; obtain ⟨w, hw, rfl⟩ := mem_map.1 hu; exact (mem_filter.1 hw).2
      · intro hu
        exact mem_map.2 ⟨⟨u, mem_range.1 (hY hu)⟩, mem_filter.2 ⟨mem_univ _, hu⟩, rfl⟩
    rw [this]
  have := gk_leaves j (t.map Fin.val) hgk
  rw [leaves_map] at this
  calc (2 * 27 ^ 2 ^ j : ℕ) ≤ 16 ^ 2 ^ j * t.leaves := by exact_mod_cast this
    _ ≤ _ := Nat.mul_le_mul_left _ hl

/-- FK-A as published (the degree-sum rule): the same bound on GK `f_k = coalt (2k - 1)`. -/
theorem fkA_gk_degree_sum (j : ℕ) (modified : Bool) :
    2 * 27 ^ (2 ^ j) ≤ 16 ^ (2 ^ j) *
      ((2 ^ (j + 2) + 1) *
        (fkA (2 ^ (j + 2) + 1) modified (gkH (j + 2)) (tr univ (gkH (j + 2)))).2) :=
  fkA_gk_tree valid_splitVar modified

end HD

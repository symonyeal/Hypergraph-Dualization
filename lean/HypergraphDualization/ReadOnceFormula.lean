/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Read-once formulas and the leftmost split rule (research track C)

A monotone formula `f` over `Fin n` has the DNF `dnf f` (edges = terms after distributing, not
reduced) and the dual `dual f` (AND and OR exchanged). For every formula, restriction commutes
with the DNF: `dnf(f|x=0) = dnf f − x` and `dnf(f|x=1) = dnf f / x`, and
`Tr(dnf f) = min(dnf(dual f))`; for a read-once `f` the reduction is unnecessary.

*Theorem 4.16* (Hertel's Theorem 4.4.1 for FK-A). Number the leaves of a read-once formula from
left to right (`Ordered`) and split always on the least live vertex (`leftRule`). Then every
subproblem is `(H, Tr H)` or `(Tr H, H)` for `H` a constant or one of the states `St f`: a
restriction of `f` fixing the leftmost leaves. There are at most `n` states, so FK-A has at most
`2n + 2` distinct subproblems, under either variant and for any fuel (`leftmost_delta`). The
states and the constants, labelled by the leftmost rule, are an FBDD for `f` with at most
`|vars f| + 2` nodes (`Fm.leftmost_fbdd` in `BranchingProgram`).

A read-once formula on all of `Fin n` has a read-once DNF in the hypergraph sense of `Primitive`
(Sperner, conformal, cograph primal graph): `readOnce_dnf`, the easy direction of Gurvich's
characterisation. The converse is cited, not proved.

| Lean | Statement |
| --- | --- |
| `Fm`, `eval`, `dnf`, `dual`, `upHit_dnf` | monotone formulas; `dnf f` contains an edge of `S` iff `f(S)` |
| `dnf_restrict_false`, `dnf_restrict_true` | `dnf(f\|x=0) = dnf f − x`, `dnf(f\|x=1) = dnf f / x` |
| `tr_dnf`, `tr_dnf_readOnce` | `Tr(dnf f) = min(dnf(dual f))`; `= dnf(dual f)` for read-once `f` |
| `St`, `card_St_le`, `St_closed` | the leftmost states: at most `\|vars f\|`, closed under the leftmost split |
| `leftmost_delta` | `δ ≤ 2·\|vars f\| + 2 ≤ 2n + 2` under the leftmost rule (Theorem 4.16) |
| `readOnce_dnf` | `Fm.ReadOnce f`, `vars f = univ` imply `HD.ReadOnce (dnf f)` |
| `minor_union`, `minor_join`, `rminor_determined` | interleaving (Lemma 4.17); Remark 4.12 |
-/
import HypergraphDualization.SplitRule
import HypergraphDualization.Operations
import HypergraphDualization.Cotree

namespace HD

open Finset

variable {n : ℕ}

/-! ### Hypergraph identities -/

theorem del_join (A B : HG n) (x : Fin n) : del (join A B) x = join (del A x) (del B x) := by
  ext s
  simp only [del, mem_filter, mem_join]
  constructor
  · rintro ⟨⟨e, he, f, hf, rfl⟩, hx⟩
    exact ⟨e, ⟨he, fun h => hx (mem_union_left _ h)⟩, f, ⟨hf, fun h => hx (mem_union_right _ h)⟩,
      rfl⟩
  · rintro ⟨e, ⟨he, hxe⟩, f, ⟨hf, hxf⟩, rfl⟩
    exact ⟨⟨e, he, f, hf, rfl⟩, by simp [hxe, hxf]⟩

theorem con_join (A B : HG n) (x : Fin n) : con (join A B) x = join (con A x) (con B x) := by
  ext s
  simp only [con, mem_image, mem_join]
  constructor
  · rintro ⟨_, ⟨e, he, f, hf, rfl⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, _, ⟨f, hf, rfl⟩, (erase_union_distrib _ _ _).symm⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, _, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨e ∪ f, ⟨e, he, f, hf, rfl⟩, erase_union_distrib _ _ _⟩

theorem del_union (A B : HG n) (x : Fin n) : del (A ∪ B) x = del A x ∪ del B x := filter_union ..

theorem con_union (A B : HG n) (x : Fin n) : con (A ∪ B) x = con A x ∪ con B x := image_union ..

theorem del_of_notMem {A : HG n} {x : Fin n} (hx : x ∉ support A) : del A x = A :=
  filter_true_of_mem fun e he hxe => hx (mem_support.2 ⟨e, he, hxe⟩)

theorem con_of_notMem {A : HG n} {x : Fin n} (hx : x ∉ support A) : con A x = A := by
  ext e
  simp only [con, mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rwa [erase_eq_of_notMem fun hxf => hx (mem_support.2 ⟨f, hf, hxf⟩)]
  · exact fun he => ⟨e, he, erase_eq_of_notMem fun hxe => hx (mem_support.2 ⟨e, he, hxe⟩)⟩

theorem join_empty_left (B : HG n) : join ∅ B = ∅ := by simp [join]

theorem join_unit_left (B : HG n) : join {∅} B = B := by
  ext s; simp [mem_join]

/-- Two families with the same up-set have the same Sperner reduction. -/
theorem minimal_congr {X Y : HG n} (h : ∀ S, upHit X S ↔ upHit Y S) : minimal X = minimal Y :=
  eq_of_upHit_iff (within_univ _) (within_univ _) (minimal_isSperner X) (minimal_isSperner Y)
    fun A _ => by rw [upHit_minimal, upHit_minimal]; exact h A

theorem within_mono {V W : Finset (Fin n)} {H : HG n} (h : Within V H) (hVW : V ⊆ W) :
    Within W H := fun e he => (h e he).trans hVW

theorem support_subset_of_within {V : Finset (Fin n)} {H : HG n} (h : Within V H) :
    support H ⊆ V := fun x hx => by
  obtain ⟨e, he, hxe⟩ := mem_support.1 hx
  exact h e he hxe

theorem support_nonempty {H : HG n} (hn : H.Nonempty) (h0 : ∅ ∉ H) : (support H).Nonempty := by
  obtain ⟨e, he⟩ := hn
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ he))
  exact ⟨x, mem_support.2 ⟨e, he, hx⟩⟩

theorem tr_empty_hg : tr univ (∅ : HG n) = {∅} := by
  ext T
  simp only [mem_tr, IsMinHit, Hits, notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
    subset_univ, not_true_eq_false, imp_false, mem_singleton]
  exact ⟨fun h => eq_empty_iff_forall_notMem.2 h, fun h => h ▸ fun _ => notMem_empty _⟩

theorem tr_unit_hg : tr univ ({∅} : HG n) = ∅ := by
  ext T
  simp only [mem_tr, notMem_empty, iff_false, not_and]
  exact fun _ hT => not_hits_of_mem_empty (mem_singleton_self ∅) T hT.1

theorem isSperner_empty : IsSperner (∅ : HG n) := fun _ h => absurd h (notMem_empty _)

theorem isSperner_unit : IsSperner ({∅} : HG n) := fun e he f hf _ => by
  rw [mem_singleton.1 he, mem_singleton.1 hf]

/-! ### Monotone formulas -/

/-- Monotone formulas over `Fin n`, with the constants that restrictions produce. -/
inductive Fm (n : ℕ) : Type
  | tt : Fm n
  | ff : Fm n
  | var : Fin n → Fm n
  | and : Fm n → Fm n → Fm n
  | or : Fm n → Fm n → Fm n

namespace Fm

/-- `f(S)`: the value of `f` with exactly the variables of `S` true. -/
def eval : Fm n → Finset (Fin n) → Bool
  | tt, _ => true
  | ff, _ => false
  | var i, S => decide (i ∈ S)
  | and f g, S => eval f S && eval g S
  | or f g, S => eval f S || eval g S

/-- The DNF obtained by distributing: OR is union, AND is `join`. Not Sperner-reduced. -/
def dnf : Fm n → HG n
  | tt => {∅}
  | ff => ∅
  | var i => {{i}}
  | and f g => join (dnf f) (dnf g)
  | or f g => dnf f ∪ dnf g

/-- The dual formula `f^d`: AND and OR exchanged. -/
def dual : Fm n → Fm n
  | tt => ff
  | ff => tt
  | var i => var i
  | and f g => or (dual f) (dual g)
  | or f g => and (dual f) (dual g)

/-- The variables occurring in `f`. -/
def vars : Fm n → Finset (Fin n)
  | tt => ∅
  | ff => ∅
  | var i => {i}
  | and f g => vars f ∪ vars g
  | or f g => vars f ∪ vars g

/-- The restriction `f|x=b`. -/
def restrict (x : Fin n) (b : Bool) : Fm n → Fm n
  | tt => tt
  | ff => ff
  | var i => if i = x then (if b then tt else ff) else var i
  | and f g => and (restrict x b f) (restrict x b g)
  | or f g => or (restrict x b f) (restrict x b g)

/-- Read-once: no constants, and the inputs of every gate have disjoint variables. -/
def ReadOnce : Fm n → Prop
  | tt => False
  | ff => False
  | var _ => True
  | and f g => ReadOnce f ∧ ReadOnce g ∧ Disjoint (vars f) (vars g)
  | or f g => ReadOnce f ∧ ReadOnce g ∧ Disjoint (vars f) (vars g)

/-- Read-once with the leaves numbered from left to right. -/
def Ordered : Fm n → Prop
  | tt => False
  | ff => False
  | var _ => True
  | and f g => Ordered f ∧ Ordered g ∧ ∀ a ∈ vars f, ∀ b ∈ vars g, a < b
  | or f g => Ordered f ∧ Ordered g ∧ ∀ a ∈ vars f, ∀ b ∈ vars g, a < b

theorem disjoint_of_lt {V W : Finset (Fin n)} (h : ∀ a ∈ V, ∀ b ∈ W, a < b) : Disjoint V W :=
  disjoint_left.2 fun a ha hb => lt_irrefl a (h a ha a hb)

theorem Ordered.readOnce : ∀ {f : Fm n}, Ordered f → ReadOnce f
  | tt, h | ff, h => h.elim
  | var _, _ => trivial
  | and _ _, ⟨hf, hg, h⟩ => ⟨hf.readOnce, hg.readOnce, disjoint_of_lt h⟩
  | or _ _, ⟨hf, hg, h⟩ => ⟨hf.readOnce, hg.readOnce, disjoint_of_lt h⟩

/-- `dnf f` has an edge inside `S` iff `f(S)`. -/
theorem upHit_dnf (f : Fm n) (S : Finset (Fin n)) : upHit (dnf f) S ↔ eval f S = true := by
  induction f with
  | tt => simp [dnf, eval, upHit]
  | ff => simp [dnf, eval, upHit]
  | var i => simp [dnf, eval, upHit]
  | and f g hf hg => simp [dnf, eval, upHit_join, hf, hg]
  | or f g hf hg => simp [dnf, eval, upHit_union, hf, hg]

/-- `S` meets every edge of `dnf f` iff `f^d(S)`. -/
theorem hits_dnf (f : Fm n) (S : Finset (Fin n)) : Hits (dnf f) S ↔ eval (dual f) S = true := by
  induction f with
  | tt => simp [dnf, dual, eval, Hits]
  | ff => simp [dnf, dual, eval, Hits]
  | var i => simp [dnf, dual, eval, Hits, Finset.Nonempty]
  | and f g hf hg => simp [dnf, dual, eval, hits_join, hf, hg]
  | or f g hf hg => simp [dnf, dual, eval, hits_union, hf, hg]

theorem eval_restrict (x : Fin n) (b : Bool) (f : Fm n) (S : Finset (Fin n)) :
    eval (restrict x b f) S = eval f (if b then insert x S else S.erase x) := by
  induction f with
  | tt => rfl
  | ff => rfl
  | var i =>
    by_cases h : i = x
    · subst h; cases b <;> simp [restrict, eval]
    · cases b <;> simp [restrict, eval, h]
  | and f g hf hg => simp [restrict, eval, hf, hg]
  | or f g hf hg => simp [restrict, eval, hf, hg]

/-- **`dnf(f|x=0) = dnf f − x`**, for every formula. -/
theorem dnf_restrict_false (x : Fin n) (f : Fm n) : dnf (restrict x false f) = del (dnf f) x := by
  induction f with
  | tt => simp [restrict, dnf, del, filter_singleton]
  | ff => simp [restrict, dnf, del, filter_singleton]
  | var i =>
    by_cases h : i = x
    · subst h; simp [restrict, dnf, del, filter_singleton]
    · simp [restrict, dnf, del, filter_singleton, h, Ne.symm h]
  | and f g hf hg => simp only [restrict, dnf, hf, hg, del_join]
  | or f g hf hg => simp only [restrict, dnf, hf, hg, del_union]

/-- **`dnf(f|x=1) = dnf f / x`**, for every formula; hence `min dnf(f|x=1) = min(dnf f / x)`. -/
theorem dnf_restrict_true (x : Fin n) (f : Fm n) : dnf (restrict x true f) = con (dnf f) x := by
  induction f with
  | tt => simp [restrict, dnf, con]
  | ff => simp [restrict, dnf, con]
  | var i =>
    by_cases h : i = x
    · subst h; simp [restrict, dnf, con]
    · simp [restrict, dnf, con, h, erase_eq_of_notMem, Ne.symm h]
  | and f g hf hg => simp only [restrict, dnf, hf, hg, con_join]
  | or f g hf hg => simp only [restrict, dnf, hf, hg, con_union]

/-- **`Tr(dnf f) = min(dnf(f^d))`**, for every formula. -/
theorem tr_dnf (f : Fm n) : tr univ (dnf f) = minimal (dnf (dual f)) :=
  eq_of_upHit_iff (tr_within _ _) (within_univ _) (tr_isSperner _ _) (minimal_isSperner _)
    fun A _ => by rw [upHit_tr_iff (subset_univ A), upHit_minimal, upHit_dnf, hits_dnf]

theorem dnf_within (f : Fm n) : Within (vars f) (dnf f) := by
  induction f with
  | tt => intro e he; simp_all [dnf]
  | ff => intro e he; simp_all [dnf]
  | var i => intro e he; simp_all [dnf, vars]
  | and f g hf hg =>
    intro s hs
    obtain ⟨e, he, f', hf', rfl⟩ := mem_join.1 hs
    exact union_subset_union (hf e he) (hg f' hf')
  | or f g hf hg =>
    intro e he
    rcases mem_union.1 he with he | he
    · exact (hf e he).trans subset_union_left
    · exact (hg e he).trans subset_union_right

theorem vars_dual (f : Fm n) : vars (dual f) = vars f := by
  induction f with
  | tt => rfl
  | ff => rfl
  | var i => rfl
  | and f g hf hg => simp [dual, vars, hf, hg]
  | or f g hf hg => simp [dual, vars, hf, hg]

theorem ReadOnce.dual : ∀ {f : Fm n}, ReadOnce f → ReadOnce (Fm.dual f)
  | tt, h | ff, h => h.elim
  | var _, _ => trivial
  | and _ _, ⟨hf, hg, h⟩ => ⟨hf.dual, hg.dual, by rwa [vars_dual, vars_dual]⟩
  | or _ _, ⟨hf, hg, h⟩ => ⟨hf.dual, hg.dual, by rwa [vars_dual, vars_dual]⟩

theorem empty_notMem_join {A B : HG n} (hA : ∅ ∉ A) : ∅ ∉ join A B := fun h => by
  obtain ⟨e, he, f, -, hef⟩ := mem_join.1 h
  exact hA ((union_eq_empty.1 hef).1 ▸ he)

theorem join_nonempty {A B : HG n} (hA : A.Nonempty) (hB : B.Nonempty) : (join A B).Nonempty := by
  obtain ⟨e, he⟩ := hA; obtain ⟨f, hf⟩ := hB
  exact ⟨e ∪ f, mem_join.2 ⟨e, he, f, hf, rfl⟩⟩

/-- A read-once DNF is Sperner, nonempty and has no empty edge. -/
theorem dnf_props : ∀ {f : Fm n}, ReadOnce f →
    IsSperner (dnf f) ∧ ∅ ∉ dnf f ∧ (dnf f).Nonempty
  | tt, h | ff, h => h.elim
  | var i, _ => ⟨fun e he f hf _ => by rw [mem_singleton.1 he, mem_singleton.1 hf],
      by simp [dnf], by simp [dnf]⟩
  | and f g, ⟨hf, hg, hd⟩ =>
    have pf := dnf_props hf; have pg := dnf_props hg
    ⟨join_isSperner_of_disjoint hd (dnf_within f) (dnf_within g) pf.1 pg.1,
      empty_notMem_join pf.2.1, join_nonempty pf.2.2 pg.2.2⟩
  | or f g, ⟨hf, hg, hd⟩ =>
    have pf := dnf_props hf; have pg := dnf_props hg
    ⟨union_isSperner_of_disjoint hd (dnf_within f) (dnf_within g) pf.1 pg.1 pf.2.1 pg.2.1,
      by simp [dnf, pf.2.1, pg.2.1], pf.2.2.mono subset_union_left⟩

/-- **`Tr(dnf f) = dnf(f^d)`** for a read-once formula: `(dnf f, dnf f^d)` is a dual pair. -/
theorem tr_dnf_readOnce {f : Fm n} (hf : ReadOnce f) : tr univ (dnf f) = dnf (dual f) := by
  rw [tr_dnf, minimal_eq_self (dnf_props hf.dual).1]

/-! ### Read-once formulas are read-once hypergraphs (one direction of Gurvich's theorem) -/

theorem support_dnf : ∀ {f : Fm n}, ReadOnce f → support (dnf f) = vars f
  | tt, h | ff, h => h.elim
  | var i, _ => by ext u; simp [mem_support, dnf, vars]
  | and f g, ⟨hf, hg, _⟩ => by
    rw [dnf, support_join (dnf_props hf).2.2 (dnf_props hg).2.2, support_dnf hf, support_dnf hg]
    rfl
  | or f g, ⟨hf, hg, _⟩ => by rw [dnf, support_union, support_dnf hf, support_dnf hg]; rfl

theorem _root_.HD.IsCograph.congr {α : Type*} [DecidableEq α] {R R' : α → α → Prop}
    {A : Finset α} (h : IsCograph R A) (hR : ∀ a ∈ A, ∀ b ∈ A, R a b ↔ R' a b) :
    IsCograph R' A := by
  revert hR
  induction h with
  | single v => exact fun _ => .single v
  | union A B hd _ _ hno ihA ihB =>
    intro hR
    exact .union A B hd (ihA fun a ha b hb => hR a (mem_union_left _ ha) b (mem_union_left _ hb))
      (ihB fun a ha b hb => hR a (mem_union_right _ ha) b (mem_union_right _ hb))
      fun a ha b hb h => hno a ha b hb ((hR a (mem_union_left _ ha) b (mem_union_right _ hb)).2 h)
  | join A B hd _ _ hj ihA ihB =>
    intro hR
    exact .join A B hd (ihA fun a ha b hb => hR a (mem_union_left _ ha) b (mem_union_left _ hb))
      (ihB fun a ha b hb => hR a (mem_union_right _ ha) b (mem_union_right _ hb))
      fun a ha b hb => (hR a (mem_union_left _ ha) b (mem_union_right _ hb)).1 (hj a ha b hb)

theorem join_comm (A B : HG n) : join A B = join B A := by
  ext s; simp only [mem_join]
  constructor <;> rintro ⟨e, he, f, hf, rfl⟩ <;> exact ⟨f, hf, e, he, union_comm _ _⟩

/-- Inside the left part of an OR on disjoint supports, the primal graph is the left input's. -/
theorem primalAdj_union_left {V W : Finset (Fin n)} (hd : Disjoint V W) {A B : HG n}
    (hB : Within W B) {a b : Fin n} (ha : a ∈ V) : primalAdj (A ∪ B) a b ↔ primalAdj A a b := by
  rw [primalAdj_union]
  exact ⟨fun h => h.resolve_right fun ⟨_, e, he, hae, _⟩ => disjoint_left.1 hd ha (hB e he hae),
    Or.inl⟩

/-- Inside the left part of an AND on disjoint supports, the primal graph is the left input's. -/
theorem primalAdj_join_left {V W : Finset (Fin n)} (hd : Disjoint V W) {A B : HG n}
    (hA : Within V A) (hB : Within W B) (nA : A.Nonempty) (nB : B.Nonempty) {a b : Fin n}
    (ha : a ∈ V) (hb : b ∈ V) : primalAdj (join A B) a b ↔ primalAdj A a b := by
  rw [primalAdj_join hd hA hB nA nB]
  have out : ∀ {u}, u ∈ V → u ∈ support B → False := fun hu h =>
    disjoint_left.1 hd hu (support_subset_of_within hB h)
  refine ⟨fun h => ?_, Or.inl⟩
  rcases h with h | ⟨_, e, he, hae, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · exact (out ha (mem_support.2 ⟨e, he, hae⟩)).elim
  · exact (out hb h).elim
  · exact (out ha h).elim

theorem cograph_dnf : ∀ {f : Fm n}, ReadOnce f → IsCograph (primalAdj (dnf f)) (vars f)
  | tt, h | ff, h => h.elim
  | var i, _ => .single i
  | or f g, ⟨hf, hg, hd⟩ => by
    have wf := dnf_within f; have wg := dnf_within g
    refine .union _ _ hd ((cograph_dnf hf).congr fun a ha b _ => ?_)
      ((cograph_dnf hg).congr fun a ha b _ => ?_) fun a ha b hb h => ?_
    · exact (primalAdj_union_left hd wg ha).symm
    · show _ ↔ primalAdj (dnf f ∪ dnf g) a b
      rw [union_comm]; exact (primalAdj_union_left hd.symm wf ha).symm
    · rcases primalAdj_union.1 h with ⟨_, e, he, _, hbe⟩ | ⟨_, e, he, hae, _⟩
      · exact disjoint_left.1 hd (wf e he hbe) hb
      · exact disjoint_left.1 hd ha (wg e he hae)
  | and f g, ⟨hf, hg, hd⟩ => by
    have wf := dnf_within f; have wg := dnf_within g
    have nf := (dnf_props hf).2.2; have ng := (dnf_props hg).2.2
    refine .join _ _ hd ((cograph_dnf hf).congr fun a ha b hb => ?_)
      ((cograph_dnf hg).congr fun a ha b hb => ?_) fun a ha b hb => ?_
    · exact (primalAdj_join_left hd wf wg nf ng ha hb).symm
    · show _ ↔ primalAdj (join (dnf f) (dnf g)) a b
      rw [join_comm]; exact (primalAdj_join_left hd.symm wg wf ng nf ha hb).symm
    · show primalAdj (join (dnf f) (dnf g)) a b
      rw [primalAdj_join hd wf wg nf ng]
      exact Or.inr (Or.inr (Or.inl ⟨support_dnf hf ▸ ha, support_dnf hg ▸ hb⟩))

theorem conformal_dnf : ∀ {f : Fm n}, ReadOnce f → ∀ S : Finset (Fin n), S.Nonempty →
    S ⊆ vars f → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → primalAdj (dnf f) u v) → ∃ e ∈ dnf f, S ⊆ e
  | tt, h | ff, h => h.elim
  | var i, _ => fun S _ hS _ => ⟨{i}, mem_singleton_self _, hS⟩
  | or f g, ⟨hf, hg, hd⟩ => fun S ⟨u, hu⟩ hS hc => by
    have wf := dnf_within f; have wg := dnf_within g
    -- a clique of an OR on disjoint supports lies in one part
    have side : ∀ {V W : Finset (Fin n)} {A B : HG n}, Disjoint V W → Within V A → Within W B →
        u ∈ V → (∀ v ∈ S, v ≠ u → primalAdj (A ∪ B) u v) → S ⊆ V := by
      intro V W A B hVW hA hB huV hc' v hv
      by_cases hvu : v = u
      · exact hvu ▸ huV
      rcases primalAdj_union.1 (hc' v hv hvu) with ⟨_, e, he, _, hve⟩ | ⟨_, e, he, hue, _⟩
      · exact hA e he hve
      · exact absurd (hB e he hue) (disjoint_left.1 hVW huV)
    rcases mem_union.1 (hS hu) with huf | hug
    · have hSf := side hd wf wg huf fun v hv hvu => hc u hu v hv (Ne.symm hvu)
      obtain ⟨e, he, hSe⟩ := conformal_dnf hf S ⟨u, hu⟩ hSf fun a ha b hb hab =>
        (primalAdj_union_left hd wg (hSf ha)).1 (hc a ha b hb hab)
      exact ⟨e, mem_union_left _ he, hSe⟩
    · have hSg := side hd.symm wg wf hug fun v hv hvu => by
        rw [union_comm]; exact hc u hu v hv (Ne.symm hvu)
      obtain ⟨e, he, hSe⟩ := conformal_dnf hg S ⟨u, hu⟩ hSg fun a ha b hb hab => by
        have : primalAdj (dnf f ∪ dnf g) a b := hc a ha b hb hab
        rw [union_comm] at this
        exact (primalAdj_union_left hd.symm wf (hSg ha)).1 this
      exact ⟨e, mem_union_right _ he, hSe⟩
  | and f g, ⟨hf, hg, hd⟩ => fun S _ hS hc => by
    have wf := dnf_within f; have wg := dnf_within g
    have nf := (dnf_props hf).2.2; have ng := (dnf_props hg).2.2
    -- the two parts of a clique of an AND are cliques of the inputs, each inside an edge
    have part : ∀ {V : Finset (Fin n)} {A : HG n}, A.Nonempty →
        (∀ T : Finset (Fin n), T.Nonempty → T ⊆ V →
          (∀ u ∈ T, ∀ v ∈ T, u ≠ v → primalAdj A u v) → ∃ e ∈ A, T ⊆ e) →
        (∀ a ∈ S.filter (· ∈ V), ∀ b ∈ S.filter (· ∈ V), a ≠ b → primalAdj A a b) →
          ∃ e ∈ A, S.filter (· ∈ V) ⊆ e := by
      intro V A nA ih hc'
      by_cases hne : (S.filter (· ∈ V)).Nonempty
      · exact ih _ hne (fun x hx => (mem_filter.1 hx).2) hc'
      · obtain ⟨e, he⟩ := nA
        exact ⟨e, he, by rw [not_nonempty_iff_eq_empty.1 hne]; exact empty_subset _⟩
    obtain ⟨e, he, hSe⟩ := part nf (conformal_dnf hf) fun a ha b hb hab =>
      (primalAdj_join_left hd wf wg nf ng (mem_filter.1 ha).2 (mem_filter.1 hb).2).1
        (hc a (mem_filter.1 ha).1 b (mem_filter.1 hb).1 hab)
    obtain ⟨e', he', hSe'⟩ := part ng (conformal_dnf hg) fun a ha b hb hab => by
      have : primalAdj (join (dnf f) (dnf g)) a b := hc a (mem_filter.1 ha).1 b (mem_filter.1 hb).1 hab
      rw [join_comm] at this
      exact (primalAdj_join_left hd.symm wg wf ng nf (mem_filter.1 ha).2 (mem_filter.1 hb).2).1 this
    refine ⟨e ∪ e', mem_join.2 ⟨e, he, e', he', rfl⟩, fun x hx => ?_⟩
    rcases mem_union.1 (hS hx) with h | h
    · exact mem_union_left _ (hSe (mem_filter.2 ⟨hx, h⟩))
    · exact mem_union_right _ (hSe' (mem_filter.2 ⟨hx, h⟩))

/-- **A read-once formula on all of `Fin n` has a read-once DNF** in the sense of `HD.ReadOnce`
(Sperner, conformal, cograph primal graph): the easy direction of Gurvich's characterisation. -/
theorem readOnce_dnf {f : Fm n} (hf : ReadOnce f) (hv : vars f = univ) : HD.ReadOnce (dnf f) :=
  ⟨(dnf_props hf).1, fun S hS hc => conformal_dnf hf S hS (hv ▸ subset_univ S) hc,
    hv ▸ cograph_dnf hf⟩

/-! ### The leftmost states -/

/-- The restrictions of `f` that the leftmost rule reaches, as DNFs: a state of a gate is a state
of its left input combined with the whole right input, or a state of the right input. -/
def St : Fm n → Finset (HG n)
  | tt => ∅
  | ff => ∅
  | var i => {{{i}}}
  | and f g => (St f).image (fun A => join A (dnf g)) ∪ St g
  | or f g => (St f).image (fun A => A ∪ dnf g) ∪ St g

/-- The states together with the two constants. -/
def Kst (f : Fm n) : Finset (HG n) := St f ∪ {∅, {∅}}

theorem card_St_le : ∀ {f : Fm n}, Ordered f → (St f).card ≤ (vars f).card
  | tt, h | ff, h => h.elim
  | var i, _ => by simp [St, vars]
  | and f g, ⟨hf, hg, h⟩ => by
    simp only [St, vars, card_union_of_disjoint (disjoint_of_lt h)]
    exact (card_union_le _ _).trans (add_le_add (card_image_le.trans (card_St_le hf))
      (card_St_le hg))
  | or f g, ⟨hf, hg, h⟩ => by
    simp only [St, vars, card_union_of_disjoint (disjoint_of_lt h)]
    exact (card_union_le _ _).trans (add_le_add (card_image_le.trans (card_St_le hf))
      (card_St_le hg))

theorem dnf_mem_St : ∀ {f : Fm n}, Ordered f → dnf f ∈ St f
  | tt, h | ff, h => h.elim
  | var _, _ => mem_singleton_self _
  | and _ _, ⟨hf, _, _⟩ => mem_union_left _ (mem_image_of_mem _ (dnf_mem_St hf))
  | or _ _, ⟨hf, _, _⟩ => mem_union_left _ (mem_image_of_mem _ (dnf_mem_St hf))

/-- A state is Sperner, nonempty, without the empty edge, inside `vars f`. -/
theorem St_props : ∀ {f : Fm n}, Ordered f → ∀ A ∈ St f,
    IsSperner A ∧ ∅ ∉ A ∧ A.Nonempty ∧ Within (vars f) A
  | tt, h | ff, h => h.elim
  | var i, _ => fun A hA => by
    rw [St, mem_singleton] at hA; subst hA
    exact ⟨fun e he f hf _ => by rw [mem_singleton.1 he, mem_singleton.1 hf],
      by simp, by simp, fun e he => by simp_all [vars]⟩
  | and f g, ⟨hf, hg, h⟩ => fun A hA => by
    have hd := disjoint_of_lt h
    rcases mem_union.1 hA with hA | hA
    · obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
      obtain ⟨s1, e1, n1, w1⟩ := St_props hf A' hA'
      obtain ⟨s2, e2, n2, w2⟩ := St_props hg _ (dnf_mem_St hg)
      exact ⟨join_isSperner_of_disjoint hd w1 w2 s1 s2, empty_notMem_join e1, join_nonempty n1 n2,
        join_within (within_mono w1 subset_union_left) (within_mono w2 subset_union_right)⟩
    · obtain ⟨s, e, ne, w⟩ := St_props hg A hA
      exact ⟨s, e, ne, within_mono w subset_union_right⟩
  | or f g, ⟨hf, hg, h⟩ => fun A hA => by
    have hd := disjoint_of_lt h
    rcases mem_union.1 hA with hA | hA
    · obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
      obtain ⟨s1, e1, n1, w1⟩ := St_props hf A' hA'
      obtain ⟨s2, e2, n2, w2⟩ := St_props hg _ (dnf_mem_St hg)
      refine ⟨union_isSperner_of_disjoint hd w1 w2 s1 s2 e1 e2, by simp [e1, e2],
        n1.mono subset_union_left, fun e he => ?_⟩
      rcases mem_union.1 he with he | he
      · exact (w1 e he).trans subset_union_left
      · exact (w2 e he).trans subset_union_right
    · obtain ⟨s, e, ne, w⟩ := St_props hg A hA
      exact ⟨s, e, ne, within_mono w subset_union_right⟩

theorem St_sub_Kst {f : Fm n} : St f ⊆ Kst f := subset_union_left

theorem empty_mem_Kst (f : Fm n) : (∅ : HG n) ∈ Kst f := mem_union_right _ (by simp)

theorem unit_mem_Kst (f : Fm n) : ({∅} : HG n) ∈ Kst f := mem_union_right _ (by simp)

theorem mem_Kst {f : Fm n} {A : HG n} : A ∈ Kst f ↔ A ∈ St f ∨ A = ∅ ∨ A = {∅} := by
  simp only [Kst, mem_union, mem_insert, mem_singleton]

/-- Restricting a constant gives a constant. -/
theorem const_restrict {A : HG n} (hA : A = ∅ ∨ A = {∅}) (x : Fin n) :
    (del A x = ∅ ∨ del A x = {∅}) ∧ (minimal (con A x) = ∅ ∨ minimal (con A x) = {∅}) := by
  rcases hA with rfl | rfl
  · simp [del, con, minimal]
  · refine ⟨Or.inr (by simp [del]), Or.inr ?_⟩
    simp [con, minimal_eq_self isSperner_unit]

/-- **Closure.** Splitting a state at its least vertex gives a state or a constant. -/
theorem St_closed : ∀ {f : Fm n}, Ordered f → ∀ A ∈ St f, ∀ x ∈ support A,
    (∀ y ∈ support A, x ≤ y) → del A x ∈ Kst f ∧ minimal (con A x) ∈ Kst f
  | tt, h | ff, h => h.elim
  | var i, _ => fun A hA x hx _ => by
    rw [St, mem_singleton] at hA; subst hA
    have : x = i := by simpa [mem_support] using hx
    subst this
    refine ⟨?_, ?_⟩
    · rw [show del ({{x}} : HG n) x = ∅ by simp [del]]; exact empty_mem_Kst _
    · rw [show minimal (con ({{x}} : HG n) x) = {∅} by
        simp [con, minimal_eq_self isSperner_unit]]
      exact unit_mem_Kst _
  | and f g, ⟨hf, hg, h⟩ => fun A hA x hx hmin => by
    have Kg : Kst g ⊆ Kst (and f g) := union_subset_union subset_union_right subset_rfl
    rcases mem_union.1 hA with hA | hA
    · obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
      obtain ⟨s1, e1, n1, w1⟩ := St_props hf A' hA'
      obtain ⟨s2, e2, n2, w2⟩ := St_props hg _ (dnf_mem_St hg)
      have hsupp := support_join n1 n2
      -- the least vertex lies in the left input
      obtain ⟨y₀, hy₀⟩ := support_nonempty n1 e1
      have hxA : x ∈ support A' := by
        rw [hsupp] at hx
        rcases mem_union.1 hx with hx | hx
        · exact hx
        · exact absurd (hmin y₀ (by rw [hsupp]; exact mem_union_left _ hy₀))
            (not_le.2 (h _ (support_subset_of_within w1 hy₀) _ (support_subset_of_within w2 hx)))
      have hmin' : ∀ y ∈ support A', x ≤ y := fun y hy =>
        hmin y (by rw [hsupp]; exact mem_union_left _ hy)
      have hxg : x ∉ support (dnf g) := fun hx' =>
        disjoint_left.1 (disjoint_of_lt h) (support_subset_of_within w1 hxA)
          (support_subset_of_within w2 hx')
      obtain ⟨ihd, ihc⟩ := St_closed hf A' hA' x hxA hmin'
      have hjoin : ∀ K ∈ Kst f, minimal (join K (dnf g)) ∈ Kst (and f g) := fun K hK => by
        rcases mem_Kst.1 hK with hK | rfl | rfl
        · obtain ⟨sK, -, -, wK⟩ := St_props hf K hK
          rw [minimal_eq_self (join_isSperner_of_disjoint (disjoint_of_lt h) wK w2 sK s2)]
          exact St_sub_Kst (mem_union_left _ (mem_image_of_mem _ hK))
        · rw [join_empty_left]; simp [minimal]; exact empty_mem_Kst _
        · rw [join_unit_left, minimal_eq_self s2]; exact Kg (St_sub_Kst (dnf_mem_St hg))
      refine ⟨?_, ?_⟩
      · rw [del_join, del_of_notMem hxg]
        have := hjoin _ ihd
        rwa [minimal_eq_self] at this
        rcases mem_Kst.1 ihd with hK | hK | hK
        · exact join_isSperner_of_disjoint (disjoint_of_lt h) (St_props hf _ hK).2.2.2 w2
            (St_props hf _ hK).1 s2
        · rw [hK, join_empty_left]; exact isSperner_empty
        · rw [hK, join_unit_left]; exact s2
      · rw [con_join, con_of_notMem hxg]
        have : minimal (join (con A' x) (dnf g)) = minimal (join (minimal (con A' x)) (dnf g)) :=
          minimal_congr fun S => by rw [upHit_join, upHit_join, upHit_minimal]
        rw [this]; exact hjoin _ ihc
    · exact ⟨Kg (St_closed hg A hA x hx hmin).1, Kg (St_closed hg A hA x hx hmin).2⟩
  | or f g, ⟨hf, hg, h⟩ => fun A hA x hx hmin => by
    have Kg : Kst g ⊆ Kst (or f g) := union_subset_union subset_union_right subset_rfl
    rcases mem_union.1 hA with hA | hA
    · obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
      obtain ⟨s1, e1, n1, w1⟩ := St_props hf A' hA'
      obtain ⟨s2, e2, n2, w2⟩ := St_props hg _ (dnf_mem_St hg)
      have hsupp := support_union A' (dnf g)
      obtain ⟨y₀, hy₀⟩ := support_nonempty n1 e1
      have hxA : x ∈ support A' := by
        rw [hsupp] at hx
        rcases mem_union.1 hx with hx | hx
        · exact hx
        · exact absurd (hmin y₀ (by rw [hsupp]; exact mem_union_left _ hy₀))
            (not_le.2 (h _ (support_subset_of_within w1 hy₀) _ (support_subset_of_within w2 hx)))
      have hmin' : ∀ y ∈ support A', x ≤ y := fun y hy =>
        hmin y (by rw [hsupp]; exact mem_union_left _ hy)
      have hxg : x ∉ support (dnf g) := fun hx' =>
        disjoint_left.1 (disjoint_of_lt h) (support_subset_of_within w1 hxA)
          (support_subset_of_within w2 hx')
      obtain ⟨ihd, ihc⟩ := St_closed hf A' hA' x hxA hmin'
      refine ⟨?_, ?_⟩
      · rw [del_union, del_of_notMem hxg]
        rcases mem_Kst.1 ihd with hK | hK | hK
        · exact St_sub_Kst (mem_union_left _ (mem_image_of_mem _ hK))
        · rw [hK, empty_union]; exact Kg (St_sub_Kst (dnf_mem_St hg))
        · exact absurd (filter_subset _ A' (hK ▸ mem_singleton_self ∅ : ∅ ∈ del A' x)) e1
      · rw [con_union, con_of_notMem hxg]
        have : minimal (con A' x ∪ dnf g) = minimal (minimal (con A' x) ∪ dnf g) :=
          minimal_congr fun S => by rw [upHit_union, upHit_union, upHit_minimal]
        rw [this]
        rcases mem_Kst.1 ihc with hK | hK | hK
        · obtain ⟨sK, eK, -, wK⟩ := St_props hf _ hK
          rw [minimal_eq_self (union_isSperner_of_disjoint (disjoint_of_lt h) wK w2 sK s2 eK e2)]
          exact St_sub_Kst (mem_union_left _ (mem_image_of_mem _ hK))
        · rw [hK, empty_union, minimal_eq_self s2]; exact Kg (St_sub_Kst (dnf_mem_St hg))
        · rw [hK, minimal_of_empty_mem (mem_union_left _ (mem_singleton_self ∅))]
          exact unit_mem_Kst _
    · exact ⟨Kg (St_closed hg A hA x hx hmin).1, Kg (St_closed hg A hA x hx hmin).2⟩

/-- The states and constants are closed under the leftmost rule. -/
theorem leftRule_closed {f : Fm n} (hf : Ordered f) : Closed leftRule (Kst f) := by
  intro A hA
  rcases mem_Kst.1 hA with hA | hc
  · obtain ⟨sA, -, -, -⟩ := St_props hf A hA
    refine ⟨sA, fun x hx => ?_⟩
    have hs : support (tr univ A) = support A := (support_eq (within_univ A) sA rfl).symm
    simp only [leftRule, hs, union_self] at hx
    split_ifs at hx with hne
    cases hx
    exact St_closed hf A hA _ (min'_mem _ hne) fun y hy => min'_le _ y hy
  · refine ⟨by rcases hc with rfl | rfl; exacts [isSperner_empty, isSperner_unit], fun x _ => ?_⟩
    obtain ⟨hd, hc'⟩ := const_restrict hc x
    exact ⟨by rcases hd with h | h <;> rw [h]; exacts [empty_mem_Kst f, unit_mem_Kst f],
      by rcases hc' with h | h <;> rw [h]; exacts [empty_mem_Kst f, unit_mem_Kst f]⟩

theorem pairs_union (𝒮 𝒯 : Finset (HG n)) : pairs (𝒮 ∪ 𝒯) = pairs 𝒮 ∪ pairs 𝒯 := by
  simp only [pairs, image_union]
  ext p; simp only [mem_union]; tauto

/-- The constants give two pairs, `(∅, {∅})` and `({∅}, ∅)`. -/
theorem card_pairs_const : (pairs ({∅, {∅}} : Finset (HG n))).card ≤ 2 := by
  have h : pairs ({∅, {∅}} : Finset (HG n)) = {(∅, {∅}), ({∅}, ∅)} := by
    rw [pairs, image_insert, image_insert, image_singleton, image_singleton, tr_empty_hg,
      tr_unit_hg]
    ext p; simp only [mem_union, mem_insert, mem_singleton]; tauto
  rw [h]; exact (card_insert_le _ _).trans (by rw [card_singleton])
/-- **Theorem 4.16** (Hertel, Thm 4.4.1). On a read-once formula with leaves numbered left to
right, FK-A under the leftmost rule has at most `2·|vars f| + 2` distinct subproblems. -/
theorem leftmost_delta {f : Fm n} (hf : Ordered f) (fuel : ℕ) (b : Bool) :
    (fkADagR leftRule fuel b (dnf f) (dnf (dual f))).card ≤ 2 * (vars f).card + 2 := by
  rw [← tr_dnf_readOnce hf.readOnce]
  have hsub := (fkADagR_closed leftRule_symm (leftRule_closed hf) fuel b (dnf f)
    (St_sub_Kst (dnf_mem_St hf))).1
  calc _ ≤ (pairs (Kst f)).card := card_le_card hsub
    _ ≤ (pairs (St f)).card + 2 := by
      rw [Kst, pairs_union]
      have h1 := card_union_le (pairs (St f)) (pairs ({∅, {∅}} : Finset (HG n)))
      have h2 := card_pairs_const (n := n)
      omega
    _ ≤ 2 * (St f).card + 2 := by have := card_pairs_le (St f); omega
    _ ≤ _ := by have := card_St_le hf; omega

theorem leftmost_delta_le {f : Fm n} (hf : Ordered f) (fuel : ℕ) (b : Bool) :
    (fkADagR leftRule fuel b (dnf f) (dnf (dual f))).card ≤ 2 * n + 2 := by
  have := (leftmost_delta hf fuel b).trans (by
    have := card_le_univ (vars f); simp only [Fintype.card_fin] at this; omega :
      2 * (vars f).card + 2 ≤ 2 * n + 2)
  exact this

/-! ### Minors of a gate (interleaving) and Remark 4.12 -/

/-- **Interleaving, OR gate.** A minor of `A ∪ B` is, as a function, `A' ∪ B'` for minors `A'` of
`A` and `B'` of `B`: the same restriction acts on each input. -/
theorem minor_union {A B : HG n} {k : ℕ} {H : HG n} (h : Minor (A ∪ B) k H) :
    ∃ i A', Minor A i A' ∧ ∃ j B', Minor B j B' ∧ ∀ S, upHit H S ↔ upHit (A' ∪ B') S := by
  induction h with
  | refl => exact ⟨0, A, .refl, 0, B, .refl, fun S => Iff.rfl⟩
  | del x _ ih =>
    obtain ⟨i, A', hA, j, B', hB, hS⟩ := ih
    exact ⟨i + 1, del A' x, .del x hA, j + 1, del B' x, .del x hB, fun S => by
      rw [upHit_del, hS, upHit_union, upHit_union, upHit_del, upHit_del]⟩
  | con x _ ih =>
    obtain ⟨i, A', hA, j, B', hB, hS⟩ := ih
    exact ⟨i + 1, con A' x, .con x hA, j + 1, con B' x, .con x hB, fun S => by
      rw [upHit_con, hS, upHit_union, upHit_union, upHit_con, upHit_con]⟩
  | min _ ih =>
    obtain ⟨i, A', hA, j, B', hB, hS⟩ := ih
    exact ⟨i, A', hA, j, B', hB, fun S => by rw [upHit_minimal, hS]⟩

/-- **Interleaving, AND gate.** A minor of `A ∧ B` is, as a function, `A' ∧ B'`. -/
theorem minor_join {A B : HG n} {k : ℕ} {H : HG n} (h : Minor (join A B) k H) :
    ∃ i A', Minor A i A' ∧ ∃ j B', Minor B j B' ∧ ∀ S, upHit H S ↔ upHit (join A' B') S := by
  induction h with
  | refl => exact ⟨0, A, .refl, 0, B, .refl, fun S => Iff.rfl⟩
  | del x _ ih =>
    obtain ⟨i, A', hA, j, B', hB, hS⟩ := ih
    exact ⟨i + 1, del A' x, .del x hA, j + 1, del B' x, .del x hB, fun S => by
      rw [upHit_del, hS, upHit_join, upHit_join, upHit_del, upHit_del]⟩
  | con x _ ih =>
    obtain ⟨i, A', hA, j, B', hB, hS⟩ := ih
    exact ⟨i + 1, con A' x, .con x hA, j + 1, con B' x, .con x hB, fun S => by
      rw [upHit_con, hS, upHit_join, upHit_join, upHit_con, upHit_con]⟩
  | min _ ih =>
    obtain ⟨i, A', hA, j, B', hB, hS⟩ := ih
    exact ⟨i, A', hA, j, B', hB, fun S => by rw [upHit_minimal, hS]⟩

/-- On disjoint supports the OR of two states determines them: `A₀ = (A₀ ∪ B₀) ∩ 2^V`. -/
theorem union_left_part {V W : Finset (Fin n)} (hVW : Disjoint V W) {A₀ B₀ : HG n}
    (hA : Within V A₀) (hB : Within W B₀) (eB : ∅ ∉ B₀) : (A₀ ∪ B₀).filter (· ⊆ V) = A₀ := by
  ext e
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨he | he, heV⟩
    · exact he
    · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 (fun h => eB (h ▸ he))
      exact absurd (hB e he hx) (disjoint_left.1 hVW (heV hx))
  · exact fun he => ⟨Or.inl he, hA e he⟩

/-- On disjoint supports the AND of two states determines them: `A₀ = {e ∩ V : e ∈ A₀ ∧ B₀}`. -/
theorem join_left_part {V W : Finset (Fin n)} (hVW : Disjoint V W) {A₀ B₀ : HG n}
    (hA : Within V A₀) (hB : Within W B₀) (nB : B₀.Nonempty) : (join A₀ B₀).image (· ∩ V) = A₀ := by
  have key : ∀ e ∈ A₀, ∀ f ∈ B₀, (e ∪ f) ∩ V = e := fun e he f hf => by
    rw [union_inter_distrib_right, inter_eq_left.2 (hA e he),
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (hB f hf) hVW.symm), union_empty]
  ext e
  simp only [mem_image, mem_join]
  constructor
  · rintro ⟨_, ⟨e', he', f, hf, rfl⟩, rfl⟩; rw [key e' he' f hf]; exact he'
  · intro he
    obtain ⟨f, hf⟩ := nB
    exact ⟨e ∪ f, ⟨e, he, f, hf, rfl⟩, key e he f hf⟩

theorem _root_.HD.Minor.within {G H : HG n} {k : ℕ} {V : Finset (Fin n)} (h : Minor G k H)
    (hG : Within V G) : Within V H := by
  induction h with
  | refl => exact hG
  | del x _ ih => exact within_del ih x
  | con x _ ih => exact within_con ih x
  | min _ ih => exact within_minimal ih

/-- A Sperner family with empty support is a constant. -/
theorem const_of_support_empty {K : HG n} (h : support K = ∅) : K = ∅ ∨ K = {∅} := by
  refine subset_singleton_iff.1 fun e he => mem_singleton.2 ?_
  exact eq_empty_of_forall_notMem fun x hx => by
    have : x ∈ support K := mem_support.2 ⟨e, he, hx⟩
    rw [h] at this; exact notMem_empty x this

/-- Supports split along disjoint parts. -/
theorem support_parts {V W : Finset (Fin n)} (hVW : Disjoint V W) {A B A' B' : HG n}
    (hA : Within V A) (hB : Within W B) (hA' : Within V A') (hB' : Within W B')
    (h : support A ∪ support B = support A' ∪ support B') :
    support A = support A' ∧ support B = support B' := by
  have sA := support_subset_of_within hA; have sB := support_subset_of_within hB
  have sA' := support_subset_of_within hA'; have sB' := support_subset_of_within hB'
  have hl : ∀ x, x ∈ support A ↔ x ∈ support A ∪ support B ∧ x ∈ V := fun x =>
    ⟨fun hx => ⟨mem_union_left _ hx, sA hx⟩, fun ⟨hx, hV⟩ => (mem_union.1 hx).resolve_right
      fun hB => disjoint_left.1 hVW hV (sB hB)⟩
  have hl' : ∀ x, x ∈ support A' ↔ x ∈ support A' ∪ support B' ∧ x ∈ V := fun x =>
    ⟨fun hx => ⟨mem_union_left _ hx, sA' hx⟩, fun ⟨hx, hV⟩ => (mem_union.1 hx).resolve_right
      fun hB => disjoint_left.1 hVW hV (sB' hB)⟩
  have hr : ∀ x, x ∈ support B ↔ x ∈ support A ∪ support B ∧ x ∈ W := fun x =>
    ⟨fun hx => ⟨mem_union_right _ hx, sB hx⟩, fun ⟨hx, hW⟩ => (mem_union.1 hx).resolve_left
      fun hA => disjoint_left.1 hVW (sA hA) hW⟩
  have hr' : ∀ x, x ∈ support B' ↔ x ∈ support A' ∪ support B' ∧ x ∈ W := fun x =>
    ⟨fun hx => ⟨mem_union_right _ hx, sB' hx⟩, fun ⟨hx, hW⟩ => (mem_union.1 hx).resolve_left
      fun hA => disjoint_left.1 hVW (sA' hA) hW⟩
  exact ⟨ext fun x => by rw [hl, hl', h], ext fun x => by rw [hr, hr', h]⟩

/-- The reduced minors of `dnf f`: the distinct nonconstant-or-constant subfunctions `f|ρ`. -/
def RMinor (f : Fm n) (K : HG n) : Prop := ∃ k H, Minor (dnf f) k H ∧ minimal H = K

theorem RMinor.within {f : Fm n} {K : HG n} (h : RMinor f K) : Within (vars f) K := by
  obtain ⟨k, H, hH, rfl⟩ := h; exact within_minimal (hH.within (dnf_within f))

/-- Two families with the same support are equal if they are for nonempty support and, for
empty support (the constants), both or neither are `∅`. -/
theorem eq_of_support_eq {P Q : HG n} (hro : support P = support Q → (support P).Nonempty → P = Q)
    (hPQ : support P = support Q) (hc : support P = ∅ → (P = ∅ ↔ Q = ∅)) : P = Q := by
  by_cases hne : (support P).Nonempty
  · exact hro hPQ hne
  have h0 := not_nonempty_iff_eq_empty.1 hne
  rcases const_of_support_empty h0 with e1 | e1 <;>
    rcases const_of_support_empty (hPQ ▸ h0) with e2 | e2
  · rw [e1, e2]
  · exact absurd ((hc h0).1 e1) (by rw [e2]; simp)
  · exact absurd ((hc h0).2 e2) (by rw [e1]; simp)
  · rw [e1, e2]

/-- **Remark 4.12.** A restriction of a read-once formula with nonempty support is determined by
its support: two reduced minors with the same nonempty support are equal. -/
theorem rminor_determined : ∀ {f : Fm n}, ReadOnce f → ∀ {K K' : HG n}, RMinor f K → RMinor f K' →
    support K = support K' → (support K).Nonempty → K = K'
  | tt, h | ff, h => h.elim
  | var i, _ => by
    -- a Sperner family inside `{i}` with nonempty support is `{{i}}`
    have key : ∀ {K}, RMinor (var i : Fm n) K → (support K).Nonempty → K = {{i}} := by
      rintro K ⟨k, H, hH, rfl⟩ ⟨x, hx⟩
      have w := within_minimal (hH.within (dnf_within (var i)))
      obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      have hei : e = {i} := by
        have := w e he; simp only [vars] at this
        exact (subset_singleton_iff.1 this).resolve_left (ne_empty_of_mem hxe)
      subst hei
      refine eq_singleton_iff_unique_mem.2 ⟨he, fun e' he' => ?_⟩
      have := w e' he'; simp only [vars] at this
      rcases subset_singleton_iff.1 this with rfl | rfl
      · exact absurd (minimal_isSperner H _ he' _ he (empty_subset _)) (by simp)
      · rfl
    intro hK hK' hs hne
    rw [key hK hne, key hK' (hs ▸ hne)]
  | and f g, ⟨hf, hg, hd⟩ => by
    -- `K = A₀ ∧ B₀` with `A₀, B₀` reduced minors of the inputs
    have dec : ∀ {K}, RMinor (and f g) K → (support K).Nonempty → ∃ A₀ B₀, RMinor f A₀ ∧
        RMinor g B₀ ∧ A₀ ≠ ∅ ∧ B₀ ≠ ∅ ∧ K = join A₀ B₀ ∧ support K = support A₀ ∪ support B₀ := by
      rintro K ⟨k, H, hH, rfl⟩ hne
      obtain ⟨i, A', hA, j, B', hB, hS⟩ := minor_join hH
      have wA := within_minimal (hA.within (dnf_within f))
      have wB := within_minimal (hB.within (dnf_within g))
      have hK : minimal H = join (minimal A') (minimal B') := by
        rw [minimal_congr (Y := join (minimal A') (minimal B')) fun S => by
          rw [hS, upHit_join, upHit_join, upHit_minimal, upHit_minimal]]
        exact minimal_eq_self (join_isSperner_of_disjoint hd wA wB (minimal_isSperner _)
          (minimal_isSperner _))
      have nA : minimal A' ≠ ∅ := fun h => by
        rw [hK, h, join_empty_left] at hne; simp [support] at hne
      have nB : minimal B' ≠ ∅ := fun h => by
        rw [hK, h] at hne; simp [support, join] at hne
      exact ⟨_, _, ⟨i, A', hA, rfl⟩, ⟨j, B', hB, rfl⟩, nA, nB, hK, by
        rw [hK, support_join (nonempty_iff_ne_empty.2 nA) (nonempty_iff_ne_empty.2 nB)]⟩
    intro hK hK' hs hne
    obtain ⟨A₀, B₀, rA, rB, nA, nB, rfl, sK⟩ := dec hK hne
    obtain ⟨A₁, B₁, rA', rB', nA', nB', rfl, sK'⟩ := dec hK' (hs ▸ hne)
    obtain ⟨hA, hB⟩ := support_parts hd rA.within rB.within rA'.within rB'.within
      (by rw [← sK, ← sK', hs])
    rw [eq_of_support_eq (rminor_determined hf rA rA') hA (fun _ => iff_of_false nA nA'),
      eq_of_support_eq (rminor_determined hg rB rB') hB (fun _ => iff_of_false nB nB')]
  | or f g, ⟨hf, hg, hd⟩ => by
    have dec : ∀ {K}, RMinor (or f g) K → (support K).Nonempty → ∃ A₀ B₀, RMinor f A₀ ∧
        RMinor g B₀ ∧ ∅ ∉ A₀ ∧ ∅ ∉ B₀ ∧ K = A₀ ∪ B₀ ∧ support K = support A₀ ∪ support B₀ := by
      rintro K ⟨k, H, hH, rfl⟩ hne
      obtain ⟨i, A', hA, j, B', hB, hS⟩ := minor_union hH
      have wA := within_minimal (hA.within (dnf_within f))
      have wB := within_minimal (hB.within (dnf_within g))
      have hU : minimal H = minimal (minimal A' ∪ minimal B') := minimal_congr fun S => by
        rw [hS, upHit_union, upHit_union, upHit_minimal, upHit_minimal]
      have eA : ∅ ∉ minimal A' := fun h0 => by
        rw [hU, minimal_of_empty_mem (mem_union_left _ h0)] at hne; simp [support] at hne
      have eB : ∅ ∉ minimal B' := fun h0 => by
        rw [hU, minimal_of_empty_mem (mem_union_right _ h0)] at hne; simp [support] at hne
      have hK : minimal H = minimal A' ∪ minimal B' := by
        rw [hU, minimal_eq_self (union_isSperner_of_disjoint hd wA wB (minimal_isSperner _)
          (minimal_isSperner _) eA eB)]
      exact ⟨_, _, ⟨i, A', hA, rfl⟩, ⟨j, B', hB, rfl⟩, eA, eB, hK, by rw [hK, support_union]⟩
    intro hK hK' hs hne
    obtain ⟨A₀, B₀, rA, rB, nA, nB, rfl, sK⟩ := dec hK hne
    obtain ⟨A₁, B₁, rA', rB', nA', nB', rfl, sK'⟩ := dec hK' (hs ▸ hne)
    obtain ⟨hA, hB⟩ := support_parts hd rA.within rB.within rA'.within rB'.within
      (by rw [← sK, ← sK', hs])
    have z : ∀ {P : HG n}, ∅ ∉ P → support P = ∅ → P = ∅ := fun nP h0 =>
      (const_of_support_empty h0).resolve_right fun h => nP (h ▸ mem_singleton_self _)
    rw [eq_of_support_eq (rminor_determined hf rA rA') hA
        (fun h0 => iff_of_true (z nA h0) (z nA' (hA ▸ h0))),
      eq_of_support_eq (rminor_determined hg rB rB') hB
        (fun h0 => iff_of_true (z nB h0) (z nB' (hB ▸ h0)))]

/-- Distinct reduced minors of a read-once `f` with nonempty support have distinct supports:
their number is at most the number of supports they use. -/
theorem card_rminor_le {f : Fm n} (hf : ReadOnce f) (𝒦 : Finset (HG n))
    (h𝒦 : ∀ K ∈ 𝒦, RMinor f K ∧ (support K).Nonempty) :
    𝒦.card ≤ (𝒦.image support).card :=
  le_of_eq (card_image_of_injOn fun K hK K' hK' hs =>
    rminor_determined hf (h𝒦 K hK).1 (h𝒦 K' hK').1 hs (h𝒦 K hK).2).symm

end Fm

end HD

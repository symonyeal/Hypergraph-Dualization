/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Degree monotonicity under reduced minors

Deletion and contraction cannot increase any vertex degree. Consequently each degree-sum
key weakly decreases in either FK-A child, including the child that exchanges the sides.
-/
import HypergraphDualization.Dag
import HypergraphDualization.Recursion
import HypergraphDualization.Blowup
import Mathlib.Data.List.FinRange

namespace HD

open Finset

variable {α : Type*} [DecidableEq α]

theorem degree_del_le (G : Finset (Finset α)) (x y : α) :
    degree (del G x) y ≤ degree G y := by
  apply card_le_card
  intro e he
  obtain ⟨he, hy⟩ := mem_filter.1 he
  exact mem_filter.2 ⟨(mem_filter.1 he).1, hy⟩

theorem degree_con_le (G : Finset (Finset α)) (x y : α) :
    degree (con G x) y ≤ degree G y := by
  have h : (con G x).filter (y ∈ ·) ⊆ (G.filter (y ∈ ·)).image (·.erase x) := by
    intro e he
    obtain ⟨he, hy⟩ := mem_filter.1 he
    obtain ⟨f, hf, rfl⟩ := mem_image.1 he
    exact mem_image_of_mem _ (mem_filter.2 ⟨hf, mem_of_mem_erase hy⟩)
  exact (card_le_card h).trans (card_image_le)

theorem degree_minimal_del_le (G : Finset (Finset α)) (x y : α) :
    degree (minimal (del G x)) y ≤ degree G y :=
  (degree_minimal_le _ _).trans (degree_del_le G x y)

theorem degree_minimal_con_le (G : Finset (Finset α)) (x y : α) :
    degree (minimal (con G x)) y ≤ degree G y :=
  (degree_minimal_le _ _).trans (degree_con_le G x y)

/-- Deleting `x` preserves the degree of `y` when no edge contains both. -/
theorem degree_del_eq_of_separate {G : Finset (Finset α)} {x y : α}
    (h : ∀ e ∈ G, y ∈ e → x ∉ e) : degree (del G x) y = degree G y := by
  unfold degree
  congr 1
  ext e
  simp only [del, mem_filter]
  exact ⟨fun ⟨⟨he, _⟩, hy⟩ => ⟨he, hy⟩,
    fun ⟨he, hy⟩ => ⟨⟨he, h e he hy⟩, hy⟩⟩

/-- Erasing one of two vertices that always occur together preserves Spernerness. -/
theorem con_isSperner_of_together {G : Finset (Finset α)} {x y : α}
    (sG : IsSperner G) (hne : x ≠ y) (h : ∀ e ∈ G, x ∈ e ↔ y ∈ e) :
    IsSperner (con G x) := by
  intro e he f hf hsub
  obtain ⟨a, ha, rfl⟩ := mem_image.1 he
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hf
  have hab : a ⊆ b := by
    intro z hz
    by_cases hzx : z = x
    · subst z
      have hy : y ∈ a.erase x := mem_erase.2 ⟨hne.symm, (h a ha).1 hz⟩
      exact (h b hb).2 (mem_of_mem_erase (hsub hy))
    · exact mem_of_mem_erase (hsub (mem_erase.2 ⟨hzx, hz⟩))
  rw [sG a ha b hb hab]

/-- Contracting `x` preserves the degree of a distinct `y` that always accompanies it. -/
theorem degree_con_eq_of_together {G : Finset (Finset α)} {x y : α}
    (hne : x ≠ y) (h : ∀ e ∈ G, y ∈ e → x ∈ e) :
    degree (con G x) y = degree G y := by
  have he : (con G x).filter (y ∈ ·) = (G.filter (y ∈ ·)).image (·.erase x) := by
    ext e
    simp only [con, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hy⟩
      exact ⟨a, ⟨ha, mem_of_mem_erase hy⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hy⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, mem_erase.2 ⟨hne.symm, hy⟩⟩
  unfold degree
  rw [he]
  apply card_image_of_injOn
  intro a ha b hb hab
  have hxa := h a (mem_filter.1 ha).1 (mem_filter.1 ha).2
  have hxb := h b (mem_filter.1 hb).1 (mem_filter.1 hb).2
  have heq := congrArg (insert x) hab
  simpa [insert_erase hxa, insert_erase hxb] using heq

variable {n : ℕ}

theorem key_left_child_le (C D : HG n) (x y : Fin n) :
    key (minimal (del C x)) (minimal (con D x)) y ≤ key C D y :=
  Nat.add_le_add (degree_minimal_del_le C x y) (degree_minimal_con_le D x y)

theorem key_right_child_le (C D : HG n) (x y : Fin n) :
    key (minimal (del D x)) (minimal (con C x)) y ≤ key C D y := by
  unfold key
  simpa [Nat.add_comm] using
    Nat.add_le_add (degree_minimal_del_le D x y) (degree_minimal_con_le C x y)

private theorem split_fold_keep (C D : HG n) (z : Fin n) (k : ℕ) (l : List (Fin n))
    (h : ∀ y ∈ l, key C D y ≤ k) :
    l.foldl (splitStep C D) (some (z, k)) = some (z, k) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (List.mem_cons_self ..)
    have he : splitStep C D (some (z, k)) a = some (z, k) := by
      simp only [splitStep]
      split_ifs with h0 hlt
      · rfl
      · exact absurd hlt (by unfold key at ha; omega)
      · rfl
    simpa only [List.foldl_cons, he] using ih (fun y hy => h y (List.mem_cons_of_mem a hy))

private theorem split_fold_below (C D : HG n) (k : ℕ) (l : List (Fin n))
    (h : ∀ y ∈ l, key C D y < k) (acc : Option (Fin n × ℕ))
    (ha : acc = none ∨ ∃ z q, acc = some (z, q) ∧ q < k) :
    l.foldl (splitStep C D) acc = none ∨
      ∃ z q, l.foldl (splitStep C D) acc = some (z, q) ∧ q < k := by
  induction l generalizing acc with
  | nil => exact ha
  | cons a l ih =>
    apply ih (fun y hy => h y (List.mem_cons_of_mem a hy))
    have hk := h a (List.mem_cons_self ..)
    rcases ha with rfl | ⟨z, q, rfl, hq⟩
    · simp only [splitStep]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr ⟨a, key C D a, rfl, hk⟩
    · simp only [splitStep]
      split_ifs
      · exact Or.inr ⟨z, q, rfl, hq⟩
      · exact Or.inr ⟨a, key C D a, rfl, hk⟩
      · exact Or.inr ⟨z, q, rfl, hq⟩

/-- The code's exact least-label tie convention, in addition to maximal positive degree sum. -/
theorem splitVar_of_least_max {C D : HG n} {x : Fin n} (hp : 0 < key C D x)
    (hm : ∀ y, key C D y ≤ key C D x)
    (hl : ∀ y, y < x → key C D y < key C D x) : splitVar C D = some x := by
  have hsort : (List.finRange n).Pairwise (fun a b => a < b) := by
    apply List.pairwise_iff_getElem.2
    intro i j hi hj hij
    simpa [Fin.lt_def] using hij
  obtain ⟨l, r, he⟩ := List.mem_iff_append.1 (List.mem_finRange x)
  have hpre : ∀ y ∈ l, key C D y < key C D x := by
    intro y hy
    apply hl y
    rw [he] at hsort
    exact hsort.rel_of_mem_append hy (List.mem_cons_self ..)
  rw [splitVar_eq, he, List.foldl_append, List.foldl_cons]
  rcases split_fold_below C D (key C D x) l hpre none (Or.inl rfl) with h | ⟨z, q, h, hq⟩
  · rw [h]
    have hx : splitStep C D none x = some (x, key C D x) := by
      unfold splitStep
      rw [ite_eq_right (show degree C x + degree D x ≠ 0 from Nat.ne_of_gt hp)]
      rfl
    rw [hx, split_fold_keep C D x _ r (fun y _ => hm y)]
    rfl
  · rw [h]
    have hx : splitStep C D (some (z, q)) x = some (x, key C D x) := by
      unfold splitStep
      rw [ite_eq_right (show degree C x + degree D x ≠ 0 from Nat.ne_of_gt hp)]
      change (if q < key C D x then some (x, key C D x) else some (z, q)) = _
      exact ite_eq_left hq
    rw [hx, split_fold_keep C D x _ r (fun y _ => hm y)]
    rfl

/-- Every earlier vertex has strictly smaller score than the returned split vertex. -/
theorem splitVar_earlier {C D : HG n} {x : Fin n} (hx : splitVar C D = some x) :
    0 < key C D x ∧ (∀ y, key C D y ≤ key C D x) ∧
      ∀ y, y < x → key C D y < key C D x := by
  obtain ⟨z, hz, hp, hm⟩ := splitVar_spec C D (by
    by_contra h
    have h0 : ∀ y, key C D y = 0 := by
      intro y
      by_contra hy
      obtain ⟨w, hw, hpw, -⟩ := splitVar_spec C D (Nat.pos_of_ne_zero hy)
      rw [hx] at hw
      cases hw
      exact h hpw
    have hf := (splitStep_fold C D (List.finRange n) none).1 rfl (fun y _ => h0 y)
    rw [splitVar_eq, hf] at hx
    cases hx)
  rw [hx] at hz
  cases hz
  let S := univ.filter fun y => key C D y = key C D x
  have hs : S.Nonempty := ⟨x, by simp [S]⟩
  let y := S.min' hs
  have hy : y ∈ S := min'_mem S hs
  have hkey : key C D y = key C D x := (mem_filter.1 hy).2
  have he : splitVar C D = some y := splitVar_of_least_max (hkey ▸ hp)
    (fun w => hkey ▸ hm w) (by
      intro w hw
      have hwle := hm w
      have hne : key C D w ≠ key C D x := by
        intro heq
        have hwS : w ∈ S := mem_filter.2 ⟨mem_univ _, heq⟩
        exact (not_le_of_gt hw) (min'_le S w hwS)
      rw [hkey]
      omega)
  rw [hx] at he
  have hxy : x = y := Option.some.inj he
  refine ⟨hp, hm, fun w hw => ?_⟩
  have hwle := hm w
  have hne : key C D w ≠ key C D x := by
    intro heq
    have hwS : w ∈ S := mem_filter.2 ⟨mem_univ _, heq⟩
    have hyw := min'_le S w hwS
    change y ≤ w at hyw
    rw [← hxy] at hyw
    exact (not_le_of_gt hw) hyw
  omega

/-- If a consecutive successor keeps the old maximum while all scores decrease and
the old split disappears, it is the next exact split. No equivariance is assumed. -/
theorem splitVar_successor {C D A B : HG n} {x y : Fin n}
    (hx : splitVar C D = some x) (hxy : y.val = x.val + 1)
    (hdec : ∀ z, key A B z ≤ key C D z) (hzero : key A B x = 0)
    (hkeep : key A B y = key C D x) : splitVar A B = some y := by
  obtain ⟨hp, hm, hl⟩ := splitVar_earlier hx
  apply splitVar_of_least_max (by omega)
  · intro z
    rw [hkeep]
    exact (hdec z).trans (hm z)
  · intro z hz
    rw [hkeep]
    by_cases hzx : z = x
    · subst hzx
      simpa [hzero] using hp
    · have hlt : z < x := by
        have hzv : z.val < y.val := hz
        have hne : z.val ≠ x.val := fun h => hzx (Fin.ext h)
        show z.val < x.val
        omega
      exact (hdec z).trans_lt (hl z hlt)

/-- The identity child of an OR-sibling split selects the consecutive mate next.
The hypotheses describe the two edge families at this node, not an arbitrary minor.
This is a statement about the next pivot if recursion continues past its leaf tests. -/
theorem splitVar_or_mate {C D : HG n} {x y : Fin n}
    (sC : IsSperner C) (sD : IsSperner D) (hx : splitVar C D = some x)
    (hxy : y.val = x.val + 1) (heq : key C D y = key C D x)
    (hsep : ∀ e ∈ C, y ∈ e → x ∉ e)
    (hboth : ∀ e ∈ D, x ∈ e ↔ y ∈ e) :
    splitVar (minimal (del C x)) (minimal (con D x)) = some y := by
  have hne : x ≠ y := by
    intro h
    have := congrArg Fin.val h
    omega
  apply splitVar_successor hx hxy (key_left_child_le C D x)
  · have h1 := degree_minimal_le (del C x) x
    have h2 := degree_minimal_le (con D x) x
    rw [degree_del_self] at h1
    rw [degree_con_self] at h2
    unfold key
    omega
  · rw [minimal_eq_self (del_isSperner sC x),
      minimal_eq_self (con_isSperner_of_together sD hne hboth)]
    unfold key
    rw [degree_del_eq_of_separate hsep,
      degree_con_eq_of_together hne (fun e he hy => (hboth e he).2 hy)]
    exact heq

/-- The analogous identity child for AND siblings is the side-exchanging child. -/
theorem splitVar_and_mate {C D : HG n} {x y : Fin n}
    (sC : IsSperner C) (sD : IsSperner D) (hx : splitVar C D = some x)
    (hxy : y.val = x.val + 1) (heq : key C D y = key C D x)
    (hboth : ∀ e ∈ C, x ∈ e ↔ y ∈ e)
    (hsep : ∀ e ∈ D, y ∈ e → x ∉ e) :
    splitVar (minimal (del D x)) (minimal (con C x)) = some y := by
  have hx' : splitVar D C = some x := by rwa [splitVar_comm]
  apply splitVar_or_mate sD sC hx' hxy _ hsep hboth
  simpa [key, Nat.add_comm] using heq

end HD

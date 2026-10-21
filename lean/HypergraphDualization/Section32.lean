/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# Small hypergraphs (§3.2), checked

Every concrete statement of §3.2 about the hypergraphs on at most four vertices: the
transversal of each named hypergraph, its automorphism group order, the vertex frequencies,
and the size of the modified FK-A tree for each choice of first split vertex. Where the
printed pair is not a transversal pair, both the printed form's failure and the corrected
pair are recorded. Vertices are 0-indexed: thesis `v_i` is `i - 1`.

The checks evaluate the definitions of `Basic`, `Symmetry` and `Algorithm` with
`native_decide`, as in `Instances`.

| Lean | Thesis (§3.2) |
| --- | --- |
| `sperner_four_card`, `classes_four` | 168 Sperner hypergraphs on 4 vertices, 30 classes under `S₄` |
| `self_dual_classes_four` | 4 classes are self-transversal, so the other 26 form 13 pairs |
| `max_tree_three`, `max_tree_four` | the largest FK-A tree on 3 (resp. 4) vertices has 3 (resp. 7) nodes |
| `*_tr`, `*_aut`, `*_freq`, `*_splits` | the per-hypergraph statements |
| `*_printed_*` | printed pairs that are not transversal pairs |
| `young_aut_singletons` | `Aut(D_{m,1}) ≅ S_m × S_{n-m}`, for every `n` and `m` |
-/
import HypergraphDualization.Instances

namespace HD.S32

open HD HD.Data Finset

variable {n : ℕ}

/-! ### Tools -/

/-- The vertex frequencies `max(deg_C v / |C|, deg_D v / |D|)`, listed by vertex. -/
def freqs (C D : HG n) : List ℚ := (List.finRange n).map (freq C D)

/-- Modified FK-A with the root split forced to `x`; both subtrees use the default rule. -/
def sizeAt (C D : HG n) (x : Fin n) : ℕ :=
  1 + (fkA n true (del C x) (con D x)).2 + (fkA n true (del D x) (con C x)).2

/-- `sizeAt` for every vertex of positive degree, in vertex order. -/
def splits (C D : HG n) : List (Fin n × ℕ) :=
  ((List.finRange n).filter fun x => 0 < degree C x + degree D x).map fun x => (x, sizeAt C D x)

/-- The largest modified FK-A tree over every choice of split vertex at every node,
as `(nodes, height)`. -/
def maxTree : ℕ → HG n → HG n → ℕ × ℕ
  | 0, _, _ => (1, 0)
  | fuel + 1, C₀, D₀ =>
    let C := minimal C₀
    let D := minimal D₀
    if C.card * D.card ≤ 1 || C.card == 1 || D.card == 1 then (1, 0) else
      (List.finRange n).foldl (fun best x =>
        if degree C x + degree D x = 0 then best else
          let l := maxTree fuel (del C x) (con D x)
          let r := maxTree fuel (del D x) (con C x)
          (max best.1 (1 + l.1 + r.1), max best.2 (1 + max l.2 r.2))) (0, 0)

/-- All Sperner hypergraphs on `Fin n`. -/
def sperner (n : ℕ) : Finset (HG n) := (univ : Finset (HG n)).filter IsSperner

/-- `G` and `H` are isomorphic: some permutation carries one onto the other. -/
def Iso (G H : HG n) : Prop := ∃ σ : Equiv.Perm (Fin n), pimg σ G = H

instance (G H : HG n) : Decidable (Iso G H) := by unfold Iso; infer_instance

/-! ### Counting the hypergraphs on four vertices -/

/-- One hypergraph from each `S₄`-class of Sperner hypergraphs on four vertices. -/
def reps4 : List (HG 4) :=
  [∅, {∅}, {{0}}, {{0}, {1}}, {{0}, {1}, {2}}, {{0}, {1}, {2}, {3}}, {{0}, {1}, {2, 3}},
   {{0}, {1, 2}}, {{0}, {1, 2}, {1, 3}}, {{0}, {1, 2}, {1, 3}, {2, 3}}, {{0}, {1, 2, 3}},
   {{0, 1}}, {{0, 1}, {0, 2}}, {{0, 1}, {0, 2}, {0, 3}}, {{0, 1}, {0, 2}, {0, 3}, {1, 2}},
   {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}}, {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}},
   {{0, 1}, {0, 2}, {0, 3}, {1, 2, 3}}, {{0, 1}, {0, 2}, {1, 2}}, {{0, 1}, {0, 2}, {1, 2, 3}},
   {{0, 1}, {0, 2}, {1, 3}}, {{0, 1}, {0, 2}, {1, 3}, {2, 3}}, {{0, 1}, {0, 2, 3}},
   {{0, 1}, {0, 2, 3}, {1, 2, 3}}, {{0, 1}, {2, 3}}, {{0, 1, 2}}, {{0, 1, 2}, {0, 1, 3}},
   {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}}, {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}},
   {{0, 1, 2, 3}}]

/-- **§3.2.** There are 168 Sperner hypergraphs on four vertices (`d(4) = 168`). -/
theorem sperner_four_card : (sperner 4).card = 168 := by native_decide

/-- **§3.2.** They fall into exactly 30 classes under relabelling: `reps4` lists 30 Sperner
hypergraphs, no two isomorphic, and every Sperner hypergraph is isomorphic to one of them. -/
theorem classes_four :
    reps4.length = 30 ∧ (∀ r ∈ reps4, IsSperner r) ∧
    reps4.Pairwise (fun r s => ¬ Iso r s) ∧
    ∀ H ∈ sperner 4, ∃ r ∈ reps4, Iso r H := by native_decide

/-- **§3.2.** Exactly 4 of the 30 classes are self-transversal, so the remaining 26 classes
form 13 pairs `{G, Tr(G)}` with `G ≇ Tr(G)`. -/
theorem self_dual_classes_four :
    (reps4.filter fun r => Iso r (tr univ r)).length = 4 ∧
    ∀ r ∈ reps4, ∃ s ∈ reps4, Iso s (tr univ r) := by native_decide

/-- **§3.2.** On three vertices the largest modified FK-A tree, over every choice of split
vertex, has 3 nodes. -/
theorem max_tree_three : ((sperner 3).image fun G => (maxTree 4 G (tr univ G)).1).max = 3 := by
  native_decide

/-- **§3.2.** On four vertices the largest modified FK-A tree has 7 nodes and height 2
(three levels). -/
theorem max_tree_four :
    ((sperner 4).image fun G => (maxTree 5 G (tr univ G)).1).max = 7 ∧
    ((sperner 4).image fun G => (maxTree 5 G (tr univ G)).2).max = 2 := by native_decide

/-! ### The named hypergraphs -/

def st2 : HG 3 := {{0}, {1, 2}}
/-- `St₂` on four vertices (`v₄` isolated). -/
def st2on4 : HG 4 := {{0}, {1, 2}}
def d31 : HG 3 := {{0}, {1}, {2}}
def pn3 : HG 4 := {{0, 1}, {0, 2}, {0, 3}, {2, 3}}
def pn3bar : HG 4 := {{0}, {1, 2}, {1, 3}}
def p4 : HG 4 := {{0, 1}, {1, 2}, {2, 3}}
def st3 : HG 4 := {{0, 1}, {0, 2}, {0, 3}}
def hw3 : HG 4 := {{0, 3}, {1, 3}, {2, 3}, {0, 1, 2}}
def k3dot : HG 4 := {{1}, {0, 2}, {0, 3}, {2, 3}}
def k4minus : HG 4 := {{2, 3}, {0, 3}, {0, 2}, {1, 3}, {1, 2}}
def k2dd : HG 4 := {{0}, {1}, {2, 3}}
def c4 : HG 4 := {{0, 1}, {1, 2}, {2, 3}, {0, 3}}
def d41 : HG 4 := {{0}, {1}, {2}, {3}}
def k4 : HG 4 := {{0, 1}, {1, 2}, {1, 3}, {0, 2}, {2, 3}, {0, 3}}

/-- The transversals. -/
theorem st2_tr : tr univ st2 = {{0, 1}, {0, 2}} := by native_decide
theorem d31_tr : tr univ d31 = {{0, 1, 2}} := by native_decide
theorem pn3_tr : tr univ pn3 = {{0, 2}, {0, 3}, {1, 2, 3}} := by native_decide
theorem pn3bar_tr : tr univ pn3bar = {{0, 1}, {0, 2, 3}} := by native_decide
theorem p4_tr : tr univ p4 = {{0, 2}, {1, 2}, {1, 3}} := by native_decide
theorem st3_tr : tr univ st3 = {{0}, {1, 2, 3}} := by native_decide
theorem hw3_tr : tr univ hw3 = hw3 := by native_decide
theorem k3dot_tr : tr univ k3dot = {{0, 1, 2}, {0, 1, 3}, {1, 2, 3}} := by native_decide
theorem k4minus_tr : tr univ k4minus = {{0, 1, 2}, {0, 1, 3}, {2, 3}} := by native_decide
theorem k2dd_tr : tr univ k2dd = {{0, 1, 2}, {0, 1, 3}} := by native_decide
theorem c4_tr : tr univ c4 = {{0, 2}, {1, 3}} := by native_decide
theorem d41_tr : tr univ d41 = {{0, 1, 2, 3}} := by native_decide
theorem k4_tr : tr univ k4 = {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by native_decide

/-- The automorphism group orders of the table at the end of §3.2. -/
theorem table_aut :
    autOrder st2 = 2 ∧ autOrder pn3 = 2 ∧ autOrder pn3bar = 2 ∧ autOrder p4 = 2 ∧
    autOrder d31 = 6 ∧ autOrder k3C = 6 ∧ autOrder st3 = 6 ∧ autOrder hw3 = 6 ∧
    autOrder k3dot = 6 ∧ autOrder k4minus = 4 ∧ autOrder k2dd = 4 ∧ autOrder c4 = 8 ∧
    autOrder d41 = 24 ∧ autOrder k4 = 24 := by native_decide

/-- The orbit sizes `24 / |Aut|` quoted at the end of §3.2. -/
theorem table_orbits :
    24 / autOrder st2on4 = 12 ∧
    24 / autOrder st3 = 4 ∧ 24 / autOrder hw3 = 4 ∧ 24 / autOrder k4minus = 6 ∧
    24 / autOrder k4 = 1 ∧ 24 / autOrder c4 = 3 ∧ 24 / autOrder k2dd = 6 ∧
    24 / autOrder k3dot = 4 ∧ 24 / autOrder p4 = 12 ∧ 24 / autOrder pn3 = 12 ∧
    24 / autOrder pn3bar = 12 := by native_decide

/-- The frequencies quoted in §3.2 (corrected where the text differs; see the claim register). -/
theorem p4_freq : freqs p4 (tr univ p4) = [1/3, 2/3, 2/3, 1/3] := by native_decide
theorem pn3_freq : freqs pn3 (tr univ pn3) = [3/4, 1/3, 2/3, 2/3] := by native_decide
theorem pn3bar_freq : freqs pn3bar (tr univ pn3bar) = [1, 2/3, 1/2, 1/2] := by native_decide
theorem st3_freq : freqs st3 (tr univ st3) = [1, 1/2, 1/2, 1/2] := by native_decide
theorem hw3_freq : freqs hw3 (tr univ hw3) = [1/2, 1/2, 1/2, 3/4] := by native_decide
theorem k3dot_freq : freqs k3dot (tr univ k3dot) = [2/3, 1, 2/3, 2/3] := by native_decide
theorem k4minus_freq : freqs k4minus (tr univ k4minus) = [2/3, 2/3, 2/3, 2/3] := by native_decide
theorem k2dd_freq : freqs k2dd (tr univ k2dd) = [1, 1, 1/2, 1/2] := by native_decide
theorem c4_freq : freqs c4 (tr univ c4) = [1/2, 1/2, 1/2, 1/2] := by native_decide
theorem k4_freq : freqs k4 (tr univ k4) = [3/4, 3/4, 3/4, 3/4] := by native_decide

/-- Tree sizes for each forced first split vertex. -/
theorem st2_splits : splits st2 (tr univ st2) = [(0, 3), (1, 3), (2, 3)] := by native_decide
theorem pn3_splits : splits pn3 (tr univ pn3) = [(0, 3), (1, 7), (2, 5), (3, 5)] := by
  native_decide
theorem pn3bar_splits : splits pn3bar (tr univ pn3bar) = [(0, 5), (1, 3), (2, 5), (3, 5)] := by
  native_decide
theorem p4_splits : splits p4 (tr univ p4) = [(0, 7), (1, 3), (2, 3), (3, 7)] := by native_decide
theorem k3_splits : splits k3C (tr univ k3C) = [(0, 3), (1, 3), (2, 3)] := by native_decide
theorem st3_splits : splits st3 (tr univ st3) = [(0, 3), (1, 5), (2, 5), (3, 5)] := by
  native_decide
theorem hw3_splits : splits hw3 (tr univ hw3) = [(0, 7), (1, 7), (2, 7), (3, 3)] := by
  native_decide
theorem k3dot_splits : splits k3dot (tr univ k3dot) = [(0, 5), (1, 5), (2, 5), (3, 5)] := by
  native_decide
theorem k4minus_splits :
    splits k4minus (tr univ k4minus) = [(0, 5), (1, 5), (2, 5), (3, 5)] := by native_decide
theorem k2dd_splits : splits k2dd (tr univ k2dd) = [(0, 5), (1, 5), (2, 3), (3, 3)] := by
  native_decide
theorem c4_splits : splits c4 (tr univ c4) = [(0, 5), (1, 5), (2, 5), (3, 5)] := by native_decide
theorem k4_splits : splits k4 (tr univ k4) = [(0, 5), (1, 5), (2, 5), (3, 5)] := by native_decide

/-- `K₂··`: the most frequent vertices (`v₁`, `v₂`, frequency 1) give 5 nodes, the others 3,
so splitting on a most frequent vertex is not optimal. -/
theorem k2dd_mfv_not_optimal :
    sizeAt k2dd (tr univ k2dd) 0 = 5 ∧ sizeAt k2dd (tr univ k2dd) 2 = 3 := by native_decide

/-! ### Printed pairs that are not transversal pairs -/

theorem pn3bar_printed_not_tr :
    tr univ ({{1, 2}, {2, 3}, {0}} : HG 4) ≠ {{0, 1}, {0, 2, 3}} := by native_decide
theorem p4_printed_not_tr :
    tr univ ({{0, 2}, {1, 2}, {1, 3}, {0, 1}} : HG 4) ≠ p4 ∧
    tr univ p4 ≠ ({{0, 2}, {1, 2}, {1, 3}, {0, 1}} : HG 4) := by native_decide
theorem k3dot_printed_not_sperner : ¬ IsSperner ({{1}, {0, 2}, {1, 3}, {2, 3}} : HG 4) := by
  native_decide
theorem k4minus_printed_not_tr : tr univ k4minus ≠ {{0, 1, 2, 3}, {0, 1, 3}, {0, 2, 3}} := by
  native_decide
theorem k2dd_printed_not_tr : tr univ ({{0, 1}, {2, 3}} : HG 4) ≠ {{0, 1}, {2, 3}} := by
  native_decide
theorem k4_printed_not_tr : tr univ k4 ≠ {{0, 1, 2, 3}} := by native_decide

/-! ### The Example of §3.4 -/

/-- Two vertices lie in a common edge (the primal graph `G(H)`). -/
def PAdj (H : HG n) (u v : Fin n) : Prop := u ≠ v ∧ ∃ e ∈ H, u ∈ e ∧ v ∈ e

instance (H : HG n) (u v : Fin n) : Decidable (PAdj H u v) := by unfold PAdj; infer_instance

/-- `σ` is an automorphism of the primal graph. -/
def PrimalAut (H : HG n) (σ : Equiv.Perm (Fin n)) : Prop := ∀ a b, PAdj H (σ a) (σ b) ↔ PAdj H a b

instance (H : HG n) (σ : Equiv.Perm (Fin n)) : Decidable (PrimalAut H σ) := by
  unfold PrimalAut; infer_instance

def ex34 : HG 4 := {{0, 1, 2}, {1, 3}, {2, 3}}

/-- **Example of §3.4, corrected.** The printed `α = (v₁ v₃)` is not an automorphism of
`G(H)`; `(v₁ v₄)` is, and it is not an automorphism of `H`. -/
theorem ex34_corrected :
    ¬ PrimalAut ex34 (Equiv.swap 0 2) ∧
    PrimalAut ex34 (Equiv.swap 0 3) ∧ Equiv.swap 0 3 ∉ aut ex34 := by native_decide

/-! ### `Aut(D_{m,1})` for every `n`, `m` -/

section Young

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `D_{m,1}`: the singletons of a set `S` (`|S| = m`). -/
def singletons (S : Finset α) : Finset (Finset α) := S.image ({·})

theorem mem_aut_singletons {S : Finset α} {σ : Equiv.Perm α} :
    σ ∈ aut (singletons S) ↔ ∀ a, σ a ∈ S ↔ a ∈ S := by
  constructor
  · intro h a
    have key : ∀ b ∈ S, σ b ∈ S := fun b hb => by
      have : pmap σ {b} ∈ pimg σ (singletons S) := mem_image_of_mem _ (mem_image_of_mem _ hb)
      rw [mem_aut.1 h] at this
      obtain ⟨c, hc, hcb⟩ := mem_image.1 this
      have : σ b ∈ ({c} : Finset α) := by rw [hcb]; simp [mem_pmap]
      rwa [mem_singleton.1 this]
    refine ⟨fun ha => ?_, key a⟩
    -- `σ` maps `S` into `S`, hence onto `S`; so `σ a ∈ S` forces `a ∈ S`.
    have hinj : Set.InjOn σ S := fun x _ y _ h => σ.injective h
    have hsurj : S.image σ = S :=
      eq_of_subset_of_card_le (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact key x hx)
        (by rw [card_image_of_injective _ σ.injective])
    rw [← hsurj] at ha
    obtain ⟨b, hb, hba⟩ := mem_image.1 ha
    rwa [← σ.injective hba]
  · intro h
    refine mem_aut_of_subset fun e he => ?_
    obtain ⟨f, hf, rfl⟩ := mem_image.1 he
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hf
    refine mem_image.2 ⟨σ b, (h b).2 hb, ?_⟩
    ext x; simp [mem_pmap, Equiv.symm_apply_eq]

/-- The automorphisms of `D_{m,1}` are the permutations preserving `S`, which are exactly
the images of `Perm S × Perm Sᶜ` (`subtypeCongrHom`). -/
theorem aut_singletons_eq_range (S : Finset α) :
    aut (singletons S) = (Equiv.Perm.subtypeCongrHom (· ∈ S)).range := by
  ext σ
  rw [mem_aut_singletons, MonoidHom.mem_range]
  constructor
  · intro h
    refine ⟨(σ.subtypePerm fun a => h a, σ.subtypePerm fun a => not_congr (h a)), ?_⟩
    ext a
    by_cases ha : a ∈ S
    · simp [Equiv.Perm.subtypeCongr.left_apply _ _ ha]
    · simp [Equiv.Perm.subtypeCongr.right_apply _ _ ha]
  · rintro ⟨⟨e, f⟩, rfl⟩ a
    by_cases ha : a ∈ S
    · simp [Equiv.Perm.subtypeCongr.left_apply _ _ ha, ha]
    · simp [Equiv.Perm.subtypeCongr.right_apply _ _ ha, ha]
      exact (f ⟨a, ha⟩).2

/-- **§3.2, `Aut(D_{m,1}) ≅ S_m × S_{n-m}`.** -/
noncomputable def young_aut_singletons (S : Finset α) :
    aut (singletons S) ≃* Equiv.Perm {a // a ∈ S} × Equiv.Perm {a // a ∉ S} :=
  (MulEquiv.subgroupCongr (aut_singletons_eq_range S)).trans
    (MonoidHom.ofInjective (Equiv.Perm.subtypeCongrHom_injective (· ∈ S))).symm

end Young

end HD.S32

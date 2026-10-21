/-
Copyright (c) 2026 Saimon Y. Islam. Released under the GPL-3.0-or-later.

# The recursion trees, node by node

`fkATree` builds the tree that `fkA` walks: every node holds its Sperner-reduced pair and
its split vertex (`none` at a leaf). `autActive H` is the order of the automorphism group of
`H` on the vertices it uses: the automorphisms fixing every vertex outside its support. The
figures of Chapter 5 print, at each node, the split vertex and this group; `TreeFacts`
checks both against the printed numbering.
-/
import HypergraphDualization.Instances

namespace HD

open Finset

variable {n : ℕ}

/-- A recursion tree: a leaf, or a split node with its `L` child and, when `L` is dual,
its `R` child. -/
inductive FTree (n : ℕ)
  | leaf (C D : HG n)
  | node (C D : HG n) (x : Fin n) (l : FTree n) (r : Option (FTree n))

/-- The tree of Algorithm 1, node for node with `fkA`. -/
def fkATree : ℕ → Bool → HG n → HG n → FTree n
  | 0, _, C₀, D₀ => .leaf (minimal C₀) (minimal D₀)
  | fuel + 1, modified, C₀, D₀ =>
    let C := minimal C₀
    let D := minimal D₀
    if !conds C D then .leaf C D
    else if C.card * D.card ≤ 1 || (modified && (C.card == 1 || D.card == 1)) then .leaf C D
    else
      match splitVar C D with
      | none => .leaf C D
      | some x =>
        let l := fkATree fuel modified (del C x) (con D x)
        if (fkA fuel modified (del C x) (con D x)).1 then
          .node C D x l (some (fkATree fuel modified (del D x) (con C x)))
        else .node C D x l none

/-- Preorder, `L` before `R`. -/
def FTree.preorder : FTree n → List (HG n × HG n × Option (Fin n))
  | .leaf C D => [(C, D, none)]
  | .node C D x l none => (C, D, some x) :: l.preorder
  | .node C D x l (some r) => (C, D, some x) :: (l.preorder ++ r.preorder)

/-- Preorder with the root's `R` subtree numbered first, as six of the printed figures do. -/
def FTree.preorderRL : FTree n → List (HG n × HG n × Option (Fin n))
  | .node C D x l (some r) => (C, D, some x) :: (r.preorder ++ l.preorder)
  | t => t.preorder

/-- `|Aut(H)|` on the vertices `H` uses. -/
def autActive (H : HG n) : ℕ :=
  ((univ : Finset (Equiv.Perm (Fin n))).filter
    fun σ => σ ∈ aut H ∧ ∀ v, v ∉ support H → σ v = v).card

/-- The printed data of a tree: split vertex and group order at each node. -/
def treeData (rl : Bool) (C D : HG n) : List (Option (Fin n) × ℕ) :=
  ((if rl then (fkATree (n + 1) true C D).preorderRL else (fkATree (n + 1) true C D).preorder).map
    fun p => (p.2.2, autActive p.1))

end HD

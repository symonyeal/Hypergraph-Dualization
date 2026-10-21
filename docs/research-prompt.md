# Research prompt: Hypergraph Dualization, the next layer

A prompt for the next agent session (Claude or Codex), on any machine. Read the whole file
before touching anything. Part 1 is the state at hand-off on 2026-10-21; Part 2 is the
research program. Each track ends in statements that are **proved in Lean**, **refuted by a
Lean-checked counterexample**, or **recorded as open with the evidence that bounds them**.
Nothing else counts as a result.

---

# Part 1. State at hand-off (2026-10-21)

## Build state

- `lake build` (the default target) is green: 1220 jobs, the 281 theorems of the thesis
  library. Nothing in it changed.
- Four new files are committed **unfinished**. None is imported by
  `lean/HypergraphDualization.lean`, so the default build ignores them:

| File | State |
| --- | --- |
| `experiments/witt_m11.py` | Runs (about 35 s). Re-derives the A1/A2 facts and, with `--lean`, writes `WittData.lean` |
| `lean/HypergraphDualization/WittData.lean` | Generated. The 66 blocks of `w11` and a Schreier transversal `wittU0..wittU3` of `Aut(w11)` along the base `0,1,2,3` (sizes 11, 10, 9, 8) |
| `lean/HypergraphDualization/Witt.lean` | A1 and A2 written in full; **has never compiled to the end**. Build alone with `lake build HypergraphDualization.Witt` |
| `experiments/steiner_selftr.py` | Runs (about 3 s). The A4 check and the A5 parameter and 2-colouring scans |

## What to do first

1. Get `Witt.lean` to build. The first attempt's errors are fixed in the file:
   `Function.Embedding.fintype` is noncomputable, so `wit_check` now quantifies over injective
   functions `Fin 4 → Fin 11`; `Equiv.Perm.inv_apply_self` does not exist in this Mathlib, so
   proofs use `Equiv.Perm.inv_def` and `Equiv.symm_apply_apply`. The second attempt ran more
   than 10 minutes on the work laptop without finishing, and was stopped. Some
   `native_decide` check is too slow, and the file's later proofs have never been
   checked. Steps:
   - Time each check on its own (`set_option profiler true`, or comment the others out).
     Suspects: `wit_check` (14,641 functions, each permutation a composite of four
     `Equiv`s evaluated through `![…]` lookups, 66 membership tests per tuple) and
     `w11_self_tr` (2^11 subsets × 11 erasures × 66 edges).
   - If `wit_check` is the problem, flatten each `wit t` to a lookup table before testing
     edges, or test edges as bitmasks against a sorted array. If the default `by decide` in
     `WittData.mk` is slow, switch it to `by native_decide`.
   - Then fix whatever the remaining proofs (`tuple_injective` … `w11_preprimitive`) report.
2. Add `Witt` to the root imports, rebuild, record `#print axioms card_aut_w11`.
3. Commit. Then continue with the order in Part 2 §7.

## Findings so far (Python; none is a Lean result yet)

**F1. A1 reproduced.** `w11` is self-transversal; each of the 330 four-sets lies in exactly
one block; unordered block pairs meet in 1, 2 or 3 points 495, 660 and 990 times;
`|Aut| = 7920`; only the identity fixes `0,1,2,3`; the base has 7920 images.

**F2. Archive correction: the FK-A children of `w11`.** At the root FK-A splits on `v1` (all
degrees tie at 30). The deletion child has 36 blocks of size 5. The contraction child is
**not** `S(3,4,10)`: it keeps the 36 blocks avoiding `v1` beside the 30 four-sets, 66 edges in
all. Both have `|Aut| = 720` on the 10 active points, both transitive and primitive. The
archive's 1440 is `|Aut S(3,4,10)| = |PΓL(2,9)|`, which belongs to the derived design, not to
any FK-A node. A6's `w11_children` target must say 720 and 720.

**F3. Archive correction: tree sizes.** The current `results/` give FK-A (modified) 475 nodes,
FK-A faithful 1015, FK-B 323 for `w11`, not 483 and 321 (ratio 1.47, not 1.50). Confirm with
`runFKA true w11 w11` in Lean before quoting any of them.

**F4. A4 on paper.** The proof needs only *intersecting*, `r`-uniform, `d`-regular: fix an edge
`e`; the other `b − 1` edges each meet `e`, so `r(d − 1) = Σ_{x∈e}(deg x − 1) ≥ b − 1`; with
`br = td` this gives `d(r² − t) ≥ r(r − 1)`, with equality iff every other edge meets `e` in
exactly one point. State the Lean theorem for intersecting families; self-transversal is a
special case. The Lean equality clause is "distinct edges meet in exactly one point". The step
to "projective plane of order `r − 1`" is not proved; leave it as a remark. Checked on `K₃`,
Fano, `w11`, `Maj₅`, `Maj₇`, `Maj₉`: the inequality holds everywhere, with equality exactly on
`K₃` and Fano.

**F5. A5 is settled by parameters, not enumeration.** In a Steiner system `S(t,k,v)` the number
of blocks disjoint from a fixed block is

  `n₀(t,k,v) = Σ_{i<t} (−1)^i C(k,i)(λ_i − 1)`,  `λ_i = C(v−i, t−i) / C(k−i, t−i)`

by inclusion–exclusion over the subsets of the block (`λ_i` blocks through an `i`-set, and one
block through any larger subset of the block). A self-transversal family is intersecting, so it
needs `n₀ = 0`. This disposes of every system with given parameters at once, including all 80
`S(2,3,15)` and all `S(3,4,16)`. By hand from the formula (the script prints only the zero
cases; re-run before quoting): `S(2,3,9)` 2, `S(2,3,13)` 10, `S(2,3,15)` 16, `S(3,4,8)` 1,
`S(3,4,10)` 3, `S(3,4,14)` 20, `S(3,4,16)` 39, `S(5,6,12)` 1, `S(5,8,24)` 30. The script
checks the formula against brute force on the five systems it builds.

For `2 ≤ t < k < v ≤ 100`, the admissible parameter sets with `n₀ = 0` are:
- the projective planes `S(2, q+1, q²+q+1)`, `q = 2, …, 9`;
- `S(4,7,23)`;
- `S(t, t+1, 2t+3)` for `t = 2, 4, 8, 10, 14, 16, 20, 26, 28, 34, 38, 40, 44`.

Admissible sets with `n₀ < 0` (so no such system exists; Fisher's inequality in another form):
`S(2,6,16)`, `S(2,6,21)`, `S(2,12,45)`, `S(2,10,46)`, `S(2,10,55)`, `S(4,12,57)`,
`S(2,15,85)`, `S(2,14,92)`, `S(2,20,96)`, `S(2,12,100)`.

Full 2^v scans of the intersecting systems the script can build (labels are the script's):

| System | 2-colourable? | Colour class |
| --- | --- | --- |
| `PG(2,2) = S(2,3,7)` | no: self-transversal | |
| `PG(2,3) = S(2,4,13)` | yes | `{0,2,3,4,6,9}` |
| `PG(2,4) = S(2,5,21)` | yes | `{0,1,3,4,5,6,8,16}` |
| `S(4,5,11)` | no: self-transversal | |
| `S(4,7,23)` (weight-7 words of the binary Golay code) | yes | `{0,1,2,4,5,6,7,8,9,11,12}` |

The original prompt missed a trivial family: `S(k,k,2k−1)`, all `k`-subsets of `2k − 1` points
(the majority function), is self-transversal. Restrict the classification to `t < k`.

**F6. A new theorem candidate: every `S(t, t+1, 2t+3)` is self-transversal.** Fano is `t = 2`
and `w11` is `t = 4`; this would explain both at once. Paper proof, to formalise:
1. *Intersecting.* Apply the inclusion–exclusion of F5 to the blocks and to the family of all
   `(t+1)`-subsets, over the subsets `S` of a block `B`. Key lemma, for `|S| = i ≤ t`:
   `(t+3) · #{blocks ⊇ S} = C(2t+3−i, t+1−i)`. (Double-count pairs `(T, e)` with
   `S ⊆ T ⊆ e`, `|T| = t`, and use `C(n, m+1)(m+1) = C(n, m)(n − m)`.) This gives
   `(t+3)·n₀ = (t+2)(1 + (−1)^{t+1})`. For odd `t`, `t+3` cannot divide `2(t+2)`, so no
   system exists. For even `t`, `n₀ = 0`.
2. *Every `(t+2)`-set contains a block or is the complement of one.* Sets containing a block:
   `b(t+2)` of them, since no `(t+2)`-set holds two blocks. Complements of blocks: `b`. The two
   kinds are disjoint by step 1, and `b(t+3) = C(2t+3, t+2)`, so together they are all of them.
3. *Every set of at least `t+3` points contains a block.* Otherwise take a `(t+2)`-subset `S`
   with complement block `B`, and `x` in the set but outside `S`. For each `y ∈ S`, the set
   `S − y + x` forces `(B − x) + y` to be a block, so `t+2` distinct blocks contain the
   `t`-set `B − x`. Contradiction.
4. Hence for every `A`, `A` or its complement contains a block: not 2-colourable. With step 1
   and A3, `Tr(H) = H`.

The literature was not searched. Before calling this new, check the simple-games literature
(constant-sum games whose minimal winning coalitions form a Steiner system) and the design
literature on `S(t, t+1, 2t+3)`. Steiner systems with these parameters are known only for
`t = 2, 4`.

**Conjecture (to state with its bound):** a self-transversal Steiner system `S(t,k,v)` with
`t < k` has `k = t+1` and `v = 2t+3`. The evidence for `v ≤ 100` combines three things: F5's
parameter list, the 2-colourings above, and two cited facts (projective planes of order `≥ 3`
have blocking sets, Bruen; `S(4,7,23)` is unique, Witt).

## Designs ready but not written

**A3.** `TwoColourable U H := ∃ A ⊆ U, ¬ upHit H A ∧ ¬ upHit H (U \ A)`.
Statement: `Within U H → IsSperner H → (tr U H = H ↔ OpenAI.Intersecting H ∧ ∅ ∉ H ∧
¬ TwoColourable U H)`. Proof from `eq_tr_iff_partition` with `G = H`. Sperner is needed:
`{{1},{1,2}}` satisfies the right side but `Tr = {{1}}`.

**A7.** Define cographs by their cotree decomposition on a `Finset α`: a single vertex, or a
disjoint union / join of two nonempty cographs. (`Cotree.lean` is ℕ-labelled with no
disjointness, so it does not fit.) Core lemma: a graph preserved by a group acting primitively
is connected or edgeless. Proof: the reachability classes are blocks, via
`MulAction.IsBlock` and `IsPreprimitive.isTrivialBlock_of_isBlock`. Apply it to the primal
graph (root is a union) or its complement (root is a join). The union case makes every edge a
singleton. The join case, with conformality (every nonempty clique of the primal graph lies in
an edge) and Sperner, gives `H = {V}`. Either way `aut H = ⊤`. Corollaries: `w11` from
`w11_preprimitive` and `7920 ≠ 11!`; Fano needs a 2-transitivity witness (a Schreier transversal
along `(0,1)`, as `witt_m11.py` does), or the direct route (primal graph complete, `H ≠ {V}`).

## Useful Mathlib names (v4.35.0)

`MulAction.IsMultiplyPretransitive G α n` (`= IsPretransitive G (Fin n ↪ α)`),
`MulAction.isMultiplyPretransitive_of_le`, `MulAction.isPreprimitive_of_is_two_pretransitive`,
`MulAction.IsPreprimitive`, `MulAction.IsBlock`, `Equiv.Perm.ofSubtype_subtypePerm`,
`Fintype.card_embedding_eq`, `Function.Embedding.smul_apply`; `Jordan.lean` has
`Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`.

---

# Part 2. The research program

## 0. Ground rules

1. **A result is a Lean declaration.** Every new statement goes into
   `lean/HypergraphDualization/` (Lean `v4.35.0`, Mathlib `v4.35.0`) and builds with
   `lake build`. Finite facts may use `native_decide`; say so in the docstring. General
   statements must rest only on `propext`, `Classical.choice`, `Quot.sound`; check with
   `#print axioms`.
2. **Computation first, proof second.** Before formalising a conjecture, try to falsify it:
   run the Python engine (`src/fka`) on every instance in `data/instances` and on exhaustive
   small cases. A conjecture that survives goes to Lean; one that fails becomes a Lean
   counterexample.
3. **Archived numbers are leads, not facts.** Figures quoted below from the August 2026
   research archive were computed in Python and never formalised; F2 and F3 above show two of
   them are wrong. Re-derive each one before relying on it.
4. **Machine setup.** Install elan; `lake exe cache get` in `lean/`. On Windows with long paths
   disabled, run lake from a `subst` drive. Write Lean with an editor, not shell heredocs,
   which can collapse backslashes.
5. **Statement types.** Use the thesis vocabulary exactly: *Theorem* (general, proved),
   *Proposition* (general, proved, smaller), *Lemma* (a step), *Observation* (a finite or
   computational fact, Lean-checked), *Conjecture* (open, with the evidence and the search bound
   stated). Each new item gets a row in `thesis/CLAIMS.md` with its Lean name.

## 1. What exists

- 281 Lean theorems: every numbered statement of the 2024 thesis is proved, corrected with a
  counterexample, or marked open (`thesis/CLAIMS.md`). General results include FK-A correctness
  (`fkA_correct`), the Kraft condition (`kraft_sum`), the corrected Cor. 2.3.1
  (`two_pow_shortest_le`), `Aut(Tr H) = Aut(min H)` (`aut_tr_eq_aut_minimal`), alternating
  trees are cotrees (`primalAdj_alt`), uniform sizes and frequencies of GK/TK (`alt_shape`),
  `7^k` transversals of `k` Fano planes (`tr_kFano_card`), and node-by-node checks of all eight
  printed recursion trees (`TreeFacts`).
- Bridges to `openai/math` (`Connections.lean`, `docs/openai-math-connections.md`): Ryser
  covers are transversals; `τ(H)` is the smallest edge of `Tr(H)`; Ryser-extremal `H` have
  `|H| + |Tr H| ≥ 2^r`; `P_p(G) + P_{1-p}(Tr G) = 1`, so self-transversal hypergraphs have
  critical probability exactly `1/2`.
- Open from the thesis: `ε(7) = 3/7` (Observation 5.2.3). Known exactly: `ε(3) = 2/3` (unique
  minimiser `K₃`), `ε(4) = ε(5) = 1/2`.
- Not started: the interactive FK-A/FK-B explorer site (handed back; separate from this
  program).

## 2. Track A: the Mathieu group `M₁₁` and the self-transversal Witt design

The instance is `data/instances/w11.json`: the Witt design `S(4,5,11)`, 11 points, 66 blocks of
size 5. Facts re-derived so far are in F1–F3.

**A1. Observation (Lean, finite).** `w11` is a Steiner system `S(4,5,11)`, is self-transversal,
and any two blocks meet in 1, 2 or 3 points. Written as `w11_steiner`, `w11_self_tr`,
`w11_meet`.

**A2. Theorem (Lean, the main target).** `|Aut(w11)| = 7920`, and `Aut(w11)` acts sharply
4-transitively. Written as `card_aut_w11`, `w11_four_transitive`, `w11_four_free`,
`w11_preprimitive`. The method avoids enumerating `11!` permutations:
- *Free action:* the 5040 permutations fixing `0,1,2,3` are checked once (`stab_check`), so
  `σ ↦ (σ0, σ1, σ2, σ3)` is injective on `Aut`.
- *Surjective:* an explicit automorphism for each of the `11·10·9·8 = 7920` tuples, built from
  the Schreier transversal (`wit`, `wit_check`).
- Sharp 4-transitivity and primitivity follow.
Record the identification with `M₁₁` as cited (Jordan: a sharply 4-transitive group of degree
11 is `M₁₁`), not as a Lean claim.

**A3. Proposition (Lean, general).** `H = Tr(H)` iff `H` is intersecting, has no empty edge and
is not 2-colourable (for Sperner `H` inside `U`). Design in Part 1.

**A4. Theorem (Lean, general).** For an intersecting, `r`-uniform, `d`-regular hypergraph on `t`
points, `d(r² − t) ≥ r(r − 1)`, with equality iff distinct edges meet in exactly one point.
See F4. Cite Bruen for "every plane of order ≥ 3 has a blocking set containing no line"; do
not claim it.

**A5. Theorem and Observation.** See F5 and F6. Targets, in order:
- *Theorem A5a.* Inclusion–exclusion: in a Steiner system `S(t,k,v)`, every block is disjoint
  from exactly `n₀(t,k,v)` blocks.
- *Observation A5b.* The table of `n₀` for the parameters in F5, by `decide`, so that every
  listed system with `n₀ > 0` is Lean-certified not self-transversal.
- *Lean 2-colourings* for `PG(2,3)` (already `pg23_not_self_dual`), `PG(2,4)` and `S(4,7,23)`,
  via `tr_ne_of_blocking`.
- *Theorem A5c.* Every `S(t, t+1, 2t+3)` is self-transversal (F6).
- *Conjecture A5d.* The converse, with the `v ≤ 100` evidence stated exactly.

**A6. Observation: symmetry depth under FK-A.** Define the *primitivity depth* of a dual pair
as the largest depth of a node whose `Aut(C)`, on the vertices present, is primitive and is
not `S_n` or `A_n`. Compute it for every instance and both FK-A variants with the `TreeFacts`
machinery (extend `autActive` with a primitivity test). Lead: Fano has depth 0; `w11` has depth
≥ 1, with both children of order 720 (F2).
- `w11_children`: the two children of the root, both of order 720, primitivity of both
  (`MulAction.IsPreprimitive` on the subgroup), and neither read-once.
- The full automorphism tree of `w11` (475 nodes per F3; confirm), as a figure and a
  `TreeFacts` entry.
- *Conjecture to test:* for self-transversal pairs, the ratio of FK-A to FK-B nodes falls as
  primitivity depth rises. One data point per instance is not evidence of a law. Add the SDFP
  and Asym instances, the `Maj` family, and every self-transversal pair on ≤ 9 points, before
  stating it.

**A7. Proposition (Lean, general): a read-once certificate.** If `H` is read-once (Sperner,
conformal, cograph primal graph) on `n ≥ 2` points and `Aut(H)` is primitive, then
`Aut(H) = S_n`. Design in Part 1.

## 3. Track B: `ε(7)` (Observation 5.2.3; a new result either way)

`ε(n)` is the least most-frequent-vertex frequency over transversal pairs on `n` points (both
sides nonempty, no empty edge). Known: `ε(3) = 2/3`, `ε(4) = ε(5) = 1/2` (Lean `eps_three`,
`eps_four`; `n = 5` exhaustive in Python only). The thesis claims `ε(7) = 3/7` via the Fano
plane. Random and hill-climbing searches never went below `1/2`, which settles nothing.

**B1. Observation.** `ε(6)`: enumerate the 16,353 Sperner classes on 6 points up to `S₆`,
compute `ε` for each with its transversal. Lean: the minimiser by `native_decide`. The lower
bound needs the class list to be complete; prove completeness like `classes_four`, or give a
sound pruning argument.

**B2. Theorem or counterexample: is `ε(7) = 3/7`?** Encode as a 0/1 program on the truth table
of a monotone `f : {0,1}^7 → {0,1}` (128 variables): monotonicity clauses; minterm indicators
`m_x ⟺ f(x) ∧ ∧_{i∈x} ¬f(x−i)`; the dual `g(x) = ¬f(¬x)` with maxterm indicators likewise;
then `7·deg_G(v) < 3·|G|` and `7·deg_H(v) < 3·|H|` for every `v` as linear constraints over
the indicators. Solvers known to install on Python 3.14: OR-Tools CP-SAT, HiGHS via
`scipy.optimize.milp`; PySAT was not installed on the work laptop.
- *Feasible:* the solver returns a pair with `ε < 3/7`. Lean-check it by `native_decide`. This
  **refutes** the `n = 7` half of Observation 5.2.3.
- *Infeasible:* `ε(7) = 3/7` is **proved** if the infeasibility certificate can be checked in
  Lean: an LRAT proof from a SAT encoding checked by Lean's LRAT checker (`bv_decide`
  machinery), or a split into symmetry classes small enough for `native_decide`. Otherwise
  record "infeasible by solver X, not Lean-certified" as a **Conjecture**, with the encoding
  committed.
- Run the same encoding at `n = 8` against `2/5` (8-Ver attains `2/5`).

**B3. Conjecture.** Fit `ε(n)` against `n` for `n ≤ 8` and against the Fredman–Khachiyan lower
bound `1/log₂ N`. State only what the table shows.

## 4. Track C: subproblem DAG versus recursion tree

Archive lead (`docs/tree-vs-dag.md`, `src/fka/memo.py`): with `τ` = FK-A tree nodes and `δ` =
distinct irredundant `(C,D)` pairs in the tree, `δ ≤ 2N` on every instance and family measured
(`N = |C| + |D|`), while `τ/δ` reaches 280 on GK `f₃`. `matching(v)` has `δ = v` and
`τ = 2^{v/2+1} − 3`; `threshold(v)` has `τ = δ = v − 1`.

**C1. Theorem.** The exact laws for `matching(v)` and `threshold(v)`: define the families in
Lean, define `fkADag` (the set of distinct pairs reached), and prove `δ` and `τ` for every `v`
by induction, with the node counts as corollaries of `fkATree`.

**C2. Theorem (the main target of this track).** *FK-A with memoisation is polynomial on
read-once pairs:* `δ(H, Tr H) ≤ c·N` for every read-once `H`. Lead: a split of a read-once
function gives read-once restrictions determined by the cotree path. Measure `δ` on GK/TK to
`f₄` and on `word-xy`, `word-yx`; find the exact formula; prove it on `alt`/`coalt` using
`Cotree`, then for general read-once hypergraphs.

**C3. Conjecture (falsify first).** `δ ≤ 2N` for all dual pairs. A proof would put DUAL in P, so
it is almost certainly false: search for the counterexample (substitution products, Track D;
self-dualisations; random pairs on 15–20 points biased toward high repeat rate). A pair with
`δ > 2N` is a new Observation; a family with `δ/N → ∞` is a new Theorem.

## 5. Track D: the frequency threshold and substitution

Archive lead (`docs/hard-classes.md`, `src/fka/substitution.py`): the threshold ratio
`c = ε·log₂ N`; FK96 gives `c ≥ 1`; GK and TK reach `c → 2`; word families `T_w` reach
`c_∞ = 3/2 + 1/(2(2^k − 1))`; under `(P): k·k* ≥ 8^{r−1}` every composition has `c_∞ ≥ 3/2`.
Open: is there a prime template with `k·k* < 8^{r−1}`?

**D1. Theorem.** Define substitution `T[Γ₁,…,Γ_m]` on disjoint vertex sets and prove
`Tr(T[Γ]) = Tr(T)[Tr Γ]`, the edge-count products, and `ε(T[Γ]) = ε_T·ε_Γ` for uniform regular
inputs. These generalise `tr_union_disjoint` and `tr_join_disjoint`.

**D2. Proposition.** `(P)` is closed under substitution.

**D3. Open problem.** Search for a prime template with `k·k* < 8^{r−1}` at `r = 4` using
transitive groups of degree 16. A find gives `c_∞ < 3/2`. A complete negative search at
`r = 4` is an Observation.

## 6. Track E: the `openai/math` bridges, extended

**E1.** Compute `|H| + |Tr H|` for the smallest explicit Ryser counterexample of `openai/math`
family 162 (count `Tr` by structure, not enumeration) and compare with `ryser_extremal_size`'s
`2^r`. If the bound is far from tight, look for a sharper inequality from the equality case of
`kraft_sum`.

**E2.** For a self-transversal `H` with a transitive automorphism group (Fano, `w11`):
`P_p(H)` is strictly increasing, equals `1/2` at `p = 1/2`, and every vertex has the same
influence there. The influence statement needs `bernoulliProbability` reindexed by an
automorphism.

## 7. Deliverables and acceptance

| Deliverable | Accepted when |
| --- | --- |
| New Lean modules (`Witt.lean`, `SelfTransversal.lean` for A3–A5, `Primitive.lean`, `EpsSeven.lean`, `Dag.lean`, `Substitution.lean`) | `lake build` clean with each module imported by the root; `#print axioms` recorded for each headline theorem |
| `thesis/CLAIMS.md` rows | one row per new statement, with status and Lean name |
| `docs/research-2026-10.md` | each result as Theorem/Proposition/Observation/Conjecture, numbered, textbook register, with its Lean name and the command that reproduces it |
| Data | every new instance in `data/instances/` with a source note; every search script under `experiments/`, seeded |
| Negative results | stated with the exact search space and bound ("no example among …"), never "none exist" |

Order of work: finish A1–A2 (Part 1) → A3 → A7 → A4 → A5 → B2 → C1 → C2, then the rest. Commit
after each track with the build green; push to `main` (solo repository). Ask before deleting
anything or changing what the 2024 recovered edition says.

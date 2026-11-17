# FK-A on the alternating trees: complex evaluation

Elbassioni (arXiv:2610.34474, §3) bounds the size of a decision tree by the multilinear
extension of its function at `w = (1 + i√3)/2`. Research Theorem 4.25 (Lean) turns any
decision-tree bound into a bound on FK-A's recursion tree under every valid rule. This
note evaluates Elbassioni's bound exactly on GK and TK, bounds the result from above, and
compares the two. §4 replaces his evaluation point by measures on blocks
of eight variables, which raises the rate to `0.41433`, and shows that no measure bounded on
every subcube can give more than `0.41434` (17 November 2026). §5 checks Conjecture 6 for all
weights at once and reduces the rest of the gap to one inequality at each gate.

Status labels: *written proof* (prose, not in Lean), *exact check* (integer arithmetic by
`experiments/subcube_norm.py`), *computed* (`experiments/alternating_dt.py`,
`experiments/subcube_norm.py` or `experiments/readonce_dag`, with its bound), *conjecture*.

| Bound on `log₂(leaves)/v` for GK `f_k`, TK `S_k` | Rate | Source |
| --- | --- | --- |
| Elbassioni, Lemma 3.5 | `log₂3/12 = 0.1321` | arXiv:2610.34474 (GK only) |
| JRSW Fourier `ℓ₁` | `log₂(27/16)/4 = 0.1887` | research Theorem 4.24, Lean |
| exact `log₂|P(w)|` | `0.37245` | Theorem 2 here, written proof |
| subcube norm | `0.41433` to `0.41434` | Theorem 8, Proposition 9, written proof and exact check |
| depth-first tree (upper bound) | `→ 0.46925` | Proposition 4, computed |
| least decision tree, `f₁–f₃`, `S₁–S₂` | equals depth-first | Observation 5, computed |

## Setting

GK `f_k` is the binary alternating tree with an OR root and `v = 2^{2k−1}` variables:
`f₁ = x₁ ∨ x₂`, `f_{k+1} = (f ∧ f) ∨ (f ∧ f)` on disjoint copies; it is Elbassioni's `f_k`
(his `v_k = 2·4^{k−1}`) and research `coalt(2k − 1)`. TK `S_k` has an AND root and `4^k`
variables: `S₁ = (x₁ ∨ x₂) ∧ (x₃ ∨ x₄)`, `S_{k+1} = (S ∨ S) ∧ (S ∨ S)`. A decision tree's size is
its number of leaves. `P_F` is the multilinear extension of `F` over `ℂ`; on read-once
formulas `P_{g∧h} = P_g P_h` and `P_{g∨h} = P_g + P_h − P_g P_h`. Put

```text
w = (1 + i√3)/2,   u_k = P_{f_k}(w, …, w),   t_k = P_{S_k}(w, …, w).
```

## 1. The bound

**Lemma 1 (Elbassioni Lemma 3.4, both leaf colours; written proof).** Let `|z| ≤ 1` and
`|1 − z| ≤ 1`. A decision tree computing `F` has at least `|P_F(z, …, z)|` leaves labelled 1
and at least `|1 − P_F(z, …, z)|` labelled 0.

*Proof.* First remove repeated queries on each path, keeping the branch the earlier answer
forces; this does not add leaves (Elbassioni does the same). Then every path reads distinct
variables, the leaves partition the cube into subcubes, and
`P_F(x) = Σ_{1-leaves} Π_{ρ(v)=1} x_v Π_{ρ(v)=0} (1 − x_v)` as multilinear polynomials, `ρ` the
leaf's partial assignment. At `x = (z, …, z)` every term has modulus at most 1. The 0-leaves
are the 1-leaves of the same tree for `¬F`, and `P_{¬F} = 1 − P_F`. ∎

Elbassioni's Lemma 3.4 counts the 1-leaves; the 0-leaves add `|1 − u_k|`, which is close to
`|u_k|` for large `k`.

## 2. The exact rate

**Theorem 2 (written proof and exact computation).**

```text
u_{k+1} = u_k² (2 − u_k²),      t_{k+1} = t_k² (2 − t_k)²,
γ = lim log₂|u_k| / 2^{2k−1} = lim log₂|t_k| / 4^k = 0.372450326 ± 3·10⁻⁹.
```

For `k ≥ 3`, `|u_k| ≥ 2^{0.37245 v}` and `|t_k| ≥ 2^{0.37245 v}`. So every decision tree for
`f_k` or `S_k`, `k ≥ 3`, has at least `2^{0.37245 v}` leaves, i.e. `1.29455^v`.

*Proof.* The recursions are the gate rules: `f ∧ f` gives `u²`, and OR of two copies gives
`2u² − u⁴`; `S ∨ S` gives `2t − t² = t(2 − t)`, and AND squares it (`experiments/alternating_dt.py
rates` computes `u_k`, `t_k` exactly in `ℚ(i√3)`). Hence

```text
|u_{k+1}| = |u_k|⁴ |1 − 2u_k⁻²|,      |t_{k+1}| = |t_k|⁴ |1 − 2t_k⁻¹|².
```

Let `g_k = log₂|u_k|/v_k`. Since `v_{k+1} = 4 v_k`,
`g_{k+1} = g_k + log₂|1 − 2u_k⁻²|/v_{k+1}`, and
`|log₂|1 − 2u⁻²|| ≤ −log₂(1 − 2|u|⁻²)` for `|u|² > 2`. In `ℚ(i√3)` the value `u₃` is exact,
with `g₃ = 0.372450325` and `|u₃| ≈ 3871`. Then the first correction is below
`−log₂(1 − 2/3871²)/128 < 1.6·10⁻⁹`. `|u_{k+1}| ≥ |u_k|⁴(1 − 2|u_k|⁻²)` grows doubly
exponentially, so the later corrections add less than `10⁻¹⁰`. For TK the correction is
`2 log₂|1 − 2t⁻¹|/v_{k+1}`; `g = 0.372450325` at `S₃` (`v = 64`, `|t₃| ≈ 2^{23.8}`) and the
corrections total below `3·10⁻⁹`. Lemma 1 gives the leaf bound. ∎

Elbassioni's Lemma 3.5 proves `|u_k| ≥ 3^{(v_k + 4)/12}` from `|u_{k+1}| ≥ |u_k|⁴/3`. That
step is tight only at `k = 1`, where `|u₁|² = 3`; afterwards `|1 − 2u_k⁻²|` is within
`2|u_k|⁻²` of 1. The exact rate is 2.82 times his in the exponent, and 1.97 times research
Theorem 4.24's.

**Corollary 3 (FK-A on GK and TK, every rule).** Under every valid split rule, either
variant, FK-A's recursion tree on GK `f_k` or TK `S_k`, `k ≥ 3`, has

```text
τ ≥ 2^{0.37245 n} / (n + 1).
```

On GK, `log₂ N = 2^k − 2 + log₂ 3` and `n = (log₂ N + 2 − log₂ 3)²/2`, so
`τ ≥ N^{(0.18622 − o(1)) log₂ N}`, against `c = log₂(27/16)/8 ≈ 0.094` in research
Corollary 4.26(b).

*Proof.* Research Theorem 4.25 (Lean `fkA_tree_dt`): the recursion tree unfolds into a
decision tree for `f_C` with at most `(n + 1)τ` leaves. Apply Theorem 2. ∎

## 3. The upper side

**Proposition 4 (leftmost rule on GK and TK; argued, and computed).** Number the variables
of a read-once formula so that every subformula has consecutive indices, as GK and TK have
in their natural numbering, the input of the runs below. The leftmost rule of research
Theorem 4.16 splits on the least live variable. After simplification every remaining
variable of a read-once formula is relevant, so this is the variable the left-to-right
depth-first decision tree reads next. FK-A's recursion tree is therefore that decision tree,
cut at the nodes where `|C| ≤ 1` or `|D| ≤ 1`: the cut nodes root disjoint subtrees of it,
each with at least one leaf, so FK-A's tree has at most `L_df` leaves and, being a full
binary tree (both children of a dual pair are visited), `τ ≤ 2 L_df − 1` nodes. With
interleaved indices the least live variable need not be the next depth-first read. On GK
and TK every order of the children gives the same `L_df`, which satisfies

```text
AND: L₁ = L₁(g) L₁(h),  L₀ = L₀(g) + L₁(g) L₀(h);    OR: dual;    L_df = L₁ + L₀,
log₂ L_df / v = 0.4981, 0.4765, 0.4711, 0.4697 on GK f₃–f₆   (limit 0.469254).
```

| Pair | `v` | `τ`, leftmost (`readonce_dag --leftmost`) | `2 L_df − 1` | `τ`, degree sum (research Obs. 4.4) |
| --- | --- | --- | --- | --- |
| GK `f₂` | 8 | 25 | 49 | 25 |
| GK `f₃` | 32 | 66,913 | 125,665 | 103,377 |
| GK `f₄` | 128 | 2,434,669,133,753,841,601 | 4,572,325,561,231,243,201 | 78,146,658,241,629,218,193 |
| TK `S₂` | 16 | 433 | 817 | 481 |
| TK `S₃` | 64 | 2,638,064,353 | 4,954,303,201 | 19,609,201,217 |

So the least `τ` over valid rules on GK lies between `2^{0.37245 n}/(n + 1)` and
`2^{(0.46926 + o(1)) n}`, i.e. between `N^{(0.1862 − o(1)) log₂ N}` and
`N^{(0.2347 + o(1)) log₂ N}` (Corollary 10 raises the lower end to `0.2071`); the leftmost
rule meets the upper end, and `τ/L_df ≈ 1.065` on
GK `f₃`, `f₄` and TK `S₃`. FK-A's own rule, largest degree sum, runs 1.545 and 32.1 times
longer than the leftmost rule on GK `f₃`
and `f₄`; its rate there is 0.521 and 0.516 against 0.501 and 0.477. Under the leftmost rule
`δ ≤ 2n + 2` (Theorem 4.16; `δ = n` measured), so memoisation saves at least
`2^{0.37245 n}/((n + 1)(2n + 2))`.

**Observation 5 (computed).**

- The least decision trees of GK `f₁–f₃` have 3, 25 and 62,833 leaves, and those of TK
  `S₁–S₂` 7 and 409: exactly the depth-first values. The program is a DP over isomorphism
  classes of restricted read-once formulas (20,806 classes at `f₃`), checked by truth tables
  on `f₂` (`alternating_dt.py least 3`, `lp`).
- On `f₂` the subcube-partition LP (maximise `Σ_x c(x)` subject to `Σ_{x∈Q} c(x) ≤ 1` for every
  monochromatic subcube `Q`, over 3,714 subcubes) has value 25, the exact size; Lemma 1 gives
  14.94. On TK `S₂` it has value 383, below the exact 409 (Observation 11). Coordinate ascent
  over a different `z` for each variable (200 starts on the lens boundary; working-folder
  prototype `hd-dtsize/brute.py`, not in the repository) found nothing above the uniform `w`.
- Depth-first is optimal on all 52 *balanced* alternating formulas (at every gate the
  children are isomorphic) with arities 2 and 3, at most 5 levels and 36 leaves, among them
  GK `f₃` and `T₆` of [`frequency-constant.md`](frequency-constant.md) with 364,687 leaves.
  It stays optimal for the cost `a L₁ + b L₀` for all `a, b > 0` (Proposition 12,
  `alternating_dt.py balanced`).
- It is not optimal for every read-once formula: among 800 random formulas with at most 14
  leaves (two seeds), 47 have a smaller tree, by at most 8.9% in this sample
  (`alternating_dt.py random`). All 47 are unbalanced.

**Conjecture 6.** For a balanced read-once formula and all `a, b > 0`, a depth-first decision
tree minimises `a L₁ + b L₀` over all decision trees; `a = b = 1` is the number of leaves. For
GK this would make the least `τ` over valid rules `N^{(0.2347 + o(1)) log₂ N}`, met by the
leftmost rule. The evidence is `k ≤ 3` and the balanced formulas above, for all weights (§5). The weights are the
form an induction over the gates needs: below an AND gate whose first child is evaluated
first, that child's tree is charged `L₀ + L(h) L₁`.

*Routes that do not reach it.* A lower bound by a dual solution of the subcube-partition LP
cannot prove the conjecture, since the LP is below the least tree on `S₂` (Observation 11).
A bound by a measure bounded on every subcube, which includes Lemma 1 and research
Theorem 4.24, stops at rate `0.41434` (Proposition 9). The LP's own rate on GK is not known.

## 4. The subcube norm

For `F` on `{0,1}^v` let `N₁(F)` be the least `Σ|y_Q|` over real representations
`1_{F=1} = Σ_Q y_Q 1_Q` by indicators of subcubes `Q`, and `N₀(F) = N₁(¬F)`.

**Lemma 7 (written proof).**

- (a) A decision tree for `F` has at least `N₁(F)` 1-leaves and `N₀(F)` 0-leaves.
- (b) `N₁(F) ≥ |μ(F = 1)|` for every complex measure `μ` on `{0,1}^v` with `|μ(Q)| ≤ 1` on every
  subcube `Q`.
- (c) Let `F = G(B₁, …, B_m)` with `G` read-once and the `B_i` on disjoint sets of variables. If
  each `μ_i` satisfies the condition of (b) on the cube of `B_i` and `μ_i(cube) = 1`, then so
  does `μ = μ₁ ⊗ … ⊗ μ_m`, and `μ(F = 1) = P_G(z₁, …, z_m)` with `z_i = μ_i(B_i = 1)`.

*Proof.* (a) The 1-leaves partition `F⁻¹(1)` into subcubes. (b) `μ(F = 1) = Σ y_Q μ(Q)`.
(c) A subcube of the product cube is a product of subcubes `Q_i`, and `μ(Q) = Π μ_i(Q_i)`.
Grouping the points of `F⁻¹(1)` by `y_i = B_i(x_i)` gives
`μ(F = 1) = Σ_{y ∈ G⁻¹(1)} Π_i (z_i if y_i = 1, 1 − z_i if y_i = 0)`, since `μ_i(B_i = 0) = 1 − z_i`. ∎

Lemma 1 is (b) for the product of the one-variable measures `(1 − z, z)`. A subcube indicator
has Fourier `ℓ₁` norm 1, so the bound of research Theorem 4.24 is also at most `N₁ + N₀`.

**Theorem 8 (written proof and exact check).** Write points as bit strings `x₁x₂…`, and let

```text
ν on OR(x₁, x₂):   ν(00) = −1,  ν(10) = ν(01) = 1,  ν(11) = 0;                ν(OR = 1) = 2
σ on S₁ = AND(OR(x₁, x₂), OR(x₃, x₄)):
                   σ = 1 at 1000, 0100, 0010, 0001, 1111;
                   σ = −1 at 0000, 0110, 1001, 0101;  σ = 0 elsewhere;        σ(S₁ = 1) = −2
ρ on f₂ = OR(S₁, S₁):  ρ = (ν ⊗ ν) ⊗ σ;            ρ(f₂ = 1) = 1 − (1 − 4)(1 + 2) = 10
```

Each of `ν`, `ν ⊗ ν`, `σ`, `ρ` has total 1 and modulus at most 1 on every subcube (exact check on
all 9, 81, 81 and 6,561 subcubes, `subcube_norm.py check`). Put `u₂ = 10` and
`u_{k+1} = u_k²(2 − u_k²)`. Then for `k ≥ 2`

```text
N₁(f_k) ≥ |u_k|,  N₀(f_k) ≥ |1 − u_k|,  N₁(S_k) ≥ u_k²,  N₀(S_k) ≥ u_k² − 1,
log₂|u_k| / v(f_k) ≥ λ = lim log₂|u_k| / v(f_k) = 0.4143301883 (to ten places).
```

So every decision tree for GK `f_k` or TK `S_k`, `k ≥ 2`, has more than `2^{0.41433 v}` leaves.

*Proof.* GK `f_k`, `k ≥ 2`, is a read-once formula in `4^{k−2}` disjoint copies of `f₂`, and
`S_k = AND(f_k, f_k)`. Apply Lemma 7(c) with `ρ` on every copy: the gate rules of Theorem 2
give `u_{k+1} = 2s − s²` with `s = u_k²`, the value at `S_k`. Lemma 7(b) gives the bounds.
The `u_k` are integers with `|u_k| ≥ 10`, so `|u_{k+1}| = u_k⁴ (1 − 2u_k⁻²)` and
`log₂|u_k|/v_k` decreases in `k`, by `−log₂(1 − 2u_k⁻²)/v_{k+1}`: `9.1·10⁻⁴` from `k = 2`
(`log₂ 10 / 8 = 0.41524`), less than `3·10⁻¹⁰` in total after (`|u₃| = 9800`). The same
holds for `S_k`, where `log₂ u_k² / 4^k = log₂|u_k|/v(f_k)`. ∎

The measure `σ` is not a product. A product of measures on the two `OR` blocks gives
`z₁z₂` with `|1 − z_i| = |μ_i(00)| ≤ 1`, so `|arg z_i| ≤ π/2` and `|z_i| ≤ 2 cos arg z_i`, and no such
product equals `−2`. Without `σ`, `ν ⊗ ν` on every `S₁` gives `u₂ = −8` and rate `0.3736`.

**Proposition 9 (written proof; the subcube norm on GK).** On disjoint variables
`1_{g∨h} = 1_g + 1_{¬g} 1_h = 1 − 1_{¬g} 1_{¬h}` and `1_{¬(g∨h)} = 1_{¬g} 1_{¬h}`, so

```text
OR:   N₁ ≤ min(N₁(g) + N₀(g) N₁(h), 1 + N₀(g) N₀(h)),   N₀ ≤ N₀(g) N₀(h);   AND: dual.
```

From `(N₁, N₀)(f₁) ≤ (2, 1)` these give `(4, 3)` at `S₁`, `(10, 9)` at `f₂`, `(100, 99)` at `S₂` and
`(9802, 9801)` at `f₃`, and `log₂ N₁(f_k)/v → 0.4143393882` (`subcube_norm.py check`). With
Theorem 8, `N₁ + N₀` is exactly `19` on `f₂` and `199` on `S₂`, and on GK it is
`2^{(λ_N + o(1)) v}` with `0.4143301 ≤ λ_N ≤ 0.4143394`.

So a lower bound of the form `|μ(F = 1)| + |μ(F = 0)|` with `μ` bounded on every subcube, which
includes Lemma 1 at any points with `|z| ≤ 1` and `|1 − z| ≤ 1`, Fourier `ℓ₁` and every product
of block measures, gives at most `2^{(0.41434 + o(1)) v}` leaves on GK, against `2^{(0.46926 + o(1)) v}` for depth-first.
Closing the rest needs a bound that constrains only the monochromatic subcubes.

**Corollary 10 (FK-A on GK and TK, every rule).** Under every valid split rule, either
variant, FK-A's recursion tree on GK `f_k` or TK `S_k`, `k ≥ 2`, has

```text
τ ≥ 2^{0.41433 n} / (n + 1);   on GK, τ ≥ N^{(0.20716 − o(1)) log₂ N}.
```

*Proof.* Research Theorem 4.25 and Theorem 8, as in Corollary 3. ∎

The least `τ` over valid rules on GK therefore lies between `N^{(0.2071 − o(1)) log₂ N}` and
`N^{(0.2347 + o(1)) log₂ N}`: the exponent is known within a factor `0.46926/0.41433 = 1.133`.

**Observation 11 (computed, `subcube_norm.py lp`).** The LPs reduced by the trees'
automorphisms (21 point and 231 subcube types on `f₂`; 231 and 26,796 on `S₂`), solved by
HiGHS:

| Formula | `v` | `N₁ + N₀` | partition LP | least tree = depth-first |
| --- | --- | --- | --- | --- |
| GK `f₂` | 8 | 19 | 25 | 25 |
| TK `S₂` | 16 | 199 | 383 | 409 |

## 5. All weights, and the one-gate question

Write `V(F; a, b)` for the least `a L₁ + b L₀` over decision trees for `F` (`a, b > 0`), `DF(F; a, b)`
for the least over depth-first trees, and `m₁(F)`, `m₀(F)` for the least numbers of 1-leaves and of
0-leaves, each minimised on its own. `V` is the support function of the lower-left convex hull
`H(F)` of the achievable pairs `(L₁, L₀)`, so `V = DF` for all weights exactly when the two hulls
agree. Exactly,

```text
H(1) = {(1, 0)},   H(0) = {(0, 1)},   H(F) = lower hull of ⋃_x  H(F|x=0) ⊕ H(F|x=1)   (Minkowski sum),
```

and the depth-first hull composes `(p₁, p₀) ∘ (q₁, q₀) = (p₁q₁, p₀ + p₁q₀)` for a child evaluated first
with the rest of an AND gate at its 1-leaves (OR by De Morgan). `m₁(F)` and `m₀(F)` are the ends of
`H(F)`. `alternating_dt.py` computes both hulls in integers over the restriction classes.

**Proposition 12 (computed, exact).** For GK `f₁–f₃`, TK `S₁–S₂` and the 52 balanced formulas of
Observation 5, `H(F)` is a single point and equals the depth-first hull: one depth-first tree
minimises `L₁` and `L₀` at once, and `V(F; a, b) = DF(F; a, b)` for all `a, b > 0`
(`alternating_dt.py least 3`, `balanced`). On GK `f₃` the point is `(39,424, 23,409)`.

**Lemma 13 (written proof).** Let `C` be a class of read-once formulas closed under restriction.
Then `V = DF` on `C` for all weights if and only if `DF(F) ≤ DF(F|x=0) + DF(F|x=1)` for every
`F ∈ C`, every variable `x` of `F` and all weights.

*Proof.* If the inequality holds, induct on the number of variables: constants agree, and
`V(F) = min_x (V(F|x=0) + V(F|x=1)) = min_x (DF(F|x=0) + DF(F|x=1)) ≥ DF(F) ≥ V(F)`. Conversely,
`DF(F) = V(F) ≤ V(F|x=0) + V(F|x=1) = DF(F|x=0) + DF(F|x=1)`. ∎

**Observation 14 (computed, `classes 3`).** `H ≠ DF` on 4,028 of the 20,804 non-constant
restriction classes of GK `f₃`. The least is
`(x ∧ x′ ∧ (x″ ∨ x‴ ∨ x⁗)) ∨ (y ∧ (y′ ∨ y″ ∨ (y‴ ∧ y⁗)))`, with `H = {(11, 9)}` and depth-first
`{(12, 9)}`: 20 leaves against 21. So every restriction-closed class that contains `f₃` fails Lemma
13's inequality, and Lemma 13's induction over such a class, with `DF` as its potential, cannot prove
Conjecture 6.

**Lemma 15 (written proof).** For `g, h` on disjoint variables, `m₁(g ∧ h) = m₁(g) m₁(h)` and
`m₀(g ∨ h) = m₀(g) m₀(h)`.

*Proof.* A tree for `g` with `m₁(g)` 1-leaves, with a tree for `h` with `m₁(h)` 1-leaves at each of
them, gives `≤`. For `≥`, induct on the number of variables. A tree that is a single leaf computes a
constant: a 1-leaf needs `g ≡ h ≡ 1`, where both sides are 1; a 0-leaf needs `g ≡ 0` or `h ≡ 0`, where
the right side is 0. If the root reads a variable `x` of `g`, its subtrees compute `g|x=0 ∧ h` and
`g|x=1 ∧ h`, so by induction the tree has at least `(m₁(g|x=0) + m₁(g|x=1)) m₁(h) ≥ m₁(g) m₁(h)`
1-leaves, since reading `x` first and then using least trees is a tree for `g`. A variable of `h` is
the same. The OR case is the AND case for the complements. ∎

Savický (ECCC TR02-009, Lemma 2.1) proves `dt(f₁ ⊕ f₂) ≥ dt(f₁) dt(f₂)` by the same induction. A 0-leaf
of an AND gate can end the computation while the other child is still unread, so `m₀` at an AND
gate, and `m₁` at an OR gate, have no such product; those are where interleaving can pay.

**Lemma 16 (written proof).** Let `F` be built by binary gates over disjoint blocks, and let `G` be
the number of gates above the blocks. For a gate over `g, h` put

```text
SEQ_AND = min( V(g; V(h; a, b), b),  V(h; V(g; a, b), b) ),    SEQ_OR = min( V(g; a, V(h; a, b)), … ).
```

- (a) If `V = DF` on every block for all weights, and `V(gate) ≥ θ · SEQ(gate)` at every gate for all
  weights, then `V(F) ≥ θ^G DF(F)`.
- (b) If every block has `m₁ = L₁` and `m₀ = L₀` of one depth-first tree, and every gate satisfies the
  one inequality Lemma 15 leaves open,

  ```text
  AND:  m₀(g ∧ h) ≥ θ · min( m₀(g) + m₁(g) m₀(h),  m₀(h) + m₁(h) m₀(g) ),     OR: the dual for m₁,
  ```

  then `m₁ ≥ ℓ₁` and `m₀ ≥ ℓ₀` on every subformula, where `(ℓ₁, ℓ₀)` follows the depth-first
  recursion from the blocks' `(L₁, L₀)` with the factor `θ` on the open coordinate. With `θ = 1` this
  is the depth-first pair, so `V = DF` for all weights. On GK with `f₃` blocks every decision tree for
  `f_K`, `K ≥ 3`, has at least `2^{(z₃/96 − log₂(1/θ)/48) v}` leaves, where
  `z₃ = log₂(39,424² · 23,409)` and `z₃/96 = 0.4692536`.

*Proof.* (a) Induct over the gates: `V(F) ≥ θ^{G(F)} DF(F)` for every subformula `F` above the
blocks. Two facts are used. `V(g; a, b)` is nondecreasing in each weight, and for `0 < λ ≤ 1`,
`V(g; λc, b) ≥ V(g; λc, λb) = λ V(g; c, b)`, likewise in the second weight. At an AND gate,

```text
V(g; V(h; a, b), b) ≥ V(g; θ^{G(h)} DF(h; a, b), b) ≥ θ^{G(h)} V(g; DF(h; a, b), b) ≥ θ^{G(g)+G(h)} DF(g; DF(h; a, b), b),
```

and the same with `g` and `h` exchanged. `DF` of the gate is the smaller of the two orders, so
`V(F) ≥ θ · SEQ ≥ θ^{G(g)+G(h)+1} DF(F)`. At an OR gate the inner value enters the second weight.

(b) Define lower bounds `ℓ₁, ℓ₀` by the depth-first recursion with the factor `θ` on the open
coordinate, starting from the exact block values. Lemma 15 is exact on the other coordinate, and
both right sides are nondecreasing in `m₁` and `m₀`, so `m₁ ≥ ℓ₁` and `m₀ ≥ ℓ₀` by induction. Every
tree has `L₁ ≥ m₁` and `L₀ ≥ m₀`, so with `θ = 1` it has `a L₁ + b L₀ ≥ a ℓ₁ + b ℓ₀ = DF(F; a, b)`.
On GK, drop the `1 +` terms (the rate below is weaker than the recursion): with `p = log₂ ℓ₁`, `q = log₂ ℓ₀` at
`f_k` and `t = log₂ θ ≤ 0`, the AND gate gives `S_k` the bounds `2p` and `q + p + t`, and the OR gate
gives `f_{k+1}` the bounds `3p + q + 2t` and `2p + 2q + 2t`. So `z = 2p + q` satisfies
`z_{k+1} ≥ 4z_k + 6t`, hence `z_K ≥ 4^{K−3}(z₃ + 2t)`, while `v = 32 · 4^{K−3}`. A tree has at least
`max(ℓ₁, ℓ₀) ≥ 2^{z/3}` leaves. TK `S_K = f_K ∧ f_K′` has the bounds `2p` and `p + q + t`, so the same
rate up to `o(1)` per variable. ∎

| Hypothesis at each gate above `f₃` blocks | Rate bound | `θ` that passes `0.4143394` |
| --- | --- | --- |
| (a) `V(gate) ≥ θ · SEQ`, all weights | `0.469254 − log₂(1/θ)/32` | `0.2958` |
| (b) the open coordinate only | `0.4692536 − log₂(1/θ)/48` | `0.1609` |

Proposition 12 supplies the blocks for both (`alternating_dt.py theta`). Hypothesis (a) implies
(b): at weights `(ε, 1)`, `ε → 0`, `V(g ∧ h)` tends to `m₀(g ∧ h)` and `V(g; V(h; ε, 1), 1)` to
`min_{p ∈ H(g)} (p₁ m₀(h) + p₀) ≥ m₁(g) m₀(h) + m₀(g)`. So (b) asks for less, and it loses on one
coordinate per gate. With `θ = 1` and one-variable blocks, the first conclusion of (b) gives
Conjecture 6 on GK and TK.

**Conjecture 17 (one gate).** For a balanced binary alternating formula `g` with an OR root and a
disjoint copy `g′`, `m₀(g ∧ g′) ≥ θ · m₀(g)(1 + m₁(g))` with an absolute `θ > 0.1609`.

By De Morgan this covers the OR gates of GK, whose children are TK trees. Any such `θ` puts the
least `τ` over valid rules on GK above every subcube-bounded measure (Proposition 9); with `θ = 1`
Lemma 16(b) gives Conjecture 6 on GK and TK.

**Observation 18 (computed, `gates 18 12`).** For the 14 balanced alternating formulas `g, h` with
an OR root, arities 2 and 3 and at most 18 leaves, isomorphic or not, the least trees for
`g ∧ h` are depth-first at the gate for all weights: `H(g ∧ h)` is the hull of the two orders with
least trees for the children, on all 105 pairs. Restricted children break this. For `g, h` with at
most 12 leaves and `a, b` restrictions of them, compare `H(a ∧ b)` with the hull of the two orders that
finish `a` or `b` first (`a`, `b` as units), and, more leniently, with depth-first at the flattened gate,
where an AND-rooted restriction's own children may be interleaved with the other child:

| Children | Pairs | Not depth-first, units (least ratio) | Not depth-first, flattened (least ratio) |
| --- | --- | --- | --- |
| one unrestricted, one restricted | 2,299 | 77 (`5/7`) | 42 (`7/8`) |
| both restricted | 25,993 | 1,733 (`44/65 = 0.6769`) | 1,096 (`88/109 = 0.8073`) |

The least ratio with one child unrestricted is `5/7`, at the unrestricted `g = (x∧x∧x) ∨ (x∧x∧x)` and
`b = x ∧ x ∧ (x ∨ x)`, a restriction of the balanced `OR₂(AND₃(OR₂))`. So the statement that held
in every test needs both children unrestricted and balanced. An induction over a decision tree passes through restricted pairs, so a proof of
Conjecture 17 needs a potential other than the gate's depth-first value, or an exchange argument
over whole subtrees in the manner of Tarsi's theorem for i.i.d. leaves (cited, not read).

*Rank.* A tree of rank `r` has at least `2^r` leaves. GK `f₁–f₃` have least rank 1, 3 and 11, and the
depth-first tree of `f_k` has rank `(v + 1)/3` for `k ≤ 9` (`alternating_dt.py rank 9`). So rank gives
rate at most `1/3` on these, below Theorem 8.

## 6. Scope

- Elbassioni's FK-B bound (his §4) and the padded KKW instances are not touched here.
- The bounds hold for unmemoised FK-A. With memoisation the leftmost rule has `δ ≤ 2n + 2`; the
  degree-sum rule's `δ` (Conjectures 4.19, 4.30) is not bounded by this method.
- Lean: research Theorem 4.25 is in Lean; Lemma 1 and Theorem 2 need complex
  multilinear evaluation of `DecisionTree` and the recursion estimate. Lemma 7 and Theorem 8
  need only integer measures, finite block checks (at most 6,561 subcubes) and the integer
  recursion `u_k`, so they are the shorter route to a formal `0.41433`.

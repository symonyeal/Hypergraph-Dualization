# FK-A on the alternating trees: complex evaluation

Elbassioni (arXiv:2610.34474, §3) bounds the size of a decision tree by the multilinear
extension of its function at `w = (1 + i√3)/2`. Research Theorem 4.25 (Lean) turns any
decision-tree bound into a bound on FK-A's recursion tree under every valid rule. This
note evaluates Elbassioni's bound exactly on GK and TK, bounds the result from above, and
compares the two. Dated 17 November 2026.

Status labels: *written proof* (prose, not in Lean), *computed* (`experiments/alternating_dt.py`
or `experiments/readonce_dag`, with its bound), *conjecture*.

| Bound on `log₂(leaves)/v` for GK `f_k`, TK `S_k` | Rate | Source |
| --- | --- | --- |
| Elbassioni, Lemma 3.5 | `log₂3/12 = 0.1321` | arXiv:2610.34474 (GK only) |
| JRSW Fourier `ℓ₁` | `log₂(27/16)/4 = 0.1887` | research Theorem 4.24, Lean |
| exact `log₂|P(w)|` | `0.37245` | Theorem 2 here, written proof |
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
`N^{(0.2347 + o(1)) log₂ N}`; the leftmost rule meets the upper end, and `τ/L_df ≈ 1.065` on
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
  14.94. Coordinate ascent over a different `z` for each variable (200 starts on the lens
  boundary; working-folder prototype `hd-dtsize/brute.py`, not in the repository) found
  nothing above the uniform `w`.
- Depth-first is optimal on all 50 *balanced* alternating formulas (at every gate the
  children are isomorphic) with arities 2 and 3, at most 4 levels and 36 leaves, among them
  `T₆` of [`frequency-constant.md`](frequency-constant.md) with 364,687 leaves
  (`alternating_dt.py balanced`).
- It is not optimal for every read-once formula: among 800 random formulas with at most 14
  leaves (two seeds), 47 have a smaller tree, by at most 8.9% in this sample
  (`alternating_dt.py random`). All 47 are unbalanced.

**Conjecture 6.** For a balanced read-once formula the least decision tree is a depth-first
one. For GK this would make the least `τ` over valid rules `N^{(0.2347 + o(1)) log₂ N}`, met
by the leftmost rule. The evidence is `k ≤ 3` and the balanced formulas above.

*A possible route.* Lemma 1 is a dual solution of the subcube-partition LP that composes
through AND and OR, and reaches only `γ = 0.37245`. A composable dual reaching the
depth-first recursion would prove the conjecture. The only LP evidence is its exactness at
`f₂`; whether it is exact on the unbalanced formulas where depth-first loses is untested.

## 4. Scope

- Elbassioni's FK-B bound (his §4) and the padded KKW instances are not touched here.
- The bounds hold for unmemoised FK-A. With memoisation the leftmost rule has `δ ≤ 2n + 2`; the
  degree-sum rule's `δ` (Conjectures 4.19, 4.30) is not bounded by this method.
- Lean: research Theorem 4.25 is in Lean; Lemma 1 and Theorem 2 need complex
  multilinear evaluation of `DecisionTree` and the recursion estimate.

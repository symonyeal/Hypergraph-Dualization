# The constant in the Fredman–Khachiyan frequency lemma

Track B asked how small the largest variable frequency of a dual pair can be. This note
puts the question in product form, `|C|·|D| ≥ b^{1/eps − 1}`, and asks for the best base
`b`. It proves `b = 4` for all dual pairs, shows that the alternating word families of
[`hard-classes.md`](hard-classes.md) §3 meet `b = 8` exactly, and refutes `b = 8` with a
read-once pair on 36 variables. For read-once pairs it proves
`|C|·|D| ≥ e^{2(1/eps − 1)}`. Dated 17 November 2026; Conjecture 6 was stated and refuted
the same day.

Status labels: *written proof* (proved here in prose, not in Lean), *computed* (a program
in `experiments/`, with its bound), *conjecture*. Nothing in this note is in Lean yet.

## Setting

A *dual pair* is `(C, D)` with `C` a Sperner family of nonempty sets and `D = Tr(C)`: the
minterms and the maxterm clauses of a nonconstant monotone function `f`. Write

```text
A = |C|,  B = |D|,  N = A + B,
a_v = deg_C(v)/A,  b_v = deg_D(v)/B,
s = 1/max_v a_v,  t = 1/max_v b_v,  r = 1/eps = min(s, t).
```

`eps` is the quantity `ε(G, H)` of research §3 and the `eps` of `hard-classes.md` §0,
where `c = eps · log₂N`.

Known before this note:

- Fredman–Khachiyan 1996, in the form of Gurvich–Khachiyan 1997, (1)–(2): some edge of
  `C ∪ D` has at most `log₂N` points, every term meets every clause, hence
  `eps ≥ 1/log₂N`, i.e. `c ≥ 1`.
- Gurvich–Khachiyan 1997, Proposition: the alternating trees `f_k` (the GK family) have
  `eps = 2^{1−k}` and `eps ≤ 2/log₂N`, so `c ≤ 2` is attained; "tight up to a factor of 2".
- `hard-classes.md` (3.1): the words `w ∈ {X, Y}^k` reach `c → 3/2`.

So the asymptotic constant `c_∞ = liminf eps · log₂N`, over dual pairs with `eps → 0`,
lies in `[1, 3/2]`; GK97's bracket `[1, 2]` is for this constant. Over all pairs the best
constant is 1, attained by a single variable (`eps = 1`, `N = 2`). Since
`2√(A·B) ≤ N ≤ 2 max(A, B)`, a product base `b` gives `c_∞ ≥ (log₂ b)/2`.

## 1. A product form of the lemma

**Lemma 1 (edge sizes; written proof).** Every term of a dual pair has at least `t`
points and every clause at least `s`; in particular every edge has at least `r = 1/eps`.

*Proof.* A term `c` meets every clause, so `B ≤ Σ_{v∈c} deg_D(v) ≤ |c| · B/t`. The same
count with the roles exchanged bounds clauses. ∎

**Theorem 2 (product form; written proof).** Let `(C, D)` be a dual pair with `eps < 1`
and `s' = eps/(1 − eps)`. Then

```text
A^{−s'} + B^{−s'} ≤ 1,   hence   A·B ≥ 4^{1/eps − 1}   and   eps ≥ 2/(2 + log₂(A·B)).
```

The last form implies Fredman–Khachiyan's `eps ≥ 1/log₂N`, and is strictly stronger
unless `A = B`, since `A·B ≤ N²/4`.

*Proof.* Let `X` contain each point independently with probability `p`. Then `f(X) = 1`
iff `X` contains a term, and `f(X) = 0` iff `V \ X` contains a clause. By the union bound
and Lemma 1, for every `p ∈ (0, 1)`,

```text
1 ≤ Σ_{c∈C} p^{|c|} + Σ_{d∈D} (1 − p)^{|d|} ≤ A p^r + B (1 − p)^r.
```

The right side is least at `p/(1 − p) = (B/A)^{s'}`, with `s' = 1/(r − 1)`, where it equals
`A·B·(A^{s'} + B^{s'})^{−1/s'}`. So `A^{s'} + B^{s'} ≤ (A·B)^{s'}`, which is the first claim.
By AM–GM, `1 ≥ A^{−s'} + B^{−s'} ≥ 2 (A·B)^{−s'/2}`, so `A·B ≥ 2^{2/s'} = 4^{r−1}`. ∎

The union bound at a chosen bias is FK96's Kraft argument, and the step from Lemma 1 is
the one FK96 use; choosing the bias and keeping the product is the only new step. The
statement was not found in FK96 (as quoted by GK97), GK97 or the sources of
[`literature-2026-11.md`](literature-2026-11.md); priority is not claimed.

## 2. Exact equality on the word families

**Proposition 3 (written proof).** Every word `w ∈ {X, Y}^k` of `hard-classes.md` §3 is a
dual pair with `eps = 2^{−k}` and `A·B = 8^{2^k − 1} = 8^{1/eps − 1}`. The single
variable `x` also has `A·B = 1 = 8^{1/eps − 1}`. The GK family has
`A·B = 2^{2^{k+1} − 3}` against `8^{1/eps − 1} = 2^{3·2^{k−1} − 3}`.

*Proof.* `T_w` is `2^k`-uniform and regular on `4^k` points, and so is `Tr(T_w) = T_w̄`, so
every frequency is `2^{−k}`. By (3.1), `log₂ A + log₂ B = a(w) + a(w̄) = 3(2^k − 1)`. The GK
counts are GK97's `|F_k| = 2^{2^k−1}`, `|G_k| = 2^{2^k−2}`, `eps = 2^{1−k}`. ∎

So the base 4 of Theorem 2 cannot be raised past 8, and §4 lowers that ceiling to 7.78.
The GK family is far from it: its defect, defined next, is `2^{k−1}`.

## 3. Tensor powers

Define the *defect* of a dual pair

```text
Δ(C, D) = log₂ A + log₂ B + 3 − 3/eps.
```

**Lemma 4 (tensor power; written proof).** Let `T` be a template with `k` edges and
`k*` minimal transversals, both `ρ`-uniform, each point in `k/ρ` edges and `k*/ρ`
transversals: a word of rank `ρ`, or the template `T₆` of Proposition 7 with `ρ = 6`.
Let `F = T[f, …, f]` substitute disjoint copies of a nonconstant monotone `f` into the
points of `T`. Then `F` is a dual pair with

```text
eps(F) = eps(f)/ρ   and   Δ(F) = ρ · Δ(f) + Δ(T),   Δ(T) = log₂(k k*) + 3 − 3ρ.
```

For a word, `Δ(T) = 0` (Proposition 3).

*Proof.* Research Theorem 5.1 (`tr_subst_of_disjoint`, `card_subst`) gives `C_F = T[C]`,
`D_F = Tr(T)[D]`, `|C_F| = k A^ρ`, `|D_F| = k* B^ρ`. A point `(i, v)`, copy `i` of `v`, lies
in `(k/ρ) · A^{ρ−1} · deg_C(v)` terms, so its term frequency is `a_v/ρ`; the clause side is
the same with `Tr T`. Then
`Δ(F) = log₂(k k*) + ρ log₂(A·B) + 3 − 3ρ/eps(f) = ρ Δ(f) + Δ(T)`. ∎

**Corollary 5.** The following are equivalent:

1. every dual pair satisfies `A·B ≥ 8^{1/eps − 1}`;
2. `liminf eps · log₂(A·B) ≥ 3` over dual pairs with `eps → 0`;
3. some function `g(eps) = o(1/eps)` bounds `log₂(A·B) ≥ 3/eps − g(eps)` on all dual pairs.

*Proof.* (1) gives (3) with `g = 3`, and (3) gives (2). If (1) fails at `f`, Lemma 4 with
words of length `j`, rank `2^j`, gives pairs `F_j` with
`eps(F_j) · log₂(A_j B_j) = 3 − 3 eps(F_j) + eps(f) Δ(f) → 3 + eps(f) Δ(f) < 3`. ∎

## 4. The base 8 fails

**Conjecture 6 (refuted by Proposition 7).** Every dual pair satisfies
`|C| · |D| ≥ 8^{1/eps − 1}`.

The exhaustive checks below found no counterexample on at most 6 points or among
read-once formulas with at most 13 input leaves.

**Proposition 7 (counterexample; written proof and computed).** Let

```text
T₆ = AND_{k<2} OR_{j<3} AND_{i<3} (x_{kji0} ∨ x_{kji1})
```

on 36 variables. Its minterms take, in each half `k`, one branch `j` and one of the two
variables in each of its three clauses, so `|C| = (3 · 2³)² = 576`. Its maxterms are the
maxterms of one half, one clause `x_{kji0} ∨ x_{kji1}` from each branch `j`, so
`|D| = 2 · 3³ = 54`. Every term and every clause has 6 points, and every variable has
frequency exactly `1/6` on both sides. So `eps = 1/6` and

```text
|C| · |D| = 31,104 < 32,768 = 8⁵,    Δ(T₆) = log₂ 31,104 + 3 − 18 = −0.0752.
```

*Proof.* The counts are research Theorem 5.1 on the formula; the frequencies follow by
symmetry, every variable being equivalent under the automorphisms of the formula.
`experiments/frequency_readonce.py check` builds the 576 terms explicitly, computes `Tr`
with `fka.transversal`, confirms duality with FK-A, and recounts every number above. ∎

*Consequences.*

- By Corollary 5, `liminf eps · log₂(A·B) < 3`. Iterating `T₆` (Lemma 4 with `f = T₆`)
  gives `Δ = −0.0752 (6^n − 1)/5` at `eps = 6^{−n}`, and
  `eps · log₂(A·B) → log₂(k k*)/(ρ − 1) = 2.985`.
- Symmetric templates do better. Gates `AND_m`, `OR_m` alternating, with the products of
  the AND arities and of the OR arities both equal to `ρ`, give a template as in Lemma 4.
  The best found with `m ≤ 6`, `ρ ≤ 400` is `ρ = 384`, bottom-up
  `AND₂ OR₃ (AND₂ OR₂)⁶ AND₃ OR₂`, with rate `log₂(k k*)/(ρ − 1) = 2.9595`
  (`frequency_readonce.py templates 6 400`). So the best base `b` is at most
  `2^{2.9595} ≈ 7.78`.
- The words gain by balance, not by product. Among the same templates the least
  `max(log₂ k, log₂ k*)/(ρ − 1)`, the value of `c_∞` for iterating one template, is
  1.5007; none went below `3/2`. `T₆` itself has `log₂ k = 9.17`, `log₂ k* = 5.75`.
- Research Proposition 5.2 assumes `(P)`: `k·k* ≥ 8^{ρ−1}`. `T₆` is a read-once template
  of the kind it treats (`ρ`-uniform on `ρ²` points, with `ρ`-uniform dual) that violates
  `(P)`. So `(P)` is not automatic, even without primes. Open problem 5.3 (D3) asks only
  about prime templates and is unchanged.
- Corollary 5's other equivalent forms fail too: no `o(1/eps)` loss rescues the base 8.

*Evidence for Conjecture 6 before the counterexample (computed).*

| Search | Bound | Least defect | Pairs of defect 0 |
| --- | --- | --- | --- |
| `frequency_constant N` (Rust) | every monotone function of `N ≤ 6` variables: 7,828,352 dual pairs at `N = 6` | 0 | `x` and the labelled copies of `X`, `Y`: 10, 35, 96 at `N = 4, 5, 6` |
| `frequency_families.py closure 13` | every read-once formula with ≤ 13 leaves: 29,228 tuples `(A, B, s, t)`, `1/eps ≤ 3` | 0 | |

The count of equality cases at `N = 6` is `6 + 15·6`: one single variable per point, and on
each 4-set the three labellings of `X` and three of `Y`. A read-once pair needs at least
`r²` leaves (`Σ_v a_v b_v = 1` below), so the closure stops at `r = 3`, and `T₆` needs 36.
The earlier random composition results (`frequency_families.py compose 4000 S`, seeds 1–4)
are withdrawn. The script read one-indexed Witt blocks as zero-indexed, so 30 of its
66 template edges used a vertex outside the declared ground set. The resulting
36 edges on the purported dual side should have been the same 66 Witt blocks.
The corrected command derives both sides from the repository's hypergraph
constructors. The exhaustive counts in the table use separate code paths.

*How it was found.* The largest `Ψ` satisfying (a)–(c) of §5, computed on a grid of step
1/8, has `Ψ(6, 6) = 89.55 < 90 = 3r(r − 1)`; its optimal splits are `T₆`.

## 5. Read-once pairs: the base e²

For a read-once function `f`, research Theorem 5.1 on disjoint supports gives the gate
rules. If `f = g₁ ∨ g₂` then `A = A₁ + A₂`, `B = B₁ B₂`, and with `μ_i = A_i/A`,
`a_v(f) = μ_i a_v(g_i)` and `b_v(f) = b_v(g_i)` for `v` in `g_i`; AND is dual. Every term
meets every clause in exactly one point, so `Σ_v a_v b_v = 1`.

Write `lg = log₂`, `h` for the binary entropy, `c = 2/ln 2 ≈ 2.885`, and for `X, Y ≥ 1`

```text
Φ(X, Y) = X Y [c (1 − 1/m) + lg(M/m)/m],   m = min(X, Y),  M = max(X, Y);
        = c Y (X − 1) + Y lg(Y/X)   when X ≤ Y.
Ψ(x, y) = Φ(max(x, 1), max(y, 1))   for x, y > 0.
```

**Theorem 8 (read-once pairs; written proof).** Every read-once dual pair satisfies

```text
x lg A + y lg B ≥ Ψ(x, y)   for all 0 < x ≤ s, 0 < y ≤ t.
```

In particular, with `m = min(s, t)`, `M = max(s, t)`,

```text
lg A / t + lg B / s ≥ c (1 − 1/m) + lg(M/m)/m,
lg A + lg B ≥ (2/ln 2)(1/eps − 1),   i.e.   |C| · |D| ≥ e^{2(1/eps − 1)}.
```

*Proof.* Induction on the formula. A single variable has `A = B = s = t = 1`. Let
`f = g₁ ∨ g₂`, `x ≤ s(f)`, `y ≤ t(f)`. The gate rules give `s(g_i) ≥ x μ_i`,
`t(g_i) ≥ y`, and `lg A = μ₁ lg A₁ + μ₂ lg A₂ + h(μ₁)`. So, by induction,

```text
x lg A + y lg B = Σ_i (x μ_i lg A_i + y lg B_i) + x h(μ₁) ≥ Ψ(x μ₁, y) + Ψ(x μ₂, y) + x h(μ₁).
```

AND is the same with the roles of `(x, A)` and `(y, B)` exchanged. So it suffices that

- (a) `Ψ(x, y) ≤ 0` for `x, y ≤ 1`;
- (b) `Ψ(x₁ + x₂, y) ≤ Ψ(x₁, y) + Ψ(x₂, y) + x₁ lg(x/x₁) + x₂ lg(x/x₂)`, `x = x₁ + x₂`;
- (c) (b) with the arguments exchanged.

(a) holds as `Φ(1, 1) = 0`, and (c) follows from (b) since `Ψ(x, y) = Ψ(y, x)`.

For (b), fix `y`, put `Y = max(y, 1)`, `φ(X) = Φ(X, Y)`, `ψ(X) = φ(X) − X lg X` and
`q(X) = ψ(X)/X` for `X ≥ 1`. For `X ≥ Y`, `q(X) = c(Y − 1) − lg Y` is constant. For
`1 ≤ X ≤ Y`, with `z = Y/X ≥ 1`,

```text
q′(X) = (z − 1 − z ln z)/(X ln 2) ≤ 0,
```

since `z ln z ≥ z − 1`. So `q` is non-increasing on `[1, ∞)`, and `ψ(1) = Y lg Y ≥ 0`.
Write `E = x₁ lg(x/x₁) + x₂ lg(x/x₂) ≥ 0`.

- `x₁, x₂ ≥ 1`. Then `E = x lg x − x₁ lg x₁ − x₂ lg x₂`, and (b) reads
  `ψ(x) ≤ ψ(x₁) + ψ(x₂)`. This holds: `ψ(x) = x₁ q(x) + x₂ q(x) ≤ x₁ q(x₁) + x₂ q(x₂)`.
- `x₁ < 1 ≤ x₂`. Then (b) reads `ψ(x) ≤ ψ(1) + ψ(x₂) − x₁ lg x₁`. This holds:
  `ψ(x) = x₂ q(x) + x₁ q(x) ≤ ψ(x₂) + x₁ ψ(1) ≤ ψ(x₂) + ψ(1)`, and `−x₁ lg x₁ > 0`.
- `x₁, x₂ < 1`, `x ≤ 1`. Then (b) reads `φ(1) ≤ 2φ(1) + E`, true as `φ(1) ≥ 0`.
- `x₁, x₂ < 1 < x`. Then (b) reads `ψ(x) ≤ 2ψ(1) − x₁ lg x₁ − x₂ lg x₂`. This holds:
  `ψ(x) = x q(x) ≤ x ψ(1) ≤ 2 ψ(1)`.

At `(x, y) = (s, t)`, `s lg A + t lg B ≥ s t G(s, t)` with `G` the right side of the
second display; at `(r, r)`, `r(lg A + lg B) ≥ Φ(r, r) = c r (r − 1)`. Finally
`2^{c} = e²`. ∎

*Remarks.*

- The two-parameter form is an equality for `AND` or `OR` of `k` variables, where both
  sides equal `lg k`; the product form is an equality only for a single variable. The
  words are not equality cases: `3(r − 1) > c(r − 1)`.
- For read-once pairs, `eps · lg N ≥ (1 − eps)/ln 2 + eps`, so their asymptotic constant
  satisfies `log₂ e ≈ 1.4427 ≤ c_∞ ≤ 3/2`, against `[1, 3/2]` in general. Their best base
  satisfies `e² ≈ 7.389 ≤ b ≤ 7.78`.
- The two-parameter form is failed route 4 below with the constant 3 replaced by
  `2/ln 2`. For the AND of two copies of a pair with `t < s < 2t` at equality in the form
  with constant `c`, the AND satisfies the form iff `(z + 1) ln z ≥ c ln 2 · (z − 1)`,
  `z = s/t`. For `c = 3` this fails near `z = 1`; for `c = 2/ln 2` it is the classical
  `ln z ≥ 2(z − 1)/(z + 1)`.
- `frequency_readonce.py split` checks (b) on a grid over `(0.001, 1000)³`, and
  `frequency_readonce.py closure 13` checks the two-parameter form on every read-once
  formula with at most 13 leaves (least slack 0, at `AND` of variables).

## 6. Failed routes

1. *Union bounds at any bias.* The inequalities `A p^r + B(1 − p)^r ≥ 1`, `p ∈ (0, 1)`,
   are all that Theorem 2 uses, and `A = B = 2^{r−1}` satisfies every one of them, so the
   base 4 is the limit of this route. Replacing the union bound by Harris–Kleitman,
   `Π_c (1 − p^{|c|}) + Π_d (1 − (1 − p)^{|d|}) ≤ 1`, changes only constant factors. On the
   all-`X` word of rank `r`, at its threshold `p* = (√5 − 1)/2`, the two union bounds are
   `A p*^r = 1.236^r/2` and `B (1 − p*)^r = 1.528^r/4`: both are off by exponential factors.
2. *Superadditivity across a split.* With `f₀ = f|x=0`, `f₁ = f|x=1`, the inequality
   `A·B ≥ A(f₀)B(f₀)·A(f₁)B(f₁)` holds with equality on `X` but fails on
   `f = xw ∨ yu ∨ z` at `x`: `12 < 4 · 6`.
3. *Induction on inherited degree caps.* Children keep the parent's degree caps, but `D/x`
   can shrink to the clauses through `x`, so a child's own frequency bound degenerates.
4. *The two-parameter half-plane `Q`.* With `s ≤ t`:
   `(s/t) lg A + lg B ≥ 3s − 3 + lg(t/s)`, and its mirror. It holds on all six-variable
   functions and fails on the 12-leaf read-once
   formula `(((x&x)|((x&x)|(x&x)))&((x&x)|((x&x)|(x&x))))`, with
   `(A, B, s, t) = (9, 16, 3, 4)` and slack `−0.0376`. With 3 replaced by `2/ln 2` it is
   Theorem 8.
5. *Bounded closure.* Every read-once tuple `(A, B, deg_max C, deg_max D)` with
   `A·B ≤ K`, pruned to the Pareto-least degrees for each `(A, B)`, is finite but has
   21,499 tuples at `K = 2^{10}` (`r ≤ 4`) and did not finish at `2^{12}` in two minutes.

## 7. Open questions

- **The FK constant.** Is `c_∞ = 3/2`, i.e. does every family with `eps → 0` have
  `eps · lg max(|C|, |D|) ≥ 3/2 − o(1)`? The product form cannot decide it (Proposition
  7); the evidence is the template search above (least 1.5007). For read-once pairs,
  `c_∞ ≥ log₂ e` by Theorem 8.
- **The read-once base.** It lies in `[e², 2^{2.9595}]`. Theorem 8's induction allows any
split ratio `μ`, while a gate has `μ = A₁/A`. Optimizing the potential `Ψ` under the
  sampled constraints (a)–(c) on a grid of step 1/8 gives
  `Ψ(8, 8) ≤ 167.02 = 2.9825 · 8 · 7`. This bounds this potential method at `r = 8`.
- **General pairs.** Theorem 8's induction uses the gate decomposition. For general
  pairs, the analogue would split on a variable; only Theorem 2's base 4 is proved.
- **Lean.** Lemma 1, Theorem 2 and Lemma 4 use counting, the union bound and Theorem 5.1,
  which is already in Lean. Theorem 8 needs an induction on read-once formulas and the
  one-variable inequality `q′ ≤ 0`.

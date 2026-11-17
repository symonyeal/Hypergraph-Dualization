# The constant in the Fredman–Khachiyan frequency lemma

Track B asked how small the largest variable frequency of a dual pair can be. This note
puts the question in product form, proves a product-form strengthening of the
Fredman–Khachiyan lemma, shows that the alternating word families of
[`hard-classes.md`](hard-classes.md) §3 attain an exact identity, reduces the sharp
statement to an asymptotic one, and states the sharp statement as Conjecture 6 with its
evidence and search bounds. Dated 17 November 2026.

Status labels: *written proof* (proved here in prose, not in Lean), *computed* (a program
in `experiments/`, with its bound), *conjecture*. Nothing in this note is in Lean yet.

## Setting

A *dual pair* is `(C, D)` with `C` a Sperner family of nonempty sets and `D = Tr(C)`: the
minterms and the maxterm clauses of a nonconstant monotone function `f`. Write

```text
A = |C|,  B = |D|,  N = A + B,
a_v = deg_C(v)/A,  b_v = deg_D(v)/B,  eps = max_v max(a_v, b_v),  r = 1/eps.
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

So the asymptotic constant `c_∞ = liminf eps · log₂N`, over dual pairs with `eps → 0`, lies
in `[1, 3/2]`; GK97's bracket `[1, 2]` is for this constant. Over all pairs the best
constant is 1, attained by a single variable (`eps = 1`, `N = 2`).

## 1. A product form of the lemma

**Lemma 1 (edge sizes; written proof).** Every term and every clause of a dual pair has at
least `r = 1/eps` points.

*Proof.* A term `c` meets every clause, so `B ≤ Σ_{v∈c} deg_D(v) ≤ |c| · eps · B`. The same
count with the roles exchanged bounds clauses. ∎

**Theorem 2 (product form; written proof).** Let `(C, D)` be a dual pair with `eps < 1`
and `s = eps/(1 − eps)`. Then

```text
A^{−s} + B^{−s} ≤ 1,   hence   A·B ≥ 4^{1/eps − 1}   and   eps ≥ 2/(2 + log₂(A·B)).
```

The last form implies Fredman–Khachiyan's `eps ≥ 1/log₂N`, and is strictly stronger
unless `A = B`, since `A·B ≤ N²/4`.

*Proof.* Let `X` contain each point independently with probability `p`. Then `f(X) = 1`
iff `X` contains a term, and `f(X) = 0` iff `V \ X` contains a clause. By the union bound
and Lemma 1, for every `p ∈ (0, 1)`,

```text
1 ≤ Σ_{c∈C} p^{|c|} + Σ_{d∈D} (1 − p)^{|d|} ≤ A p^r + B (1 − p)^r.
```

The right side is least at `p/(1 − p) = (B/A)^s`, with `s = 1/(r − 1)`, where it equals
`A·B·(A^s + B^s)^{−1/s}`. So `A^s + B^s ≤ (A·B)^s`, which is the first claim. By AM–GM,
`1 ≥ A^{−s} + B^{−s} ≥ 2 (A·B)^{−s/2}`, so `A·B ≥ 2^{2/s} = 4^{r−1}`. ∎

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

So the constant 4 of Theorem 2 cannot be raised past 8, and on the words the base 8 is
exact at every size. The GK family is far from it: its defect, defined next, is `2^{k−1}`.

## 3. The sharp statement reduces to an asymptotic one

Define the *defect* of a dual pair

```text
Δ(C, D) = log₂ A + log₂ B + 3 − 3/eps.
```

**Lemma 4 (tensor power; written proof).** Let `T` be a word of rank `ρ` and let
`F = T[f, …, f]` substitute disjoint copies of a nonconstant monotone `f` into the points
of `T`. Then `F` is a dual pair with

```text
eps(F) = eps(f)/ρ   and   Δ(F) = ρ · Δ(f).
```

*Proof.* Research Theorem 5.1 (`tr_subst_of_disjoint`, `card_subst`) gives `C_F = T[C]`,
`D_F = Tr(T)[D]`, `|C_F| = k A^ρ`, `|D_F| = k* B^ρ`, with `k = |T|`, `k* = |Tr T|`. A point
`(i, v)`, copy `i` of `v`, lies in `deg_T(i) · A^{ρ−1} · deg_C(v)` terms. `T` is regular, so
`deg_T(i) = k/ρ` and the term frequency of `(i, v)` is `a_v/ρ`; the clause side is the
same with `Tr T`. Then, with `log₂(k k*) = 3(ρ − 1)` (Proposition 3),
`Δ(F) = 3(ρ − 1) + ρ log₂(A·B) + 3 − 3ρ/eps(f) = ρ Δ(f)`. ∎

**Corollary 5.** The following are equivalent:

1. every dual pair satisfies `A·B ≥ 8^{1/eps − 1}`;
2. `liminf eps · log₂(A·B) ≥ 3` over dual pairs with `eps → 0`;
3. some function `g(eps) = o(1/eps)` bounds `log₂(A·B) ≥ 3/eps − g(eps)` on all dual pairs.

*Proof.* (1) gives (3) with `g = 3`, and (3) gives (2). If (1) fails at `f`, Lemma 4 with
words of length `j`, rank `2^j`, gives pairs `F_j` with
`eps(F_j) · log₂(A_j B_j) = 3 − 3 eps(F_j) + eps(f) Δ(f) → 3 + eps(f) Δ(f) < 3`. ∎

So a proof may lose any `o(1/eps)` term, for example a polylogarithmic factor.

## 4. The conjecture

**Conjecture 6.** Every dual pair satisfies

```text
|C| · |D| ≥ 8^{1/eps − 1},   equivalently   eps ≥ 3/(3 + log₂(|C|·|D|)).
```

*Consequences, if true.*

- Since `N ≥ 2√(A·B)`, `eps · log₂N ≥ 3/2 − eps/2`. With the words, the asymptotic
  constant is `c_∞ = 3/2` exactly, against GK97's bracket `[1, 2]`. Over all pairs the
  constant stays 1.
- FK-A's frequency guarantee improves by the same factor at every node: some point has
  frequency at least `3/(3 + log₂(|C|·|D|))` on one side.
- No family of dual pairs, so no iterated template, prime or not, has `c_∞ < 3/2`. Open
  problem 5.3 (D3) itself stays open. A remaining candidate `T` is `u`-uniform on `u²`
  points with both sides irregular (research §5), so `eps_T > 1/u`, and the conjecture
  gives only `k k* ≥ 8^{1/eps_T − 1}`, weaker than D3's `8^{u−1}`.

*Evidence (computed).*

| Search | Bound | Least defect | Pairs of defect 0 |
| --- | --- | --- | --- |
| `frequency_constant N` (Rust) | every monotone function of `N ≤ 6` variables: 7,828,352 dual pairs at `N = 6` | 0 | `x` and the labelled copies of `X`, `Y`: 10, 35, 96 at `N = 4, 5, 6` |
| `frequency_families.py closure 13` | every read-once formula with ≤ 13 leaves: 29,228 tuples `(A, B, s, t)`, `1/eps ≤ 3` | 0 | |
| `frequency_families.py compose 4000 S`, `S = 1..4` | 16,000 nested substitutions of P4, K3, Fano, `w11`, threshold 2-of-4, AND, OR; depth 5–8; largest `1/eps` 112.4, 116.1, 123.5, 114.3 by seed | ≥ 0; least `Δ·eps` over `1/eps > 3` is 0.0566, 0.692, 0.183, 0.775 by seed | |

The count of equality cases at `N = 6` is `6 + 15·6`: one single variable per point, and on
each 4-set the three labellings of `X` and three of `Y`. The exhaustive search reaches only
`1/eps ≤ 2.45` (`n eps² ≥ 1`, research Theorem 3.1), and the read-once closure `1/eps ≤ 3`,
so the evidence at small `eps` rests on the substitution family. That family is closed
under the tensor power of Lemma 4 and contains every word, but every function in it has a
modular decomposition into the listed templates; pairs with large prime parts and small
`eps` were not tested.

## 5. Failed routes

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
4. *The two-parameter half-plane `Q`.* With `s = 1/eps_C ≤ t = 1/eps_D`:
   `(s/t) log₂A + log₂B ≥ 3s − 3 + log₂(t/s)`, and its mirror. It holds on all six-variable
   functions, is invariant under doubling by AND or OR, and fails on the 12-leaf read-once
   formula `(((x&x)|((x&x)|(x&x)))&((x&x)|((x&x)|(x&x))))`, with
   `(A, B, s, t) = (9, 16, 3, 4)` and slack `−0.0376`.
5. *Path identity.* For a read-once formula and every leaf `v`,
   `log₂A = log₂(1/eps_C(v)) + Σ_{AND ancestors} log₂A(sibling)` and
   `log₂B = log₂(1/eps_D(v)) + Σ_{OR ancestors} log₂B(sibling)` (written proof, from the
   degree product rules). It reduces a read-once proof to a two-parameter region closed
   under the gates; the half-planes of route 4 are not that region.

## 6. Next steps

- Prove Conjecture 6 for read-once pairs: find the two-parameter region of `(log₂A, log₂B)`
  at given `(1/eps_C, 1/eps_D)` that both gates preserve. The read-once closure gives its
  exact boundary to 13 leaves.
- In general, Corollary 5 allows `o(1/eps)` losses: entropy or random-restriction arguments
  that are too lossy for the exact statement become admissible.
- Lean: Lemma 1, Theorem 2 and Lemma 4 use only counting, the union bound and Theorem 5.1,
  which is already in Lean.

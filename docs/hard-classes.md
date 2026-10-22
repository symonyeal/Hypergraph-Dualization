# Hard classes for FK-A: the frequency threshold, and which symmetry causes it

What the thesis sets out to understand in Chapter 4 is *which* hypergraphs make
FK-A's bounds tight, and *what their symmetry looks like*. This note states what
is now settled, what is measured, and what is open. Every number is regenerable:

```text
python experiments/hard_classes.py     -> results/hard-classes.{json,md}
python experiments/prime_templates.py  -> results/prime-templates.md
python experiments/selfdual_orbits.py  -> results/selfdual-orbits.md
pytest tests/test_hard_classes.py
```

## 0. The one number

For a dual pair, with `N = nC + nD` and `eps` the largest variable
frequency in either hypergraph,

    c(C, D) = eps(C, D) * log2 N.

FK96 Lemma 2.3.2 gives `c >= 1`; Observation 2.3.3 says that is tight only to a
factor of 2. So `c` places any pair against both ends at once, and *small* `c`
means FK-A's split guarantee is at its weakest. Section 4.3's computation for
the GK- and TK-families is exactly the statement `c -> 2`, and both also have
`s / log2 N -> 1/2`, the other half of Observation 2.3.3.

A correction while passing: thesis Corollary 2.3.1 states `s >= log n`, but its
own derivation `n * 2^-s >= 1` gives `s <= log2 n`, which is the [FK96]
direction and the one used here.

## 1. Structure: the tight class is P4-free

Iterating a template, `Gamma_{j+1} = T[Gamma_j, ..., Gamma_j]`, the exact
recursions of `fka.bound.iterate` are `eps -> eps_T * eps` and
`log2 m -> log2 m_T + r_T log2 m`. So `c` converges **iff** `eps_T * r_T = 1`,
and since `eps_T >= r_T / t`, that forces

> **(1.1)** `T` is `r`-uniform and *regular* on `t = r^2` vertices, and so is
> `Tr(T)`; then `c_inf = max(log2 |E(T)|, log2 |E(Tr T)|) / (r - 1)`.

Counting `sum_{v in e} deg*(v)` two ways gives a second, free consequence:

> **(1.2)** every block of `T` meets every block of `Tr(T)` in exactly one
> point, so `Tr(T)` is the set of *perfect selectors*.

That is what makes the search Berge-free, and `experiments/prime_templates.py`
runs it exhaustively:

> **(1.3)** every regular convergent template satisfying (1.1) is read-once, for
> every `r`: the singleton intersections (1.2) imply this by Gurvich's theorem.
> The exhaustive searches classify the small cases: `r = 2` admits only `M(4)` and `C_4`, both with `c_inf = 2`
> exactly; `r = 3` only the partitions of 9 points into three triples, with
> `c_inf = 3 log2(3) / 2 ~ 2.377`.

The incidence and equality arguments are now consolidated in
[`research-2026-10.md`, Theorems 3.4–3.5](research-2026-10.md#the-gap-and-its-equality-case),
with kernel proofs in `FrequencyGap.lean`. The read-once implication is cited:
[Das–Straßburger 2016, Theorem 4.10](https://lmcs.episciences.org/2621/pdf).
It is not a Lean theorem about the repository's `ReadOnce` definition. The broader
uniform-template question D3, which omits regularity, remains open.

Since read-once means a cograph primal graph (Gurvich; Section 4.4), the answer
to "what does the underlying graph structure of the hard families look like" is
**P4-free** -- derived rather than assumed.

## 2. Their automorphism groups: imprimitive iterated wreath products

For read-once hypergraphs `Aut` is the cotree's group, built from direct and
wreath products of symmetric groups (4.4.15). For the binary alternating trees
that is an iterated wreath product of `S_2`, so
`|Aut(f_k)| = 2^(2^(2k-1) - 1)` -- a Sylow 2-subgroup of `S_(2^(2k-1))`.
Verified exactly in `tests/test_hard_classes.py`: GK `f_2` gives `2^7`, TK `S_1`
gives `2^3`, TK `S_2` gives `2^15`, and the mixed-arity `T_XY` gives
`|S_2 wr S_4 wr S_2| = 294912`. All imprimitive.

There is a second read-once certificate, cheaper than conformality where
conformality is awkward (the Fano plane, the asymmetric instances):

> **(2.1)** if `Aut(MBF)` is primitive and is not `S_n`, then `MBF` is not read-once.
> This is research Proposition 2.5 (`aut_eq_top_of_readOnce`, Lean); the Python check in
> `fka.selfdual` tests the weaker form with `A_n` excluded as well.

A cograph on at least two vertices has exactly one of `G`, `G^c` disconnected
(4.4.7), so the cotree's subtrees at any level are a block system unless the
cotree has depth 1, which gives `S_n`. `PGL(3,2)` settles the Fano plane in one
line. It lives in `fka.selfdual`.

**(2.1)** and **(1.3)** together give the finding that inverts the natural
guess: the symmetry behind the known superpolynomial lower bounds is the
*imprimitive, solvable, iterated-wreath* kind, not the primitive/simple kind.

## 3. The word families: GK and TK are two extreme points

Take the atoms `X = (v1^v2) v (v3^v4)` and `Y = X^d`. For a word `w` in
`{X,Y}^k` put `T_w = w_1[w_2[...w_k]]`. Composition of templates is a template,
and `(S[T])^d = S^d[T^d]` with `X^d = Y` gives `T_w^d = T_wbar`. Writing
`a(w) = log2 |E(T_w)|`, composition gives `a(w) = sum_i 2^(i-1) a(w_i)` with
`a(X) = 1`, `a(Y) = 2`, hence

> **(3.1)** `a(w) + a(wbar) = 3(2^k - 1)` for every word, so
> `c_inf(w) = max(a(w), a(wbar)) / (2^k - 1) >= 3/2`; and `a(w) - a(wbar)` is
> odd, so the bound is approached but never met. The minimum at length `k` is
> `3/2 + 1/(2(2^k - 1))`: 2, 5/3, 11/7, 23/15, ...

> **(3.2)** the constant words `XX..X` and `YY..Y` are exactly the GK- and
> TK-families, and are the *worst-balanced* words -- both land on `c_inf = 2`.

So the thesis' two tight families are the two degenerate members of a class
indexed by a binary word, and balancing the word gives strictly harder
instances. `word-xy` and `word-yx` are in the instance library.

## 4. Self-duality: the other regime, and why it is not the cause

For a Sperner family without the empty edge, `MBF = Tr(MBF)` iff it is intersecting
and **not 2-colourable** (`tr_eq_self_iff`). The Python scan now checks Sperner first:
redundant terms can represent a self-dual function without the family equalling its
transversal. For nonempty self-transversal families on `n > 1` points,
`n eps^2 > 1` (`eps_self_strict`). In the uniform regular case:

> **(4.1)** for self-dual, uniform, regular `MBF`, counting gives
> `d(r^2 - t) >= r(r-1)`, hence for `r > 1`, `t < r^2` and `eps > 1/r`.
> Equality holds iff any two distinct blocks meet in one point
> (`intersecting_regular_bound`). See the canonical proof in
> [`research-2026-10.md`, Theorem 2.2](research-2026-10.md#2-self-transversal-hypergraphs).

Among projective planes only `PG(2,2)` survives: `PG(2,3)` has a 6-point
projective triangle whose complement also blocks, so it is 2-colourable. Among
Witt designs only `S(2,3,7)` and `S(4,5,11)` are intersecting -- `S(5,6,12)` has
a block's complement for a block, `S(5,8,24)` has disjoint octads. `S(4,5,11)`,
with `|Aut| = 7920 = |M_11|`, is therefore the only sequel to the Fano plane,
and it is in the library as `w11`.

Both standard ways of manufacturing an *infinite* self-dual family destroy the
frequency bound: self-dualisation (SDFP) adds two vertices of degree about
`m/2`, so `eps >= 1/2`; and `Maj_(2k-1)` has `eps -> 1/2` with `Aut = S_n`. So
this regime supplies remarkable single objects, not lower-bound families.

## 5. What the split does to the symmetry, exhaustively

`results/hard-classes.{json,md}` classifies **every node of both trees** for
every instance -- deduplicated on the compacted `(cnf, dnf)` -- as read-once,
transitive and primitive, and records the deepest level still carrying a
primitive non-symmetric group. Read-once nodes are not enumerated (their group
is the cotree's by 4.4.15); for the rest the enumeration is capped, and a capped
subgroup with no nontrivial block still *proves* primitivity, so the cap can
only under-report.

Two things come out of the exhaustive pass, 26 rows over 21 distinct pairs.

> **(5.1)** A read-once root produces **no** primitive node anywhere in either
> tree -- 13 of 13 such rows, `prim depth = -1` (computed). It is consistent with
> **(2.1)** applied at every node: a restriction of a read-once function is
> read-once, so a primitive node would need the full symmetric group. That
> substitution never manufactures a primitive group is this reading, not a proof.
> The converse fails, and widely: `6a`, `7ver`, `8ver`, `fano`, `sdfp-sd-1`,
> `sdfp-sd-2` and `threshold-10` all have non-read-once roots and still no
> primitive node, being non-conformal with imprimitive groups. Only four rows
> carry a primitive node at all -- `k3`, `trivial-aut-1`, `w11`, `w11-sd-1`.

> **(5.2)** Primitivity *depth* does **not** predict FK-B's advantage.
> `w11-sd-1` keeps primitive nodes to depth 10 and FK-B wins only 1.33x, while
> `gk-f3` carries no primitive node anywhere and FK-B wins 52.96x. There is no
> monotone relation between the two columns -- if anything the sign is the
> opposite of the one a three-instance reading suggested.
>
> **Corrected 2026-08-10.** This paragraph previously refuted the same claim
> with "`sdfp-sd-2` keeps primitive nodes to depth 9 and FK-B still wins
> 6.18x", and described Fano as dying "at depth 0". Neither is in the data:
> `sdfp-sd-2` and `fano` both have zero primitive nodes and `prim depth = -1`,
> in this pass and in the one the paragraph was written from. The conclusion is
> unchanged and now rests on instances that carry the property.

The repeat rate remains the better predictor at scale (99.6% -> 52.96x on
`gk-f3`), but it is not sufficient either: `word-xy` repeats 95.2% of its nodes
and FK-B gains only 2.99x. What separates them is tree size, not symmetry --
FK-B's saving compounds with the number of nodes there are to reuse. See
`docs/fk-a-vs-fk-b.md`.

The repeat column is worth reading in the other direction too. `1/(1 - repeat)`
is exactly `tau/delta`, FK-A's tree over its distinct-subproblem count: 280x on
`gk-f3`, 20.6x on `word-xy`. Measured that way the small members look easy --
`gk-f3` needs 369 subproblems on `N = 192`, and the constant word at `N = 16512`
needs 4139 -- but `gk-f4` needs 67,247,387 on `N = 49,152` under FK-A's own split
rule, against 128 under the leftmost rule (`docs/tree-vs-dag.md` section 4,
corrected 2026-10-21). The families in this note make FK-A's *frequency bound*
tight, which is what section 0 claims; whether they make its memoised recursion
large depends on the split rule.

Nodes whose incidence graph is too large to enumerate are counted in the
`undet` column and excluded from the primitivity counts rather than guessed:
16 nodes on `w11-sd-1`, 6 on `w11`, 2 on `sdfp-sd-2`, none anywhere else.

## Caveats

* The searches above do not settle D3's irregular case; its status is research
  Open problem 5.3, and open problems are listed once, in
  [research §7](research-2026-10.md#7-open-items).
* The placement rows are one size point per family. The `exp` column is
  indicative, not a fitted growth rate.

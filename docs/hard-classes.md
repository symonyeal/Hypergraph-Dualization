# Hard classes for FK-A: the frequency threshold, and which symmetry causes it

What the thesis sets out to understand in Chapter 4 is *which* hypergraphs make
FK-A's bounds tight, and *what their symmetry looks like*. This note states what
is now settled, what is measured, and what is open. Every number is regenerable:

```text
python experiments/hard_classes.py     -> results/hard-classes.{json,md}
python experiments/selfdual_orbits.py  -> optional local orbit-search report
pytest tests/test_hard_classes.py
```

## 0. The one number

For a dual pair, with `N = nC + nD` and `eps` the largest variable
frequency in either hypergraph,

    c(C, D) = eps(C, D) * log2 N.

FK96 Lemma 2.3.2 gives `c >= 1`; the GK97 bracket is `[1,2]`. The word
families below improve the asymptotic upper endpoint to `3/2` (see
[`frequency-constant.md`](frequency-constant.md)); GK and TK themselves tend to 2. So `c` places any pair against both ends at once, and *small* `c`
means FK-A's split guarantee is at its weakest. Section 4.3's computation for
the GK- and TK-families is exactly the statement `c -> 2`, and both also have
`s / log2 N -> 1/2`, the other half of Observation 2.3.3.

A correction while passing: thesis Corollary 2.3.1 states `s >= log n`, but its
own derivation `n * 2^-s >= 1` gives `s <= log2 n`, which is the [FK96]
direction and the one used here.

## 1. Regular equality templates are P4-free

Iterating a template, `Gamma_{j+1} = T[Gamma_j, ..., Gamma_j]`, the exact
recursions of `fka.bound.iterate` are `eps -> eps_T * eps` and
`log2 m -> log2 m_T + r_T log2 m` on an equal-rank template. For rank `r_T > 1`
on `t = r_T²` points, the frequency bound gives `eps_T ≥ 1/r_T`.
The iterated constant `c` has a finite positive limit exactly at
`eps_T r_T = 1`, and the equality case gives

> **(1.1)** `T` is `r`-uniform and *regular* on `t = r^2` vertices, and so is
> `Tr(T)`; then `c_inf = max(log2 |E(T)|, log2 |E(Tr T)|) / (r - 1)`.

Research Proposition 3.7 (which needs only one regular side) gives:

> **(1.2)** every block of `T` meets every block of `Tr(T)` in exactly one
> point, so `Tr(T)` is the set of *perfect selectors*.

This gives the perfect-selector search used in the finite classification
([results](../results/prime-templates.md)):

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

The resulting read-once templates have cograph primal graphs and therefore no
induced `P₄` (Gurvich and thesis §4.4).

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

The known superpolynomial families (GK, TK, the words) are read-once, so their groups are iterated
wreath products of symmetric groups and imprimitive.

## 3. The word families and the constant words

Take the atoms `X = (v1^v2) v (v3^v4)` and `Y = X^d`. For a word `w` in
`{X,Y}^k` put `T_w = w_1[w_2[...w_k]]`. Composition of templates is a template,
and `(S[T])^d = S^d[T^d]` with `X^d = Y` gives `T_w^d = T_wbar`. Writing
`a(w) = log2 |E(T_w)|`, composition gives `a(w) = sum_i 2^(i-1) a(w_i)` with
`a(X) = 1`, `a(Y) = 2`, hence

> **(3.1)** `a(w) + a(wbar) = 3(2^k - 1)` for every word, so
> `c_inf(w) = max(a(w), a(wbar)) / (2^k - 1) >= 3/2`; and `a(w) - a(wbar)` is
> odd, so the bound is approached but never met. The minimum at length `k` is
> `3/2 + 1/(2(2^k - 1))`: 2, 5/3, 11/7, 23/15, ...

> **(3.2)** The constant words are the even-height alternating trees of the TK
> family and their duals. They have `4^k` input leaves and attain the largest
> word-family value `c_inf = 2`. The GK family uses the odd heights, with
> `2^(2k−1)` input leaves.

Mixed words can give smaller `c_inf`. The instance library includes `word-xy`
and `word-yx`.

## 4. Self-duality: the other regime, and why it is not the cause

For a Sperner family without the empty edge, `MBF = Tr(MBF)` iff it is intersecting
and **not 2-colourable** (`tr_eq_self_iff`). The Python scan now checks Sperner first:
redundant terms can represent a self-dual function without the family equalling its
transversal. For nonempty self-transversal families on `n > 1` points,
`n eps^2 > 1` (`eps_self_strict`). In the uniform regular case research Theorem 2.2 gives `d(r² − t) ≥ r(r − 1)`,
hence `t < r²` and `eps > 1/r` for `r > 1`.

Among projective planes only `PG(2,2)` survives: `PG(2,3)` has a 6-point
projective triangle whose complement also blocks, so it is 2-colourable. The self-transversal examples among these Witt designs are `S(2,3,7)` and
`S(4,5,11)`: `S(5,6,12)` has a block's complement for a block, `S(5,8,24)`
has disjoint octads, and the intersecting `S(4,7,23)` is not self-transversal
(the certificate below checks this). `S(4,5,11)`,
with `|Aut| = 7920 = |M_11|`, is the larger self-transversal example here,
and it is in the library as `w11`.

Both standard ways of manufacturing an *infinite* self-dual family destroy the
frequency bound: self-dualisation (SDFP) adds two vertices of degree about
`m/2`, so `eps >= 1/2`; and `Maj_(2k-1)` has `eps -> 1/2` with `Aut = S_n`. So
this regime supplies remarkable single objects, not lower-bound families.

## 5. What the split does to the symmetry in the measured sample

`results/hard-classes.{json,md}` classifies **every node of both trees** for
each measured instance, with the compacted `(cnf, dnf)` used for deduplication.
It checks read-once structure and records the deepest certified primitive
group at a non-read-once node (full symmetric groups included). The read-once cases use the structural result in §2 without
enumerating their groups. Elsewhere, a capped subgroup certifies primitivity
only if it is transitive and primitive. The remaining capped cases leave the
full-group classification unresolved.

The retained historical survey has 26 rows over 21 distinct pairs. The current script
regenerates 21 unique pairs and records capped negative group searches as undetermined;
this full survey has not been rerun after that correction. Positive primitivity certificates
remain valid, but zero counts and negative depths do not certify absence.

> **(5.1)** Read-once restrictions remain read-once. This survey excludes their
> groups from the count of primitive non-read-once nodes, so `prim depth = -1`
> in those rows is a consequence of the classification rule. A read-once
> hypergraph can have a primitive full symmetric group. The historical capped
> enumeration also leaves some non-read-once nodes unresolved; its negative
> counts cannot establish that the converse holds or fails.

> **(5.2)** Whether primitivity *depth* predicts FK-B's advantage is unresolved
> (corrected 2026-11-18; the earlier text called it refuted with the sign reversed).
> `w11-sd-1` (depth 10, 1.33x) against `gk-f3` (no primitive node, 52.96x) agrees
> with "the FK-A/FK-B ratio falls as depth rises"; among the positive depths,
> `k3` (0, 1.00x), `trivial-aut-1` (4, 1.24x) and `w11` (8, 1.47x) rise instead.
> The column counts primitive groups of non-read-once nodes, full symmetric groups
> included (`k3` has `Aut = S₃`); it compares modified FK-A with faithful FK-B; and
> capped negatives are undetermined. Four positive-depth instances decide nothing.
>

The FK-A repeat rates are 99.6% on `gk-f3` and 95.2% on `word-xy`, with
FK-A/FK-B tree ratios of 52.96x and 2.99x. The repeat rate gives the size of the
FK-A tree relative to its own DAG. The FK-B ratio also depends on its branches
and terminal cases. See [fk-a-vs-fk-b.md](fk-a-vs-fk-b.md).

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
  Open problem 5.3, and the consolidated open-item list is in
  [research §7](research-2026-10.md#7-open-items).
* The placement rows are one size point per family. The `exp` column is
  indicative, not a fitted growth rate.

## 6. Witt designs and the bounded self-transversal search

`w11` is the 66-block design `S(4,5,11)`, with `Aut = M11`;
`w11-sd-1` is its self-dualisation. A Sperner family equals its transversal
exactly when it is intersecting, has no empty edge and is not 2-colourable
(research Proposition 2.1).
For an intersecting family with minimum edge size `s`, maximum degree `D`
and `m` edges, `m ≤ 1 + s(D−1)`, so `eps > 1/s` for `s > 1`.
Uniform vertex-transitive candidates consequently have `n ≤ s²−1`.

Reproduce with `sage -python experiments/hard_case_search.py 3 15`,
`python experiments/build_instances.py`, and `pytest tests/test_hard_cases.py`.

The bounded search found 21 vertex-transitive self-transversal hypergraphs
up to isomorphism on at most 15 points. It enumerates single subset orbits
and pairs of orbits, with pairs tested only through degree 12. Candidate orbit
ranks range from 2 through `⌊(n+3)/2⌋` for both uniform and mixed inputs. Unions
of three or more orbits and mixed inputs with ranks outside the interval are
outside the search. Rows are sorted by FK-A nodes per unit of input.

| n | \|E\| | sizes | ε | c | FK-A | FK-B | A/2m | B/2m | primitive | Aut |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | :---: | --- |
| 15 | 300 | 6 | 0.400 | 3.69 | 3687 | 2695 | 6.14 | 4.49 | no | (A5×A5×A5) : (C2×S4) |
| 15 | 270 | 6 | 0.400 | 3.63 | 3199 | 1659 | 5.92 | 3.07 | no | (C3⁵) : (C2×((C2⁴):S5)) |
| **11** | **66** | **5** | **5/11** | **3.20** | **483** | **321** | **3.66** | **2.43** | **yes** | **M11** |
| 7 | 7 | 3 | 3/7 | **1.63** | 35 | 11 | 2.50 | 0.79 | yes | PSL(3,2) — *the Fano plane* |
| 9 | 27 | 4 | 4/9 | 2.56 | 119 | 57 | 2.20 | 1.06 | no | S3 wr S3 |
| 11 | 121 | 5,6 | 0.496 | 3.93 | 479 | 317 | 1.98 | 1.31 | yes | PSL(2,11) |
| 10 | 51 | 4,5 | 0.471 | 3.14 | 179 | 109 | 1.75 | 1.07 | yes | A6 |
| 11 | 110 | 5 | 5/11 | 3.54 | 271 | 163 | 1.23 | 0.74 | yes | C11 : C10 |
| 6 | 10 | 3 | 1/2 | 2.16 | 19 | 11 | 0.95 | 0.55 | yes | A5 |
| 3, 5, 7, 9, 11, 13, 15 | C(n, (n+1)/2) | | ≈ 1/2 | 1.7–7.3 | | | ≤ 0.56 | ≤ 0.58 | yes | S_n — *majority* |

The imprimitive examples with larger FK-A/input ratios than Fano are
`MAJ3[MAJ3]`, `MAJ5[MAJ3]` and `MAJ3[MAJ5]` (checked by isomorphism).
Composition multiplies their frequencies, giving `eps = 0.4` on the
15-point examples. Among the primitive examples found, W11 has the
largest FK-A/input ratio, followed by Fano.

### Perfect codes

The blocks of both are the supports of the minimum-weight words of a perfect
code:

| code | design | n | \|E\| | \|e\| | ε | Aut |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| Hamming [7,4,3] | S(2,3,7) — Fano | 7 | 7 | 3 | 3/7 | PSL(3,2), 168 |
| ternary Golay [11,6,5] | **S(4,5,11) — W11** | 11 | 66 | 5 | 5/11 | **M11, 7920** |
| binary Golay [23,12,7] | S(4,7,23) | 23 | 253 | 7 | 7/23 | M23, 10200960 |

`fka.instances.witt_11` builds W11 that way, from the cyclic generator
polynomial `g(x) = −1 + x² − x³ + x⁴ + x⁵` over GF(3), so nothing is a
transcribed block list.

**The family stops at 11.** S(4,7,23) is intersecting — its blocks meet in 1 or
3 points — but it is *not* self-transversal: 16744 of the 1352078 11-subsets of
its 23 points contain no block and have a complement containing no block, and
each is a thesis equation 2.1 certificate against it. One of them,
`{1,2,3,4,5,6,7,8,10,14,21}`, is asserted in `tests/test_hard_cases.py`. The
same test also shows why the search cannot be run at that size naively: the
certificate settles the question in `O(|E|)`, while building `Tr` of 253 blocks
on 23 points is not a bounded computation.

Note also that this is where the analogy to *projective planes* ends, and the
thesis' framing of the Fano plane as "the smallest projective plane" slightly
undersells it. PG(2,q) for `q ≥ 3` is **not** self-transversal — it has
non-trivial blocking sets, i.e. blocking sets containing no line, and such a set
and its complement are a certificate. The Fano plane is the only projective
plane in the class. What generalises it is not the plane, it is the perfect code.


### Library node counts

On the library instance `w11` (66 blocks, ternary-Golay labelling), against the
Fano plane:

| | Fano | W11 | |
| --- | ---: | ---: | --- |
| FK-A `faithful` | 59 nodes, 4.21/2m | 1015, **7.69/2m** | depth 6 → 10 |
| FK-A `modified` | 35 nodes, 2.50/2m | 475, **3.60/2m** | depth 5 → 9 |
| FK-B `faithful` | 11 nodes, 0.79/2m | 323, **2.45/2m** | depth 3 → 9 |
| FK-A repeat rate (`modified`) | 60.0% | 70.5% | |
| FK-B repeat rate | **0.0%** | **33.4%** | |
| FK-A / FK-B | 3.18× | 1.47× | |

`w11-sd-1` is the same instance put through SDFP's self-dualisation (133 edges
on 13 vertices), for direct comparison with `sdfp-sd-1` (15 edges on 9). It
holds FK-A's rate (3.59/2m against 4.10) and roughly doubles FK-B's (2.70/2m
against 1.23). `k = 2` is not in the library: it would have `66² + 133 = 4489`
edges.


### Search limits

- Vertex-transitive only. A self-transversal hypergraph with a non-transitive
  group is not reachable this way; the uniform transitive bound does not apply, so it needs a
  different enumeration.
- Degrees ≤ 15, and pairs of orbits only up to degree 12. Unions of three or
  more orbits are not enumerated at any degree.
- Node counts depend on the vertex labelling, because the labelling moves the
  pivot choice. The search reports 483/321 for its own labelling of `S(4,5,11)`
  and the library instance reports 475/323 for the ternary-Golay labelling; they
  are the same design. `docs/fk-a-vs-fk-b.md` records the same caveat for the
  SDFP instances against the MATLAB reference.

# The tree is not the subproblem count

Thesis p.12: "The performance of FK-A is determined by the number of subproblems
it generates, and this is reflected in the number of nodes of the recursion
tree." The first clause is the right measure. The second is false on this
project's own instances, by a factor of 280 on `gk-f3` and of about `10¹²` on `gk-f4`
(research §4, Observation 4.4).

Write, for a dual pair with `N = |C| + |D|`,

    tau(C, D)     nodes of the FK-A recursion tree
    delta(C, D)   *distinct* subproblems among them -- the tree's DAG

A node's verdict depends on its irredundant `(n, C, D)` alone, and the
short-circuit is deterministic, so the DAG unfolds to exactly the tree and
`delta <= tau`. `fka.memo.fk_a_memo` runs the identical recursion with a
transposition table; its node count *is* `delta`, and it decides the same
question. Everything below is regenerable:

```text
python experiments/dag_size.py            -> results/dag-size.{json,md}
python experiments/dag_size.py --deep     -> plus the length-3 words
pytest tests/test_memo.py
```

---

## 1. The separation, and where it lives

| | N | tau | delta | tau/delta |
| --- | ---: | ---: | ---: | ---: |
| `threshold(12)` | 43 | 11 | 11 | **1.0x** |
| `fano` | 14 | 35 | 14 | 2.5x |
| `sdfp-sd-2` | 128 | 1,427 | 126 | 11.3x |
| `tk-s2` | 72 | 481 | 34 | 14.2x |
| `word-xy` | 48 | 577 | 28 | 20.6x |
| `gk-f3` | 192 | **103,377** | **369** | **280.1x** |

On `gk-f3` the tree has degree 2.20 in `N` and the DAG has degree 1.12. The
alternating trees of Chapter 4 -- the families chosen precisely because they sit
at the frequency floor -- cost FK-A 369 subproblems and 103,377 nodes to
re-derive them.

**The blow-up is in the unfolding, not in the split rule.** Nothing about which
vertex FK-A pivots on produces it; the recursion simply has no memory.

`fka.analysis.annotate` already memoises this exact key when annotating a
finished tree, for the stated reason that "FK-A regenerates identical
subproblems". The recursion that builds the tree does not.

## 2. Two closed forms

Both are exact, for every size tested, and are asserted in `tests/test_memo.py`:

    matching(v):    tau = 2^(v/2+1) - 3       delta = v
    threshold(v):   tau = v - 1               delta = v - 1

`threshold` is the only family in the library with `tau = delta` -- no repeated
subproblem at all. It is also the only instance class where FK-B *loses*
(`beta = 37` against `tau = 11` at `v = 12`). Those are one fact: there is no
redundancy for either mechanism to remove.

`matching` corrects [fk-a-vs-fk-b.md](fk-a-vs-fk-b.md) §6. That section calls
the family **output-bound** -- `|Tr| = 2^(v/2)`, so "both must pay it" and its
90.4% repeat rate is "unavoidable". Not for the decision problem:
`delta(matching(v)) = v` exactly, so duality is settled in `v` subproblems while
the tree grows as `2^(v/2)`. Output size lower-bounds *generation*; FK-A and
FK-B are deciding, and neither has to touch `Tr`. The repeats there are as
avoidable as anywhere else. "Output-bound" is not a fourth regime.

## 3. What `delta` buys: instances the tree cannot reach

`delta` is computable where `tau` is not an observable at all.

| instance | n | N | delta | delta/N |
| --- | ---: | ---: | ---: | ---: |
| `word-xy` | 16 | 48 | 28 | 0.583 |
| `word-xxy` | 64 | 3,072 | 2,973 | 0.968 |
| `word-xyx` | 64 | 4,608 | 3,025 | 0.657 |
| `word-xyy` | 64 | 8,448 | 4,244 | 0.502 |
| `word-xxx` | 64 | 16,512 | 4,139 | 0.251 |
| `word-yyy` | 64 | 16,512 | 4,139 | 0.251 |

`word-xxx` and `word-yyy` are the constant words -- by
[hard-classes.md](hard-classes.md) §3.2 the GK- and TK-families, the two
worst-balanced members at `c_inf = 2`. At `N = 16,512` they need 4,139 distinct
subproblems. Their trees are far past enumeration; `word-xy`, 344 times smaller,
already unfolds to 577 nodes. The two agree exactly, as `T_w^d = T_wbar`
requires.

## 4. `delta <= 2N` on the first corpus, and where it fails

Across the first corpus -- the library, the alternating families up to `gk-f3`, `matching` to
`v = 20`, `threshold` to `v = 20`, the words to `N = 16,512`, and 234,135 random dual pairs on at
most 14 vertices -- `delta` never exceeds `2N`. The maxima are 1.92 (`gk-f3`) among structured
instances and 1.681 among random ones; 7.2% of random pairs exceed `delta = N`, 0.01% exceed
`1.5N`, and not one reaches `2N`.

**Corrected 2026-10-21.** This section called `delta <= 2N` a regularity of every instance
measured and concluded that no published hard instance for FK-A is hard for memoised FK-A. Both
are false under FK-A's own split rule:

| instance | n | N | delta (degree sum) | delta (leftmost) |
| --- | ---: | ---: | ---: | ---: |
| `ro12` (read-once, 12 points) | 12 | 21 | **43** | 12 (leaves renumbered); 91 (labels as given) |
| `gk-f3` | 32 | 192 | 369 | 32 |
| `gk-f4` | 128 | 49,152 | **67,247,387** | 128 |

`ro12` is proved read-once with `delta = 43 > 2N` in Lean (`Blowup.lean`, `ro12_delta`). Its
leftmost count depends on the labelling: 12 with the leaves renumbered left to right, 91 with the
interleaved labels of `ro12` itself (`ro12_rules`; research §4, *Split rules*);
`gk-f4` is computed by `experiments/readonce_dag`. Random read-once formulas with fan-in 3 or 4
exceed `2N` often. The first corpus missed them because its random formulas were binary and
small. See `docs/research-2026-10.md`, Observations 4.4-4.11.

The leftmost rule (leaves numbered left to right, Hertel's order) keeps `delta = n` on the same
instances. So the alternating trees are hard for memoised FK-A under its most-frequent-vertex
rule and easy under a coordinated order: the remaining hardness is the split rule's, not the
instance's. Under ETH some dual family must defeat every rule
(`docs/research-2026-10.md`, Proposition 4.6), but no explicit one is known.

The search in [hard-cases.md](hard-cases.md) was run against `tau`; run against `delta`,
`S(4,5,11)` places at 140 subproblems on `N = 132`.

## 5. FK-B and memoisation are orthogonal

`delta` against FK-B's `beta` on the same instance:

| | `delta` | `beta` | `delta/beta` |
| --- | ---: | ---: | ---: |
| `6c`, `tk-s1` | 4 | 1 | 4.00 |
| `fano` | 14 | 11 | 1.27 |
| `trivial-aut-1` | 34 | 33 | 1.03 |
| `sdfp-sd-2` | 126 | 231 | 0.55 |
| `w11` | 140 | 323 | 0.43 |
| `gk-f3` | 369 | 1,952 | 0.19 |
| `word-xy` | 28 | 193 | 0.14 |

`delta <= 4*beta` on every instance of this table, with the maximum on the two
smallest; and `delta/beta` falls as these instances grow. So **on this library
FK-B's advantage is subsumed by a transposition table on FK-A**, and what FK-B
keeps is a constant factor from its shallower base case -- `min(|C|,|D|) <= 2`
against `nC*nD <= 1`, which is a whole binary subtree per leaf
([fk-a-vs-fk-b.md](fk-a-vs-fk-b.md) §4). The two improvements are independent,
and on this library the algorithm to reach for is FK-A with both. The table is
seven instances, not an asymptotic statement: under FK-A's own rule `gk-f4` has
`delta = 67,247,387` (research §4), where `beta` was not measured, and whether
`delta/N` is unbounded on GK is open (Conjecture 4.19).

This also dissolves the "predictor" of [fk-a-vs-fk-b.md](fk-a-vs-fk-b.md) §2.
The repeat rate `rho` is not an empirical correlate of FK-B's advantage; it is
the identity

    tau/delta = 1/(1 - rho),

so `rho` measures the redundancy a memo removes *in full*, and is a ceiling on
any such speedup. FK-B captures 14-55% of it. That is why `word-xy` at
`rho = 95.2%` gains only 2.99x where `gk-f3` at 99.6% gains 52.96x: the
ceilings are 20.6x and 280.1x, and FK-B takes a similar fraction of each. The
documented exception was never an exception.

## Caveats

* `delta` is split-rule- and labelling-specific, as `tau` is
  ([hard-cases.md](hard-cases.md) §6). The agreement in `tests/test_memo.py`
  holds across both variants and both split rules; the *values* above are
  `modified` / `degree_sum`.
* `gk-f4` is beyond this program; `experiments/readonce_dag` measures it on
  live-variable sets (section 4).

Open problems are listed once, in [research §7](research-2026-10.md#7-open-items).

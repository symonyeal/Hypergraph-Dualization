# Research prompt: the next phase (from 2026-10-22)

The live hand-off for the next research session, on any machine. Read it whole before touching
anything. Results count only under the README's policy: proved or refuted in Lean, checked by
evaluation, computed (and said so), cited, or open with the search bound stated. New statements
get a row in `thesis/CLAIMS.md` and a numbered entry in the research write-up. Pull `main` first.

## 1. Where things stand

The October tracks A–E are written up in [`research-2026-10.md`](research-2026-10.md); its §7 is
the one list of open items. In short, the work has moved from the thesis's question (how does
the symmetry of `H` shape FK-A's recursion?) to the subproblem DAG: `τ` the tree, `δ` the
distinct subproblems, the memo DAG as an FBDD (Theorem 4.13), and split rules as variable orders.
The open core is C3: an explicit family hard for memoised FK-A under every valid symmetric rule,
which up to a factor 2 is a monotone function with small DNF and CNF and no small FBDD named by
its functions. It is the monotone case of Question 1 of Jukna, Razborov, Savický and Wegener
(ECCC TR97-023, 1997), still open (Proposition 4.27). The tree side is settled on GK and TK
(Track T, 2026-10-23): `τ ≥ 2·(27/16)^{n/4}/(n+1)` under every valid rule, in Lean
(`fkA_gk_tree`, Theorems 4.24–4.25), so memoisation saves an exponential factor there. Track S's
soundness theorem and measurements are research Theorem 4.28, Observation 4.29 and Conjecture
4.30 (2026-10-23); §2 says what remains.

## 2. Focus: Track S, how much of FK-A's work is symmetry

**Status 2026-10-23.** S0 is done for the read-once families and the library without Sage
(Observation 4.29, `experiments/iso_classes.py`, `results/iso-memo.md`): at GK `f₄` under the
degree-sum rule `δ_iso = 827,175`, `δ_Aut = 1,183,141`, so `δ/δ_iso = 81.3` and `δ_iso/N = 16.8`.
S1 is Theorem 4.28 (`fkAI_correct`), S2 is Theorem 4.22. The stop rule does not apply: `δ/δ_iso`
grows under the degree-sum rule on GK, TK and `alt3`. Left: S3's recurrence and Conjecture 4.30,
and S4's reading of thesis Chapter 3. Not computed on the work laptop (about 1.7 GB free): the
label-exact DAGs of GK `f₅`, TK `S₄` and `alt3 d₅` under the degree-sum rule; `--classes --spill`
needs about 60,000 nodes per second and little memory, so these are runtime-bound (`alt3 d₅` has
more than `10⁸` subproblems).

**Question.** Split FK-A's cost into three factors:

    τ  =  (τ / δ)  ·  (δ / δ_iso)  ·  δ_iso
          exact       repetition     distinct
          repeats     up to          work
                      isomorphism

and measure, then prove, how large each is on the thesis's hard classes. This answers the
thesis's title question with exact quantities instead of group orders at a few nodes, and it
reuses the DAG machinery already in Lean.

**Lead** (computed 2026-10-22, `python experiments/iso_memo.py 4 3`; `δ` agrees with
research Observation 4.4 and `results/split-rules.md`). `d_iso` counts the subproblems
expanded when the memo is keyed by isomorphism class. On read-once pairs that class is the
formula's shape with labels forgotten.

| pair | `n` | `N` | rule | `δ` | `d_iso` | `δ / d_iso` |
| --- | ---: | ---: | --- | ---: | ---: | ---: |
| GK `f₃` | 32 | 192 | degree sum | 369 | 155 | 2.4 |
| GK `f₄` | 128 | 49,152 | degree sum | 67,247,387 | 734,303 | 92 |
| GK `f₄` | 128 | 49,152 | guarded | 263 | 215 | 1.2 |
| TK `S₂` | 16 | 72 | degree sum | 34 | 29 | 1.2 |
| TK `S₃` | 64 | 16,512 | degree sum | 4,139 | 762 | 5.4 |

The factor 92 is `δ/d_iso`, a cache-count ratio. It is an upper bound on the
isomorphic-repetition factor `δ/δ_iso`, since `d_iso ≤ δ_iso`. The distinction is
strict already at GK `f₃`: the exact DAG has 160 classes, whereas the cache visits
155. At `f₄`, `d_iso/N ≈ 15` is a lower bound on `δ_iso/N`; the exact class count
was not measured. See the bounded rerun and independent checks in
[`../results/iso-memo.md`](../results/iso-memo.md).

**Related work.** Caching isomorphic components is known in model counting: van Bremen,
Derkinderen, Sharma, Roy and Meel, *Symmetric component caching for model counting on
combinatorial instances*, AAAI 2021 (SymGANAK). The technique is not the contribution here. The
decomposition of FK-A's cost, and the theorems below, are. Read that paper before S1 and cite it.

### Definitions (fix these first)

For a dual input `(G, Tr G)` and a split rule, let `R` be the set of subproblems memoised FK-A
reaches (`fkADag`, `|R| = δ`). Every element of `R` is `(H, Tr H)` or `(Tr H, H)` for a minor
`H = G − A / B` (Theorem 4.7).

- `δ_Aut`: the number of `Aut(G)`-orbits that meet `R`, with `σ · (C, D) = (σC, σD)`.
- `δ_iso`: the number of isomorphism classes of pairs in `R`.
- `d_iso`: the number of nodes iso-memoised FK-A expands. It depends on the traversal order,
  because the tie-break by least index is not relabelling-equivariant.

Then `d_iso ≤ δ_iso ≤ δ_Aut ≤ δ ≤ τ` and `δ_Aut ≥ δ / |Aut(G)|`.

### Phases

**S0. Measure (computed).** One or two sessions.
- Extend `experiments/readonce_dag` (Rust) with a shape key, as in `iso_memo.py`, to reach
  GK `f₅` and TK `S₄` under all three rules, with `δ_iso` as well as `d_iso`.
- `δ_Aut` on read-once pairs: the orbit of a subproblem under the tree automorphisms of the
  input is the AHU form of the input tree with the minor's deleted and contracted leaves
  marked.
- The non-read-once library (`fano`, `w11`, `w11-sd-1`, `sdfp-sd-1`, `sdfp-sd-2`,
  `trivial-aut-1`, the words): canonical labels of the pair as one 2-coloured incidence graph
  (Sage `canonical_label`, or nauty). Sage is on the personal machine (`docs/sagemath.md`).
- Output: `results/iso-memo.md` with the three-factor table for every instance and rule.
  Seeded and rerunnable. Add a test in `tests/` that `iso_memo.py`'s `δ` matches `fka.memo`
  on the small cases.

**S1. Correctness (Lean).** Proposition: duality is invariant under relabelling,
`σ • C = Tr (σ • D) ↔ C = Tr D`. Then iso-memoised FK-A, with any canonical-form function `κ`
such that `κ p` is isomorphic to `p`, returns the verdict of `fkA` (`fkA_correct` plus the
invariance). Small. It turns `d_iso` into a count for a correct algorithm.
The foundation is now proved: `tr_eq_pimg_iff`, `dual_pimg`, `fkAR_pimg`
(Proposition 4.21). A cache implementation and its invariant remain to be formalized;
verdict invariance alone does not prove the cache algorithm correct.

**S2. Early collapse under transitivity (Lean, general).** Target: *if `Aut(G)` acts
`k`-transitively on the vertices, the subproblems at depth at most `k` fall into at most
`(k+1)(k+2)` isomorphism classes, under every split rule.* Route: a node at depth `j` is the
minor `G − A / B` with `|A| + |B| = j`, in one of two orientations (Theorem 4.7, Lemma 4.1).
The path's points are distinct, and `k`-transitivity moves any `(A, B)` with given sizes to any
other. If the orientation is fixed by `|B|` (each contraction swaps the sides), the bound
halves to `(k+1)(k+2)/2`: check that first on Fano (2-transitive) and `w11` (sharply
4-transitive) with S0's data. This is the precise form of the old A6 idea, which `hard-classes.md`
§5.2 refuted as a predictor of FK-A against FK-B, and it gives the thesis's
"symmetry depth" a theorem.

**S3. The alternating trees (the main target).** Is `δ_iso` polynomial in `N` on GK `fₖ`
under the degree-sum rule?
- Measure `δ_iso` separately from the cache counts `1, 8, 155, 734,303` before fitting
  its growth. Done: `δ_iso = 1, 8, 160, 827,175` for `k = 1–4`.
- If the growth is polynomial, look for the recurrence. A subproblem of `fₖ` is a restriction
  of the alternating tree, and its shape is a pruned tree, so `δ_iso` counts the pruned shapes
  the degree-sum rule reaches. Prove the recurrence in Lean on the `alt` family (`Cotree`,
  `ReadOnceFormula`), as `matching_tau_delta` was proved.
- If iso-memo with the degree-sum rule is polynomial on read-once pairs, it answers the §7
  item "a rule with FK96's frequency guarantee and small `δ` on read-once pairs" in a weaker
  form (memo by class, not by label). Say which form.
- If `log d_iso / log N` keeps rising at `f₅` (about 0.96 at `f₃`, 1.25 at `f₄`), state Conjecture:
  `δ_iso / N` is unbounded on GK under the degree-sum rule. Conjecture 4.19 then holds for a
  reason beyond symmetry. That outcome is a result too.

**S4. Write-up.** A new section of the research write-up: the three-factor table, S1–S3 with
Lean names, and a corrected reading of thesis Chapter 3 against it (which statements about
`Aut` at nodes predict the factor `δ / δ_iso`, and which do not). Add review-log rows for every
identification it relies on.

**Stop rule.** If S0 shows `δ / δ_iso` bounded by a constant on every family except GK under
the degree-sum rule, do S1 and S2, record S3's data as an Observation, and move to §3 below.

## 3. Short items (one session each, any order)

| Item | Done when |
| --- | --- |
| B: `ε(8) = 2/5` | The CP-SAT infeasibility of `experiments/eps_search.py` re-encoded as SAT, its LRAT proof checked in Lean (`bv_decide`'s LRAT checker), or the search split into `native_decide` cases. Otherwise it stays Conjecture 3.3 |
| B3: `ε(s²) ≤ 1/s` for all `s` | Lean, generalising `eps_four` and `eps_nine` |
| A6: the two FK-A children of `w11` | `|Aut| = 720` for both and primitivity, by evaluation (`WittData.lean` style) |
| T2: FK-A's worst-case exponent | Between `N^{Ω(log N)}` (Corollary 4.26) and FK96's `N^{O(log² N)}`. Either a family where every rule with the frequency guarantee needs `N^{ω(log N)}`, or a rule with `τ ≤ N^{O(log N)}` on all dual pairs; the second would remove JRSW's `log n` factor for monotone functions |
| A5d for `t = 2, 3` | Conjecture 2.12 proved for `t = 2` (an intersecting `S(2,k,v)` is a projective plane: `n₀ = 0` gives `v = k² − k + 1`; then cite Bierbrauer for blocking sets in order `≥ 3`) and for `t = 3` from `n₀(3,k,v) = 0` |

## 4. Parked, with the reason

| Item | Why parked |
| --- | --- |
| C3, the FBDD separation | It is JRSW Question 1 for monotone functions, open since 1997 (Proposition 4.27; literature check of 2026-10-23, review row 66). Mixedness cannot give it (§4). A lower-bound method that tolerates short terms and clauses would be needed; no candidate family is known |
| D3 from `r = 3` | Both sides must be irregular (Proposition 3.7); the transitive groups of degree 16 search needs Sage and many hours |
| E1, Ryser family 162 | Needs `Tr` counted by structure; no bridge to the focus |
| Explorer site | Not research; handed back in the thesis redesign |

## 5. Machines

Lean builds and long searches run on the personal machine. The work laptop takes no multi-hour
runs. Lean builds use the repository path and the Mathlib cache; no drive mapping is needed.
Commit after each phase with `lake build` and targeted tests for changed Python code green,
and push to `main`. Ask before running the full Python suite.

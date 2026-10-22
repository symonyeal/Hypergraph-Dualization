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
its functions. No route to it is in sight.

## 2. Focus: Track S, how much of FK-A's work is symmetry

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

Under FK-A's own rule, isomorphic repetition accounts for a factor of 92 at GK `f₄`, and the
factor grows with `k`. The rest does not collapse: `d_iso / N ≈ 15` at `f₄`, against 0.81 at
`f₃`. So symmetry explains a large and growing share of the blow-up, but the data do not show
that it explains all of it. That is the question for this phase.

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
- Fit `1, 8, 155, 734,303` and S0's `f₅` value. State only what the table shows.
- If the growth is polynomial, look for the recurrence. A subproblem of `fₖ` is a restriction
  of the alternating tree, and its shape is a pruned tree, so `δ_iso` counts the pruned shapes
  the degree-sum rule reaches. Prove the recurrence in Lean on the `alt` family (`Cotree`,
  `ReadOnceFormula`), as `matching_tau_delta` was proved.
- If iso-memo with the degree-sum rule is polynomial on read-once pairs, it answers the §7
  item "a rule with FK96's frequency guarantee and small `δ` on read-once pairs" in a weaker
  form (memo by class, not by label). Say which form.
- If `log d_iso / log N` keeps rising at `f₅` (0.96 at `f₃`, 1.25 at `f₄`), state Conjecture:
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
| A5d for `t = 2, 3` | Conjecture 2.12 proved for `t = 2` (an intersecting `S(2,k,v)` is a projective plane: `n₀ = 0` gives `v = k² − k + 1`; then cite Bierbrauer for blocking sets in order `≥ 3`) and for `t = 3` from `n₀(3,k,v) = 0` |

## 4. Parked, with the reason

| Item | Why parked |
| --- | --- |
| C3, the FBDD separation | No route. First do a bounded literature check of whether a monotone family with polynomial `N` and superpolynomial FBDD size is known: Jukna–Razborov–Savický–Wegener (ECCC TR97-023), Wegener's *Branching Programs and Binary Decision Diagrams* ch. 6–7, the Bollig–Wegener monotone 2-DNF lower bounds for OBDDs and read-once BPs (is the CNF also small?), Beame–Li–Roy–Suciu on decision-DNNF for query lineages. Record the verdict as a review-log row |
| D3 from `r = 3` | Both sides must be irregular (Proposition 3.7); the transitive groups of degree 16 search needs Sage and many hours |
| E1, Ryser family 162 | Needs `Tr` counted by structure; no bridge to the focus |
| Explorer site | Not research; handed back in the thesis redesign |

## 5. Machines

Lean builds and long searches run on the personal machine. The work laptop takes no multi-hour
runs; for Lean there, build from a short `subst` path with the Mathlib cache. Commit after each
phase with `lake build` and `pytest -m "not slow"` green, and push to `main`.

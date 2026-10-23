# Research prompt: the next phase (from 2026-10-23)

The live hand-off for the next research session, on any machine. Pull `main`, then read this file
whole. A result is proved or refuted in Lean, checked by evaluation, computed (and said so), cited,
or open with its search bound. Each new statement gets a numbered entry in
[`research-2026-10.md`](research-2026-10.md) and a row in `thesis/CLAIMS.md`. The Track S plan this
file used to hold is done; its results are research Theorem 4.28, Observation 4.29 and Conjecture
4.30, and the plan is in git history.

## Where things stand

- **Tree.** On GK and TK, FK-A's recursion tree has `τ ≥ 2·(27/16)^{n/4}/(n+1) = N^{Ω(log N)}`
  under every valid rule (Theorems 4.24–4.25, Lean).
- **DAG.** The leftmost rule has `δ ≤ 2n + 2` on GK (Theorem 4.16). FK-A's degree-sum rule has
  `δ/N = 0.67, 1.92, 1368` on GK `f₂–f₄` (Conjecture 4.19).
- **Symmetry.** A memo keyed by isomorphism class is sound (Theorem 4.28, `fkAI_correct`). At GK
  `f₄` under the degree-sum rule it removes a factor 81.3 and leaves `δ_iso/N = 16.8`; under the
  leftmost rule there are no symmetric repeats (Observation 4.29, `results/iso-memo.md`).
- **C3** is the monotone case of JRSW's Question 1, open since 1997 (Proposition 4.27). Parked.

## Q1. A squaring law on GK (main target: settles Conjectures 4.19 and 4.30)

*Frame.* On GK, `|C(f_{k+1})| = 2|C(f_k)|²` and `|D(f_{k+1})| = 4|D(f_k)|²`, so
`N_{k+1} = (4/3)·N_k²` exactly (`N = 3, 12, 192, 49,152, 3,221,225,472`). Write `r_k = δ_k/N_k`.
If `δ_{k+1} ≥ c·δ_k²` for every `k ≥ k₀`, then `r_{k+1} ≥ (3c/4)·r_k²`, so `r_k → ∞` doubly
exponentially in `k` (hence `δ ≥ N^{1+ε}`) once `r_{k₀} > 4/(3c)`. Computed: `r₄ = 1368` for `δ`
and `16.8` for `δ_iso`, so `c = 1/4` suffices from `k₀ = 4` for both (`16.8 > 16/3`).

*Question.* Under the degree-sum rule, is `δ(f_{k+1}) ≥ δ(f_k)²/4`, and the same for `δ_iso`?
Every measured step meets the plain square: `δ = 1, 8, 369, 67,247,387`; `δ_iso = 1, 8, 160, 827,175`.

*Route.* An embedding lemma: projected onto two top blocks in different halves (`a` and `c` of
`(a∧b)∨(c∧d)`), the live sets FK-A reaches on `f_{k+1}` include every pair of live sets it reaches
on `f_k`. Since `δ_{k+1}` is at least the number of distinct projections, and `f_k` has at least
`δ_k/2` distinct live sets, this gives `c = 1/4`. Containment is not automatic: by the identity in
Observation 4.29, inside block `a` the rule maximises `deg_a x + λ·deg_{a^d} x` with
`λ = (|c^d| + |d^d|)/|b|`, not `λ = 1`. For `δ_iso`, use block shapes in place of live sets; they are
an invariant only while no block's root gate collapses into its parent.

*Falsification update (Observation 4.31).* At GK `f₃`, all seven nonempty standalone `f₂`
supports occur in each marginal, but only 21 of their 49 pairs occur jointly. The unrestricted
embedding is false at that level; the proposed squaring law from `k ≥ 4` remains open. The
Rust `--joint` probe and `experiments/block_probe.py` reproduce the missing support witness.
The probe tests nonempty targets, forgetting orientation; passing it is necessary but does not
by itself certify the full embedding or its isomorphism analogue.

*Route after 4.31* (research §4, "The Q1 route after Observation 4.31").
- *Balance* (Proposition 4.34, Lean): on GK every vertex has equal term and clause degree, so
  every OR-rooted block starts at weight `λ = 1`; GK sits on the fixed point of the count flow,
  which is where `N_{k+1}/N_k²` is least (`4/3`).
- *Target* (Proposition 4.37): for `δ` the step may lose a factor `A·n_k` with `A < 2.004` and
  still settle Conjecture 4.19 from `r₄ = 1368`; for `δ_iso` only a constant `A < 12.6`.
- *Block states* (Lemma 4.36): a top block's projections are reached by the hull rule (any
  maximiser of `deg_C + λ·deg_D`, `λ > 0` free at each node), so condition (i) below is about
  which `λ` the environment produces.
- *New embedding* (Conjecture 4.38): only pairs of standalone supports of **equal size** must
  occur jointly. Cauchy–Schwarz over the `n_k` sizes then gives the `β = 1` step. All three
  known missing pairs are of unequal size. The four-block form would make `δ` superpolynomial
  in `N`.

*Next tests, in order.* (1) Recount the existing GK `f₃` and TK `S₂–S₃` joint probes on
equal-size pairs: seconds. (2) Rust `--joint` on GK `f₄` (personal machine; runtime not
measured). Index each block's live sets (at most 1,908) and record the joint `(S∩a, S∩c)` pairs
in a 1,908² bitset. Check (i) that `f₃`'s reached live sets, moved onto block `a`, are among
block `a`'s states, and (ii) that the equal-size pairs of them all occur. (3) Count `R*(f₃)`, the
hull rule's reach, against the 1,893–1,908 marginal supports.

*Not by enumeration.* If the law holds, `δ(f₅) ≥ 1.1·10¹⁵`; the evidence must come from `f₄`
projections and from proof.

*The TK contrast* (Observation 4.35). The step `δ_{k+1} ≥ δ_k²/4` holds at every measured step
of TK too (`δ_{k+1}/δ_k² = 2.13, 3.58`), and `log δ / log N` rises there as well
(`0.77, 0.82, 0.86`). TK's `δ/N` falls because `N_{k+1}/N_k² → 4` off balance while `r < 1`. A
proof of the step need not use anything TK lacks. Open: whether `δ/N` turns up on TK; it needs TK
`S₄` under the degree-sum rule (personal machine).

*Deliverable.* The reduction in Lean on `coalt` (sizes from `alt_shape`); the embedding lemma in
Lean, or the failing step as an Observation.

## Q2. A rule with FK96's guarantee and small `δ` (Track 3)

*Frame.* The leftmost rule has `δ = n` and no frequency guarantee. The guarded rule keeps the
frequency `≥ 1/⌊log₂ N⌋` at every node (Proposition 4.18), but `δ = 32, 263, 124,876` on GK `f₃–f₅`
(`n = 32, 128, 512`), and keying by class saves little (`δ_iso = 32, 215, 23,099`).

*Question.* Is there a valid rule with the guarantee and `δ` polynomial in `n` on GK and TK? Or
does every rule with the guarantee have `δ` superpolynomial in `n` on GK?

*First step completed (Observation 4.32).* GK `f₅` has zero degree-sum fallbacks. The guarded
rule already chooses the least eligible variable. It departs from leftmost at 92,776 of
124,874 split states; first at live support `{18,…,511}`, choosing 20 rather than leftmost 18
or degree-sum 256. The full per-support-size trace is `results/block-probes/gk5-guard.json`.
Next: investigate eligibility-driven interleaving and alternative eligible choices. FK96's
bound `τ ≤ N^{O(log² N)}` for the guarded rule still needs Lean formalisation.

## Q3. FK-A's worst-case exponent (T2)

*Frame.* FK-A's tree is a decision tree with at most `(n+1)τ` leaves (Theorem 4.25). JRSW ask
whether the `log n` in Ehrenfeucht–Haussler's `exp(O(log n · log² N))` can be removed; a valid rule
with `τ ≤ N^{O(log N)}` on every monotone dual pair would remove it for monotone `f`, and Theorem
4.24 makes that tight on GK. FK96 gives `τ ≤ N^{O(log² N)}` under the guarantee.

*Lead* (computed from `results/iso-memo.md`). `log₂ τ / (log₂ N)²` is `0.28, 0.25, 0.25` on GK
`f₃–f₅` under the guarded rule, `0.29, 0.27` under the degree sum, and `0.27, 0.10, 0.25` on
`alt3 d₃–d₅` (guarded): flat, consistent with `N^{Θ(log N)}` on these families.

*Question.* Prove `τ ≤ N^{O(log N)}` for one rule, first on read-once pairs (states are live sets;
the `Fm` library applies), or find a family where `log τ / log² N` grows under every rule with the
guarantee.

## Q4. What the thesis's symmetry statements predict (S4, write-up)

*Frame.* Of the factor 81.3 at GK `f₄`, `δ/δ_Aut = 56.8` comes from the input's automorphisms;
`w11` has `δ/δ_iso = δ/δ_Aut = 4.0`; `trivial-aut-1` has `|Aut| = 1` and still `δ/δ_iso = 1.7`.

*Question.* Which statements of thesis Chapter 3 about `Aut` at nodes predict `δ/δ_Aut`, which
predict `δ/δ_iso`, and which predict neither? Deliverable: a section of the research write-up with
a review-log row for each identification.

*Scope audit written:* Audit 4.33 and review rows 73–78 distinguish inherited input symmetries,
local node automorphisms and maps between reached nodes. None of the Chapter 3 local group
statements alone supplies either measured repetition factor. The revised chapter's retained
§3.5 discussion still makes unsupported group-comparison claims; it has not been rewritten.

## Short items (one session each)

| Item | Done when |
| --- | --- |
| B: `ε(8) = 2/5` | The CP-SAT infeasibility of `experiments/eps_search.py` re-encoded as SAT and its LRAT proof checked in Lean, or the search split into `native_decide` cases; otherwise it stays Conjecture 3.3 |
| B3: `ε(s²) ≤ 1/s` for all `s` | Lean, generalising `eps_four` and `eps_nine` |
| A6: the two FK-A children of `w11` | `|Aut| = 720` for both, and primitivity, by evaluation (`WittData.lean` style) |
| A5d for `t = 2, 3` | Conjecture 2.12 for `t = 2` (an intersecting `S(2,k,v)` is a projective plane; cite Bierbrauer for order `≥ 3`) and for `t = 3` from `n₀(3,k,v) = 0` |
| Observation 4.29's dashes | TK `S₄` and `alt3 d₅` under the degree-sum rule with `--classes --spill` on the personal machine (about 60,000 nodes per second; `alt3 d₅` has more than `10⁸` subproblems). Fills the table; decides nothing in Q1 |

## Parked, with the reason

| Item | Why parked |
| --- | --- |
| C3, the FBDD separation | JRSW Question 1 for monotone functions (Proposition 4.27, review row 66). Needs an FBDD lower-bound method that tolerates short terms and clauses; no candidate family is known. A hard family for the iso-keyed memo would be harder still, since `d_iso ≤ δ` |
| D3 from `r = 3` | Both sides must be irregular (Proposition 3.7); the degree-16 transitive-group search needs Sage and many hours |
| E1, Ryser family 162 | Needs `Tr` counted by structure; no bridge to the focus |

## Machines

Lean builds and long runs go on the personal machine; the work laptop takes no multi-hour runs and
has about 1.7 GB free. Rust: `cargo build --release` in `experiments/readonce_dag`. Commit after each
phase with `lake build` and the changed code's tests green, and push to `main`. Ask before running
the full Python suite.

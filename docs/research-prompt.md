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

*Falsify first* (Rust `--classes` on GK `f₄`, about 20 minutes, little memory). Index each block's
live sets (at most 1,908) and record the joint `(S∩a, S∩c)` pairs in a 1,908² bitset. Check that
(i) `f₃`'s reached live sets, moved onto block `a`, are among block `a`'s states, and (ii) the
joint pairs include all pairs of them. If (i) fails, find the family of rules `argmax deg + λ·deg^d`
whose reached states block `a` sees, and ask the squaring question for that family.

*Not by enumeration.* If the law holds, `δ(f₅) ≥ 1.1·10¹⁵`; the evidence must come from `f₄`
projections and from proof.

*Explain the contrast.* On TK, `N_{k+1}/N_k² = 2, 3.19, 3.94` and `δ/N = 0.67, 0.47, 0.25` falls; a
proof has to use what GK has and TK lacks.

*Deliverable.* The reduction in Lean on `coalt` (sizes from `alt_shape`); the embedding lemma in
Lean, or the failing step as an Observation.

## Q2. A rule with FK96's guarantee and small `δ` (Track 3)

*Frame.* The leftmost rule has `δ = n` and no frequency guarantee. The guarded rule keeps the
frequency `≥ 1/⌊log₂ N⌋` at every node (Proposition 4.18), but `δ = 32, 263, 124,876` on GK `f₃–f₅`
(`n = 32, 128, 512`), and keying by class saves little (`δ_iso = 32, 215, 23,099`).

*Question.* Is there a valid rule with the guarantee and `δ` polynomial in `n` on GK and TK? Or
does every rule with the guarantee have `δ` superpolynomial in `n` on GK?

*First step.* Count, per level, where the guarded rule falls back to the degree sum at GK `f₅`,
and test fallbacks that stay close to leftmost (the least variable among those meeting the
frequency bound). Then FK96's bound `τ ≤ N^{O(log² N)}` for the guarded rule, in Lean.

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

# Connections to `openai/math`

[`openai/math`](https://github.com/openai/math) collects 719 manuscripts in 372 result families,
with a Lean library for some of them. This note records which of those results touch the thesis,
surveyed on 2026-10-20 from the repository's `CONTENTS.md`, `overview.tex` and
`lean/formalization.yaml`. Every statement made here about the thesis side is proved in
[`lean/HypergraphDualization/Connections.lean`](../lean/HypergraphDualization/Connections.lean);
statements about the `openai/math` results are theirs and are cited, not re-proved.

## Direct connections

| Family | Result | Bridge to the thesis | Lean |
| --- | --- | --- | --- |
| 162 | Counterexamples to Ryser's covering conjecture: intersecting `(q+1)`-partite `(q+1)`-uniform hypergraphs with covering number `q+1`, formalized as `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank` | A cover is a transversal, and the covering number `τ(H)` is the size of a smallest edge of `Tr(H)`. An intersecting `r`-uniform `H` always has `τ ≤ r`; Ryser's bound is `r − 1`, so the counterexamples are the extremal case `τ = r`. In that case every edge of `H` and of `Tr(H)` has at least `r` vertices, and Corollary 2.3.1 (corrected) gives `|H| + |Tr(H)| ≥ 2^r` | `isCover_iff_hits`, `coverNumber_eq_tr_min`, `coverNumber_le_of_intersecting`, `ryser_extremal_size` |
| 186, 176, 175 | Friedgut–Kalai threshold widths; the second Kahn–Kalai conjecture (formalized as `OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds`); Talagrand's expectation-threshold conjectures | A Sperner hypergraph is a monotone property: a set has it when it contains an edge. For a transversal pair `(G, H)`, `P_p(G) + P_{1−p}(H) = 1`, with `P_p` the product measure `bernoulliProbability` of the formalization. Duality is complementation composed with `p ↦ 1 − p`, so a self-transversal hypergraph (`K₃`, `hw₃`, the Fano plane) has `P_{1/2} = 1/2`: its critical probability is exactly `1/2` | `bernoulli_dual`, `bernoulli_self_dual`, `fano_k3_balanced` |
| 186 | The Friedgut–Kalai hypothesis is relabeling invariance: a transitive symmetry group | A transitive `Aut(H)` makes every vertex equally frequent, the frequency FK-A splits on (§5.2.2); this is the setting in which the Fano plane is hard for FK-A | `degree_eq_of_transitive` |

The definitions `IsCover`, `Intersecting`, `coverCardinalities`, `coverNumber`,
`bernoulliWeight` and `bernoulliProbability` are restated verbatim from
`lean/ComparatorChallenges/RyserCovering.lean` and `SecondKahnKalai.lean`, so the bridge
theorems are statements about the same objects. The `openai/math` library itself is not imported:
it pins Lean `v4.34.1` and this project pins `v4.35.0`.

## Reproduction

`lake build HypergraphDualization.Connections` from `lean/` checks the bridge declarations
named in the table. It does not check the cited manuscripts or their identifications.
The candidates were drawn from the theoretical computer science, combinatorics and group theory
sections of `overview.tex`, read entry by entry, and from a keyword search of the whole catalogue
(transversal, hypergraph, covering, monotone, Boolean, DNF, threshold, self-dual, automorphism,
permutation group, projective plane, Sperner, antichain, Dedekind). Families outside those
sections that match no keyword were not read.

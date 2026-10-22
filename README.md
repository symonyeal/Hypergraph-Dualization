# Hypergraph Dualization

Research companion to the MSc thesis *Tracing the Effects of Symmetry in Hypergraphs on the
Fredman–Khachiyan Algorithm* (Saimon Y. Islam, Simon Fraser University, 2024; supervisor Tamon
Stephen).

[![Lean](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/lean.yml/badge.svg)](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/lean.yml)
[![Tests](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/tests.yml/badge.svg)](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/tests.yml)

## The problem

A set `T ⊆ V` is a *transversal* of a hypergraph `H` on `V` if it meets every hyperedge, and a
*minimal* transversal if no proper subset is one. The minimal transversals form the *transversal
hypergraph* `Tr(H)`, which is Sperner. **TransHyp** asks, given two Sperner hypergraphs `H₁` and
`H₂`, whether `H₂ = Tr(H₁)`. No polynomial algorithm is known. Fredman and Khachiyan (1996) gave
two quasi-polynomial algorithms, **FK-A** (`n^{O(log² n)}`) and **FK-B** (`n^{o(log n)}`), where
`n` is the total number of hyperedges. FK-A recurses on a split vertex of high frequency; some
highly symmetric families, the alternating trees (the GK- and TK-families, which Hertel unified)
and the Fano plane, make its recursion tree superpolynomial. The thesis studies how the symmetry of a hypergraph,
through its automorphism group `Aut(H)` and its underlying graph, interacts with that recursion.

## Policy: a result is a Lean declaration

Every statement in this repository is one of:

- **proved** in Lean 4 against Mathlib, for every input;
- **refuted** by a counterexample that Lean checks;
- **checked**, a finite fact about named instances evaluated in Lean (`native_decide`);
- **computed**, a number from the Python or Rust code, reported as computation;
- **cited** or **conditional**, resting on a named source or hypothesis, and saying so;
- **open**, stated as a conjecture with its evidence and the exact bound of the search behind it.

The Python engine (`src/fka`, `src/fkb`) runs the algorithms, draws their recursion trees and
searches for candidates; a number it produces is a lead until it is formalised.
[`thesis/CLAIMS.md`](thesis/CLAIMS.md) is the register: every statement, its status and the Lean
declaration that settles it. General theorems use only the axioms `propext`, `Classical.choice`
and `Quot.sound`, and checked facts are evaluations; `lean/HypergraphDualization/Axioms.lean`
makes the build fail otherwise.

## The thesis in Lean

The source was recovered from the deposited PDF in October 2026 and every statement the thesis
makes on its own authority was checked. Most hold as printed. The revised edition
([`thesis/revised/main.pdf`](thesis/revised/main.pdf)) applies the corrections, tags each
statement with its Lean proof and lists the corrections in its preface; the 2024 text is kept
verbatim in [`thesis/2024/`](thesis/2024). Among the corrections:

- Corollary 2.3.1: the inequality is reversed; the shortest hyperedge has `s ≤ log₂ n` vertices.
- Lemma 3.3.1 needs the Sperner hypothesis; Lemma 3.3.3 is false (counterexample in Lean).
- Claim 3.1.6: invariant vertex sets are unions of orbits, not orbits.
- The §3.2 edge sets, the §4.2.3 recurrences and the transversal count of Definition 5.2.1.
- Observation 5.2.3: `ε(7) = 3/7` is now proved, not only claimed (below).
- Chapter 4 cited Hertel's bound for the alternating trees as an upper bound on subproblems; it is
  a lower bound on every DPLL decision tree, hence on FK-A's recursion tree.

## New results (October 2026)

Written up in [`docs/research-2026-10.md`](docs/research-2026-10.md). Lean names are given in
parentheses; a statement without one is cited or conditional, and says so.

**Self-transversal hypergraphs** (`H = Tr(H)`).
- For Sperner `H`: `H = Tr(H)` iff `H` is intersecting, has no empty hyperedge and is not
  2-colourable (`tr_eq_self_iff`). For intersecting `H` without the empty hyperedge this is the
  case iff exactly `2^{n−1}` vertex sets contain a hyperedge (`tr_eq_self_iff_card`).
- A self-transversal hypergraph covering `n` vertices has at least `n` hyperedges, by Seymour's theorem
  on 3-critical hypergraphs (`card_le_of_critical`, `card_le_of_tr_eq_self`); `K₃` and the Fano
  plane attain it.
- If every minimal transversal of `H` is a hyperedge and `Aut(H)` is transitive on hyperedges,
  it is transitive on the vertices `H` covers (`transitive_of_edge_transitive`).
- Intersecting, `r`-uniform, `d`-regular on `t` vertices: `d(r² − t) ≥ r(r − 1)`, with equality
  iff distinct hyperedges meet in one vertex (`intersecting_regular_bound`).

**Steiner systems and the Witt design.**
- Every Steiner system `S(t, t+1, 2t+3)` is self-transversal, and `t` is even (`witt_tr_eq`). The
  Fano plane is `t = 2`; the Witt design `S(4,5,11)` is `t = 4`.
- In `S(t,k,v)` every block is disjoint from exactly `n₀(t,k,v)` blocks (`steiner_disjoint`),
  which rules out self-transversality for whole parameter families at once (`n0_table`).
- `|Aut(S(4,5,11))| = 7920`, acting sharply 4-transitively (`card_aut_w11`, checked by
  evaluation); by Jordan's theorem this is the Mathieu group `M₁₁` (cited).
- A read-once hypergraph on `n ≥ 2` vertices with primitive `Aut(H)` has `Aut(H) = Sₙ`
  (`aut_eq_top_of_readOnce`), so neither the Fano plane nor `S(4,5,11)` is read-once.

**The frequency `ε`.** If `s` is the size of a smallest hyperedge, then `sε ≥ 1` and `s ≤ nε`
(`eps_bound`). Hence `ε(7) = 3/7`, attained by the Fano plane (`eps_seven`), and `nε² ≥ 1` (`eps_sq`);
`s` disjoint `s`-sets attain `ε(s²) = 1/s` (in Lean for `s = 2, 3`). `ε(8) = 2/5` is supported by a CP-SAT search but not proved.

**Frequency rigidity and stability.** For nonempty cross-intersecting families, let
`X = Σ_{g,h} (|g ∩ h| − 1)`. Then `1 + X/(|G||H|) ≤ nε²` (`eps_crossExcess`). Attaining
`nε² = 1` forces square order, uniformity, regularity and singleton cross intersections (`eps_eq_rigid`);
Gurvich's theorem then implies read-once structure (cited). Self-transversal families on more
than one point satisfy the strict inequality (`eps_self_strict`). The [source audit](docs/frequency-equality-research.md)
distinguishes these proofs from the cited structural bridge; novelty is not claimed.

**FK-A's recursion tree against its distinct subproblems.** For the perfect matching on `v ≥ 4`
vertices the tree has `2^{v/2+1} − 3` nodes but only `v` distinct subproblems; for the threshold
graph both are `v − 1` (`matching_tau_delta`, `threshold_tau_delta`). Under the exponential-time
hypothesis no polynomial bounds the number of distinct subproblems on all dual pairs
(conditional, from Kobayashi–Kurita–Wasa 2026).

**Substitution.** For a template `T` and hypergraphs `Γᵢ`,
`Tr(T[Γ]) = min(Tr(T)[Tr Γ])`; on disjoint vertex sets no reduction is needed and
`|T[Γ]| = Σ_{t∈T} Π_{i∈t} |Γᵢ|` (`tr_subst`, `tr_subst_of_disjoint`, `card_subst`). Union and
join are the two smallest templates; the alternating trees and the word families are iterated substitutions.

**Bridges to [`openai/math`](https://github.com/openai/math).** Covers in Ryser's conjecture are
transversals; `P_p(H) + P_{1−p}(Tr H) = 1`, so a self-transversal hypergraph has critical
probability `1/2`; automorphisms preserve influences, so the Fano plane's seven vertices have
equal influence at every `p` (`influence_aut`, `fano_influence_eq`). See
[`docs/openai-math-connections.md`](docs/openai-math-connections.md).

**Why FK-A's subproblems multiply.** On a dual pair every subproblem is a minor `H` of the
input with its transversal, `(H, Tr H)` or `(Tr H, H)`, and both orientations have the same
children (`fkADag_minor`, `fkA_comm`). A dual node is never pruned, so `d`-resilient inputs have
`τ ≥ 2^{d+1} − 1` (`tau_ge_of_resilient`), and the repeated work `τ − δ` is superadditive with
the children's overlap as surplus (`excess_split`). The distinct subproblems `δ` depend on the
split rule. FK-A's most-frequent-vertex rule gives the read-once pair `ro12` on 12 points
`δ = 43 > 2N = 42` (`ro12_delta`), refuting the conjecture `δ ≤ 2N` on read-once pairs, and
GK `f₄` `δ = 67,247,387` on `N = 49,152` (computed). D3 has no counterexample at rank 2
(`template_rank_two`, checked).

**The split rule is a variable order.** Under a valid symmetric split rule, the subproblems of
memoised (unmodified) FK-A form a free binary decision diagram named by its functions for the
input function, of size at most `2δ + 2`; conversely every such diagram gives a valid symmetric
rule with `δ` at most twice its size (`memo_fbdd`, `rule_of_fbdd`). Research §4 states the
qualifications. Splitting on the least vertex of a read-once formula with leaves in order gives
`δ ≤ 2n + 2` (`leftmost_delta`; cf. Hertel's Theorem 4.4.1); on GK `f₄` it gives `δ = 128`
(computed). A guarded rule keeps FK96's frequency guarantee at every node (`guardRule_frequent`)
and gives `δ = 263` on GK `f₄` (computed). The dictionary to knowledge compilation, resolution, fault trees, matroids and monomial
ideals is §4 of [`docs/applications.md`](docs/applications.md).

Open: the converse of the Steiner theorem, `ε(8)`, whether `δ/N` is unbounded on the
alternating trees under FK-A's rule, D3 from rank 3, and an explicit family that is hard for
memoised FK-A under every valid symmetric split rule: up to a factor 2, a monotone function with
small DNF and CNF but no small FBDD named by its functions (research §7, C3). The list is §7 of the research write-up.

## Layout

| Path | Contents |
| --- | --- |
| [`lean/`](lean) | The Lean library: thesis statements, corrections, new results ([module index](lean/README.md)) |
| [`thesis/`](thesis) | The 2024 text as deposited and recovered, the revised edition, [`CLAIMS.md`](thesis/CLAIMS.md) |
| [`docs/research-2026-10.md`](docs/research-2026-10.md) | The new results, with proofs and Lean names |
| [`docs/applications.md`](docs/applications.md) | Where TransHyp is used, by what `H` and `Tr(H)` are, with a shortlist |
| `docs/` (other) | Computational notes from the Python engine: FK-A against FK-B, hard instances, hard classes, tree against distinct subproblems; the code's vocabulary ([`dictionary.md`](docs/dictionary.md)) |
| `src/fka`, `src/fkb` | FK-A (faithful and the thesis's modified variant), FK-B, Berge's sequential method as an independent check, automorphism groups, memoisation |
| `data/instances/` | The thesis hypergraphs and the later instances (`w11` is `S(4,5,11)`), as JSON with provenance |
| `results/` | Recursion trees of both algorithms on every instance (JSON, DOT, HTML) |
| `experiments/` | Searches and generators, each seeded ([index](experiments/README.md)) |
| `tests/` | The engine checked against the printed recursion trees and the MATLAB FK-B reference |
| `_archive/` | Superseded material, each folder with a note |

The code is written in the monotone Boolean register of the FK-B reference (`cnf` for `H`, `dnf`
for `Tr(H)`); [`docs/dictionary.md`](docs/dictionary.md) gives the correspondence with the
thesis's hypergraph terms.

## Build

```text
cd lean && lake exe cache get && lake build      # every proof; a few minutes with the cache
cd thesis/revised && pdflatex main && bibtex main && pdflatex main && pdflatex main
python -m pip install -e ".[dev]" && python -m pytest -m "not slow"
python -m fka run fano                           # FK-A on the Fano plane, with its recursion tree
python -m fkb compare --all                      # FK-A against FK-B on the instance library
```

SageMath is an optional independent backend for the group computations
([`docs/sagemath.md`](docs/sagemath.md)).

## Authorship and licence

Saimon Y. Islam; the original implementation was written with Lacey Liang. GPL-3.0-or-later. The
revised edition uses SFU's `sfuthesis` class (LPPL 1.3). FK-B is an independent implementation
from the published algorithm; the MATLAB reference it was checked against stays local
(`FK- B/`), since its redistribution terms are not established. Cite the thesis
([`CITATION.cff`](CITATION.cff)).

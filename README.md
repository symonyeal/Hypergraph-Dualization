# Hypergraph Dualization

Research companion to the MSc thesis *Tracing the Effects of Symmetry in Hypergraphs on the
Fredman–Khachiyan Algorithm* (Saimon Y. Islam, Simon Fraser University, 2024; supervisor Tamon
Stephen).

[![Lean](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/lean.yml/badge.svg)](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/lean.yml)
[![Tests](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/tests.yml/badge.svg)](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/tests.yml)

## Problem

- A set `T ⊆ V` is a *transversal* of a hypergraph `H` on `V` if it meets every hyperedge, and a
  *minimal* transversal if no proper subset is one.
- The minimal transversals form the *transversal hypergraph* `Tr(H)`, which is Sperner.
- **TransHyp**: given two Sperner hypergraphs `H₁` and `H₂`, decide whether `H₂ = Tr(H₁)`. No polynomial
  algorithm is known.
- Fredman and Khachiyan (1996) gave two quasi-polynomial algorithms, **FK-A** (`n^{O(log² n)}`) and
  **FK-B** (`n^{o(log n)}`), where `n` is the total number of hyperedges.
- FK-A recurses on a split vertex of high frequency. The alternating trees (the GK- and TK-families,
  which Hertel unified) give superpolynomial recursion trees. The Fano plane is a small symmetric
  instance used to study the same decomposition.
- The thesis studies how the symmetry of a hypergraph, through its automorphism group `Aut(H)` and its
  underlying graph, interacts with that recursion.

## Methods

- **Engine** (`src/fka`, `src/fkb`, Python): FK-A (the faithful version and the thesis's modified
  variant), FK-B, Berge's sequential method as an independent check, automorphism groups and
  memoisation. It runs the algorithms, draws their recursion trees and searches for candidates. A number
  it produces is a lead until it is formalised.
- **Vocabulary**: the code uses the monotone Boolean register of the FK-B reference (`cnf` for `H`,
  `dnf` for `Tr(H)`); [`docs/dictionary.md`](docs/dictionary.md) gives the correspondence with the
  thesis's hypergraph terms.
- **Formalisation** (`lean/`, Lean 4 against Mathlib): the thesis statements, their corrections and the
  new results. The thesis source was recovered from the deposited PDF in October 2026.
- **Claim register**: [`thesis/CLAIMS.md`](thesis/CLAIMS.md) records the audited thesis
  statements and later results with their status and Lean declaration or written source.
  Its key distinguishes proofs, finite checks, computations, cited or conditional
  results, and open or withdrawn claims.
- **Axiom check**: general theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`,
  and checked facts are evaluations; `lean/HypergraphDualization/Axioms.lean` makes the build fail
  otherwise.
- **Thesis**: one corrected source in [`thesis/`](thesis), with its
  [compiled PDF](thesis/main.pdf) and Lean declaration references.
- **Experiments** (`experiments/`): searches and generators, each seeded ([index](experiments/README.md)).
- **Validation** (`tests/`): the engine is checked against the printed recursion trees and the MATLAB
  FK-B reference. FK-B is an independent implementation from the published algorithm; the MATLAB
  reference stays local (`FK- B/`), since its redistribution terms are not established.

## Layout

- [`lean/`](lean): the Lean library ([module index](lean/README.md)).
- [`thesis/`](thesis): the corrected source, compiled PDF and
  [`CLAIMS.md`](thesis/CLAIMS.md).
- `data/instances/`: the thesis hypergraphs and the later instances (`w11` is `S(4,5,11)`), as JSON with
  provenance.
- `docs/`: the research record ([`research-2026-10.md`](docs/research-2026-10.md)), notes on the later
  results, computational notes from the Python engine, and the code vocabulary
  ([`dictionary.md`](docs/dictionary.md)).
- `_archive/`: original source log and withdrawn thesis instances required to reproduce the corrections.

## Execution

```text
python -m pip install -e ".[dev]" && python -m pytest -m "not slow"
python -m fka run fano                           # FK-A on the Fano plane, with its recursion tree
python -m fkb compare --all                      # FK-A against FK-B on the instance library
```

Build instructions are in [`lean/README.md`](lean/README.md) and
[`thesis/README.md`](thesis/README.md). SageMath is an optional backend for group computations
([`docs/architecture.md#sagemath`](docs/architecture.md#sagemath)).

## Since the thesis

New results from October–November 2026, apart from corrections to the thesis, with their status as
defined under Methods. Theorem numbers are those of [`research-2026-10.md`](docs/research-2026-10.md).

- **Self-transversal designs.** Every Steiner system `S(t, t+1, 2t+3)` has `t` even and satisfies
  `Tr(H) = H`; the Fano plane and the Witt design `S(4,5,11)` are the cases `t = 2, 4` (Theorem 2.11,
  Lean).
- **Least frequency.** Every non-trivial transversal pair on `n` points has `n·ε² ≥ 1` (Theorem 3.1,
  Lean); `s` disjoint `s`-sets attain `ε = 1/s` at `n = s²`, so `ε(n) = Θ(n^{−1/2})` (written).
  `ε(7) = 3/7`, attained by the Fano plane (Corollary 3.2, Lean).
- **The frequency-lemma constant.** Every dual pair has `|C||D| ≥ 4^{1/ε − 1}`, and every read-once pair
  `|C||D| ≥ e^{2(1/ε − 1)}`; the alternating words attain `8^{1/ε − 1}` (written proofs,
  [`frequency-constant.md`](docs/frequency-constant.md)).
- **FK-A's subproblems.** The memo DAG of unmodified FK-A is a free binary decision diagram (FBDD) of
  size at most `2δ + 2` (Theorem 4.13, Lean), so a monotone family with polynomially many edges and
  superpolynomial FBDD size would defeat every valid symmetric rule. A memo keyed by isomorphism
  class is sound (Theorem 4.28, Lean).
- **FK-A's recursion tree.** It unfolds into a decision tree (Theorem 4.25, Lean). So on the GK and
  TK families on `n` vertices every valid rule has `τ ≥ 2·(27/16)^{n/4}/(n + 1)` (Lean), which is
  `N^{Ω(log N)}` (written), while under the leftmost rule memoisation saves a factor exponential in `n` (Corollary 4.26, Lean); under the degree-sum rule of the implementation whether `δ/N` is bounded is open (Conjecture 4.19).
- **The exponent of that tree.** On GK and TK the least `τ` over valid rules is bounded below by
  `2^{0.41433 n}/(n + 1)` and above by `2^{(0.469254 + o(1)) n}` (written lower bound;
  upper bound argued and computed). Depth-first trees are
  optimal for every leaf weighting on GK `f₁–f₃` (computed). The remaining gap reduces to one
  inequality per gate, Conjecture 17 ([`complex-evaluation.md`](docs/complex-evaluation.md)).
- **Substitution.** `Tr(T[Γ]) = min(Tr(T)[Tr Γ])`, without the `min` on disjoint supports
  (Theorem 5.1, Lean).

## Results

Results are in [`docs/research-2026-10.md`](docs/research-2026-10.md) (proofs and Lean names),
[`thesis/CLAIMS.md`](thesis/CLAIMS.md) (status of every statement and the thesis corrections),
[`results/`](results) (computed tables; per-run JSON, HTML and DOT generated on demand) and
[`docs/research-2026-10.md#7-open-items`](docs/research-2026-10.md#7-open-items) (open problems).

## Authorship and licence

Saimon Y. Islam; the original implementation was written with Lacey Liang. GPL-3.0-or-later. The
corrected thesis uses SFU's `sfuthesis` class (LPPL 1.3). Cite the thesis
([`CITATION.cff`](CITATION.cff)).

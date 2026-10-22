# Hypergraph Dualization

Fredman–Khachiyan algorithms FK-A and FK-B.

[![Tests](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/tests.yml/badge.svg)](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/tests.yml)
[![Lean](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/lean.yml/badge.svg)](https://github.com/symonyeal/Hypergraph-Dualization/actions/workflows/lean.yml)
[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/symonyeal/Hypergraph-Dualization/main?urlpath=lab)

## In plain terms

This is the code for an MSc thesis in mathematics. It studies one basic problem that comes
up whenever someone asks for all the smallest ways to do something.

An example: an organization has several committees and wants a delegation that includes at
least one member of every committee. A delegation is *minimal* if removing anyone from it
breaks that rule. Listing every minimal delegation is called *dualization*. The same problem
appears when listing every minimal way a system can fail, in database design, and in data
mining. The companion project
[Resilient-Supplier-Panels](https://github.com/symonyeal/Resilient-Supplier-Panels) uses it
to find every minimal panel of backup food suppliers.

The hard part is checking that a list is complete, with no minimal delegation missing. In
1996, Fredman and Khachiyan gave a method far faster than trying every possibility. Whether
a truly efficient method exists (one that runs in polynomial time) is still an open
problem. This repository implements two versions of their method, called FK-A and FK-B. It
runs both on the same examples, draws their search trees side by side, and looks for the
examples that make them work hardest.

**Findings, briefly.** The two versions always agree, and an independent check confirms
every answer. The search for new hard examples found one, built from a classical structure
in combinatorics (the Witt design S(4,5,11)). Many examples that look hard make the method
solve the same sub-problem over and over. When only distinct sub-problems are counted, none
of the published hard examples is hard for the method itself.

The rest of this page is written for specialists.

## Overview

This is the maintained research implementation for Saimon Y. Islam's work on
hypergraph dualization, symmetry, and the Fredman-Khachiyan algorithms. The
mathematical reference is [Saimon Islam Manuscript MSc Thesis (1).pdf](Saimon%20Islam%20Manuscript%20MSc%20Thesis%20(1).pdf).
The definitive repository is
[symonyeal/Hypergraph-Dualization](https://github.com/symonyeal/Hypergraph-Dualization).

Both algorithms decide the same question against one shared model, one instance
library, and one visualiser, so their recursion trees are directly comparable.
They state it in different languages, and the identification is the point:

```
G = Tr(H)          hypergraph dualization        FK-A's statement
f^d = g            monotone Boolean duality
C ≡ D              a CNF and a DNF agree         FK-B's statement
```

A monotone Boolean function **is** a hypergraph and its dual **is** the
transversal hypergraph, so the code is written in **one** vocabulary — the
monotone-Boolean register of the FK-B reference. `cnf` is the `G` side, `dnf`
the `H` side, and `fk_a(cnf, dnf)` and `fk_b(cnf, dnf)` take the same arguments
and return the same answer. [docs/dictionary.md](docs/dictionary.md) is the full
correspondence, and the only place the hypergraph names are recorded.

| | package | source | what it returns |
| --- | --- | --- | --- |
| **FK-A** | `src/fka/` | thesis Algorithm 1, p.13 | a conflicting assignment `S` satisfying equation 2.1 |
| **FK-B** | `src/fkb/` | *How to apply SAT-solving for the equivalence test of monotone normal forms*, p.5 | a conflicting assignment `S` with `C(S) ≠ D(S)` |

What the project provides:

- an exact bitset term-set model;
- faithful and thesis-modified FK-A variants, and a faithful FK-B port with its
  single- and multiple-assignment variants;
- FK-B run as a *generator* of `Tr(D)`, not only as a decision procedure;
- FK-A's recursion memoised, so its subproblem *DAG* is measurable separately
  from its tree — and reachable on instances whose tree is not;
- an independent transversal oracle and checkable conflicting assignments;
- structured, provenance-bearing JSON instances;
- deterministic JSON, DOT, and self-contained interactive HTML results;
- a pytest suite tied to the published recursion trees and to the MATLAB
  reference's own recorded test vectors; and
- an optional SageMath backend for independent group and graph checks.

## Start here

From this directory, the source-tree tests require no installation:

```text
python -m pytest -m 'not slow'
```

That is the working invocation: 457 passed, 13 skipped, 12 deselected in about
four minutes. A bare `python -m pytest` also runs the twelve `slow`-marked
exhaustive checks, one of which — `tk(2)`, enumerating a group of order 32768 —
takes 26 minutes on its own. Nothing is wrong when that happens; CI runs the full
set deliberately.

Install the command-line package into whichever interpreter you use (no project
virtual environment is required):

```text
python -m pip install -e ".[dev]"
```

Then use the same interpreter consistently. Under SageMath, substitute that
environment's Python and the Sage-backed checks come with it — see
[docs/sagemath.md](docs/sagemath.md):

```text
python -m fka env            what this interpreter can do
python -m fka list           the instance library
python -m fka show fano      one instance, with its baseline
python -m fka run fano       FK-A + annotation + HTML report
python -m fka verify         FK-A against the oracle

python -m fkb run fano       FK-B, same reports
python -m fkb verify         FK-B against the oracle
python -m fkb compare --all  FK-A vs FK-B vs the oracle
python -m fkb benchmark      both, on the scaling families
python -m fkb dualize --all  Tr(D) by repeated FK-B tests
```

`run` writes a portable HTML explorer and machine-readable JSON to `results/`.
Open the HTML directly; it has no network, font, JavaScript, or image dependency.

## Thesis source and Lean proofs

The thesis' LaTeX source was rebuilt from the deposited PDF in October 2026, and every statement
it makes on its own authority was checked in Lean 4 against Mathlib.

| Path | Contents |
| --- | --- |
| [thesis/2024/](thesis/2024) | the recovered source, as deposited, with its compiled PDF |
| [thesis/revised/](thesis/revised) | the revised edition: corrections applied, each statement tagged with its Lean proof |
| [thesis/CLAIMS.md](thesis/CLAIMS.md) | every statement, its status and its Lean proof |
| [lean/](lean) | the Lean library (445 theorems); `cd lean && lake exe cache get && lake build` |
| [docs/openai-math-connections.md](docs/openai-math-connections.md) | where the [`openai/math`](https://github.com/openai/math) results meet the thesis, with Lean bridges |
| [docs/research-2026-10.md](docs/research-2026-10.md) | results beyond the thesis: the Witt design, self-transversal hypergraphs, `ε(n)`, FK-A's subproblems, substitution |
| [docs/applications.md](docs/applications.md) | where dualization is used, grouped by what `H` and `Tr(H)` are, with a shortlist for this repository |

Most statements hold as printed. Those that do not are corrected, each with a counterexample to
the printed form where one exists: among them Corollary 2.3.1 (the inequality is reversed), Lemma
3.3.3 (false), Lemma 3.3.1 (needs the Sperner hypothesis), several §3.2 edge sets and Figure
3.3(b), the §4.2.3 recurrences and the transversal count of Definition 5.2.1. Observation 5.2.3's
case `n = 7`, open in 2024, was proved in October 2026; that work, and the research beyond the
thesis, is in [docs/research-2026-10.md](docs/research-2026-10.md).

## Research contracts

- **Duality is decided by the oracle, never by either algorithm.**
  `fka.transversal.is_dual_oracle` builds `Tr(dnf)` by Berge's method and
  compares. A passing FK-A or FK-B run alone is not a ground-truth proof.
- **The two algorithms must never disagree.** They decide the same predicate;
  `tests/test_fkb.py` asserts agreement with each other and with the oracle on
  the library, on randomised pairs, and under every variant and split rule.
- FK-A: `variant="faithful"` implements the FK96 base case; `variant="modified"`
  adds the thesis Section 5.1.1 `D_{1,k}` / `D_{k,1}` rule.
  `split_rule="degree_sum"` reproduces the published tree numbering;
  `split_rule="frequency"` implements the normalized frequency quantity bounded
  in the thesis.
- FK-B: `variant="faithful"` is `FK_B.m`; `variant="multiple"` is `MFK_B.m` and
  returns every conflicting assignment a node can see, leaving the tree
  unchanged. `split_rule="most_frequent"` is `Choose_SplitVar.m`;
  `split_rule="degree_sum"` matches FK-A so both can run on identical splits.
- Changes to preprocessing, split choice, base cases, or recursion order must
  preserve the published node counts and split sequences in
  `tests/test_thesis_reproduction.py` unless the research interpretation itself
  is deliberately revised.
- Corrections never overwrite a printed instance. `6a` and `8ver` record the
  corrected pairs and the evidence in their JSON notes; the as-printed forms,
  which are **not** transversal pairs, are preserved under
  [`_archive/20260804-verbatim-nontransversal/`](_archive/20260804-verbatim-nontransversal/)
  and are still re-derived by the test suite.
- Deviations from the MATLAB FK-B reference are corrections, are enumerated in
  `fkb.algorithm`'s docstring, and each has a test naming the case.

## Filing system

| Path | Purpose |
| --- | --- |
| `src/fka/` | FK-A, and the shared model: hypergraph, tree, analysis, report, instances |
| `src/fkb/` | FK-B, and dualization by repeated equivalence testing |
| `data/` | Every research input: `instances/`, the MATLAB `reference/` vectors, thesis `baselines/` |
| `tests/` | Unit, randomized, thesis-reproduction, MATLAB-conformance, output, and Sage checks |
| `results/` | Every run of both algorithms and every variant, plus the cross-algorithm report |
| `experiments/` | Explicit migration or one-off research programs |
| `docs/` | Architecture, the FK-A/FK-B findings, the hard-case search, Sage setup, and assessment notes |
| `thesis/` | The thesis source: the recovered 2024 edition, the revised edition, the claim register, figure tools |
| `lean/` | Lean 4 proofs of every thesis statement, its corrections, and the `openai/math` bridges |
| `Reading/` | Local-only third-party reference library; PDFs are not redistributed |
| `FK- B/` | Local-only third-party MATLAB FK-B reference snapshot |
| `Dedekind/` | Third-party MIT snapshot of Jäkel's `d(9)` computation — the size of the space both algorithms search |
| `_archive/` | Preserved superseded material, each with an archive note |

`src/fkb` imports the shared model from `src/fka`; the dependency is one-way and
is about layout, not about one algorithm needing the other. Do not add new
research logic to notebooks or `.txt` logs. Add a module or an explicit program,
store inputs as JSON, and make the claim executable as a test. See
[docs/architecture.md](docs/architecture.md) for the repeatable workflow and
[docs/fk-a-vs-fk-b.md](docs/fk-a-vs-fk-b.md) for what the comparison found.
[docs/hard-cases.md](docs/hard-cases.md) reports the search for new hard
instances and the one it found: the Witt design `S(4,5,11)`, in the library as
`w11`. [docs/hard-classes.md](docs/hard-classes.md) states what is settled about
the families that make FK-A's frequency bound tight, and which kind of symmetry
causes it. [docs/tree-vs-dag.md](docs/tree-vs-dag.md) separates FK-A's tree from
its distinct-subproblem count and finds that no published hard instance is hard
for the recursion itself. [docs/dedekind-atoms.md](docs/dedekind-atoms.md) classifies the
five-variable space from the four-variable one — 210 classes, not 7581 functions
— and assesses what the vendored `Dedekind/` snapshot can and cannot supply.

## SageMath

The package runs completely under CPython. Sage is an optional independent
backend, not an import-time dependency. Use the Binder badge above to run Sage
10.9 in a browser without installing it locally, and GitHub Actions runs the
same Sage-backed checks for every definitive revision.

Sage 10.9 is installed on the maintenance workstation, so the Sage-marked tests
execute rather than skip: 469 passed / 1 skipped under Sage's Python against
457 passed / 13 skipped under plain CPython, both with `-m 'not slow'`. The
difference is exactly the twelve `sage`-marked tests, which run in one case and
skip in the other.
[docs/sagemath.md](docs/sagemath.md) has the conda recipe and the two traps in
that build (no `sage -python`, no GAP `design` package).

## Authorship and license

The legacy implementation credits Saimon Islam and Lacey Liang and declares
GPL-3.0 licensing. The archived original notice is retained in
`_archive/20260804-legacy-code/LEGACY README.md`. The maintained package carries
the same `GPL-3.0-or-later` project metadata.

FK-B is an independent Python implementation written from the algorithm as
published and from the MATLAB reference's stated behaviour. The benchmark
families it is measured on are generated by `fka.instances`, not copied, and
the MATLAB snapshot in `FK- B/` stays local and git-ignored because its
redistribution terms are not established.

`Dedekind/` is the one vendored third party, kept because it carries an explicit
MIT licence permitting it. It is not covered by this project's GPL, nothing in
`src/` links against it, and its copyright notice travels with it — see
[Dedekind/README.md](Dedekind/README.md).

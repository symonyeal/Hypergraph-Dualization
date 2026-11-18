# Architecture and research workflow

## Why the maintained model is different

The legacy code represented every hyperedge as a mutable NumPy row and mixed
preprocessing, recursion, analysis, plotting, and notebook state. The maintained
model stores an edge as an integer bitset and a hypergraph as an immutable,
canonical tuple. Intersection, subset, deletion, and contraction are exact
integer operations, while incidence matrices remain a lossless interchange
format for SageMath and MATLAB.

## Layout

Two algorithms, one model. `src/fka` holds FK-A *and* everything neither
algorithm owns; `src/fkb` holds FK-B and imports that model. The dependency is
one-way and is about where files sit, not about one algorithm needing the other.

| Module | Owns |
| --- | --- |
| `fka/hypergraph.py`, `fka/irredundant.py` | the term-set model, its restrictions, and `Irredundant` |
| `fka/tree.py` | the serializable `Tree`, shared by both algorithms |
| `fka/transversal.py` | the independent Berge-method oracle |
| `fka/algorithm.py` | FK-A |
| `fka/memo.py` | the same recursion with a transposition table: FK-A's subproblem DAG, `delta`, against its tree `tau` |
| `fkb/algorithm.py` | FK-B |
| `fkb/dualize.py` | `Tr(D)` by repeated FK-B equivalence tests |
| `fka/automorphism.py` | the one automorphism search, for one term set or a pair |
| `fka/groups.py` | naming the group it finds, without SageMath |
| `fka/graphs.py`, `fka/properties.py` | the primal graph's class; conformality, alpha-acyclicity, read-once |
| `fka/selfdual.py` | self-dual families and primitivity |
| `fka/substitution.py`, `fka/bound.py` | monotone composition and the Chapter 2 frequency bound |
| `fka/analysis.py` | annotating completed nodes, memoizing repeated subproblems |
| `fka/backends/` | SageMath as an optional independent check, never an import-time dependency |
| `fka/report.py`, `fka/dot.py` | rendering a stored tree without changing it |
| `fka/instances.py` | the instance library, its generators, and its baselines |
| `fka/cli.py`, `fkb/cli.py` | the two entry points; neither holds research logic |

`fka/automorphism.py` is the module Chapter 3 is about: every recursion node is
annotated with the group of both its subhypergraphs, and that annotation is what
`docs/fk-a-vs-fk-b.md` and `docs/hard-classes.md` measure.

`fka/memo.py` is deliberately not a flag on `fka/algorithm.py`. The tree is the
published object and its node counts are fixed by
`tests/test_thesis_reproduction.py`; the DAG is a second measurement of the same
recursion, and it is defined on instances whose tree cannot be built. See
`docs/tree-vs-dag.md`.

Neither algorithm plots, computes automorphism groups, or touches the filesystem
while recursing. That separation is what makes a result reproducible and
reviewable months later, and it is what lets one visualiser serve both.

The code is written in one vocabulary, the monotone-Boolean register of the
FK-B reference. [dictionary.md](dictionary.md) maps it to the thesis' hypergraph
notation and is the only place that correspondence is recorded.

## Adding a research instance

1. Add one entry to `experiments/build_instances.py`. Use a short stable `id`,
   1-indexed edge lists, a precise source, and one of `verbatim`, `corrected`,
   or `derived` for provenance.
2. If a printed source needs repair, keep the as-printed form and state exactly
   what changed and why in the corrected file's `notes`.
3. Rerun `python experiments/build_instances.py`. It recomputes
   every `expected` block: duality from the oracle, `epsilon` as an exact
   fraction, and node counts for both algorithms and all four variants. Review
   every changed value; never accept the diff mechanically.
4. Run `python -m pytest`, then
   `python -m fka verify` and
   `python -m fkb verify`.
5. Generate the deliverables with `python -m fka run <id>` and `python -m fkb run <id>`.
6. Put a durable mathematical claim in a focused test and cite the thesis page
   or archived source log in its docstring.

Prefer a **generator** to a copied edge list when the instance has a stated
construction: `fka.instances` builds the Fano plane, the self-dualized Fano
benchmarks, and the matching and threshold families from their definitions, so
they are reproducible and carry no third-party redistribution question.

## Withdrawing an instance

An instance that turns out not to be a usable research input is moved to
`_archive/<YYYYMMDD>-<slug>/`, not deleted, and the directory gets a `README.md`
saying what and why. `fka.instances.load_archived` reads it back, so any finding
that depended on it stays executable; `list_ids` does not include it, so nothing
runs against it by accident. See
`_archive/20260804-verbatim-nontransversal/` for the worked example.

## Where things are

Two folders, and each holds all of its kind:

- **`data/`** — every research input. `instances/` is the `(cnf, dnf)` library,
  `reference/` the MATLAB FK-B authors' recorded test vectors, `baselines/` the
  node counts and split sequences printed in the thesis. Tests load these fixtures
  with `fka.instances.load_data` and also use literal and seeded cases. Superseded
  inputs move to `_archive/` and return through `load_archived`.
- **`results/`** holds research tables, certificates and other retained evidence.
  Generate per-run tree exports on demand with `python -m fka run` or `python -m fkb run`.

## Result formats

Three formats per run — compact JSON, a self-contained interactive HTML
explorer, and optional Graphviz DOT — named
`<instance>.<algorithm>.<variant>.<extension>`, so rerunning a configuration
replaces its own deterministic artifacts rather than creating numbered copies.

[`../results/README.md`](../results/README.md) is the single record of what each
format holds and how to generate it.

## Annotation cost

The automorphism search and the primal-graph classification are exponential in
the worst case, and `AnalysisOptions` caps both. The defaults are set from
measurement: on `sdfp-sd-2` the group search costs about 19 seconds per distinct
node against about a millisecond on every thesis instance, so a cap that admits
it makes a thousand-node tree unannotatable. Raise the caps deliberately, per
run, when a specific group is the question — not as a default.

## Validation layers

- Unit tests cover representation, Sperner reduction, tree serialization,
  groups, graph classes, properties, and output safety.
- Randomized tests compare both algorithms, all variants, and all
  split rules against the independent transversal oracle, and verify that every
  conflicting assignment holds at the root.
- Cross-algorithm tests assert FK-A and FK-B never disagree.
- Thesis tests lock published node counts and, where available, full split
  sequences.
- Conformance tests replay the MATLAB FK-B reference's own recorded test
  vectors from `Unit_Tests_Equivalency.m` and `Unit_tests_Check_Conditions.m`.
- Sage-marked tests cross-check automorphism orders and graph classes using
  Sage's independent implementations.

The Sage tests are expected to skip in ordinary CPython. A release or quoted
cross-backend result should also be run in the Sage environment described in
the SageMath section below.

## Interfaces

| Task | Implementation |
| --- | --- |
| Generate `Tr(H)` | `fka.transversal` |
| Decide whether `G = Tr(H)`, with a witness when false | `fka.algorithm.fk_a`, FK-B |
| Test self-transversality | `SelfTransversal.lean`, `Critical.lean` |
| Measure distinct subproblems and compare split rules | `fka.memo`, `experiments/split_rules.py` |

The applied supplier-panel study and its data are maintained in
[Resilient-Supplier-Panels](https://github.com/symonyeal/Resilient-Supplier-Panels).
Algorithmic correspondences and their proof status are recorded in research §8.

## SageMath

The package runs under CPython. Sage is an optional independent backend:
`--backend sage` requires an interpreter that can import `sage.all`, and no
module imports Sage at package load. `python -m fka env` reports availability.

### Checks

The Sage job in `.github/workflows/tests.yml` runs the full Python suite and
the two algorithm verifiers in the Sage 10.9 image pinned there. Check that
job for the revision being used; a historical local run establishes no current
Sage result. The Dockerfile uses the same image for browser notebooks.

With Sage's interpreter:

```text
sage -python -m pip install -e ".[dev]"
sage -python -m pytest -m sage
sage -python -m fka env
sage -python -m fka run fano --backend sage
sage -python experiments/hard_case_search.py 3 15
```

For a distribution that exposes Sage as a Python package rather than a `sage`
launcher, use that interpreter directly. The expected test signal is that
Sage-marked tests execute rather than skip. Sage is not required for the Lean build.

### Adapter contract

The adapter uses `IncidenceStructure` for automorphism groups and GAP-backed
group descriptions, and Sage graph predicates for independent structure checks.
It translates Sage's zero-based points to the thesis's one-based vertex labels;
a pure-Python regression test covers this translation without Sage installed.

The backend tests compare group orders and orbits and validate generators.
Group names need not match the Python catalogue: GAP's `StructureDescription`
can give different descriptions of isomorphic groups. Name assertions use the
Python backend; Sage comparisons test the mathematical group instead.

`fka.instances.witt_11` derives `S(4,5,11)` from the ternary Golay code without
Sage or GAP's optional `design` package.

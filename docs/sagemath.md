# SageMath compatibility

The package runs under CPython. Sage is an optional independent backend:
`--backend sage` requires an interpreter that can import `sage.all`, and no
module imports Sage at package load. `python -m fka env` reports availability.

## Checks

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

## Adapter contract

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

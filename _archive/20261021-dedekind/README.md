# 2026-10-21 — the Dedekind-number study

Archived because it is not part of the thesis question. It counted and classified the space of
monotone Boolean functions (Sperner hypergraphs) on `n ≤ 5` points; the thesis and the research
program study individual dual pairs and FK-A's recursion on them.

| File | Was |
| --- | --- |
| `Dedekind/` | Jäkel's MIT-licensed `d(9)` computation, vendored; its licence and notice travel with it |
| `dedekind.py` | `src/fka/dedekind.py`: `FDL(n)`, its `S_n`-classes, the lift from `n` to `n + 1` |
| `test_dedekind_atoms.py` | `tests/`: the 30 classes on four points, the 210 on five, Cauchy–Frobenius checks |
| `dedekind_atoms.py` | `experiments/`: wrote `results/dedekind-atoms.md` |
| `dedekind-atoms.md` | `docs/`: the derivation and an assessment of the vendored snapshot |
| `results-dedekind-atoms.md` | `results/dedekind-atoms.md` |

Paths inside these files refer to their old locations. To run them again, move `dedekind.py` back
to `src/fka/` and the test back to `tests/`.

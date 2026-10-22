# Experiments

Explicit, rerunnable research and migration programs that do not belong in the
importable library.

| Program | What it does |
| --- | --- |
| `build_instances.py` | Authors `data/instances/` and the withdrawn instances under `_archive/`. Every `expected` block is computed here, not typed. |
| `compare_algorithms.py` | Runs FK-A and FK-B on the same instances, annotates both trees, and writes `results/fk-a-vs-fk-b.{json,md}`. |
| `hard_case_search.py` | Enumerates every vertex-transitive self-transversal hypergraph on <= 15 points, over SageMath's transitive-group database, and measures both algorithms on each. Writes `results/hard-case-search.json`. Requires SageMath. |
| `hard_classes.py` | Places every instance against FK96's `c = eps * log2 N` window and classifies every node of both trees as read-once / transitive / primitive. Writes `results/hard-classes.{json,md}`. |
| `dag_size.py` | Measures FK-A's tree `tau` against its distinct-subproblem count `delta`, the closed forms along `matching` and `threshold`, and `delta` on words whose tree cannot be enumerated. Writes `results/dag-size.{json,md}`. `--deep` adds the length-3 words, minutes rather than seconds. |
| `prime_templates.py` | Searches for a template at the frequency threshold that is not read-once. Writes `results/prime-templates.md`. |
| `selfdual_orbits.py` | Hunts self-dual families beyond the Fano plane as unions of transitive-group orbits. Writes `results/selfdual-orbits.md`. |
| `witt_m11.py` | Re-derives the facts about the Witt design `S(4,5,11)` (Steiner property, self-transversality, `|Aut| = 7920`, the FK-A children's groups); `--lean` writes `lean/HypergraphDualization/WittData.lean`. |
| `steiner_selftr.py` | Checks `d(r² − t) ≥ r(r − 1)` on self-transversal hypergraphs, lists the Steiner parameters with no two disjoint blocks, and scans the intersecting ones for 2-colourings; `--lean` writes `SteinerData.lean`. See `docs/research-2026-10.md` §2. |
| `eps_search.py` | Decides `eps(n) < p/q` by CP-SAT on the truth table of a monotone function; the table `n = 3..8` at the thesis' bounds. See `docs/research-2026-10.md` §3. |
| `readonce_sim.py` | Modified FK-A on read-once pairs simulated on formulas: `tau`, `delta` for GK, TK and random formulas, validated against `fka.algorithm` and `fka.memo`. See `docs/research-2026-10.md` §4. |

Core correctness claims belong in `tests/`, and normal runs belong in the `fka`
and `fkb` CLIs. Avoid adding notebooks or unstructured output logs. Naming
follows [`../docs/dictionary.md`](../docs/dictionary.md), the same as `src/`.

Each program is deterministic and safe to rerun. Any that writes into
`data/instances/` prints what changed, so the diff can be reviewed rather than
accepted mechanically.

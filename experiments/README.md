# Experiments

Explicit, rerunnable research and migration programs that do not belong in the
importable library.

| Program | What it does |
| --- | --- |
| `build_instances.py` | Authors `data/instances/` and the withdrawn instances under `_archive/`. Every `expected` block is computed here, not typed. |
| `compare_algorithms.py` | Runs FK-A and FK-B on the same instances, annotates both trees, and writes `results/fk-a-vs-fk-b.{json,md}`. |
| `hard_case_search.py` | Searches single subset orbits through 15 points and pairs of orbits through 12, over SageMath's transitive-group database, and measures both algorithms on each. Writes `results/hard-case-search.json`. Requires SageMath. |
| `hard_classes.py` | Places every instance against FK96's `c = eps * log2 N` window and classifies every node of both trees as read-once / transitive / primitive. Writes `results/hard-classes.{json,md}`. |
| `dag_size.py` | Measures FK-A's tree `tau` against its distinct-subproblem count `delta`, the closed forms along `matching` and `threshold`, and `delta` on words whose tree cannot be enumerated. Writes `results/dag-size.{json,md}`. `--deep` adds the length-3 words, minutes rather than seconds. |
| `witt_m11.py` | Re-derives the facts about the Witt design `S(4,5,11)` (Steiner property, self-transversality, `|Aut| = 7920`, the FK-A children's groups); `--lean` writes `lean/HypergraphDualization/WittData.lean`. |
| `steiner_selftr.py` | Checks `d(r² − t) ≥ r(r − 1)` on self-transversal hypergraphs, lists the Steiner parameters with no two disjoint blocks, and scans the intersecting ones for 2-colourings; `--lean` writes `SteinerData.lean`. See `docs/research-2026-10.md` §2. |
| `eps_search.py` | Decides `eps(n) < p/q` by CP-SAT on the truth table of a monotone function; the table `n = 3..8` at the thesis' bounds. See `docs/research-2026-10.md` §3. |
| `readonce_formulas.py` | Prints an alternating formula for the Rust engine. `python experiments/readonce_formulas.py gk 4` prints GK `f₄`. |
| `readonce_dag/` | Rust: modified FK-A on live-variable sets, `n ≤ 512`, degree-sum, `--leftmost` or `--guarded` rule. `cargo build --release`, then `python experiments/readonce_formulas.py gk 4 \| readonce_dag/target/release/readonce_dag` prints `n N delta tau` (GK `f₄`: about five minutes). |
| `iso_classes.py` | Classifies exact, input-orbit and isomorphism repeats; writes `results/iso-memo.md`. `--deep --spill DIR` includes larger cases. |
| `block_probe.py` | Probes the top-block projections of reached read-once states, including joint reach; the durable summary is `results/block-probes.md`. |
| `symmetry_depth.py` | Exact ordered incidence-graph isomorphism classes by depth on Fano, Witt and complete(10,3), under three rules and both variants. `--write` regenerates `results/symmetry-depth.md`; research Theorem 4.22 and Observation 4.23. |
| `frequency_constant/` | Rust: every monotone function of `N ≤ 6` variables, the defect `log₂|C| + log₂|D| + 3 − 3/eps` of its dual pair, the least value and the pairs at 0. `cargo build --release`, then `frequency_constant 6` (about six seconds). See `docs/frequency-constant.md`. |
| `frequency_families.py` | The same defect on every read-once formula with ≤ `N` leaves (`closure 13`) and on random nested substitutions of prime templates (`compose 4000 SEED`). See `docs/frequency-constant.md`. |
| `alternating_dt.py` | Decision-tree size of GK and TK: the exact value of `P_F` at `(1 + i√3)/2` in `ℚ(i√3)` and the depth-first size (`rates 6`); for all leaf weights at once, the hull of achievable `(L₁, L₀)` by DP over isomorphism classes of restricted read-once formulas, against the depth-first hull: GK `f₁–f₃`, TK `S₁–S₂` (`least 3`, about ten seconds), every restriction class of `f₃` (`classes 3`, ten seconds), balanced formulas (`balanced`, about a minute), gates over balanced and restricted children (`gates 18 12`, about a minute); random read-once formulas (`random 1 400`); the rate bounds of the one-gate lemma (`theta`); decision-tree rank (`rank 9`, seconds). See `docs/complex-evaluation.md` §§3, 5. |
| `subcube_norm.py` | Subcube norm of GK and TK: exact integer check of the block measures behind the rate `0.41433` and of the upper recursion (`check`, under a second); partition LP and subcube norm reduced by symmetry (`lp "|&|"` for GK `f₂`, a second; `lp "|&|&"` for TK `S₂`, about three minutes; needs scipy). See `docs/complex-evaluation.md` §4. |
| `frequency_readonce.py` | The counterexample `T₆` to the base 8, checked on its explicit hypergraph with `fka.transversal` and FK-A (`check`, about two minutes); rates of symmetric templates (`templates 6 400`); the read-once theorem's split inequality on a grid (`split`) and on every read-once formula with ≤ `N` leaves (`closure 13`). See `docs/frequency-constant.md` §§4–5. |
| `split_rules.py` | `delta` under the degree-sum, leftmost and guarded rules on read-once pairs, copies of a gadget, uniform matroids and the library; writes `results/split-rules.md`. `--deep` adds GK `f₄` under the degree-sum rule. See `docs/research-2026-10.md` §4. |

`readonce_dag` accepts one nonempty read-once formula: gates are `&` or `|`,
and variable ids (optionally prefixed by `x`) are distinct integers in `0..511`.
Malformed formulas and conflicting or unknown flags fail before a spill queue is created.
Spill runs hold `.readonce.lock` until exit; an interrupted run may leave that lock and
pending levels, so preserve the directory and choose a fresh one. `block_probe.py` also
requires fresh output and log paths; a competing writer's file is preserved.

Core correctness claims belong in `tests/`, and normal runs belong in the `fka`
and `fkb` CLIs. Avoid adding notebooks or unstructured output logs. Naming
follows [`../docs/dictionary.md`](../docs/dictionary.md), the same as `src/`.

Each program is deterministic and safe to rerun. Any that writes into
`data/instances/` prints what changed, so the diff can be reviewed rather than
accepted mechanically.

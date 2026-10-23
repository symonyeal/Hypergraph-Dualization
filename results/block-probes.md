# Joint block projections and guarded departures

Evidence for research Observations 4.31 and 4.32 (Q1 and Q2 of `docs/research-prompt.md`).
Every count is computed by `experiments/readonce_dag` (Rust, `src/probe.rs`) through
`python experiments/block_probe.py FAMILY K MODE --out OUT.json`; the JSON files in
`block-probes/` hold each run's records and the SHA-256 of the Rust sources. Modified FK-A,
leaves numbered left to right.

## Joint projections (`--joint`, degree-sum rule)

At every reached nonconstant node of the larger instance, the probe records the pair
`(S∩a, S∩c)` for the first grandchild `a` of the root's first child and the first grandchild
`c` of its second child, each block's labels renumbered `0,…,m−1`. The targets `T` are the
nonempty supports the same rule reaches on the standalone block, orientation forgotten.
`a_states` and `c_states` count the projected supports, the empty support included.

| larger instance | block | `|T|` | `a_states` | `c_states` | joint pairs | targets hit in `a`, `c` | target pairs hit | missing | `δ` | file |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: | --- |
| GK `f₂` | `f₁` | 1 | 3 | 3 | 5 | 1, 1 | 1 / 1 | 0 | 8 | `gk2-joint.json` |
| GK `f₃` | `f₂` | 7 | 14 | 14 | 78 | 7, 7 | 21 / 49 | 28 | 369 | `gk3-joint.json` |
| TK `S₂` | `S₁` | 3 | 5 | 5 | 14 | 3, 3 | 5 / 9 | 4 | 34 | `tk2-joint.json` |
| TK `S₃` | `S₂` | 33 | 43 | 71 | 456 | 33, 33 | 259 / 1,089 | 830 | 4,139 | `tk3-joint.json` |

One missing target pair per run, in block labels:

| instance | `S∩a` | `S∩c` |
| --- | --- | --- |
| GK `f₃` | `{6,7}` | `{1,…,7}` |
| TK `S₂` | `{1,2,3}` | `{2,3}` |
| TK `S₃` | `{2,3,6,7}` | `{11,…,15}` |

A zero in the missing column is necessary for the embedding of Q1, not sufficient: the probe
forgets orientation and constants.

## Equal-size target pairs and GK `f₄` (Observation 4.39)

The probe also counts, for each support size, the target pairs of that size and how many occur
jointly (`equal_size` records). Files `gk2-equal.json`, `gk3-equal.json`, `tk2-equal.json`,
`tk3-equal.json` repeat the runs above with these records; `gk4-joint.json` is GK `f₄` (219 s).

| larger instance | targets | target pairs occurring | equal even sizes | equal odd sizes |
| --- | ---: | ---: | ---: | ---: |
| GK `f₂` | 1 | 1 / 1 | 1 / 1 | — |
| GK `f₃` | 7 | 21 / 49 | 4 / 4 | 0 / 3 |
| GK `f₄` | 348 | 64,155 / 121,104 | 2,573 / 3,102 | 0 / 2,786 |
| TK `S₂` | 3 | 5 / 9 | 2 / 2 | 0 / 1 |
| TK `S₃` | 33 | 259 / 1,089 | 19 / 50 | 0 / 41 |

GK `f₄`: blocks `a` and `c` take 1,904 and 1,893 projected supports (empty included) and 664,275
joint pairs; first missing target pair `{2,3}` against `{11,…,15, 18, 19, 28,…,31}`; first missing
equal-size pair `({5,6,7}, {5,6,7})`; `δ = 67,247,387`, as in Observation 4.4.

## Guarded rule on GK `f₅` (`--guard-trace --guarded`)

Distinct ordered nodes, counted by live-support size (`gk5-guard.json`, 1.96 s):

| quantity | count |
| --- | ---: |
| `δ` (ordered subproblems, constants included) | 124,876 |
| nonconstant nodes | 124,875 |
| split nodes | 124,874 |
| least live vertex fails the frequency test | 92,776 |
| degree-sum fallback used | 0 |
| chosen vertex differs from the degree-sum vertex | 124,520 |

First departure from the leftmost vertex, scanning support sizes downward: `|S| = 494`,
`S = {18,…,511}`; leftmost 18, chosen 20 (the least eligible vertex), degree sum 256.
`tests/test_readonce_probe.py::test_gk5_first_departure_certificate` re-derives this choice
from the pruned formula in Python.

## TK `S₄`, degree-sum rule, partial (Observation 4.41)

Stopped for memory on the work laptop (3.6 GB of spill, under 2 GB free) at live-support size 85
of 257 levels, so this is a running total, not the final count: `δ ≥ 330,149,945`. Against
`N₄ = 1,073,774,592`: `δ/N ≥ 0.307`, `log δ / log N ≥ 0.943`. Per-level trace in
`hd-rust/tk4-joint.log` (work folder, not in the repository); no `--out` JSON, since the run did
not reach level 0.

## Checks

`tests/test_readonce_probe.py` compares the joint counts on GK `f₂–f₃` and TK `S₂–S₃` under all
three rules, and the guarded per-level counts, with the Python formula engine
(`experiments/readonce_sim.py`).

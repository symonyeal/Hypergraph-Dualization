# Tree against DAG

Regenerate with `python experiments/dag_size.py` (`--deep` for the length-3 words).

`tau` = FK-A recursion-tree nodes; `delta` = distinct subproblems among them, the size of the DAG and the node count of `fka.memo.fk_a_memo`; `beta` = FK-B nodes. `c = eps * log2 N` places the pair against the FK96 window, as in `hard-classes.md`.

| instance | class | N | c | tau | beta | delta | tau/delta | delta/beta | delta/N | tau exp | delta exp |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `6a` | library | 8 | 1.50 | 11 | 3 | 8 | 1.4x | 2.67 | 1.000 | 1.15 | 1.00 |
| `6b` | library | 11 | 1.73 | 13 | 6 | 6 | 2.2x | 1.00 | 0.545 | 1.07 | 0.75 |
| `6c` | library | 10 | 1.66 | 5 | 1 | 4 | 1.2x | 4.00 | 0.400 | 0.70 | 0.60 |
| `6d` | library | 8 | 1.50 | 9 | 3 | 8 | 1.1x | 2.67 | 1.000 | 1.06 | 1.00 |
| `7ver` | library | 18 | 1.90 | 21 | 11 | 15 | 1.4x | 1.36 | 0.833 | 1.05 | 0.94 |
| `8ver` | library | 25 | 1.86 | 21 | 21 | 11 | 1.9x | 0.52 | 0.440 | 0.95 | 0.74 |
| `f2g2` | library | 12 | 1.79 | 25 | 7 | 8 | 3.1x | 1.14 | 0.667 | 1.29 | 0.84 |
| `fano` | library | 14 | 1.63 | 35 | 11 | 14 | 2.5x | 1.27 | 1.000 | 1.35 | 1.00 |
| `k3` | library | 6 | 1.72 | 3 | 3 | 2 | 1.5x | 0.67 | 0.333 | 0.61 | 0.39 |
| `sdfp-sd-1` | library | 30 | 2.62 | 75 | 37 | 16 | 4.7x | 0.43 | 0.533 | 1.27 | 0.81 |
| `sdfp-sd-2` | library | 128 | 5.47 | 1427 | 231 | 126 | 11.3x | 0.55 | 0.984 | 1.50 | 1.00 |
| `trivial-aut-1` | library | 66 | 3.63 | 41 | 33 | 34 | 1.2x | 1.03 | 0.515 | 0.89 | 0.84 |
| `w11` | library | 132 | 3.20 | 475 | 323 | 140 | 3.4x | 0.43 | 1.061 | 1.26 | 1.01 |
| `w11-sd-1` | library | 266 | 4.06 | 955 | 719 | 142 | 6.7x | 0.20 | 0.534 | 1.23 | 0.89 |
| `word-xy` | library | 48 | 1.40 | 577 | 193 | 28 | 20.6x | 0.14 | 0.583 | 1.64 | 0.86 |
| `word-yx` | library | 48 | 1.40 | 577 | 223 | 28 | 20.6x | 0.13 | 0.583 | 1.64 | 0.86 |
| `gk-f2` | alternating | 12 | 1.79 | 25 | 7 | 8 | 3.1x | 1.14 | 0.667 | 1.29 | 0.84 |
| `gk-f3` | alternating | 192 | 1.90 | 103377 | 1952 | 369 | 280.1x | 0.19 | 1.922 | 2.20 | 1.12 |
| `tk-s1` | alternating | 6 | 1.29 | 5 | 1 | 4 | 1.2x | 4.00 | 0.667 | 0.90 | 0.77 |
| `tk-s2` | alternating | 72 | 1.54 | 481 | 67 | 34 | 14.2x | 0.51 | 0.472 | 1.44 | 0.82 |
| `matching-8` | output | 20 | 2.16 | 29 | 15 | 8 | 3.6x | 0.53 | 0.400 | 1.12 | 0.69 |
| `matching-10` | output | 37 | 2.60 | 61 | 32 | 10 | 6.1x | 0.31 | 0.270 | 1.14 | 0.64 |
| `matching-12` | output | 70 | 3.06 | 125 | 65 | 12 | 10.4x | 0.18 | 0.171 | 1.14 | 0.58 |
| `matching-14` | output | 135 | 3.54 | 253 | 130 | 14 | 18.1x | 0.11 | 0.104 | 1.13 | 0.54 |
| `threshold-8` | shape | 21 | 3.51 | 7 | 18 | 7 | 1.0x | 0.39 | 0.333 | 0.64 | 0.64 |
| `threshold-10` | shape | 31 | 4.13 | 9 | 27 | 9 | 1.0x | 0.33 | 0.290 | 0.64 | 0.64 |
| `threshold-12` | shape | 43 | 4.65 | 11 | 37 | 11 | 1.0x | 0.30 | 0.256 | 0.64 | 0.64 |

## Closed forms

Both families admit an exact law, checked in `tests/test_memo.py`:

    matching(v):   tau = 2^(v/2+1) - 3      delta = v
    threshold(v):  tau = v - 1              delta = v - 1

| family | v | N | tau | delta |
| --- | ---: | ---: | ---: | ---: |
| `matching` | 8 | 20 | 29 | 8 |
| `matching` | 10 | 37 | 61 | 10 |
| `matching` | 12 | 70 | 125 | 12 |
| `matching` | 14 | 135 | 253 | 14 |
| `matching` | 16 | 264 | 509 | 16 |
| `matching` | 18 | 521 | 1021 | 18 |
| `matching` | 20 | 1034 | 2045 | 20 |
| `threshold` | 8 | 21 | 7 | 7 |
| `threshold` | 10 | 31 | 9 | 9 |
| `threshold` | 12 | 43 | 11 | 11 |
| `threshold` | 14 | 57 | 13 | 13 |
| `threshold` | 16 | 73 | 15 | 15 |
| `threshold` | 18 | 91 | 17 | 17 |
| `threshold` | 20 | 111 | 19 | 19 |

## Past the tree

`delta` on the alternating-tree words, including sizes where `tau` cannot be enumerated.

| instance | n | N | delta | delta/N | delta exp | depth |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `word-xy` | 16 | 48 | 28 | 0.583 | 0.86 | 8 |
| `word-yx` | 16 | 48 | 28 | 0.583 | 0.86 | 9 |
| `word-xxy` | 64 | 3072 | 2973 | 0.968 | 1.00 | 38 |
| `word-xyx` | 64 | 4608 | 3025 | 0.656 | 0.95 | 35 |
| `word-xyy` | 64 | 8448 | 4244 | 0.502 | 0.92 | 39 |
| `word-xxx` | 64 | 16512 | 4139 | 0.251 | 0.86 | 36 |
| `word-yyy` | 64 | 16512 | 4139 | 0.251 | 0.86 | 36 |

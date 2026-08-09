# Dedekind numbers — third-party reference implementation

`DedekindNumbersShiftFourMatrixMultiplication-main/` is a verbatim snapshot of
[Christian Jäkel's](https://github.com/cjaekel) implementation accompanying
*A computation of the ninth Dedekind Number*
([arXiv:2304.00895](https://arxiv.org/abs/2304.00895), 2023).

Unlike the MATLAB FK-B snapshot in `FK- B/`, this **is** committed: it carries an
explicit MIT licence (`LICENSE.txt`, Copyright (c) 2023 Christian Jäkel), which
permits redistribution provided the copyright notice travels with it. That file
is included unmodified and is the notice.

The snapshot is unmodified apart from collapsing the doubled
`…-main/…-main/` directory that GitHub's zip export produces. Nothing in `src/`,
the instance library, or either test suite reads it.

## Why it is in this repository

`d(n)`, the *n*-th Dedekind number, counts the antichains on an `n`-element set
— which is exactly the number of Sperner hypergraphs on `n` vertices, and so the
size of the space FK-A and FK-B search:

| n | d(n) | |
| ---: | ---: | --- |
| 4 | 168 | |
| 5 | 7,581 | |
| 6 | 7,828,354 | |
| 7 | 2,414,682,040,998 | |
| 8 | 56,130,437,228,687,557,907,788 | the thesis' largest instances live at n = 8 |
| 9 | 286386577668298411128469151667598498812366 | Jäkel 2023, and independently Van Hirtum et al. |

That is the honest scale of the dualization problem. It is also why the
instance library is a curated dozen rather than a sample: at `n = 8` there is no
meaningful notion of sampling the space, and every instance has to earn its
place by being a published or constructed object.

`Reading/Yusun Dedekind.pdf` is the companion reading. See
`docs/fk-a-vs-fk-b.md` for what the two algorithms actually do inside that
space.

## What the `data/` tables actually are, and what they are good for

The table above counts **labelled** functions. `d(4) = 168` and `d(5) = 7581`
count them without quotienting by anything, so most of what they count is
relabellings: up to `S_n` there are only 30 and 210 respectively (OEIS A003182).
That distinction is the subject of [`../docs/dedekind-atoms.md`](../docs/dedekind-atoms.md),
which classifies the five-variable space from the four-variable one and uses this
snapshot as a check. Two findings about the snapshot belong here.

**The `data/n/intervals.txt` files are a decomposition of `MBF(n+1)`.** Reading
the third column as a multiplicity and summing it:

| file | rows | multiplicities sum to | |
| --- | ---: | ---: | --- |
| `data/2/intervals.txt` | 6 | 20 | `= d(3)` |
| `data/3/intervals.txt` | 18 | 168 | `= d(4)` |
| `data/4/intervals.txt` | 134 | 7581 | `= d(5)` |

This is Shannon expansion on one variable: `f = f|x=0 v (x ^ f|x=1)` is a
bijection between `MBF(n+1)` and the comparable pairs of `MBF(n)`, so `d(n+1)`
is the number of intervals of `FDL(n)` counted with multiplicity. It is the
recursion the `d(9)` computation is built on, and `data/4/` is already a
decomposition of the five-variable space over four-variable data.

**The 134 rows are not a symmetry classification.** They are not the 210 classes
up to `S_5`, nor the 620 up to `S_4`, nor even isomorphism classes of the
intervals — colour refinement puts at least 227 of those in `FDL(4)`, and 134 is
below the bound. Jäkel's classes merge intervals with their order duals, which is
sound for him because all he needs from an interval is its length. At `n = 2` the
row `0 7 2` covers `[0,7]` and `[1,15]`: five elements each, anti-isomorphic, one
row. So the files can confirm a total but cannot answer a question about
relabelling.

Nothing here needs building. `docs/dedekind-atoms.md` reaches the classification
in under a second of pure Python, and this snapshot's role is unchanged — the
scale of the space, and an independent witness that 7581 is right.

## Licensing

This snapshot is MIT and is **not** covered by the repository's
`GPL-3.0-or-later`. The two licences coexist here because MIT is
GPL-compatible and the code is vendored, not linked: nothing in `src/` imports
or compiles against it.

Building it needs Eigen, Intel TBB, and CUDA for the GPU path — see its own
`README.md`. None of that is a dependency of this project.

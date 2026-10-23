# Isomorphism classes and cache visits

Computed 2026-10-23 with `python experiments/iso_memo.py 3 2`. All runs use modified
FK-A and the formula's original leaf labels. The cache traversal is depth-first,
visiting the right child first (`st.extend(kids(...))`, then `st.pop()`).

`delta` counts labelled subproblems, `d_shp = δ_iso` counts their ordered-pair
isomorphism classes, and `d_iso` counts classes visited when an isomorphic cache
hit stops expansion. The two class counts need not agree.

| Pair | Rule | n | N | delta | d_shp | d_iso |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| GK f1 | degree sum | 2 | 3 | 1 | 1 | 1 |
| GK f1 | guarded | 2 | 3 | 1 | 1 | 1 |
| GK f1 | leftmost | 2 | 3 | 1 | 1 | 1 |
| GK f2 | degree sum | 8 | 12 | 8 | 8 | 8 |
| GK f2 | guarded | 8 | 12 | 8 | 8 | 8 |
| GK f2 | leftmost | 8 | 12 | 8 | 8 | 8 |
| GK f3 | degree sum | 32 | 192 | 369 | 160 | 155 |
| GK f3 | guarded | 32 | 192 | 32 | 32 | 32 |
| GK f3 | leftmost | 32 | 192 | 32 | 32 | 32 |
| TK S1 | degree sum | 4 | 6 | 4 | 4 | 4 |
| TK S1 | guarded | 4 | 6 | 4 | 4 | 4 |
| TK S1 | leftmost | 4 | 6 | 4 | 4 | 4 |
| TK S2 | degree sum | 16 | 72 | 34 | 29 | 29 |
| TK S2 | guarded | 16 | 72 | 16 | 16 | 16 |
| TK S2 | leftmost | 16 | 72 | 16 | 16 | 16 |

For GK f3 under degree sum, the repetition factor `δ/δ_iso` is `369/160 = 2.30625`.
Using `369/155` instead includes the classes avoided by the cache's choice of
representatives. Thus the earlier GK f4 measurement `67,247,387/734,303 ≈ 92`
is a cache-count ratio, an upper bound on `δ/δ_iso`; `δ_iso` at f4 was not measured
because the exact traversal exceeded the script's 500,000-node cap. The exact
value of `δ_iso/N` at f4 and its asymptotic growth do not follow from that ratio.

Validation: `python -m pytest tests/test_iso_memo.py` passes 18 tests. The 15
table rows agree with `fka.memo.fk_a_memo`. A separate oracle compares AHU shape
equality with colour-preserving graph isomorphism on 465 pairs drawn from 30
formulas (seed 0, at most five active vertices, fixed five-vertex ground set).
Both hypergraph sides have separate edge colours; isolated vertices are retained.
Constants and variable relabellings are included. These finite checks do not
prove the AHU characterization for every read-once formula.

The relabelling foundation is proved separately in Lean: `tr_eq_pimg_iff`,
`dual_pimg` and `fkAR_pimg`. They establish equality of verdicts, including for
redundant families and different split rules. They do not formalize a cache
implementation or prove a node-count identity.

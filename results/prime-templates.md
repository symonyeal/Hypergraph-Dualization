# Convergent templates at the FK-A frequency threshold

Historical bounded perfect-selector search (base revision `9e840c1`).
The retired search and full labelled table are preserved in the cleanup archive.
Regular equality templates are read-once by the cited Gurvich consequence in
research Theorems 3.4–3.5; this computation adds only the small-rank classification.

A template is r-uniform and regular on t = r^2 vertices with an
r-uniform regular dual; c_inf = max(log2|E|, log2|Tr E|)/(r-1).

## r = 2, t = 4

c_inf <= 2 needs |E| <= 4, and |E| = 2d.

| d | \|E\| | groups tried | sel(E) nonempty | closed + regular | DUAL | not read-once |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 2 | 2 | 2 | 2 | 0 |
| 2 | 4 | 1 | 1 | 1 | 1 | 0 |
| 3 | 6 | 0 | 0 | 0 | 0 | 0 |

## r = 3, t = 9

c_inf <= 2 needs |E| <= 16, and |E| = 3d.

| d | \|E\| | groups tried | sel(E) nonempty | closed + regular | DUAL | not read-once |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 90 | 90 | 90 | 90 | 0 |
| 2 | 6 | 8010 | 8010 | 360 | 0 | 0 |
| 3 | 9 | 309675 | 309675 | 0 | 0 | 0 |
| 4 | 12 | 5234220 | 5234220 | 0 | 0 | 0 |
| 5 | 15 | 41233122 | 41233122 | 0 | 0 | 0 |

## Templates found

| r | \|E\| | \|Tr(E)\| | c_inf | read-once | E |
| ---: | ---: | ---: | ---: | :-: | --- |
| 2 | 2 | 4 | 2.0000 | yes | `{{1,3},{2,4}}` |
| 2 | 4 | 2 | 2.0000 | yes | `{{1,3},{1,4},{2,3},{2,4}}` |
| 3 | 3 | 27 | 2.3774 | yes | `{{1,4,5},{2,6,7},{3,8,9}}` |

Every template enumerated here is read-once. The general exclusion
for regular equality templates follows from singleton cross intersections
and Gurvich's theorem; see docs/research-2026-10.md, Theorems 3.4-3.5.

_3072s_

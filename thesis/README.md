# Thesis

*Tracing the Effects of Symmetry in Hypergraphs On the Fredman–Khachiyan Algorithm*,
Saimon Y. Islam, MSc thesis, Simon Fraser University, 2024.

This is the single maintained, corrected source, reconstructed from the deposited
PDF and subsequently audited. [main.pdf](main.pdf) is the compiled text.
[CLAIMS.md](CLAIMS.md) records the scope, evidence and remaining open statements.
The corrected source is edited directly; there is no recovery or revision generator.

From this directory, build with:

```text
pdflatex -halt-on-error main
bibtex main
pdflatex -halt-on-error main
pdflatex -halt-on-error main
```

The SFU class is `sfuthesis.cls`, licensed under LPPL 1.3; see
[sfuthesis-LICENSE.txt](sfuthesis-LICENSE.txt). The bibliography is `references.bib`.
TikZ and forest drawings are checked-in TeX under `figures/`. The ten recursion-tree
PNGs are historical raster figures from the deposited PDF; they are illustrations,
rather than a source of algorithm baselines.

The superseded editions, deposited PDF, figure generators and revision scripts were
archived outside the repository during the November 2026 consolidation. Git history
also retains the previously committed material.

# Thesis source

*Tracing the Effects of Symmetry in Hypergraphs On the Fredman–Khachiyan Algorithm*, Saimon Y.
Islam, MSc thesis, Simon Fraser University, 2024.

**In plain terms.** The original LaTeX source of the thesis was lost. It was rebuilt from the
deposited PDF, and every result was then checked by a proof assistant (Lean). This folder holds
two editions: the recovered 2024 text exactly as deposited, and a revised edition in which every
error found by that check is corrected.

| Folder | Contents |
| --- | --- |
| `2024/` | The source recovered in October 2026 from the deposited PDF, reproducing the printed text, including its errors and undefined references. `deposited.pdf` is the thesis as deposited at SFU; `main.pdf` is the compiled recovery |
| `revised/` | The revised edition: corrections applied, each statement tagged with the Lean declaration that proves it, a preface listing the corrections and a proof-status appendix. `main.pdf` is the compiled edition |
| `CLAIMS.md` | The register: every statement, its status (proved, corrected, checked, computed, open) and its Lean proof |
| `tools/` | Generators and checks for the figures and the revisions |

## Build

```text
cd thesis/revised      (or thesis/2024)
pdflatex main
bibtex main
pdflatex main
pdflatex main
```

The class file `sfuthesis.cls` is the SFU Library Research Commons class (LPPL 1.3, licence in
`sfuthesis-LICENSE.txt`), included so that both editions build without a separate install.

## Figures

The hypergraph drawings are TikZ, generated from `figures/hypergraphs.json`; the automorphism
trees are `forest` code generated from `figures/autotrees.json` and the computed FK-A trees, so a
figure cannot drift from the algorithm it shows. The FK-A recursion-tree images (`*-fka.png`) are
the raster figures extracted from the deposited PDF.

From the repository root:

```text
python thesis/tools/hyperfig.py thesis/revised/figures/hypergraphs.json thesis/revised/figures
python thesis/tools/autotree.py thesis/revised/figures/autotrees.json thesis/revised/figures
```

`autotree.py` stops if a printed split vertex differs from the computed one. In the 2024 data the
§3.2 edge sets are as drawn in the deposited PDF; where a drawing was ambiguous, the transversal
panel was read from its partner.

## Revisions

The revised edition is produced from the 2024 source, not edited by hand:

```text
python thesis/tools/apply_revisions.py      chapter text: exact-span replacements, each matching once
python thesis/tools/revise_figures.py       figure data; checks every transversal drawing
python thesis/tools/check_tree_labels.py    tree labels against the computed groups and properties
```

`check_tree_labels.py revised` exits 0; `check_tree_labels.py 2024` lists the six labels the
revision corrects. `inventory.py` lists the numbered statements of an edition with their printed
numbers.

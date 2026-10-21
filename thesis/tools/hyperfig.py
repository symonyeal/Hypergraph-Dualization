"""Draw hypergraphs as TikZ: each edge is the rounded convex hull of its vertices.

Usage: python hyperfig.py <spec.json> <output dir>

The spec maps a figure id to ``{"pos": {vertex: [x, y]}, "edges": [[colour, [vertex, ...]], ...]}``.
A one-vertex edge is a disc, a two-vertex edge a capsule, a larger edge the convex hull
offset by the radius ``R``. Fills are drawn first with transparency, outlines second, so
every outline stays visible where edges overlap, as in the 2024 figures.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

R = 0.19  # hull radius, in picture units
UNIT = 0.95  # cm per picture unit

COLOURS = {
    "red": "red!70",
    "blue": "blue!65",
    "green": "green!70",
    "pink": "purple!45",
    "orange": "orange!70",
    "yellow": "yellow!80",
    "cyan": "cyan!60",
    "gray": "gray!80",
    "tan": "brown!80",
}


def hull(points: list[tuple[float, float]]) -> list[tuple[float, float]]:
    """Convex hull, counter-clockwise, collinear points dropped (monotone chain)."""
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower: list = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper: list = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def outline(points: list[tuple[float, float]]) -> str:
    """The closed TikZ path bounding the hull of ``points`` offset by ``R``."""
    h = hull(points)
    if len(h) == 1:
        x, y = h[0]
        return f"({x:.3f},{y:.3f}) circle[radius={R}]"
    k = len(h)
    normals = []
    for i in range(k):
        (x0, y0), (x1, y1) = h[i], h[(i + 1) % k]
        dx, dy = x1 - x0, y1 - y0
        ln = math.hypot(dx, dy)
        normals.append((dy / ln, -dx / ln))  # outward for a counter-clockwise polygon
    ang = [math.degrees(math.atan2(ny, nx)) for nx, ny in normals]
    parts = []
    for i in range(k):
        px, py = h[i]
        a0, a1 = ang[i - 1], ang[i]
        while a1 < a0:
            a1 += 360.0
        sx, sy = px + R * normals[i - 1][0], py + R * normals[i - 1][1]
        if i == 0:
            parts.append(f"({sx:.3f},{sy:.3f})")
        else:
            parts.append(f"-- ({sx:.3f},{sy:.3f})")
        parts.append(f"arc[start angle={a0:.2f}, end angle={a1:.2f}, radius={R}]")
    return " ".join(parts) + " -- cycle"


def label(v: str) -> str:
    """``v1`` -> ``$v_{1}$``; ``v2!`` (bold, as printed in Figure 3.4a) -> ``$\\mathbf{v_2}$``;
    a bare number stays a number (Figure 4.1b)."""
    bold = v.endswith("!")
    v = v.rstrip("!")
    if v.isdigit():
        return f"${v}$"
    body = f"{v[0]}_{{{v[1:]}}}"
    return f"$\\mathbf{{{body}}}$" if bold else f"${body}$"


def render(spec: dict) -> str:
    pos = {v.rstrip("!"): tuple(p) for v, p in spec["pos"].items()}
    names = {v.rstrip("!"): v for v in spec["pos"]}
    lines = [f"\\begin{{tikzpicture}}[x={UNIT}cm,y={UNIT}cm]"]
    paths = []
    for colour, members in spec["edges"]:
        paths.append((COLOURS[colour], outline([pos[m] for m in members])))
    for colour, path in paths:
        lines.append(f"  \\fill[{colour}, fill opacity=0.38] {path};")
    for _, path in paths:
        lines.append(f"  \\draw[black, line width=0.9pt] {path};")
    for v, (x, y) in pos.items():
        lines.append(f"  \\node[inner sep=0pt] at ({x:.3f},{y:.3f}) {{{label(names[v])}}};")
    lines.append("\\end{tikzpicture}")
    return "\n".join(lines) + "\n"


def main() -> None:
    spec_path, out = Path(sys.argv[1]), Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    specs = json.loads(spec_path.read_text(encoding="utf-8"))
    for name, spec in specs.items():
        if name.startswith("_"):
            continue
        (out / f"hg-{name}.tex").write_text(render(spec), encoding="utf-8")
        print(f"hg-{name}.tex")


if __name__ == "__main__":
    main()

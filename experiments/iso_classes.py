"""FK-A's cost split into exact repeats, symmetric repeats and distinct work (research prompt S0).

Usage (from the repository root, after `cargo build --release` in experiments/readonce_dag):
    python experiments/iso_classes.py [--deep] [--spill DIR]
Writes results/iso-memo.md from results/iso-memo.json. GK f4 under the degree-sum rule (19 minutes,
0.2 GB with --spill) and the instance library (about 10 minutes) are recomputed only with --deep,
else read from the JSON.

Legend
  tau      nodes of FK-A's recursion tree
  delta    distinct subproblems (label-exact memo)
  d_aut    Aut(f)-orbits among them (delta_Aut)
  d_shp    isomorphism classes among them (delta_iso)
  d_iso    nodes expanded when the memo is keyed by isomorphism class (iso_memo.py's iso())
  tau = (tau / delta) * (delta / d_shp) * d_shp, and d_iso <= d_shp <= d_aut <= delta <= tau
"""
import json
import subprocess
import sys
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
import readonce_sim as R  # noqa: E402
import split_rules as S  # noqa: E402
from fka.algorithm import _trivial_case, check_conditions, choose_split_var  # noqa: E402
from fka.hypergraph import phi_x_0, phi_x_1  # noqa: E402
from fka.irredundant import irredundant  # noqa: E402
from fka.instances import list_ids, load  # noqa: E402
from fka.memo import fk_a_memo  # noqa: E402

EXE = ROOT / "experiments" / "readonce_dag" / "target" / "release" / "readonce_dag"
EXE = EXE.with_suffix(".exe") if EXE.with_suffix(".exe").exists() else EXE
JS, MD = ROOT / "results" / "iso-memo.json", ROOT / "results" / "iso-memo.md"
RULES = {"degree sum": [], "guarded": ["--guarded"], "leftmost": ["--leftmost"]}
LIB = {"degree sum": "degree_sum", "guarded": "guarded", "leftmost": "leftmost"}
DEEP = {("GK f4", "degree sum")}
ISO_ONLY = {("TK S4", "degree sum"), ("alt3 d5", "degree sum")}
SKIP = {("GK f5", "degree sum"): "not run: `f4` already has 67,247,387 subproblems"}


def pair_graph(n, C, D, G0=()):
    """Ground vertices, then the edges of C, of D and of G0 as nodes in their own colours.
    Without G0, isomorphic iff the ordered pairs are relabellings of each other (the oracle of
    tests/test_iso_memo.py); with G0 = the input's edges, iff some element of Aut(G0) maps one pair
    to the other, since an isomorphism must map G0's edges onto themselves."""
    G = nx.Graph()
    G.add_nodes_from((("v", v), {"c": "v"}) for v in range(n))
    for side, H in (("C", C), ("D", D), ("G", G0)):
        for e in H:
            G.add_node((side, e), c=side)
            G.add_edges_from(((side, e), ("v", v)) for v in range(n) if e >> v & 1)
    return G


def classes(n, pairs, G0=()):
    """The number of isomorphism classes of pair_graph over `pairs`, bucketed by an invariant."""
    same = nx.algorithms.isomorphism.categorical_node_match("c", None)
    reps = {}
    for C, D in pairs:
        inv = (sorted(bin(e).count("1") for e in C), sorted(bin(e).count("1") for e in D))
        g = pair_graph(n, C, D, G0)
        hs = reps.setdefault(repr(inv), [])
        if not any(nx.is_isomorphic(g, h, node_match=same) for h in hs):
            hs.append(g)
    return sum(len(hs) for hs in reps.values())


def memo_dag(C0, D0, rule):
    """fka.memo.fk_a_memo's recursion, keeping each reduced pair's children: {key: children}."""
    kids = {}

    def go(Ci, Di):
        C, D = irredundant(Ci).reduced, irredundant(Di).reduced
        k = (C.edges, D.edges)
        if k in kids:
            return k, kids[k][0]
        kids[k] = (None, [])
        v = check_conditions(C, D) or _trivial_case(C, D, "modified")
        if v is not None:
            kids[k] = (v.dual, [])
            return k, v.dual
        x = choose_split_var(C, D, rule)
        assert x is not None
        a, v = go(phi_x_1(C, x), phi_x_0(D, x).vee(phi_x_1(D, x)))
        ch = [a]
        if v:                                 # the right child is entered iff the left is dual
            b, v = go(phi_x_1(D, x), phi_x_0(C, x).vee(phi_x_1(C, x)))
            ch.append(b)
        kids[k] = (v, ch)
        return k, v

    root, dual = go(C0, D0)
    assert dual
    return root, {k: c for k, (_, c) in kids.items()}


def library(rule):
    """(name, n, N, tau, delta, d_aut, d_shp) on the instance library under `rule`."""
    out = []
    for i in list_ids():
        inst = load(i)
        n, C0, D0 = inst.cnf.n, inst.cnf, inst.dnf
        root, ch = memo_dag(C0, D0, rule)
        assert len(ch) == fk_a_memo(C0, D0, split_rule=rule).nodes
        order, seen = [], set()

        def topo(k):
            if k not in seen:
                seen.add(k)
                for c in ch[k]:
                    topo(c)
                order.append(k)
        topo(root)
        paths = dict.fromkeys(ch, 0)
        paths[root] = 1
        for k in reversed(order):
            for c in ch[k]:
                paths[c] += paths[k]
        pairs = list(ch)
        out.append((i, n, len(C0) + len(D0), sum(paths.values()), len(ch),
                    classes(n, pairs, C0.edges), classes(n, pairs)))
    return out


def cases():
    out = [(f"GK f{k}", R.gk(k)) for k in range(1, 6)]
    out += [(f"TK S{k}", R.tk(k)) for k in range(1, 5)]
    out += [(f"alt3 d{d}", S.alt(d, 3, "|")) for d in (3, 4, 5)]
    return out


def run(f, *args):
    p = subprocess.run([str(EXE), *args], input=R.sexpr(f), capture_output=True, text=True, check=True)
    return p.stdout.split("\n")[0].split()


def row(f, rule, spill, iso_only=False):
    r = {}
    if not iso_only:
        n, N, delta, shp, aut, tau = run(f, "--classes", *RULES[rule], *spill)
        r.update(n=int(n), N=int(N), delta=int(delta), d_shp=int(shp), d_aut=int(aut),
                 tau=int(tau) if tau.isdigit() else tau)
    n, N, d_iso = run(f, "--iso", *RULES[rule])
    r.update(n=int(n), N=int(N), d_iso=int(d_iso))
    return r


def fmt(x):
    return "—" if x is None else f"{x:,}" if isinstance(x, int) else x


def ratio(a, b):
    if a is None or b is None:
        return "—"
    a = float(a.lstrip("~")) if isinstance(a, str) else a
    return f"{a / b:.3g}"


def main(deep, spill):
    data = json.loads(JS.read_text()) if JS.exists() else {}
    for name, f in cases():
        for rule in RULES:
            key = f"{name} | {rule}"
            if (name, rule) in SKIP or ((name, rule) in DEEP and not deep):
                continue
            print(key, flush=True)
            data[key] = row(f, rule, spill, (name, rule) in ISO_ONLY)
    if deep or "library" not in data:
        data["library"] = {rule: library(arg) for rule, arg in LIB.items()}
    JS.write_text(json.dumps(data, indent=1) + "\n")
    lines = ["# FK-A's work: exact repeats, symmetric repeats and distinct subproblems", "",
             "Generated by `python experiments/iso_classes.py --deep --spill DIR` (research prompt S0;",
             "research Observation 4.29). Modified FK-A, leaves numbered left to right, the cache",
             "traversal depth first with the right child first. Every count is computed.", "",
             "`τ` is the recursion tree, `δ` the distinct subproblems, `δ_Aut` their `Aut(f)`-orbits,",
             "`δ_iso` their isomorphism classes (ordered pairs, one relabelling for both sides), and",
             "`d_iso` the nodes expanded when the memo is keyed by isomorphism class (Lean `fkAI`, correct",
             "by `fkAI_correct`). Always `d_iso ≤ δ_iso ≤ δ_Aut ≤ δ ≤ τ` and",
             "`τ = (τ/δ)·(δ/δ_iso)·δ_iso`. The split rule's tie-break uses labels, so `d_iso` depends on",
             "the traversal and can be below `δ_iso`.", "",
             "## Read-once pairs", "",
             "From `experiments/readonce_dag` (Rust) on `(DNF f, DNF f^d)`. `alt3 dk` is the alternating",
             "tree of fan-in 3 and depth `k` with an OR root.", "",
             "| pair | rule | `n` | `N` | `τ` | `δ` | `δ_Aut` | `δ_iso` | `d_iso` | `τ/δ` | `δ/δ_iso` | `δ_iso/N` |",
             "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for name, _ in cases():
        for rule in RULES:
            key = f"{name} | {rule}"
            if (name, rule) in SKIP:
                lines.append(f"| {name} | {rule} | | | {SKIP[(name, rule)]} | | | | | | | |")
                continue
            g = data.get(key, {}).get
            lines.append(f"| {name} | {rule} | {g('n')} | {fmt(g('N'))} | {fmt(g('tau'))} | {fmt(g('delta'))} "
                         f"| {fmt(g('d_aut'))} | {fmt(g('d_shp'))} | {fmt(g('d_iso'))} "
                         f"| {ratio(g('tau'), g('delta'))} | {ratio(g('delta'), g('d_shp'))} "
                         f"| {ratio(g('d_shp'), g('N'))} |")
    lines += ["", "A dash means not computed. Under the degree-sum rule the label-exact DAGs of TK `S4` and",
              "`alt3 d5` were not completed on the work laptop: `--classes` on `alt3 d5`, stopped after 40",
              "minutes, had reached 104,621,934 subproblems with at least 97 live variables, in 84,290",
              "isomorphism classes (so far; `δ_iso ≥ d_iso = 266,227`). GK `f4` under the degree-sum rule took 19 minutes and 0.2 GB with",
              "`--spill`. `~` marks an f64 sum past `2^128 − 1`.", "",
              "## The instance library", "",
              "From the hypergraph engine (`fka.memo`'s recursion, keeping each subproblem's children).",
              "`δ_iso` and `δ_Aut` are counted with networkx isomorphism on coloured incidence graphs:",
              "vertices, the edges of each side, and for `δ_Aut` also the input's edges, which an",
              "isomorphism must map onto themselves.", "",
              "| pair | rule | `n` | `N` | `τ` | `δ` | `δ_Aut` | `δ_iso` | `τ/δ` | `δ/δ_iso` |",
              "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for rule, rows in data["library"].items():
        for i, n, N, tau, delta, aut, iso in rows:
            lines.append(f"| {i} | {rule} | {n} | {N:,} | {tau:,} | {delta:,} | {aut:,} | {iso:,} "
                         f"| {tau / delta:.3g} | {delta / iso:.3g} |")
    lines += ["", "## Validation", "",
              "`python -m pytest tests/test_iso_memo.py tests/test_readonce_dag.py`. The Rust `δ`, `δ_iso`",
              "and `d_iso` agree with `experiments/iso_memo.py` on GK `f1–f3` and TK `S1–S3` under all three",
              "rules, and `d_iso(GK f4) = 734,303` with that script's earlier run. `δ_Aut` agrees with an",
              "independent orbit canon (the sorted concatenation of the children's least images, valid for",
              "complete binary trees) on the same cases, and with orbits found by applying all `2^15`",
              "automorphisms on TK `S2`. `τ` is the sum of root-path counts over the DAG and agrees with the",
              "recursive count; the library's `τ` agrees with `fka.algorithm`'s trees. The graph count of",
              "the library section gives 34, 29, 29 on TK `S2` under the degree-sum rule, as the Rust tool",
              "does. `iso_memo.py`'s shape key is checked against colour-preserving graph isomorphism on",
              "465 pairs from 30 formulas (seed 0, at most five active vertices); these finite checks do not",
              "prove the shape characterisation for every read-once formula.", ""]
    MD.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    a = sys.argv[1:]
    sp = ["--spill", a[a.index("--spill") + 1]] if "--spill" in a else []
    main("--deep" in a, sp)

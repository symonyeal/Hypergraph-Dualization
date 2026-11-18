"""Check Rust counts against the recorded computations and the hypergraph engine."""
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from fka.algorithm import fk_a
from fka.hypergraph import Hypergraph
from fka.instances import gk as gk_hypergraph, tk as tk_hypergraph
from fka.memo import fk_a_memo
from fka.transversal import transversal

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
import readonce_formulas as formulas  # noqa: E402
from iso_classes import classes  # noqa: E402

EXE = ROOT / "experiments/readonce_dag/target/release/readonce_dag"
EXE = EXE.with_suffix(".exe") if EXE.with_suffix(".exe").exists() else EXE
pytestmark = pytest.mark.skipif(not EXE.exists() and not os.environ.get("CI"), reason="readonce_dag not built")
FLAG = {"degree_sum": [], "leftmost": ["--leftmost"], "guarded": ["--guarded"]}
CASES = [("gk", 1), ("gk", 2), ("gk", 3), ("tk", 1), ("tk", 2), ("tk", 3)]


def rust(f, *args):
    return subprocess.run([str(EXE), *args], input=f, capture_output=True, text=True,
                          check=True, timeout=30).stdout.splitlines()


@pytest.mark.parametrize("rule", FLAG)
@pytest.mark.parametrize("family,k", CASES)
def test_counts_match_retained_evidence(rule, family, k):
    data = json.loads((ROOT / "results/iso-memo.json").read_text(encoding="utf-8"))
    name = f"GK f{k}" if family == "gk" else f"TK S{k}"
    expected = data[f"{name} | {rule.replace('_', ' ')}"]
    f = getattr(formulas, family)(k)
    n, N, delta, d_shp, d_aut, tau = map(int, rust(f, "--classes", *FLAG[rule])[0].split())
    assert (n, N, delta, d_shp, d_aut, tau) == tuple(
        expected[key] for key in ("n", "N", "delta", "d_shp", "d_aut", "tau")
    )
    assert rust(f, "--iso", *FLAG[rule]) == [f"{n} {N} {expected['d_iso']}"]
    assert rust(f, "--delta-only", *FLAG[rule]) == [f"{n} {N} {delta} 0"]
    assert rust(f, *FLAG[rule]) == [f"{n} {N} {delta} {tau}"]


@pytest.mark.parametrize("rule", FLAG)
@pytest.mark.parametrize("family,k", CASES[:-1])
def test_small_counts_match_hypergraph_engine(rule, family, k):
    C = (gk_hypergraph if family == "gk" else tk_hypergraph)(k)
    D = transversal(C)
    tree = fk_a(C, D, variant="modified", split_rule=rule)
    memo = fk_a_memo(C, D, split_rule=rule)
    assert tree.dual and memo.dual
    f = getattr(formulas, family)(k)
    assert rust(f, *FLAG[rule]) == [f"{C.n} {len(C) + len(D)} {memo.nodes} {len(tree)}"]


@pytest.mark.parametrize("rule", FLAG)
@pytest.mark.parametrize("f,n,edges", [
    ("(| (& 0 1) (& 2 (| 3 4)))", 5, [(0, 1), (2, 3), (2, 4)]),
    ("(& (| 0 1 2) (| 3 4))", 5, [(0, 3), (0, 4), (1, 3), (1, 4), (2, 3), (2, 4)]),
    ("(| ( & 0 4 6) (& 1 7) (& 2 3))", 8, [(0, 4, 6), (1, 7), (2, 3)]),
])
def test_shape_and_orbit_counts_match_incidence_graph(rule, f, n, edges):
    C = Hypergraph.from_sets(n, edges)
    D = transversal(C)
    tree = fk_a(C, D, variant="modified", split_rule=rule)
    assert tree.dual
    pairs = {(node.cnf.edges, node.dnf.edges) for node in tree}
    actual = tuple(map(int, rust(f, "--classes", *FLAG[rule])[0].split()))
    assert actual == (C.support().bit_count(), len(C) + len(D), len(pairs),
                      classes(n, pairs), classes(n, pairs, C.edges), len(tree))

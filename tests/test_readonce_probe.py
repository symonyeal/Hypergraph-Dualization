"""Compare Rust projections and guard traces against retained bounded results."""
import json

import pytest

from test_readonce_dag import ROOT, formulas, pytestmark as pytestmark, rust

EVIDENCE = ROOT / "results/block-probes"
JOINT_KEYS = ("targets", "a_states", "c_states", "pairs", "a_hits", "c_hits", "pair_hits", "pair_missing")
LEVEL_KEYS = ("nodes", "splits", "leftmost_ineligible", "fallbacks", "diff_degree_sum")


def probe(f, *args):
    return [json.loads(line) for line in rust(f, *args)]


@pytest.mark.parametrize("family,k", [("gk", 2), ("gk", 3), ("tk", 2), ("tk", 3)])
def test_joint_matches_retained_evidence(family, k):
    path = EVIDENCE / f"{family}{k}-equal.json"
    expected = json.loads(path.read_text(encoding="utf-8"))["records"]
    assert probe(getattr(formulas, family)(k), "--joint") == expected


@pytest.mark.parametrize("family,k,expected", [
    ("gk", 2, (1, 3, 3, 5, 1, 1, 1, 0)),
    ("gk", 3, (7, 9, 9, 17, 7, 7, 7, 42)),
    ("tk", 2, (3, 5, 5, 9, 3, 3, 3, 6)),
    ("tk", 3, (15, 17, 17, 33, 15, 15, 15, 210)),
])
@pytest.mark.parametrize("rule", ["--leftmost", "--guarded"])
def test_ordered_rules_match_projection_counts(family, k, expected, rule):
    rows = probe(getattr(formulas, family)(k), "--joint", rule)
    joint = next(row for row in rows if row["kind"] == "joint")
    assert tuple(joint[key] for key in JOINT_KEYS) == expected


@pytest.mark.parametrize("family,k,expected,delta", [
    ("gk", 3, (31, 30, 0, 0, 16), 32),
    ("gk", 4, (262, 261, 83, 0, 231), 263),
    ("tk", 3, (63, 62, 0, 0, 34), 64),
    ("tk", 4, (1351, 1350, 598, 0, 998), 1352),
])
def test_guard_traces(family, k, expected, delta):
    rows = probe(getattr(formulas, family)(k), "--guard-trace", "--guarded")
    levels = [row for row in rows if row["kind"] == "level"]
    assert tuple(sum(row[key] for row in levels) for key in LEVEL_KEYS) == expected
    assert rows[-1]["delta"] == delta


def test_joint_crosses_mask_word():
    # TK S3 shifted across a 64-bit boundary exercises normalized block coordinates.
    assert probe(formulas.tk(3, 61), "--joint") == probe(formulas.tk(3), "--joint")


def test_gk5_first_departure_certificate():
    data = json.loads((EVIDENCE / "gk5-guard.json").read_text(encoding="utf-8"))
    assert probe(formulas.gk(5), "--guard-trace", "--guarded") == data["records"]

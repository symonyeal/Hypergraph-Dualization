"""Profile pairs are checked from an independent direct formula traversal."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))

import block_profiles as bp
from test_readonce_probe import probe


def test_same_profile_pairs_against_direct_reach():
    fm = bp.fm
    f, g = fm.gk(2), fm.gk(3)
    r = bp.cp.reach(g, 50000)
    joint = {(fm.MASK[h] & 255, fm.MASK[h] >> 16 & 255) for h in r}
    targets = {fm.MASK[h] for h in bp.cp.reach(f, 50000)
               if fm.MASK[h] and not bp.cp.half(fm.MASK[h])}
    pairs = {(a, c) for a in targets for c in targets
             if bp.profile(bp.prune(f, a)) == bp.profile(bp.prune(f, c))}
    actual = bp.analyze(dict(family="gk", k=3, records=probe(g, "--joint")))
    assert pairs and actual["pairs"] == len(pairs)
    assert actual["hits"] == len(pairs & joint)
    assert actual["missing"] == len(pairs - joint)
    assert actual["targets"] == len(targets)
    shape = {s: bp.cp.im.shp(bp.prune(f, s)) for s in targets}
    assert actual["shape_pairs"] == len({(shape[a], shape[c]) for a, c in pairs})
    assert actual["shape_hits"] == len({(shape[a], shape[c]) for a, c in pairs & joint})


def test_primal_orientation_is_recovered_from_support():
    fm = bp.fm
    f = fm.gk(2)
    s = 252
    primal = bp.prune(f, s)
    reached = [h for h in bp.cp.reach(f, 50000) if fm.MASK[h] == s]
    assert reached and fm.T[primal] == 6 and fm.TD[primal] == 2
    assert any(fm.T[h] == 2 and fm.TD[h] == 6 for h in reached)


def test_saved_incidence_preserves_previous_complete_counts():
    path = ROOT / "results/block-probes"
    old = json.loads((path / "gk4-joint.json").read_text(encoding="utf-8"))
    new = json.loads((path / "gk4-incidence.json").read_text(encoding="utf-8"))
    assert [r for r in new["records"] if r["kind"] != "target_incidence"] == old["records"]
    assert new["records"][-1] == dict(kind="summary", n=128, delta=67247387)


def test_even_shape_diagonal_counterexample():
    path = ROOT / "results/block-probes"
    data = json.loads((path / "gk4-incidence.json").read_text(encoding="utf-8"))
    q = next(r for r in data["records"] if r["kind"] == "target_incidence")
    f = bp.fm.gk(3)
    targets = [sum(1 << x for x in xs) for xs in q["targets"]]
    expected = {bp.fm.MASK[g] for g in bp.cp.reach(f, 50000) if bp.fm.MASK[g]}
    assert len(targets) == len(set(targets)) == 348 and set(targets) == expected
    assert len(q["rows"]) == 348 and all(len(row) == 348 for row in q["rows"])
    assert all(set(row) <= {"0", "1"} for row in q["rows"])
    assert sum(row.count("1") for row in q["rows"]) == 64155
    witness = [10, 11, 12, 13, 14, 15, 20, 21, 22, 23, 30, 31]
    s = sum(1 << x for x in witness)
    assert s in {bp.fm.MASK[g] for g in bp.cp.reach(f, 50000)}
    shape = bp.cp.im.shp(bp.prune(f, s))
    fiber = [i for i, xs in enumerate(q["targets"])
             if bp.cp.im.shp(bp.prune(f, sum(1 << x for x in xs))) == shape]
    assert len(fiber) == 2
    assert all(q["rows"][i][j] == "0" for i in fiber for j in fiber)
    out = bp.analyze(data)
    assert (out["pairs"], out["hits"], out["shape_pairs"], out["shape_hits"]) == (696, 578, 71, 66)

"""Test joint reachability of whole-pair targets with identical degree profiles.

Input: block_probe.py's JSON including target_incidence. Profile is (term count,
clause count, multiset of paired term/clause degrees) in original block orientation.
This is a necessary-condition probe; no positive result proves an embedding.
"""
import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path

import cherry_probe as cp

fm = cp.fm


def prune(f, s):
    if not fm.MASK[f] & s:
        return None
    if fm.OP[f] == "v":
        return f
    return fm.mk(fm.OP[f], [h for g in fm.KIDS[f] if (h := prune(g, s)) is not None])


def profile(g):
    c, d = fm.degrees(g, False), fm.degrees(g, True)
    return fm.T[g], fm.TD[g], tuple(sorted((c[x], d[x]) for x in c))


def analyze(data):
    q = next(q for q in data["records"] if q["kind"] == "target_incidence")
    k = data["k"] - 1
    f = getattr(fm, data["family"])(k)
    groups = defaultdict(list)
    for i, xs in enumerate(q["targets"]):
        s = sum(1 << x for x in xs)
        if s and not cp.half(s):
            groups[profile(prune(f, s))].append(i)
    pairs, hits, first, rows = 0, 0, None, []
    shape_pairs, shape_hits, first_shape = 0, 0, None
    for p, ids in groups.items():
        h = sum(q["rows"][i][j] == "1" for i in ids for j in ids)
        shapes = {i: cp.im.shp(prune(f, sum(1 << x for x in q["targets"][i]))) for i in ids}
        potential = {(shapes[i], shapes[j]) for i in ids for j in ids}
        observed = {(shapes[i], shapes[j]) for i in ids for j in ids if q["rows"][i][j] == "1"}
        if potential - observed and first_shape is None:
            a, c = min(potential - observed)
            i = next(i for i in ids if shapes[i] == a)
            j = next(j for j in ids if shapes[j] == c)
            first_shape = dict(a=q["targets"][i], c=q["targets"][j], terms=p[0], clauses=p[1],
                               degree_points=p[2])
        shape_pairs += len(potential)
        shape_hits += len(observed)
        rows.append(dict(terms=p[0], clauses=p[1], degree_points=p[2],
                         targets=len(ids), shapes=len(set(shapes.values())), pairs=len(ids)**2,
                         hits=h, shape_pairs=len(potential), shape_hits=len(observed)))
        pairs += len(ids)**2
        hits += h
        if h < len(ids)**2 and first is None:
            i, j = next((i, j) for i in ids for j in ids if q["rows"][i][j] == "0")
            first = dict(a=q["targets"][i], c=q["targets"][j], terms=p[0], clauses=p[1],
                         degree_points=p[2])
    return dict(family=data["family"], larger_k=data["k"], block_k=k,
                profile="original-orientation edge counts and full degree-point multiset",
                target_filter="nonempty unions of whole original bottom pairs",
                targets=sum(map(len, groups.values())), profiles=len(groups),
                pairs=pairs, hits=hits, missing=pairs-hits, first_missing=first,
                shape_pairs=shape_pairs, shape_hits=shape_hits,
                shape_missing=shape_pairs-shape_hits, first_missing_shape_pair=first_shape, groups=rows)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", type=Path)
    p.add_argument("--out", type=Path)
    args = p.parse_args()
    data = analyze(json.loads(args.input.read_text(encoding="utf-8")))
    data["input_sha256"] = hashlib.sha256(args.input.read_bytes()).hexdigest()
    data["source_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in map(Path, [__file__, cp.__file__, fm.__file__, cp.im.__file__])}
    text = json.dumps(data, indent=2) + "\n"
    if args.out:
        args.out.write_text(text, encoding="utf-8", newline="\n")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()

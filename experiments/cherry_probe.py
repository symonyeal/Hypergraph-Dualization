"""Bottom-pair completion and open-block weighted pivots on GK.

Run: python experiments/cherry_probe.py --out results/cherry-probes.json
All enumerations retain ordered states and original labels. `hull` suppresses local
singleton-edge stops: a block embedded in a larger formula need not stop there.
Its positive weights are independent at every step; this is a relaxation of FK-A.
"""
import argparse
import hashlib
import json
import time
from collections import Counter
from fractions import Fraction
from functools import cache
from math import prod
from pathlib import Path

import iso_memo as im
import readonce_sim as fm


def half(s):
    """Original bottom pairs with exactly one live leaf."""
    return [i for i in range((s.bit_length() + 1) // 2)
            if (s >> (2 * i)) & 3 in (1, 2)]


def reach(f, cap):
    seen, pending = set(), [f]
    while pending:
        g = pending.pop()
        if g in seen:
            continue
        seen.add(g)
        if len(seen) > cap:
            raise RuntimeError(f"exact traversal exceeded {cap} states")
        if not im.leaf(g):
            pending.extend(im.kids(g, "degree_sum"))
    return seen


def skeleton(f):
    if fm.OP[f] == "|" and fm.MASK[f].bit_count() == 2:
        xs = sorted(fm.MASK[k].bit_length() - 1 for k in fm.KIDS[f])
        assert len(xs) == 2 and xs == [2 * (xs[0] // 2), 2 * (xs[0] // 2) + 1]
        return fm.var(xs[0] // 2)
    return fm.mk(fm.OP[f], [skeleton(k) for k in fm.KIDS[f]])


@cache
def counts(h):
    """Term and clause counts with each macro atom representing OR₂."""
    if fm.OP[h] == "v":
        return 2, 1
    cs, ds = zip(*(counts(k) for k in fm.KIDS[h])) if fm.KIDS[h] else ((), ())
    return (sum(cs), prod(ds)) if fm.OP[h] == "|" else (prod(cs), sum(ds))


def degrees(h, dual=False, m=1, out=None):
    """External multipliers of a macro atom; each original leaf has local degree one."""
    out = {} if out is None else out
    if fm.OP[h] == "v":
        out[fm.MASK[h].bit_length() - 1] = m
        return out
    ts = [counts(k)[dual] for k in fm.KIDS[h]]
    for i, k in enumerate(fm.KIDS[h]):
        w = prod(ts[:i] + ts[i + 1:]) if (fm.OP[h] == "&") != dual else 1
        degrees(k, dual, m * w, out)
    return out


def expand(h):
    if fm.OP[h] == "v":
        i = fm.MASK[h].bit_length() - 1
        return fm.mk("|", [fm.var(2 * i), fm.var(2 * i + 1)])
    return fm.mk(fm.OP[h], [expand(k) for k in fm.KIDS[h]])


def macro(f, cap):
    seen, intermediates, pending = set(), set(), [(skeleton(f), False)]
    while pending:
        h, t = pending.pop()
        if (h, t) in seen:
            continue
        seen.add((h, t))
        if len(seen) > cap:
            raise RuntimeError(f"macro traversal exceeded {cap} states")
        c, d = counts(h)
        if c * d <= 1 or c == 1 or d == 1:
            continue
        a, b = degrees(h), degrees(h, True)
        i = min(a, key=lambda x: (-a[x] - b[x], x))
        g = expand(h)
        actual = fm.dual(g) if t else g
        assert fm.split_var(actual, "degree_sum") == 2 * i
        q = fm.restrict(g, 2 * i, False)
        assert not im.leaf(q)
        assert fm.split_var(q, "degree_sum") == 2 * i + 1
        intermediates.add(q)
        pending.extend([(fm.restrict(h, i, False), False), (fm.restrict(h, i, True), True)])
    complete = {fm.dual(expand(h)) if t else expand(h) for h, t in seen}
    return complete, intermediates


def candidates(g):
    """All pivots attainable at some λ>0, retaining least-label ties exactly.

    For each rival y, enforce (d[x]-d[y])λ >= c[y]-c[x], strictly if y<x.
    Rational endpoints include feasible singleton intervals, excluding λ=0.
    """
    c, d = fm.degrees(g, False), fm.degrees(g, True)
    out = []
    for x in sorted(c):
        lo, hi, lop, hip = Fraction(0), None, True, False
        for y in sorted(c):
            if x == y:
                continue
            a, b = c[y] - c[x], d[x] - d[y]
            if b == 0:
                if a > 0 or (a == 0 and y < x):
                    break
                continue
            z, strict = Fraction(a, b), y < x
            if b > 0:
                if z > lo:
                    lo, lop = z, strict
                elif z == lo:
                    lop |= strict
            else:
                if hi is None or z < hi:
                    hi, hip = z, strict
                elif z == hi:
                    hip |= strict
            if hi is not None and (hi < lo or (hi == lo and (lop or hip))):
                break
        else:
            out.append(x)
    assert out
    return out


def hull(f, forced, cap, seconds):
    start = time.perf_counter()
    seen, pending = set(), [f]
    while pending and len(seen) < cap and time.perf_counter() - start < seconds:
        g = pending.pop()
        if g in seen:
            continue
        seen.add(g)
        s = fm.MASK[g]
        if s.bit_count() <= 1:
            continue
        hs = half(s)
        xs = ([2 * hs[0] + 1 - ((s >> (2 * hs[0])) & 1)]
              if forced and hs else candidates(g))
        for x in xs:
            pending.extend([fm.restrict(g, x, False), fm.dual(fm.restrict(g, x, True))])
    supports = {fm.MASK[g] for g in seen}
    return dict(forced=forced, complete=not pending, ordered_states=len(seen),
                supports=len(supports), by_half=dict(sorted(Counter(len(half(s)) for s in supports).items())),
                pending=len(pending), seconds=time.perf_counter() - start)


def check(k, cap, seconds):
    f = fm.gk(k)
    seen = reach(f, cap)
    complete, intermediates = macro(f, cap)
    assert not complete & intermediates
    assert complete | intermediates == seen
    for g in seen:
        hs = half(fm.MASK[g])
        assert len(hs) <= 1
        if not im.leaf(g) and hs:
            assert fm.split_var(g, "degree_sum") // 2 == hs[0]
    return dict(k=k, n=fm.MASK[f].bit_count(), N=fm.T[f] + fm.TD[f], complete=True,
                delta=len(seen), delta_iso=len({im.shp(g) for g in seen}),
                macro=len(complete), intermediate=len(intermediates),
                macro_iso=len({im.shp(g) for g in complete}),
                intermediate_iso=len({im.shp(g) for g in intermediates}),
                hull=[hull(f, forced, cap, seconds) for forced in (False, True)])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cap", type=int, default=200000)
    p.add_argument("--seconds", type=float, default=60)
    p.add_argument("--out", type=Path)
    args = p.parse_args()
    sources = [Path(__file__), Path(fm.__file__), Path(im.__file__)]
    out = dict(seed=None, labels="original left-to-right", traversal="full labelled DFS, right child first",
               stop="modified singleton-edge tests; hull instead stops at constants/literals",
               cap=args.cap, seconds_cap_per_hull=args.seconds,
               sources={s.name: hashlib.sha256(s.read_bytes()).hexdigest() for s in sources},
               runs=[check(k, args.cap, args.seconds) for k in (1, 2, 3)])
    data = json.dumps(out, indent=2) + "\n"
    if args.out:
        args.out.write_text(data, encoding="utf-8", newline="\n")
    else:
        print(data, end="")


if __name__ == "__main__":
    main()

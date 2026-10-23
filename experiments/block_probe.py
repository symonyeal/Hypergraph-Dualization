"""Run the Rust joint-block or guarded-split probe with a timeout and JSON evidence.

Legend: a CLI arguments; f formula; p Rust subprocess; q output record;
exe compiled Rust executable; src Rust source hashes; dt elapsed seconds;
r evidence record; lv level records; out persistent JSON artifact.
Computation is in Rust; readonce_sim supplies the input formula only.
"""
import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

import readonce_sim as rs

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("family", choices=["gk", "tk"])
    p.add_argument("k", type=int)
    p.add_argument("mode", choices=["joint", "guard"])
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=60)
    p.add_argument("--spill", type=Path)
    a = p.parse_args()
    if a.out.exists():
        p.error("--out already exists; choose a new evidence filename")
    if not 1 <= a.k <= (5 if a.family == "gk" else 4):
        p.error("supported bounds: GK k<=5, TK k<=4 (n<=512)")
    if a.family == "gk" and a.k == 5 and a.mode == "joint":
        p.error("GK f5 degree-sum enumeration is outside the search bound")
    exe = ROOT / "experiments/readonce_dag/target/release/readonce_dag"
    if exe.with_suffix(".exe").exists():
        exe = exe.with_suffix(".exe")
    f = getattr(rs, a.family)(a.k)
    flags = ["--joint"] if a.mode == "joint" else ["--guard-trace", "--guarded"]
    if a.spill:
        a.spill.mkdir(parents=True, exist_ok=True)
        if any(a.spill.iterdir()):
            p.error("--spill must be empty; preserve previous run files")
        flags.extend(["--spill", str(a.spill)])
    src = {s.name: hashlib.sha256(s.read_bytes()).hexdigest()
           for s in (ROOT / "experiments/readonce_dag/src").glob("*.rs")}
    dt = time.perf_counter()
    q = subprocess.run([str(exe), *flags], input=rs.sexpr(f), capture_output=True,
                       text=True, timeout=a.seconds, check=True)
    dt = time.perf_counter() - dt
    rows = [json.loads(s) for s in q.stdout.splitlines()]
    assert rows and rows[-1]["kind"] == "summary"
    r = dict(family=a.family, k=a.k, mode=a.mode, seconds=dt, source_sha256=src,
             formula=rs.sexpr(f), records=rows)
    lv = [q for q in rows if q["kind"] == "level"]
    if lv:
        r["totals"] = {s: sum(q[s] for q in lv) for s in
                       ("nodes", "splits", "leftmost_ineligible", "fallbacks", "diff_degree_sum")}
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(r, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({s: v for s, v in r.items() if s not in ("records", "formula", "source_sha256")}))
    for q in rows:
        if q["kind"] not in ("level", "first_departure"):
            print(json.dumps(q))


if __name__ == "__main__":
    main()

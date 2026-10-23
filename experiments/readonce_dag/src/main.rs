//! Modified FK-A on the read-once pair (DNF f, DNF f^d), f a monotone read-once formula, n ≤ 512.
//!
//! Usage: readonce_dag [--delta-only | --classes [--spill DIR] | --iso] [--leftmost | --guarded]
//! < formula, formula an s-expression `(| (& 0 1) 2)`. `--leftmost` splits on the least live
//! variable (Hertel's order when leaves are numbered left to right); `--guarded` on the least
//! variable with |C| ≤ s·deg_C or |D| ≤ s·deg_D, s = ⌊log₂ N⌋ (FK96 Lemma 2.3.2; Lean `guardRule`),
//! else on FK-A's largest degree sum.
//! Prints `n N delta tau` (tau = 0 under `--delta-only`); under `--classes`,
//! `n N delta d_shp d_aut tau` and a line `blocks ...`; under `--iso`, `n N d_iso`.
//!
//! A node of FK-A on a dual pair is (h, t): h = f|ρ, t the last value ρ assigned, and the pair is
//! (DNF h, DNF h^d) for t = 0, swapped for t = 1. Both children of (h, t) are (h|x=0, 0) and
//! (h|x=1, 1) whatever t is (research §4, Theorem 4.7). A nonconstant restriction of a read-once
//! formula is determined by its relevant variables S (Lean `Fm.rminor_determined`), so a node is
//! the key (S, t) in place of a formula. Cost per node O(gates).
//!
//! Classes (Track S, research Observation 4.29).
//!   shp(S, t)  AHU form of h's formula pruned to S (dead leaves dropped, unary gates collapsed,
//!              equal operators merged), AND and OR swapped when t = 1. Equal shp iff the pairs are
//!              isomorphic, so d_shp = δ_iso (the AHU claim is iso_memo.py's, checked there).
//!   orb(S, t)  AHU form of the whole input tree with the leaves in S marked, and t. For an
//!              alternating input (GK, TK, `alt`) the tree's automorphisms are Aut(f), so equal orb
//!              iff one Aut(f) element maps one pair to the other: d_aut = δ_Aut.
//!   blocks     distinct S ∩ (leaves of b) over the δ live nodes, b the root's grandchildren, then
//!              its children.
//! `--classes` visits the δ nodes in decreasing |S| (a child has fewer live variables than its
//! parent), holding one level at a time; `--spill DIR` keeps the pending levels in files there.
//! All parents of a node are on higher levels, so its number of root paths is complete when its
//! level is reached, and τ is their sum over the DAG (printed `~x` from an f64 past 2^128 − 1).
//! `--iso` is iso_memo.py's iso(): depth first, the x = 1 child first, and a node whose shp was
//! seen is not expanded.
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::io::{BufWriter, Read, Write};
use std::path::PathBuf;

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct M<const W: usize>([u64; W]); // W 64-bit words: n ≤ 64·W

impl<const W: usize> M<W> {
    fn zero() -> Self { M([0; W]) }
    fn bit(x: usize) -> Self { let mut m = Self::zero(); m.0[x / 64] = 1 << (x % 64); m }
    fn or(self, o: Self) -> Self { let mut m = self; for i in 0..W { m.0[i] |= o.0[i]; } m }
    fn and(self, o: Self) -> Self { let mut m = self; for i in 0..W { m.0[i] &= o.0[i]; } m }
    fn andnot(self, o: Self) -> Self { let mut m = self; for i in 0..W { m.0[i] &= !o.0[i]; } m }
    fn any(self) -> bool { self.0.iter().any(|&w| w != 0) }
    fn ones(self) -> u32 { self.0.iter().map(|w| w.count_ones()).sum() }
    fn low(self) -> usize { for i in 0..W { if self.0[i] != 0 { return 64 * i + self.0[i].trailing_zeros() as usize; } } usize::MAX }
}

#[derive(Clone, Copy, PartialEq)]
enum Op { Var(usize), And, Or }

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum K<const W: usize> { Live(M<W>, bool), Const(bool) } // Const(c): C = {∅} iff c, else C = ∅

/// Gates in post-order: children before parents, the root last.
struct F<const W: usize> { op: Vec<Op>, kids: Vec<Vec<usize>>, par: Vec<usize>, mask: Vec<M<W>>, leaf: Vec<usize> }

#[derive(Default)]
struct Fx(u64);
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, b: &[u8]) { for &c in b { self.0 = (self.0.rotate_left(5) ^ c as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95); } }
    fn write_u64(&mut self, v: u64) { self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95); }
    fn write_u8(&mut self, v: u8) { self.write_u64(v as u64); }
    fn write_u32(&mut self, v: u32) { self.write_u64(v as u64); }
    fn write_usize(&mut self, v: usize) { self.write_u64(v as u64); }
    fn write_isize(&mut self, v: isize) { self.write_u64(v as u64); }
}
type Map<A, B> = HashMap<A, B, BuildHasherDefault<Fx>>;
type Set<A> = HashSet<A, BuildHasherDefault<Fx>>;

fn tokens(s: &str) -> Vec<String> {
    s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect()
}

fn parse<const W: usize>(tok: &[String]) -> F<W> {
    let mut f = F { op: vec![], kids: vec![], par: vec![], mask: vec![], leaf: vec![usize::MAX; 64 * W] };
    fn go<const W: usize>(t: &[String], i: &mut usize, f: &mut F<W>) -> usize {
        let g;
        if t[*i] == "(" {
            let op = if t[*i + 1] == "&" { Op::And } else { Op::Or };
            *i += 2;
            let mut ks = vec![];
            while t[*i] != ")" { ks.push(go(t, i, f)); }
            *i += 1;
            let m = ks.iter().fold(M::zero(), |a, &k| a.or(f.mask[k]));
            g = f.op.len();
            for &k in &ks { f.par[k] = g; }
            f.op.push(op); f.kids.push(ks); f.mask.push(m);
        } else {
            let x: usize = t[*i].trim_start_matches('x').parse().unwrap();
            *i += 1;
            g = f.op.len();
            f.op.push(Op::Var(x)); f.kids.push(vec![]); f.mask.push(M::bit(x));
            f.leaf[x] = g;
        }
        f.par.push(usize::MAX);
        g
    }
    let mut i = 0;
    go(tok, &mut i, &mut f);
    f
}

/// h|x=b for h with live set s: the live set, or the constant h becomes.
fn restrict<const W: usize>(f: &F<W>, s: M<W>, x: usize, b: bool) -> Result<M<W>, bool> {
    let (mut c, v) = (f.leaf[x], b);
    loop {
        let p = f.par[c];
        if p == usize::MAX { return Err(v); }
        let id = f.op[p] == Op::And;                       // identity of p: 1 for AND, 0 for OR
        if v == id && f.mask[p].and(s).andnot(f.mask[c]).any() { return Ok(s.andnot(f.mask[c])); }
        c = p;                                             // p is constant: v if absorbing, else id = v
    }
}

/// #terms of h_g and of h_g^d for every live gate g.
fn counts<const W: usize>(f: &F<W>, s: M<W>) -> (Vec<u128>, Vec<u128>) {
    let m = f.op.len();
    let (mut t, mut td) = (vec![0u128; m], vec![0u128; m]);
    for g in 0..m {
        if !f.mask[g].and(s).any() { continue; }
        let live = f.kids[g].iter().filter(|&&k| f.mask[k].and(s).any());
        (t[g], td[g]) = match f.op[g] {
            Op::Var(_) => (1, 1),
            Op::And => live.fold((1, 0), |(a, b), &k| (a * t[k], b + td[k])),
            Op::Or => live.fold((0, 1), |(a, b), &k| (a + t[k], b * td[k])),
        };
    }
    (t, td)
}

#[derive(Clone, Copy, PartialEq)]
enum Rule { DegreeSum, Leftmost, Guarded }

/// Children of a node with live set s, or None at a leaf of modified FK-A.
fn split<const W: usize>(f: &F<W>, s: M<W>, rule: Rule) -> Option<(K<W>, K<W>)> {
    let m = f.op.len();
    let (t, td) = counts(f, s);
    let (c, d) = (t[m - 1], td[m - 1]);
    if c * d <= 1 || c == 1 || d == 1 { return None; }
    // deg_C x and deg_D x by one top-down pass: at AND a child's term count multiplies by its
    // siblings' (C side), at OR by its siblings' clause count (dual side).
    let (mut mt, mut mtd) = (vec![0u128; m], vec![0u128; m]);
    (mt[m - 1], mtd[m - 1]) = (1, 1);
    let lg = 127 - (c + d).leading_zeros() as u128;      // s = ⌊log₂ N⌋
    let (mut best, mut guard) = ((0u128, usize::MAX), usize::MAX);
    for g in (0..m).rev() {
        if !f.mask[g].and(s).any() { continue; }
        match f.op[g] {
            Op::Var(x) => {
                let k = mt[g] + mtd[g];
                if k > best.0 || (k == best.0 && x < best.1) { best = (k, x); }
                if (c <= lg * mt[g] || d <= lg * mtd[g]) && x < guard { guard = x; }
            }
            op => for &k in &f.kids[g] {
                if !f.mask[k].and(s).any() { continue; }
                (mt[k], mtd[k]) = if op == Op::And { (mt[g] * (t[g] / t[k]), mtd[g]) }
                                  else { (mt[g], mtd[g] * (td[g] / td[k])) };
            },
        }
    }
    let x = match rule {
        Rule::Leftmost => s.low(),
        Rule::Guarded if guard != usize::MAX => guard,
        _ => best.1,
    };
    let key = |r: Result<M<W>, bool>, b: bool| match r {
        Err(v) => K::Const(v ^ b),
        Ok(s) => K::Live(s, b && s.ones() > 1),
    };
    Some((key(restrict(f, s, x, false), false), key(restrict(f, s, x, true), true)))
}

/// Hash-consed AHU nodes: id ↦ (code, sorted child ids). Codes: 0 variable, 1 AND, 2 OR,
/// 3 marked leaf, 4 unmarked leaf.
struct Tab { ix: Map<u64, u32>, nx: Vec<u32>, at: Vec<u32>, code: Vec<u8>, dat: Vec<u32> }

impl Tab {
    fn new() -> Tab { Tab { ix: Map::default(), nx: vec![], at: vec![0], code: vec![], dat: vec![] } }
    fn kids(&self, i: u32) -> &[u32] { &self.dat[self.at[i as usize] as usize..self.at[i as usize + 1] as usize] }
    fn get(&mut self, code: u8, ks: &[u32]) -> u32 {
        let mut h = Fx::default();
        h.write_u8(code);
        for &k in ks { h.write_u32(k); }
        let h = h.finish();
        let head = self.ix.get(&h).copied().unwrap_or(u32::MAX);
        let mut i = head;
        while i != u32::MAX {
            if self.code[i as usize] == code && self.kids(i) == ks { return i; }
            i = self.nx[i as usize];
        }
        let i = self.code.len() as u32;
        self.code.push(code); self.nx.push(head); self.dat.extend_from_slice(ks); self.at.push(self.dat.len() as u32);
        self.ix.insert(h, i);
        i
    }
}

/// shp and orb tables, with the forms of whole subtrees precomputed: full[g][t] (all of g's leaves
/// live), live[g] and dead[g] (all marked, none marked).
struct Cls { shp: Tab, orb: Tab, full: Vec<[u32; 2]>, live: Vec<u32>, dead: Vec<u32>, one: u32, zero: u32 }

fn code(op: Op, t: bool) -> u8 {
    match op { Op::Var(_) => 0, Op::And => if t { 2 } else { 1 }, Op::Or => if t { 1 } else { 2 } }
}

impl Cls {
    fn new<const W: usize>(f: &F<W>) -> Cls {
        let mut c = Cls { shp: Tab::new(), orb: Tab::new(), full: vec![], live: vec![], dead: vec![], one: 0, zero: 0 };
        let var = c.shp.get(0, &[]);
        c.one = c.shp.get(1, &[]);
        c.zero = c.shp.get(2, &[]);
        for g in 0..f.op.len() {
            let mut fl = [var; 2];
            if !matches!(f.op[g], Op::Var(_)) {
                for t in [false, true] {
                    let ks: Vec<u32> = f.kids[g].iter().map(|&k| c.full[k][t as usize]).collect();
                    fl[t as usize] = c.comb(code(f.op[g], t), ks);
                }
            }
            c.full.push(fl);
            let (lv, dd) = if matches!(f.op[g], Op::Var(_)) { (c.orb.get(3, &[]), c.orb.get(4, &[])) } else {
                let mut a: Vec<u32> = f.kids[g].iter().map(|&k| c.live[k]).collect();
                let mut b: Vec<u32> = f.kids[g].iter().map(|&k| c.dead[k]).collect();
                a.sort_unstable(); b.sort_unstable();
                (c.orb.get(code(f.op[g], false), &a), c.orb.get(code(f.op[g], false), &b))
            };
            c.live.push(lv); c.dead.push(dd);
        }
        c
    }

    /// A gate with code o over live children of shapes ks: collapse, merge, sort, intern.
    fn comb(&mut self, o: u8, ks: Vec<u32>) -> u32 {
        if ks.len() == 1 { return ks[0]; }
        let mut l = Vec::with_capacity(ks.len());
        for k in ks {
            if self.shp.code[k as usize] == o { l.extend_from_slice(self.shp.kids(k)); } else { l.push(k); }
        }
        l.sort_unstable();
        self.shp.get(o, &l)
    }

    /// shp of the subformula at g pruned to s (g must have a leaf in s).
    fn shp<const W: usize>(&mut self, f: &F<W>, g: usize, s: M<W>, t: bool) -> u32 {
        if !f.mask[g].andnot(s).any() { return self.full[g][t as usize]; }
        let ks: Vec<usize> = f.kids[g].iter().filter(|&&k| f.mask[k].and(s).any()).copied().collect();
        let ks: Vec<u32> = ks.into_iter().map(|k| self.shp(f, k, s, t)).collect();
        self.comb(code(f.op[g], t), ks)
    }

    /// orb of the subtree at g with the leaves in s marked.
    fn orb<const W: usize>(&mut self, f: &F<W>, g: usize, s: M<W>) -> u32 {
        let m = f.mask[g].and(s);
        if !m.any() { return self.dead[g]; }
        if m == f.mask[g] { return self.live[g]; }
        let mut ks: Vec<u32> = f.kids[g].clone().into_iter().map(|k| self.orb(f, k, s)).collect();
        ks.sort_unstable();
        self.orb.get(code(f.op[g], false), &ks)
    }

    fn of_key<const W: usize>(&mut self, f: &F<W>, k: K<W>) -> u32 {
        match k { K::Const(v) => if v { self.one } else { self.zero }, K::Live(s, t) => self.shp(f, f.op.len() - 1, s, t) }
    }
}

fn dfs<const W: usize>(f: &F<W>, rule: Rule, delta_only: bool) {
    let root = f.mask[f.op.len() - 1];
    let mut tau: Map<K<W>, u128> = Map::default();
    let r = K::Live(root, false);
    let mut st = vec![(r, false)];
    while let Some((k, done)) = st.pop() {
        let s = match k { K::Live(s, _) => s, K::Const(_) => { tau.insert(k, 1); continue; } };
        if !done {
            if tau.contains_key(&k) { continue; }
            match split(f, s, rule) {
                None => { tau.insert(k, 1); }
                Some((a, b)) => {
                    if delta_only { tau.insert(k, 0); } else { st.push((k, true)); }
                    for c in [a, b] { if !tau.contains_key(&c) { st.push((c, false)); } }
                }
            }
        } else {
            let (a, b) = split(f, s, rule).unwrap();
            let v = 1u128.saturating_add(tau[&a]).saturating_add(tau[&b]);
            tau.insert(k, v);
        }
    }
    let (t, td) = counts(f, root);
    let m = f.op.len();
    println!("{} {} {} {}", root.ones(), t[m - 1] + td[m - 1], tau.len(), if delta_only { 0 } else { tau[&r] });
}

fn iso<const W: usize>(f: &F<W>, rule: Rule) {
    let root = f.mask[f.op.len() - 1];
    let mut c = Cls::new(f);
    let mut seen: Set<u32> = Set::default();
    let mut st = vec![K::Live(root, false)];
    while let Some(k) = st.pop() {
        if !seen.insert(c.of_key(f, k)) { continue; }
        if let K::Live(s, _) = k {
            if let Some((a, b)) = split(f, s, rule) { st.push(a); st.push(b); }
        }
    }
    let (t, td) = counts(f, root);
    let m = f.op.len();
    println!("{} {} {}", root.ones(), t[m - 1] + td[m - 1], seen.len());
}

/// A pending node: (S, t) and the number of root paths reaching it, exact (saturating) and as f64.
type Rec<const W: usize> = (M<W>, bool, u128, f64);

/// Pending nodes of one level |S| = l: in memory, or appended to DIR/l.bin.
struct Lv<const W: usize> { dir: Option<PathBuf>, mem: Vec<Vec<Rec<W>>>, out: Vec<Option<BufWriter<File>>> }

impl<const W: usize> Lv<W> {
    fn push(&mut self, r: Rec<W>) {
        let l = r.0.ones() as usize;
        match &self.dir {
            None => self.mem[l].push(r),
            Some(d) => {
                let w = self.out[l].get_or_insert_with(|| BufWriter::with_capacity(1 << 16,
                    File::create(d.join(format!("{l}.bin"))).unwrap()));
                for x in r.0.0 { w.write_all(&x.to_le_bytes()).unwrap(); }
                w.write_all(&[r.1 as u8]).unwrap();
                w.write_all(&r.2.to_le_bytes()).unwrap();
                w.write_all(&r.3.to_le_bytes()).unwrap();
            }
        }
    }
    /// Level l with equal nodes merged, their path counts added.
    fn take(&mut self, l: usize) -> Vec<Rec<W>> {
        let mut v = match &self.dir {
            None => std::mem::take(&mut self.mem[l]),
            Some(d) => {
                let Some(w) = self.out[l].take() else { return vec![] };
                drop(w);
                let p = d.join(format!("{l}.bin"));
                let b = fs::read(&p).unwrap();
                fs::remove_file(&p).unwrap();
                b.chunks_exact(8 * W + 25).map(|r| {
                    let mut s = M::zero();
                    for i in 0..W { s.0[i] = u64::from_le_bytes(r[8 * i..8 * i + 8].try_into().unwrap()); }
                    let q = 8 * W + 1;
                    (s, r[8 * W] == 1, u128::from_le_bytes(r[q..q + 16].try_into().unwrap()),
                     f64::from_le_bytes(r[q + 16..q + 24].try_into().unwrap()))
                }).collect()
            }
        };
        v.sort_unstable_by(|a, b| (a.0, a.1).cmp(&(b.0, b.1)));
        v.dedup_by(|a, b| {
            let eq = (a.0, a.1) == (b.0, b.1);
            if eq { b.2 = b.2.saturating_add(a.2); b.3 += a.3; }
            eq
        });
        v
    }
}

fn classes<const W: usize>(f: &F<W>, rule: Rule, dir: Option<PathBuf>) {
    let m = f.op.len();
    let root = f.mask[m - 1];
    let n = root.ones() as usize;
    let mut c = Cls::new(f);
    let mut lv = Lv { dir, mem: vec![vec![]; n + 1], out: (0..=n).map(|_| None).collect() };
    let grand: Vec<usize> = f.kids[m - 1].iter().flat_map(|&k| f.kids[k].clone()).collect();
    let mut bl: Vec<Set<M<W>>> = vec![Set::default(); grand.len() + f.kids[m - 1].len()];
    let bm: Vec<M<W>> = grand.iter().chain(&f.kids[m - 1]).map(|&b| f.mask[b]).collect();
    let (mut shp, mut orb): (Set<u32>, Set<u64>) = (Set::default(), Set::default());
    let mut cst = [false; 2];
    let (mut delta, mut tau, mut tauf) = (0u64, 0u128, 0f64);
    lv.push((root, false, 1, 1.0));
    for l in (1..=n).rev() {
        let v = lv.take(l);
        for &(s, t, p, pf) in &v {
            delta += 1;
            (tau, tauf) = (tau.saturating_add(p), tauf + pf);
            shp.insert(c.shp(f, m - 1, s, t));
            orb.insert((c.orb(f, m - 1, s) as u64) << 1 | t as u64);
            for (i, &b) in bm.iter().enumerate() { bl[i].insert(s.and(b)); }
            if let Some((a, b)) = split(f, s, rule) {
                for k in [a, b] {
                    match k {
                        K::Const(x) => { cst[x as usize] = true; (tau, tauf) = (tau.saturating_add(p), tauf + pf); }
                        K::Live(s2, t2) => lv.push((s2, t2, p, pf)),
                    }
                }
            }
        }
        if !v.is_empty() {
            eprintln!("level {l}: {} nodes, delta {delta}, shapes {}, orbits {}, tables {}/{}",
                      v.len(), shp.len(), orb.len(), c.shp.code.len(), c.orb.code.len());
        }
    }
    let k = cst.iter().filter(|&&x| x).count();
    let (t, td) = counts(f, root);
    let tau = if tau == u128::MAX { format!("~{tauf:e}") } else { tau.to_string() };
    println!("{} {} {} {} {} {}", n, t[m - 1] + td[m - 1], delta + k as u64, shp.len() + k, orb.len() + k, tau);
    let b: Vec<String> = bl.iter().map(|x| x.len().to_string()).collect();
    println!("blocks {}", b.join(" "));
}

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let tok = tokens(&src);
    let args: Vec<String> = std::env::args().collect();
    let arg = |a: &str| args.iter().any(|x| x == a);
    let rule = if arg("--leftmost") { Rule::Leftmost } else if arg("--guarded") { Rule::Guarded } else { Rule::DegreeSum };
    let dir = args.iter().position(|x| x == "--spill").map(|i| PathBuf::from(&args[i + 1]));
    let n = tok.iter().filter_map(|t| t.trim_start_matches('x').parse::<usize>().ok()).max().unwrap() + 1;
    macro_rules! run {
        ($w:literal) => {{
            let f = parse::<$w>(&tok);
            if arg("--classes") { classes(&f, rule, dir) } else if arg("--iso") { iso(&f, rule) }
            else { dfs(&f, rule, arg("--delta-only")) }
        }};
    }
    if n <= 128 { run!(2) } else if n <= 256 { run!(4) } else { run!(8) }
}

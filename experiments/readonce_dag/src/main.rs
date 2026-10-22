//! Modified FK-A on the read-once pair (DNF f, DNF f^d), f a monotone read-once formula, n ≤ 128.
//!
//! Usage: readonce_dag [--delta-only] [--leftmost] < formula, formula an s-expression `(| (& 0 1) 2)`.
//! `--leftmost` splits on the least live variable (Hertel's order when leaves are numbered
//! left to right) instead of FK-A's largest degree sum.
//! Prints `n N delta tau` (tau = 0 under `--delta-only`).
//!
//! A node of FK-A on a dual pair is (h, t): h = f|ρ, t the last value ρ assigned, and the pair is
//! (DNF h, DNF h^d) for t = 0, swapped for t = 1. Both children of (h, t) are (h|x=0, 0) and
//! (h|x=1, 1) whatever t is (research §4, Theorem 4.7). A nonconstant restriction of a read-once
//! formula is determined by its relevant variables S: a live gate meets S, and a dead child of a
//! live gate holds that gate's identity. So a node is the key (S, t), 17 bytes, in place of a
//! formula (research §4, Remark 4.12). Cost per node O(gates).
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::Read;

#[derive(Clone, Copy, PartialEq)]
enum Op { Var(usize), And, Or }

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum K { Live(u128, bool), Const(bool) } // Const(c): C = {∅} iff c, else C = ∅

/// Gates in post-order: children before parents, the root last.
struct F { op: Vec<Op>, kids: Vec<Vec<usize>>, par: Vec<usize>, mask: Vec<u128>, leaf: Vec<usize> }

#[derive(Default)]
struct Fx(u64);
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, b: &[u8]) { for &c in b { self.0 = (self.0.rotate_left(5) ^ c as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95); } }
    fn write_u128(&mut self, v: u128) { self.write_u64(v as u64); self.write_u64((v >> 64) as u64); }
    fn write_u64(&mut self, v: u64) { self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95); }
    fn write_u8(&mut self, v: u8) { self.write_u64(v as u64); }
    fn write_isize(&mut self, v: isize) { self.write_u64(v as u64); }
}

fn parse(s: &str) -> F {
    let tok: Vec<String> = s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect();
    let mut f = F { op: vec![], kids: vec![], par: vec![], mask: vec![], leaf: vec![usize::MAX; 128] };
    fn go(t: &[String], i: &mut usize, f: &mut F) -> usize {
        let g;
        if t[*i] == "(" {
            let op = if t[*i + 1] == "&" { Op::And } else { Op::Or };
            *i += 2;
            let mut ks = vec![];
            while t[*i] != ")" { ks.push(go(t, i, f)); }
            *i += 1;
            let m = ks.iter().fold(0u128, |a, &k| a | f.mask[k]);
            g = f.op.len();
            for &k in &ks { f.par[k] = g; }
            f.op.push(op); f.kids.push(ks); f.mask.push(m);
        } else {
            let x: usize = t[*i].trim_start_matches('x').parse().unwrap();
            *i += 1;
            g = f.op.len();
            f.op.push(Op::Var(x)); f.kids.push(vec![]); f.mask.push(1u128 << x);
            f.leaf[x] = g;
        }
        f.par.push(usize::MAX);
        g
    }
    let mut i = 0;
    go(&tok, &mut i, &mut f);
    f
}

/// h|x=b for h with live set s: the live set, or the constant h becomes.
fn restrict(f: &F, s: u128, x: usize, b: bool) -> Result<u128, bool> {
    let (mut c, v) = (f.leaf[x], b);
    loop {
        let p = f.par[c];
        if p == usize::MAX { return Err(v); }
        let id = f.op[p] == Op::And;                       // identity of p: 1 for AND, 0 for OR
        if v == id && f.mask[p] & s & !f.mask[c] != 0 { return Ok(s & !f.mask[c]); }
        c = p;                                             // p is constant: v if absorbing, else id = v
    }
}

/// #terms of h_g and of h_g^d for every live gate g.
fn counts(f: &F, s: u128) -> (Vec<u128>, Vec<u128>) {
    let m = f.op.len();
    let (mut t, mut td) = (vec![0u128; m], vec![0u128; m]); // #terms of h_g and of h_g^d
    for g in 0..m {
        if f.mask[g] & s == 0 { continue; }
        let live = f.kids[g].iter().filter(|&&k| f.mask[k] & s != 0);
        (t[g], td[g]) = match f.op[g] {
            Op::Var(_) => (1, 1),
            Op::And => live.fold((1, 0), |(a, b), &k| (a * t[k], b + td[k])),
            Op::Or => live.fold((0, 1), |(a, b), &k| (a + t[k], b * td[k])),
        };
    }
    (t, td)
}

/// Children of a node with live set s, or None at a leaf of modified FK-A.
fn split(f: &F, s: u128, leftmost: bool) -> Option<(K, K)> {
    let m = f.op.len();
    let (t, td) = counts(f, s);
    let (c, d) = (t[m - 1], td[m - 1]);
    if c * d <= 1 || c == 1 || d == 1 { return None; }
    // deg_C x + deg_D x by one top-down pass: at AND a child's term count multiplies by its
    // siblings' (T side), at OR by its siblings' clause count (dual side).
    let (mut mt, mut mtd) = (vec![0u128; m], vec![0u128; m]);
    (mt[m - 1], mtd[m - 1]) = (1, 1);
    let mut best = (0u128, usize::MAX);
    for g in (0..m).rev() {
        if f.mask[g] & s == 0 { continue; }
        match f.op[g] {
            Op::Var(x) => { let k = mt[g] + mtd[g]; if k > best.0 || (k == best.0 && x < best.1) { best = (k, x); } }
            op => for &k in &f.kids[g] {
                if f.mask[k] & s == 0 { continue; }
                (mt[k], mtd[k]) = if op == Op::And { (mt[g] * (t[g] / t[k]), mtd[g]) }
                                  else { (mt[g], mtd[g] * (td[g] / td[k])) };
            },
        }
    }
    let x = if leftmost { s.trailing_zeros() as usize } else { best.1 };
    let key = |r: Result<u128, bool>, b: bool| match r {
        Err(v) => K::Const(v ^ b),
        Ok(s) => K::Live(s, b && s.count_ones() > 1),
    };
    Some((key(restrict(f, s, x, false), false), key(restrict(f, s, x, true), true)))
}

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let f = parse(&src);
    let root = f.mask[f.op.len() - 1];
    let delta_only = std::env::args().any(|a| a == "--delta-only");
    let leftmost = std::env::args().any(|a| a == "--leftmost");
    let mut tau: HashMap<K, u128, BuildHasherDefault<Fx>> = HashMap::default();
    let r = K::Live(root, false);
    let mut st = vec![(r, false)];
    while let Some((k, done)) = st.pop() {
        let s = match k { K::Live(s, _) => s, K::Const(_) => { tau.insert(k, 1); continue; } };
        if !done {
            if tau.contains_key(&k) { continue; }
            match split(&f, s, leftmost) {
                None => { tau.insert(k, 1); }
                Some((a, b)) => {
                    if delta_only { tau.insert(k, 0); } else { st.push((k, true)); }
                    for c in [a, b] { if !tau.contains_key(&c) { st.push((c, false)); } }
                }
            }
        } else {
            let (a, b) = split(&f, s, leftmost).unwrap();
            let v = 1 + tau[&a] + tau[&b];
            tau.insert(k, v);
        }
    }
    let (t, td) = counts(&f, root);
    let m = f.op.len();
    println!("{} {} {} {}", root.count_ones(), t[m - 1] + td[m - 1], tau.len(), if delta_only { 0 } else { tau[&r] });
}

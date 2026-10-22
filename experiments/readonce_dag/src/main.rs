//! Modified FK-A on the read-once pair (DNF f, DNF f^d), f a monotone read-once formula, n ≤ 512.
//!
//! Usage: readonce_dag [--delta-only] [--leftmost | --guarded] < formula, formula an s-expression
//! `(| (& 0 1) 2)`. `--leftmost` splits on the least live variable (Hertel's order when leaves are
//! numbered left to right); `--guarded` on the least variable with |C| ≤ s·deg_C or |D| ≤ s·deg_D,
//! s = ⌊log₂ N⌋ (FK96 Lemma 2.3.2; Lean `guardRule`), else on FK-A's largest degree sum.
//! Prints `n N delta tau` (tau = 0 under `--delta-only`).
//!
//! A node of FK-A on a dual pair is (h, t): h = f|ρ, t the last value ρ assigned, and the pair is
//! (DNF h, DNF h^d) for t = 0, swapped for t = 1. Both children of (h, t) are (h|x=0, 0) and
//! (h|x=1, 1) whatever t is (research §4, Theorem 4.7). A nonconstant restriction of a read-once
//! formula is determined by its relevant variables S (Lean `Fm.rminor_determined`), so a node is
//! the key (S, t) in place of a formula. Cost per node O(gates).
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::Read;

const W: usize = 8; // 64-bit words per mask: n ≤ 512

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
struct M([u64; W]);

impl M {
    fn bit(x: usize) -> M { let mut m = M::default(); m.0[x / 64] = 1 << (x % 64); m }
    fn or(self, o: M) -> M { let mut m = self; for i in 0..W { m.0[i] |= o.0[i]; } m }
    fn and(self, o: M) -> M { let mut m = self; for i in 0..W { m.0[i] &= o.0[i]; } m }
    fn andnot(self, o: M) -> M { let mut m = self; for i in 0..W { m.0[i] &= !o.0[i]; } m }
    fn any(self) -> bool { self.0.iter().any(|&w| w != 0) }
    fn ones(self) -> u32 { self.0.iter().map(|w| w.count_ones()).sum() }
    fn low(self) -> usize { for i in 0..W { if self.0[i] != 0 { return 64 * i + self.0[i].trailing_zeros() as usize; } } usize::MAX }
}

#[derive(Clone, Copy, PartialEq)]
enum Op { Var(usize), And, Or }

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum K { Live(M, bool), Const(bool) } // Const(c): C = {∅} iff c, else C = ∅

/// Gates in post-order: children before parents, the root last.
struct F { op: Vec<Op>, kids: Vec<Vec<usize>>, par: Vec<usize>, mask: Vec<M>, leaf: Vec<usize> }

#[derive(Default)]
struct Fx(u64);
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, b: &[u8]) { for &c in b { self.0 = (self.0.rotate_left(5) ^ c as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95); } }
    fn write_u64(&mut self, v: u64) { self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95); }
    fn write_u8(&mut self, v: u8) { self.write_u64(v as u64); }
    fn write_usize(&mut self, v: usize) { self.write_u64(v as u64); }
    fn write_isize(&mut self, v: isize) { self.write_u64(v as u64); }
}

fn parse(s: &str) -> F {
    let tok: Vec<String> = s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect();
    let mut f = F { op: vec![], kids: vec![], par: vec![], mask: vec![], leaf: vec![usize::MAX; 64 * W] };
    fn go(t: &[String], i: &mut usize, f: &mut F) -> usize {
        let g;
        if t[*i] == "(" {
            let op = if t[*i + 1] == "&" { Op::And } else { Op::Or };
            *i += 2;
            let mut ks = vec![];
            while t[*i] != ")" { ks.push(go(t, i, f)); }
            *i += 1;
            let m = ks.iter().fold(M::default(), |a, &k| a.or(f.mask[k]));
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
    go(&tok, &mut i, &mut f);
    f
}

/// h|x=b for h with live set s: the live set, or the constant h becomes.
fn restrict(f: &F, s: M, x: usize, b: bool) -> Result<M, bool> {
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
fn counts(f: &F, s: M) -> (Vec<u128>, Vec<u128>) {
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
fn split(f: &F, s: M, rule: Rule) -> Option<(K, K)> {
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
    let key = |r: Result<M, bool>, b: bool| match r {
        Err(v) => K::Const(v ^ b),
        Ok(s) => K::Live(s, b && s.ones() > 1),
    };
    Some((key(restrict(f, s, x, false), false), key(restrict(f, s, x, true), true)))
}

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let f = parse(&src);
    let root = f.mask[f.op.len() - 1];
    let arg = |a: &str| std::env::args().any(|x| x == a);
    let delta_only = arg("--delta-only");
    let rule = if arg("--leftmost") { Rule::Leftmost } else if arg("--guarded") { Rule::Guarded } else { Rule::DegreeSum };
    let mut tau: HashMap<K, u128, BuildHasherDefault<Fx>> = HashMap::default();
    let r = K::Live(root, false);
    let mut st = vec![(r, false)];
    while let Some((k, done)) = st.pop() {
        let s = match k { K::Live(s, _) => s, K::Const(_) => { tau.insert(k, 1); continue; } };
        if !done {
            if tau.contains_key(&k) { continue; }
            match split(&f, s, rule) {
                None => { tau.insert(k, 1); }
                Some((a, b)) => {
                    if delta_only { tau.insert(k, 0); } else { st.push((k, true)); }
                    for c in [a, b] { if !tau.contains_key(&c) { st.push((c, false)); } }
                }
            }
        } else {
            let (a, b) = split(&f, s, rule).unwrap();
            let v = 1u128.saturating_add(tau[&a]).saturating_add(tau[&b]);
            tau.insert(k, v);
        }
    }
    let (t, td) = counts(&f, root);
    let m = f.op.len();
    println!("{} {} {} {}", root.ones(), t[m - 1] + td[m - 1], tau.len(), if delta_only { 0 } else { tau[&r] });
}

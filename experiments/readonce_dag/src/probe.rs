//! Bounded Q1/Q2 probes; JSON lines, one final summary, levels on stderr.
//! --joint [--spill DIR]: exact support projections on grandchildren a,c; standalone
//! block targets use the same rule and increasing-label normalization. No shape inference.
//! --guard-trace: per-|S| counts of distinct ordered nodes (not tree multiplicities).
//!
//! Legend: f formula; s live support; t orientation; l support size; p split choice;
//! a,c selected blocks; b block root; xs increasing block labels; h standalone block;
//! r standalone reached supports; ix projection indices; rows joint incidence bitset;
//! ab,cb normalized projections; na,nc marginal sizes; hit number of target pairs reached;
//! q row/column index; v pending level; st DFS stack; seen visited ordered states;
//! nt nonterminal nodes; nl leftmost ineligible; nf degree-sum fallbacks;
//! nd chosen vertex differs from degree sum; first first leftmost departure;
//! delta distinct ordered states; cst reached constants; lv level queue;
//! eq equal-size target pairs by size (targets, pairs, hits); miss first equal-size missing pair.

use super::*;

fn norm<const W: usize>(s: M<W>, xs: &[usize]) -> M<W> {
    // Contiguous GK/TK blocks use word shifts; keep arbitrary labels exact.
    if !xs.is_empty() && xs[xs.len() - 1] - xs[0] + 1 == xs.len() {
        let (q, b) = (xs[0] / 64, xs[0] % 64);
        let mut m = M::zero();
        for i in 0..xs.len().div_ceil(64) {
            m.0[i] = s.0[q + i] >> b;
            if b != 0 && q + i + 1 < W { m.0[i] |= s.0[q + i + 1] << (64 - b); }
        }
        if xs.len() % 64 != 0 { m.0[xs.len() / 64] &= (1 << (xs.len() % 64)) - 1; }
        return m;
    }
    xs.iter().enumerate().fold(M::zero(), |m, (i, &x)| {
        if s.and(M::bit(x)).any() { m.or(M::bit(i)) } else { m }
    })
}

fn labels<const W: usize>(s: M<W>) -> Vec<usize> {
    (0..64 * W).filter(|&x| s.and(M::bit(x)).any()).collect()
}

fn expr<const W: usize>(f: &F<W>, b: usize, xs: &[usize]) -> String {
    match f.op[b] {
        Op::Var(x) => xs.binary_search(&x).unwrap().to_string(),
        op => format!("({} {})", if op == Op::And { "&" } else { "|" },
                      f.kids[b].iter().map(|&k| expr(f, k, xs)).collect::<Vec<_>>().join(" ")),
    }
}

fn reached<const W: usize>(f: &F<W>, rule: Rule) -> Set<M<W>> {
    let mut seen = Set::default();
    let mut r = Set::default();
    let mut st = vec![K::Live(*f.mask.last().unwrap(), false)];
    while let Some(k) = st.pop() {
        if !seen.insert(k) { continue; }
        if let K::Live(s, _) = k {
            r.insert(s);
            if let Some((a, b)) = split(f, s, rule) { st.push(a); st.push(b); }
        }
    }
    r
}

struct Joint<const W: usize> {
    xs: [Vec<usize>; 2],
    r: Vec<M<W>>,
    ix: [Map<M<W>, usize>; 2],
    rows: Vec<Vec<u64>>,
}

impl<const W: usize> Joint<W> {
    fn new(f: &F<W>, rule: Rule) -> Self {
        let top = f.op.len() - 1;
        assert!(f.kids[top].len() == 2, "joint needs two root children");
        let (a, c) = (f.kids[top][0], f.kids[top][1]);
        assert!(f.kids[a].len() == 2 && f.kids[c].len() == 2,
                "joint needs four grandchildren");
        let (a, c) = (f.kids[a][0], f.kids[c][0]);
        let xs = [labels(f.mask[a]), labels(f.mask[c])];
        let ea = expr(f, a, &xs[0]);
        assert!(ea == expr(f, c, &xs[1]), "normalized a,c blocks must agree");
        let h = parse::<W>(&tokens(&ea));
        let mut r: Vec<_> = reached(&h, rule).into_iter().collect();
        r.sort_unstable();
        Self { xs, r, ix: [Map::default(), Map::default()], rows: vec![] }
    }

    fn add(&mut self, s: M<W>) {
        let ab = norm(s, &self.xs[0]);
        let cb = norm(s, &self.xs[1]);
        let (na, nc) = (self.ix[0].len(), self.ix[1].len());
        let a = *self.ix[0].entry(ab).or_insert(na);
        let c = *self.ix[1].entry(cb).or_insert(nc);
        if self.rows.len() <= a { self.rows.push(vec![]); }
        if self.rows[a].len() <= c / 64 { self.rows[a].resize(c / 64 + 1, 0); }
        self.rows[a][c / 64] |= 1 << (c % 64);
    }

    fn has(&self, a: M<W>, c: M<W>) -> bool {
        match (self.ix[0].get(&a), self.ix[1].get(&c)) {
            (Some(&i), Some(&j)) => self.rows[i].get(j / 64)
                .is_some_and(|&w| w & (1 << (j % 64)) != 0),
            _ => false,
        }
    }

    fn report(&self) {
        let mut hit = 0usize;
        let mut first = None;
        for &a in &self.r { for &c in &self.r {
            if self.has(a, c) { hit += 1; } else if first.is_none() { first = Some((a, c)); }
        } }
        let marg: Vec<_> = self.ix.iter().map(|ix| self.r.iter().filter(|s| ix.contains_key(s)).count()).collect();
        let pairs: u64 = self.rows.iter().flatten().map(|w| w.count_ones() as u64).sum();
        println!("{{\"kind\":\"joint\",\"targets\":{},\"a_states\":{},\"c_states\":{},\"pairs\":{},\"a_hits\":{},\"c_hits\":{},\"pair_hits\":{},\"pair_missing\":{}}}",
                 self.r.len(), self.ix[0].len(), self.ix[1].len(), pairs, marg[0], marg[1], hit,
                 self.r.len() * self.r.len() - hit);
        if let Some((a, c)) = first {
            println!("{{\"kind\":\"missing\",\"a\":{:?},\"c\":{:?}}}", labels(a), labels(c));
        }
        // Conjecture 4.38 needs only target pairs of equal support size.
        let mut eq: std::collections::BTreeMap<u32, (u64, u64, u64)> = Default::default();
        let mut miss = None;
        for &a in &self.r {
            eq.entry(a.ones()).or_default().0 += 1;
            for &c in &self.r {
                if a.ones() != c.ones() { continue; }
                let e = eq.get_mut(&a.ones()).unwrap();
                e.1 += 1;
                if self.has(a, c) { e.2 += 1; } else if miss.is_none() { miss = Some((a, c)); }
            }
        }
        for (l, (m, p, h)) in &eq {
            println!("{{\"kind\":\"equal_size\",\"size\":{l},\"targets\":{m},\"pairs\":{p},\"hits\":{h}}}");
        }
        if let Some((a, c)) = miss {
            println!("{{\"kind\":\"equal_size_missing\",\"a\":{:?},\"c\":{:?}}}", labels(a), labels(c));
        }
    }
}

pub(super) fn run<const W: usize>(f: &F<W>, rule: Rule, dir: Option<PathBuf>, joint: bool, trace: bool) {
    assert!(!trace || rule == Rule::Guarded, "--guard-trace requires --guarded");
    let root = *f.mask.last().unwrap();
    let n = root.ones() as usize;
    let mut lv = Lv { dir, mem: vec![vec![]; n + 1], out: (0..=n).map(|_| None).collect() };
    let mut j = joint.then(|| Joint::new(f, rule));
    let (mut delta, mut cst, mut first) = (0u64, [false; 2], false);
    lv.push((root, false, 1, 1.0));
    for l in (1..=n).rev() {
        let v = lv.take(l);
        let (mut nt, mut nl, mut nf, mut nd) = (0u64, 0u64, 0u64, 0u64);
        for &(s, t, _, _) in &v {
            delta += 1;
            if let Some(j) = &mut j { j.add(s); }
            if let Some(p) = pick(f, s, rule) {
                nt += 1;
                nl += (p.g != s.low()) as u64;
                nf += (p.g == usize::MAX) as u64;
                nd += (p.x != p.b) as u64;
                if trace && !first && p.g != s.low() {
                    first = true;
                    println!("{{\"kind\":\"first_departure\",\"level\":{l},\"support\":{:?},\"tag\":{t},\"leftmost\":{},\"chosen\":{},\"degree_sum\":{}}}",
                             labels(s), s.low(), p.x, p.b);
                }
                let (a, b) = children(f, s, p.x);
                for k in [a, b] { match k {
                    K::Live(s, t) => lv.push((s, t, 1, 1.0)),
                    K::Const(x) => cst[x as usize] = true,
                } }
            }
        }
        if !v.is_empty() {
            eprintln!("probe level {l}: {} nodes, delta {delta}", v.len());
            if trace {
                println!("{{\"kind\":\"level\",\"level\":{l},\"nodes\":{},\"splits\":{nt},\"leftmost_ineligible\":{nl},\"fallbacks\":{nf},\"diff_degree_sum\":{nd}}}", v.len());
            }
        }
    }
    if let Some(j) = j { j.report(); }
    println!("{{\"kind\":\"summary\",\"n\":{n},\"delta\":{}}}", delta + cst.iter().filter(|&&b| b).count() as u64);
}

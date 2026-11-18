//! Exhaustive test of Conjecture 6 of `docs/frequency-constant.md` on every monotone
//! Boolean function of at most `n <= 6` variables. It holds there; Proposition 7 of the
//! note refutes it on 36 variables.
//!
//! Legend (one dual pair):
//!   f      : monotone function, truth table over 2^n points, bit x is f(x)
//!   C, D   : minterms and maxterm clauses of f, as variable bitmasks; D = Tr(C)
//!   A, B   : |C|, |D|
//!   eps    : max over variables v of max(deg_C v / A, deg_D v / B)
//!   defect : log2 A + log2 B + 3 - 3/eps; Conjecture 6 said defect >= 0
//!
//! Usage: `frequency_constant N` prints the number of dual pairs checked, the least
//! defect with a witness, and every pair of defect 0.

/// All monotone functions of `n` variables: f = f0 | f1 << 2^(n-1) with f0 <= f1.
fn monotone(n: u32) -> Vec<u64> {
    if n == 0 {
        return vec![0, 1];
    }
    let lower = monotone(n - 1);
    let half = 1u32 << (n - 1);
    let mut fs = Vec::new();
    for &f0 in &lower {
        for &f1 in &lower {
            if f0 & !f1 == 0 {
                fs.push(f0 | (f1 << half));
            }
        }
    }
    fs
}

/// (C, D): minimal true points of f, and complements of its maximal false points.
fn dual_pair(f: u64, n: u32) -> (Vec<u32>, Vec<u32>) {
    let full = (1u32 << n) - 1;
    let at = |x: u32| (f >> x) & 1 == 1;
    let mut c = Vec::new();
    let mut d = Vec::new();
    for x in 0..=full {
        if at(x) {
            if (0..n).all(|i| x >> i & 1 == 0 || !at(x ^ (1 << i))) {
                c.push(x);
            }
        } else if (0..n).all(|i| x >> i & 1 == 1 || at(x | (1 << i))) {
            d.push(full ^ x);
        }
    }
    (c, d)
}

fn eps(c: &[u32], d: &[u32], n: u32) -> f64 {
    let freq = |sets: &[u32], i: u32| {
        sets.iter().filter(|&&s| s >> i & 1 == 1).count() as f64 / sets.len() as f64
    };
    (0..n)
        .map(|i| freq(c, i).max(freq(d, i)))
        .fold(0.0, f64::max)
}

fn show(sets: &[u32], n: u32) -> String {
    let set = |s: u32| {
        (0..n)
            .filter(|i| s >> i & 1 == 1)
            .map(|i| i.to_string())
            .collect::<String>()
    };
    sets.iter().map(|&s| set(s)).collect::<Vec<_>>().join(" ")
}

fn variables(mut args: impl Iterator<Item = String>) -> Result<u32, &'static str> {
    let n = args.next().map_or(Some(5), |arg| arg.parse::<u32>().ok());
    match n {
        Some(n @ 1..=6) if args.next().is_none() => Ok(n),
        _ => Err("usage: frequency_constant [N], with 1 <= N <= 6"),
    }
}

fn main() {
    let n = variables(std::env::args().skip(1)).unwrap_or_else(|message| {
        eprintln!("{message}");
        std::process::exit(2);
    });
    let (mut pairs, mut ties) = (0u64, 0u64);
    let mut least = (f64::INFINITY, 0u64);
    for f in monotone(n) {
        let (c, d) = dual_pair(f, n);
        // Constants have an empty side or the empty edge; they are not dual pairs here.
        if c.is_empty() || d.is_empty() || c[0] == 0 || d.contains(&0) {
            continue;
        }
        pairs += 1;
        let defect = (c.len() as f64).log2() + (d.len() as f64).log2() + 3.0 - 3.0 / eps(&c, &d, n);
        if defect < least.0 {
            least = (defect, f);
        }
        if defect.abs() < 1e-9 {
            ties += 1;
            println!("defect 0: C {} | D {}", show(&c, n), show(&d, n));
        }
    }
    let (c, d) = dual_pair(least.1, n);
    println!(
        "n={n} dual pairs={pairs} defect-0 pairs={ties} least defect={:.6}",
        least.0
    );
    println!("least-defect pair: C {} | D {}", show(&c, n), show(&d, n));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn three_variable_enumeration() {
        let fs = monotone(3);
        assert_eq!(fs.len(), 20);
        assert_eq!(
            fs.iter()
                .copied()
                .collect::<std::collections::HashSet<_>>()
                .len(),
            20
        );
        assert_eq!(dual_pair(0b1110_1000, 3), (vec![3, 5, 6], vec![6, 5, 3]));
    }

    #[test]
    fn validates_argument_and_arity() {
        let parse = |args: &[&str]| variables(args.iter().map(|s| s.to_string()));
        assert_eq!(parse(&[]), Ok(5));
        assert_eq!(parse(&["6"]), Ok(6));
        for args in [&["0"][..], &["7"][..], &["x"][..], &["3", "4"][..]] {
            assert!(parse(args).is_err(), "{args:?}");
        }
    }
}

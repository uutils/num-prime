//! Micro-benchmark for the [`num_prime::factor::pollard_rho`] inner loop.
//!
//! - `production`: the crate's `pollard_rho` on `SmallMint<u64>`
//! - `lean`: the same Brent schedule hand-written over a bare REDC step, as a
//!   reference for what the loop costs without any wrapper type
//!
//! Run: cargo run --release --example rho_bench

use num_modular::MontgomeryInt;
use num_prime::detail::SmallMint;
use num_prime::factor::pollard_rho;
use std::time::{Duration, Instant};

#[inline(always)]
fn neginv(n: u64) -> u64 {
    let mut inv = 1u64;
    for _ in 0..6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(inv)));
    }
    inv.wrapping_neg()
}

/// Montgomery multiplication (Hensel/REDC) — the same shape the num-modular
/// wrapper lowers to.
#[inline(always)]
fn mulredc(a: u64, b: u64, n: u64, ni: u64) -> u64 {
    let ab = (a as u128) * (b as u128);
    let (t, carry) = ab.overflowing_add(((ab as u64).wrapping_mul(ni) as u128) * (n as u128));
    let r = (t >> 64) as u64;
    if carry || r >= n {
        r.wrapping_sub(n)
    } else {
        r
    }
}

#[inline(always)]
fn addmod(a: u64, b: u64, n: u64) -> u64 {
    let s = a.wrapping_add(b);
    if s < a || s >= n {
        s.wrapping_sub(n)
    } else {
        s
    }
}

#[inline(always)]
fn submod(a: u64, b: u64, n: u64) -> u64 {
    let d = a.wrapping_sub(b);
    if a < b {
        d.wrapping_add(n)
    } else {
        d
    }
}

fn gcd64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// The Brent schedule hand-written over bare REDC steps.
fn rho_lean(n: u64, seed: u64, max_iter: usize) -> (Option<u64>, usize) {
    let ni = neginv(n);
    let red = |v: u64| ((v as u128 * (1u128 << 64)) % n as u128) as u64;
    let offset = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) % n;
    let mut a = red(seed.max(1) % n);
    let mut b = a;
    let mut z = red(1);
    let (mut i, mut j) = (0usize, 1usize);
    let (mut s, mut backtrace) = (a, false);
    while i < max_iter {
        i += 1;
        a = mulredc(a, a, n, ni);
        a = addmod(a, offset, n);
        if a == b {
            return (None, i);
        }
        let diff = submod(a, b, n);
        z = mulredc(z, diff, n, ni);
        if z == 0 {
            if backtrace {
                return (None, i);
            }
            backtrace = true;
            a = s;
            z = red(1);
            continue;
        }
        if i == j || i & 127 == 0 || backtrace {
            let d = gcd64(z, n);
            if d != 1 && d != n {
                return (Some(d), i);
            }
            s = a;
        }
        if i == j {
            b = a;
            j <<= 1;
        }
    }
    (None, i)
}

/// The crate's `pollard_rho` with the same fixed parameters as `rho_lean`.
fn rho_production(n: u64, seed: u64, max_iter: usize) -> (Option<u64>, usize) {
    type M = SmallMint<u64>;
    let tm = M::from(n);
    let start: M = MontgomeryInt::new(seed % n, &n).into();
    let offset: M = MontgomeryInt::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) % n, &n).into();
    let (fac, iters) = pollard_rho(&tm, start, offset, max_iter);
    (fac.map(|v| v.value()), iters)
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// Deterministic Miller-Rabin, only used to generate the benchmark inputs.
fn is_prime(v: u64) -> bool {
    if v < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if v % p == 0 {
            return v == p;
        }
    }
    let (mut d, mut r) = (v - 1, 0u32);
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    'w: for w in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let (mut x, mut b, mut e) = (1u64, w % v, d);
        while e > 0 {
            if e & 1 == 1 {
                x = ((x as u128 * b as u128) % v as u128) as u64;
            }
            b = ((b as u128 * b as u128) % v as u128) as u64;
            e >>= 1;
        }
        if x == 1 || x == v - 1 {
            continue 'w;
        }
        for _ in 0..r - 1 {
            x = ((x as u128 * x as u128) % v as u128) as u64;
            if x == v - 1 {
                continue 'w;
            }
        }
        return false;
    }
    true
}

fn bench<F>(name: &str, semis: &[(u64, u64)], reps: usize, max_iter: usize, f: F)
where
    F: Fn(u64, u64, usize) -> (Option<u64>, usize),
{
    // First pass fixes the (deterministic) iteration count, later passes
    // assert the walk is stable and time it.
    let total: usize = semis.iter().map(|&(n, seed)| f(n, seed, max_iter).1).sum();
    let mut dt = Duration::MAX;
    for _ in 0..reps {
        let t0 = Instant::now();
        let mut iters = 0usize;
        for &(n, seed) in semis {
            let (fac, it) = f(n, seed, max_iter);
            assert!(
                fac.is_some() && n % fac.unwrap() == 0,
                "{} failed on {}",
                name,
                n
            );
            iters += it;
        }
        assert_eq!(iters, total, "{name} walk must be deterministic");
        dt = dt.min(t0.elapsed());
    }
    println!(
        "  {name}: {:.1} Miter/s ({} iterations, best of {reps})",
        total as f64 / dt.as_secs_f64() / 1e6,
        total
    );
}

fn main() {
    let mut rng = Lcg(0x5_DEEC_E66D);
    let mut semis: Vec<(u64, u64)> = Vec::new();
    while semis.len() < 12 {
        let mut p = 0x100_0000 | (rng.next() % 0xFF_FFFF) | 1;
        while !is_prime(p) {
            p += 2;
        }
        let mut q = 0x100_0000 | (rng.next() % 0xFF_FFFF) | 1;
        while !is_prime(q) {
            q += 2;
        }
        if p != q {
            semis.push((p * q, (p ^ q.rotate_left(32)) | 1));
        }
    }

    let reps = 20;
    println!("12 fixed semiprimes (~2^50 factors):");
    bench("production", &semis, reps, 1 << 26, rho_production);
    bench("lean ref  ", &semis, reps, 1 << 26, rho_lean);
}

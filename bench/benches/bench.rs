#[macro_use]
extern crate criterion;
use std::iter::repeat_with;

use criterion::{Criterion, SamplingMode};
use glass_pumpkin::{prime as gprime, safe_prime as safe_gprime};
use num_bigint::RandBigInt;
use num_prime::{nt_funcs, RandPrime};
#[cfg(feature = "num-primes")]
use num_primes::{Generator, Verification};
use rand::rngs::StdRng;
use rand::SeedableRng;

#[cfg(target_arch = "x86_64")]
use number_theory::NumberTheory;
use primal_check::miller_rabin;

pub fn bench_is_prime(c: &mut Criterion) {
    const N0: u64 = 1_000_000;
    const STEP: usize = 101;
    const N1: u64 = 8_000_000_000; // larger than u32
    const N2: u64 = N1 + N0;

    let numbers = || (1..N0).step_by(STEP).chain((N1..N2).step_by(STEP));

    let mut group = c.benchmark_group("primality check (u64)");

    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| numbers().filter(|&n| nt_funcs::is_prime64(n)).count())
    });

    #[cfg(target_arch = "x86_64")]
    group.bench_function("number-theory", |b| {
        b.iter(|| numbers().filter(|&n| NumberTheory::is_prime(&n)).count())
    });

    #[cfg(feature = "num-primes")]
    group.bench_function("num-primes", |b| {
        b.iter(|| {
            numbers()
                .filter(|&n| Verification::is_prime(&n.into()))
                .count()
        })
    });
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| numbers().filter(|&n| gprime::check(&n.into())).count())
    });
    group.bench_function("primal-check", |b| {
        b.iter(|| numbers().filter(|&n| miller_rabin(n)).count())
    });

    group.finish();

    ////// 256 bits Bigint /////

    let mut rng = StdRng::seed_from_u64(42);
    let numbers: Vec<_> = repeat_with(|| rng.gen_biguint(256)).take(32).collect();

    let mut group = c.benchmark_group("primality check (u256)");
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.bench_function("num-primes", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| {
                    Verification::is_prime(&num_primes::BigUint::from_bytes_le(&n.to_bytes_le()))
                })
                .count()
        })
    });
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| numbers.iter().filter(|&n| gprime::check(n)).count())
    });
    group.bench_function("glass_pumpkin (BPSW)", |b| {
        b.iter(|| numbers.iter().filter(|&n| gprime::strong_check(n)).count())
    });
    group.finish();

    let mut group = c.benchmark_group("safe primality check (u256)");
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| nt_funcs::is_safe_prime(n).probably())
                .count()
        })
    });
    group.bench_function("num-primes", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| {
                    Verification::is_safe_prime(&num_primes::BigUint::from_bytes_le(
                        &n.to_bytes_le(),
                    ))
                })
                .count()
        })
    });
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| numbers.iter().filter(|&n| safe_gprime::check(n)).count())
    });
    group.bench_function("glass_pumpkin (BPSW)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| safe_gprime::strong_check(n))
                .count()
        })
    });
    group.finish();

    ////// 2048 bits Bigint /////

    let mut rng = StdRng::seed_from_u64(123);
    let numbers: Vec<_> = repeat_with(|| rng.gen_biguint(2048)).take(8).collect();

    let mut group = c.benchmark_group("primality check (u2048)");
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.bench_function("num-primes", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| {
                    Verification::is_prime(&num_primes::BigUint::from_bytes_le(&n.to_bytes_le()))
                })
                .count()
        })
    });
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| numbers.iter().filter(|&n| gprime::check(n)).count())
    });
    group.bench_function("glass_pumpkin (BPSW)", |b| {
        b.iter(|| numbers.iter().filter(|&n| gprime::strong_check(n)).count())
    });
    group.finish();

    let mut group = c.benchmark_group("safe primality check (u2048)");
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| nt_funcs::is_safe_prime(n).probably())
                .count()
        })
    });
    group.bench_function("num-primes", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| {
                    Verification::is_safe_prime(&num_primes::BigUint::from_bytes_le(
                        &n.to_bytes_le(),
                    ))
                })
                .count()
        })
    });
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| numbers.iter().filter(|&n| safe_gprime::check(n)).count())
    });
    group.bench_function("glass_pumpkin (BPSW)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| safe_gprime::strong_check(n))
                .count()
        })
    });
    group.finish();
}

pub fn bench_factorization(c: &mut Criterion) {
    const N0: u64 = 1_000_000;
    const STEP: usize = 501;
    const N1: u64 = 8_000_000_000; // larger than u32
    const N2: u64 = N1 + N0;

    let numbers = || (1..N0).step_by(STEP).chain((N1..N2).step_by(STEP));
    let mut group = c.benchmark_group("factorize (u64)");

    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| {
            numbers()
                .filter(|&n| nt_funcs::factorize64(n).len() > 1)
                .count()
        })
    });

    #[cfg(target_arch = "x86_64")]
    group.bench_function("number-theory", |b| {
        b.iter(|| {
            numbers()
                .filter(|&n| NumberTheory::factor(&n).len() > 1)
                .count()
        })
    });

    group.finish();
}

pub fn bench_prime_gen(c: &mut Criterion) {
    let mut group = c.benchmark_group("prime generation (256 bits)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    let mut rng = StdRng::seed_from_u64(256);
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| -> num_bigint::BigUint { rng.gen_prime(256, None) })
    });
    group.bench_function("num-primes", |b| b.iter(|| Generator::new_prime(256)));
    group.bench_function("glass_pumpkin", |b| b.iter(|| gprime::new(256)));
    group.finish();

    let mut group = c.benchmark_group("safe prime generation (256 bits)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    let mut rng = StdRng::seed_from_u64(512);
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| -> num_bigint::BigUint { rng.gen_safe_prime(256) })
    });
    group.bench_function("num-primes", |b| b.iter(|| Generator::safe_prime(256)));
    group.bench_function("glass_pumpkin", |b| b.iter(|| safe_gprime::new(256)));
    group.finish();
}

criterion_group!(
    benches,
    bench_is_prime,
    bench_factorization,
    bench_prime_gen
);
criterion_main!(benches);

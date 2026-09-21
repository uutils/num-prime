#[macro_use]
extern crate criterion;
use std::iter::repeat_with;

use criterion::{Criterion, SamplingMode};
use glass_pumpkin::{prime as gprime, safe_prime as safe_gprime};
use num_bigint::BigUint;
use num_bigint::RandBigInt;
use num_prime::{nt_funcs, RandPrime};
#[cfg(feature = "num-primes")]
use num_primes::{Generator, Verification};
use rand::rngs::StdRng;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use rand_core::SeedableRng as SeedableRng2;

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
    #[cfg(feature = "num-primes")]
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
    #[cfg(feature = "num-primes")]
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
    #[cfg(feature = "num-primes")]
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
    #[cfg(feature = "num-primes")]
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

    group.finish();
}

/// Factorizations that are cheap for the right algorithm and ruinous for the
/// wrong one: products of several primes of similar, moderate size, where
/// trial division is useless, Pollard's rho has to run for a while, and the
/// O(n^(1/4)) methods never finish.
///
/// Each of these used to take seconds to tens of seconds. They are the shapes
/// a factorization regression shows up in first, so they are worth tracking
/// even though they are slower than the rest of this file.
pub fn bench_hard_factorization(c: &mut Criterion) {
    // 529341446939 * 529341447079 * 529341447139
    const THREE_PRIMES: u128 = 148_322_726_715_648_124_896_087_586_879_631_159;
    // thirteen primes near 2^39
    const THIRTEEN_PRIMES: &str = "256192672085272469290287843204387360975152374284235599731951768269391636066386517575760286247162035537155995319918598846421204855240141082924971355328149";
    // five primes near 2^38
    const FIVE_PRIMES: &str = "1569275491456096801522790424087360918295323588350447935207";
    // 34359738421^7, which Pollard's rho cannot split at all
    const PRIME_POWER: &str =
        "56539106683390492137844827055225747632151249167945695848217966183182073341";

    let mut group = c.benchmark_group("factorize (hard)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    group.bench_function("three 39-bit primes (u128)", |b| {
        b.iter(|| {
            let factors = nt_funcs::factorize128(THREE_PRIMES);
            assert_eq!(factors.len(), 3);
            factors
        })
    });

    for (name, digits, count) in [
        ("five 38-bit primes (191 bits)", FIVE_PRIMES, 5),
        ("thirteen 39-bit primes (507 bits)", THIRTEEN_PRIMES, 13),
        ("a 35-bit prime to the 7th (246 bits)", PRIME_POWER, 1),
    ] {
        let target: BigUint = digits.parse().unwrap();
        group.bench_function(name, |b| {
            b.iter(|| {
                let factors = nt_funcs::factorize(target.clone());
                assert_eq!(factors.len(), count);
                factors
            })
        });
    }

    group.finish();
}

pub fn bench_prime_gen(c: &mut Criterion) {
    let mut group = c.benchmark_group("prime generation (256 bits)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    let mut rng = StdRng::seed_from_u64(256);
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| -> num_bigint::BigUint { rng.gen_prime(256, None) })
    });
    // Note: num-primes uses thread_rng() internally, so this benchmark is not deterministic
    #[cfg(feature = "num-primes")]
    group.bench_function("num-primes", |b| b.iter(|| Generator::new_prime(256)));
    let mut rng_gp = ChaCha8Rng::seed_from_u64(257);
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| gprime::from_rng(256, &mut rng_gp))
    });
    group.finish();

    let mut group = c.benchmark_group("safe prime generation (256 bits)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    let mut rng = StdRng::seed_from_u64(512);
    group.bench_function("num-prime (this crate)", |b| {
        b.iter(|| -> num_bigint::BigUint { rng.gen_safe_prime(256) })
    });
    // Note: num-primes uses thread_rng() internally, so this benchmark is not deterministic
    #[cfg(feature = "num-primes")]
    group.bench_function("num-primes", |b| b.iter(|| Generator::safe_prime(256)));
    let mut rng_gp = ChaCha8Rng::seed_from_u64(513);
    group.bench_function("glass_pumpkin", |b| {
        b.iter(|| safe_gprime::from_rng(256, &mut rng_gp))
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_is_prime,
    bench_factorization,
    bench_hard_factorization,
    bench_prime_gen
);
criterion_main!(benches);

//! Backend A/B benchmarks: `num-bigint` vs `dashu-int` under the same generic
//! algorithms, interleaved in one binary (sequential runs of two binaries are
//! not comparable on this machine), plus kernel-level attribution benches that
//! explain where a speedup or slowdown comes from.

use std::iter::repeat_with;

#[macro_use]
extern crate criterion;
use criterion::{black_box, Criterion, SamplingMode};
use dashu_int::UBig;
use num_bigint::BigUint;
use num_bigint::RandBigInt;
use num_prime::detail::UBigMint;
use num_prime::{nt_funcs, RandPrime};
use rand::rngs::StdRng;
use rand::SeedableRng;

/// Parse a decimal string into both backends.
fn both(s: &str) -> (BigUint, UBig) {
    (s.parse().unwrap(), s.parse().unwrap())
}

/// Interleaved end-to-end comparisons on identical inputs.
pub fn bench_backend_is_prime(c: &mut Criterion) {
    // 256-bit Bigint
    let mut rng = StdRng::seed_from_u64(42);
    let numbers_big: Vec<_> = repeat_with(|| rng.gen_biguint(256)).take(32).collect();
    let numbers_dashu: Vec<UBigMint> = numbers_big
        .iter()
        .map(|b| UBigMint::from(UBig::from_str_radix(&b.to_str_radix(10), 10).unwrap()))
        .collect();

    let mut group = c.benchmark_group("backend A/B: primality check (u256)");
    group.bench_function("num-bigint", |b| {
        b.iter(|| {
            numbers_big
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.bench_function("dashu-int", |b| {
        b.iter(|| {
            numbers_dashu
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.finish();

    // 2048-bit Bigint
    let mut rng = StdRng::seed_from_u64(123);
    let numbers_big: Vec<_> = repeat_with(|| rng.gen_biguint(2048)).take(8).collect();
    let numbers_dashu: Vec<UBigMint> = numbers_big
        .iter()
        .map(|b| UBigMint::from(UBig::from_str_radix(&b.to_str_radix(10), 10).unwrap()))
        .collect();

    let mut group = c.benchmark_group("backend A/B: primality check (u2048)");
    group.bench_function("num-bigint", |b| {
        b.iter(|| {
            numbers_big
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.bench_function("dashu-int", |b| {
        b.iter(|| {
            numbers_dashu
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.finish();
}

pub fn bench_backend_hard_factorization(c: &mut Criterion) {
    // thirteen primes near 2^39 (507 bits)
    const THIRTEEN_PRIMES: &str = "256192672085272469290287843204387360975152374284235599731951768269391636066386517575760286247162035537155995319918598846421204855240141082924971355328149";
    // five primes near 2^38 (191 bits)
    const FIVE_PRIMES: &str = "1569275491456096801522790424087360918295323588350447935207";
    // 34359738421^7 (246 bits)
    const PRIME_POWER: &str =
        "56539106683390492137844827055225747632151249167945695848217966183182073341";

    let mut group = c.benchmark_group("backend A/B: factorize (hard)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    for (name, digits, count) in [
        ("five 38-bit primes (191 bits)", FIVE_PRIMES, 5),
        ("thirteen 39-bit primes (507 bits)", THIRTEEN_PRIMES, 13),
        ("a 35-bit prime to the 7th (246 bits)", PRIME_POWER, 1),
    ] {
        let (target_big, target_dashu) = both(digits);
        group.bench_function(format!("{name} [num-bigint]"), |b| {
            b.iter(|| {
                let factors = nt_funcs::factorize(target_big.clone());
                assert_eq!(factors.len(), count);
                factors
            })
        });
        group.bench_function(format!("{name} [dashu-int]"), |b| {
            b.iter(|| {
                let factors = nt_funcs::factorize(UBigMint::from(target_dashu.clone()));
                assert_eq!(factors.len(), count);
                factors
            })
        });
    }

    group.finish();
}

pub fn bench_backend_prime_gen(c: &mut Criterion) {
    let mut group = c.benchmark_group("backend A/B: prime generation (256 bits)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    let mut rng = StdRng::seed_from_u64(256);
    group.bench_function("num-bigint", |b| {
        b.iter(|| -> BigUint { rng.gen_prime(256, None) })
    });
    let mut rng = StdRng::seed_from_u64(256);
    group.bench_function("dashu-int", |b| {
        b.iter(|| -> UBigMint { rng.gen_prime(256, None) })
    });
    group.finish();

    let mut group = c.benchmark_group("backend A/B: safe prime generation (256 bits)");
    group.sample_size(10).sampling_mode(SamplingMode::Flat);

    let mut rng = StdRng::seed_from_u64(512);
    group.bench_function("num-bigint", |b| {
        b.iter(|| -> BigUint { rng.gen_safe_prime(256) })
    });
    let mut rng = StdRng::seed_from_u64(512);
    group.bench_function("dashu-int", |b| {
        b.iter(|| -> UBigMint { rng.gen_safe_prime(256) })
    });
    group.finish();
}

/// Kernel-level attribution: the same primitive operation on both integer
/// types, explaining the end-to-end differences above.
pub fn bench_backend_kernels(c: &mut Criterion) {
    use num_integer::Integer as _;
    use num_modular::Reducer as _;

    // moduli and bases at three widths, parsed once
    let cases: [(&str, &str); 3] = [
        ("256-bit", "97139905378492632848750026506426168385840487978959921168635843791752925693763"),
        ("512-bit", "8856081756609151660576435520674954574366898212202549406516451834762219198755786326544367653562643415353888306935085628680317655266330762950578278876775905341256313"),
        ("2048-bit", "2097853130179912670414231560697168902480142790080870284142258354330205087243608705850035651289948091642413225504320028627700153751423716299366658809344987601844719829496998041023139493930325629154583757600787739605382892181512028152494949307367916758893936426337672012620765330083535715437974523879146484241247138812358733867"),
    ];

    for (label, m_str) in cases {
        let (m_big, m_dashu) = both(m_str);
        // base = m - 2, exponent = m >> 1 (both in range and odd)
        let base_big = &m_big - 2u8;
        let exp_big = &m_big >> 1u8;
        let base_dashu = &m_dashu - UBig::from(2u8);
        let exp_dashu = &m_dashu >> 1usize;

        let mut group = c.benchmark_group(format!("kernel A/B: modpow ({label})"));
        group.bench_function("num-bigint", |b| {
            b.iter(|| base_big.modpow(black_box(&exp_big), black_box(&m_big)))
        });
        group.bench_function("dashu-int", |b| {
            b.iter(|| {
                let ring = dashu_int::monty::MontgomeryRepr::new(m_dashu.clone());
                ring.reduce(base_dashu.clone())
                    .pow(black_box(&exp_dashu))
                    .residue()
            })
        });
        group.finish();

        // div_rem
        let mut group = c.benchmark_group(format!("kernel A/B: div_rem ({label})"));
        group.bench_function("num-bigint", |b| {
            b.iter(|| (&exp_big * &exp_big).div_rem(black_box(&m_big)))
        });
        group.bench_function("dashu-int", |b| {
            b.iter(|| (&exp_dashu * &exp_dashu).div_rem(black_box(&m_dashu)))
        });
        group.finish();

        // mul
        let mut group = c.benchmark_group(format!("kernel A/B: mul ({label})"));
        group.bench_function("num-bigint", |b| b.iter(|| &exp_big * &exp_big));
        group.bench_function("dashu-int", |b| b.iter(|| &exp_dashu * &exp_dashu));
        group.finish();
    }

    // gcd (512-bit)
    let (a_big, a_dashu) = both(
        "8856081756609263284875002650642616838584048797895992116863584379175292569376303769558719368663457069543187784870601747148715499879166751344341339727473947360746697",
    );
    let (b_big, b_dashu) = both(
        "7586337661193832132682652968620525363226624116575482968310675100434603627388196365325207749798239514322067893124875956788505175327449427178378364592113679250412953",
    );
    let mut group = c.benchmark_group("kernel A/B: gcd (512-bit)");
    group.bench_function("num-bigint", |b| b.iter(|| a_big.gcd(black_box(&b_big))));
    group.bench_function("dashu-int", |b| b.iter(|| a_dashu.gcd(black_box(&b_dashu))));
    group.finish();
}

/// Noise floor: the same backend measured twice, to calibrate how much of a
/// small A/B difference is layout noise rather than a real effect.
pub fn bench_noise_floor(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(42);
    let numbers: Vec<BigUint> = repeat_with(|| rng.gen_biguint(256)).take(32).collect();
    let mut group = c.benchmark_group("noise floor: primality check (u256, num-bigint x2)");
    group.bench_function("run 1", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.bench_function("run 2 (same code)", |b| {
        b.iter(|| {
            numbers
                .iter()
                .filter(|&n| nt_funcs::is_prime(n, None).probably())
                .count()
        })
    });
    group.finish();
}

criterion_group!(
    benches_ab,
    bench_backend_is_prime,
    bench_backend_hard_factorization,
    bench_backend_prime_gen,
    bench_backend_kernels,
    bench_noise_floor
);
criterion_main!(benches_ab);

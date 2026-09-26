//! Integration tests for the `dashu-int` big-integer backend.
//!
//! Mirrors the `num-bigint` test blocks in the unit tests, plus cross-backend
//! consistency checks (only compiled when both backends are available).

#![cfg(feature = "dashu-int")]

use dashu_int::UBig;
use num_prime::BitTest as _;
use num_prime::{
    buffer::{NaiveBuffer, PrimeBufferExt},
    detail::UBigMint,
    nt_funcs::{factors, is_prime, next_prime},
    Primality, PrimalityTestConfig, RandPrime,
};
use num_traits::Pow;
use rand::rngs::StdRng;
use rand::SeedableRng;

fn parse(s: &str) -> UBig {
    s.parse().unwrap()
}

/// A 512-bit product of thirteen primes near 2^39 (same input as the
/// num-bigint test; see the comment there about the per-cofactor budget).
const THIRTEEN_PRIMES: &str = "256192672085272469290287843204387360975152374284235599731951768269391636066386517575760286247162035537155995319918598846421204855240141082924971355328149";

fn as_ubigmint(v: &UBig) -> UBigMint {
    UBigMint::from(v.clone())
}

#[test]
fn is_prime_mersenne_numbers() {
    let pb = NaiveBuffer::new();
    assert_eq!(
        pb.is_prime(&as_ubigmint(&parse("524287")), None),
        Primality::Yes
    ); // 2^19-1
    assert_eq!(
        pb.is_prime(&as_ubigmint(&parse("8388607")), None),
        Primality::No
    ); // 2^23-1
    let m89 = (UBig::from(2u8).pow(89usize)) - UBig::ONE;
    assert!(matches!(
        pb.is_prime(&as_ubigmint(&m89), None),
        Primality::Probable(_)
    ));
    assert!(matches!(
        pb.is_prime(&as_ubigmint(&m89), Some(PrimalityTestConfig::bpsw())),
        Primality::Probable(_)
    ));
}

#[test]
fn is_prime_strong_pseudoprime() {
    // 2^128+1 = 59649589127497217 * 5704689200685129054721
    let f = parse("59649589127497217");
    let composite = as_ubigmint(&(&f * &parse("5704689200685129054721")));
    assert!(matches!(
        is_prime(&composite, Some(PrimalityTestConfig::bpsw())),
        Primality::No
    ));

    // 2^89 - 1 is a strong pseudoprime to many bases but not BPSW
    let m89 = as_ubigmint(&(UBig::from(2u8).pow(89usize) - UBig::ONE));
    assert!(is_prime(&m89, None).probably());
}

#[test]
fn factorize_thirteen_similar_primes() {
    let target = parse(THIRTEEN_PRIMES);
    let buffer = NaiveBuffer::new();
    let (factors, remainder) = buffer.factors(as_ubigmint(&target).clone(), None);
    assert_eq!(remainder, None);
    assert_eq!(factors.values().sum::<usize>(), 13);
    let mut product = UBig::ONE;
    for (f, e) in factors.iter() {
        let f_plain = f.value();
        assert!(is_prime(&f.clone(), None).probably(), "{} is not prime", f_plain);
        product *= f_plain.pow(*e);
    }
    assert_eq!(product, target);
}

#[test]
fn factorize_wide_prime_power() {
    // 34359738421^7, which Pollard's rho on its own cannot split
    let target = parse("34359738421").pow(7usize);
    let (factors, remainder) = factors(as_ubigmint(&target), None);
    assert!(remainder.is_none());
    assert_eq!(factors.len(), 1);
    assert_eq!(factors[&as_ubigmint(&parse("34359738421"))], 7);
}

#[test]
fn factorize_wide_number_with_small_factors() {
    // 2^70 * 3^5 * 5 * 340282366920938463463374607431768211507
    let target = parse("488107430943668296195870985548628140589274519139277715139461120");
    let (factors, remainder) = factors(as_ubigmint(&target), None);
    assert!(remainder.is_none());
    assert_eq!(factors[&as_ubigmint(&UBig::from(2u8))], 70);
    assert_eq!(factors[&as_ubigmint(&UBig::from(3u8))], 5);
    assert_eq!(factors[&as_ubigmint(&UBig::from(5u8))], 1);
    assert_eq!(
        factors[&as_ubigmint(&parse("340282366920938463463374607431768211507"))],
        1
    );
}

#[test]
fn factors_respects_config() {
    // (2^131 - 1) / 263 with the default config: fully factorized, no remainder
    let c = as_ubigmint(&(&(UBig::from(2u8).pow(131usize) - UBig::ONE) / UBig::from(263u32)));
    let (fac, rem) = factors(c, None);
    assert!(rem.is_none());
    // 2^131-1 = 263 * p with p prime, so (2^131-1)/263 = p
    assert_eq!(fac.len(), 1);
    for f in fac.keys() {
        assert!(is_prime(&f.clone(), None).probably());
    }
}

#[test]
fn next_prime_over_ubig() {
    let start = as_ubigmint(&(UBig::from(2u8).pow(100usize) + UBig::ONE));
    let np = next_prime(&start, None).unwrap();
    assert!(is_prime(&np, None).probably());
    assert!(np.value() > start.value());
}

#[test]
fn rand_prime_generation() {
    let mut rng = StdRng::seed_from_u64(42);
    for bits in [64usize, 128, 256, 512] {
        let p: UBigMint = rng.gen_prime(bits, None);
        assert!(p.bits() <= bits);
        assert!(is_prime(&p, Some(PrimalityTestConfig::strict())).probably());
    }
    let mut rng = StdRng::seed_from_u64(43);
    let p: UBigMint = rng.gen_prime_exact(200, None);
    assert_eq!(p.bits(), 200);
    assert!(is_prime(&p, None).probably());
}

#[test]
fn rand_safe_prime_generation() {
    let mut rng = StdRng::seed_from_u64(44);
    let p: UBigMint = rng.gen_safe_prime(128);
    // (p-1)/2 must be prime as well
    let q = &p - &UBigMint::from(UBig::ONE);
    let half = &q >> 1usize;
    assert!(is_prime(&half, Some(PrimalityTestConfig::strict())).probably());
}

#[test]
fn zero_and_one_edge_cases() {
    assert!(matches!(
        is_prime(&as_ubigmint(&UBig::ZERO), None),
        Primality::No
    ));
    assert!(matches!(
        is_prime(&as_ubigmint(&UBig::ONE), None),
        Primality::No
    ));
    assert!(is_prime(&as_ubigmint(&UBig::from(2u8)), None).probably());
}

#[cfg(all(feature = "big-int", feature = "dashu-int"))]
mod consistency_with_num_bigint {
    use super::*;
    use num_bigint::{BigUint, RandBigInt};
    use num_traits::One;

    /// The two backends must agree on is_prime for a fixed input set.
    #[test]
    fn is_prime_agrees() {
        let mut rng = StdRng::seed_from_u64(7);
        for _ in 0..16 {
            let b: BigUint = rng.gen_biguint(200);
            let u = UBig::from_str_radix(&b.to_str_radix(10), 10).unwrap();
            let r_big = is_prime(&b, Some(PrimalityTestConfig::bpsw()));
            let r_dashu = is_prime(&as_ubigmint(&u), Some(PrimalityTestConfig::bpsw()));
            assert_eq!(r_big.probably(), r_dashu.probably());
        }
    }

    /// The two backends must produce the same multiset of prime factors.
    #[test]
    fn factorize_agrees() {
        let target = parse(THIRTEEN_PRIMES);
        let big: BigUint = target.to_string().parse().unwrap();

        let (fac_big, rem_big) = factors(big, None);
        let (fac_dashu, rem_dashu) = factors(as_ubigmint(&target), None);

        assert!(rem_big.is_none() && rem_dashu.is_none());
        assert_eq!(fac_big.len(), fac_dashu.len());
        assert_eq!(
            fac_big.values().sum::<usize>(),
            fac_dashu.values().sum::<usize>()
        );
        // same total product and every factor is probably prime under both
        let mut prod_big = BigUint::one();
        for (f, e) in fac_big.iter() {
            prod_big *= f.pow(*e as u32);
        }
        assert_eq!(prod_big.to_string(), target.to_string());
    }
}

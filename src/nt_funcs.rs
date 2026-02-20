//! Standalone number theoretic functions
//!
//! The functions in this module can be called without an instance of [`crate::traits::PrimeBuffer`].
//! However, some functions do internally call the implementation on [`PrimeBufferExt`]
//! (especially those dependent of integer factorization). For these functions, if you have
//! to call them repeatedly, it's recommended to create a [`crate::traits::PrimeBuffer`]
//! instance and use its associated methods for better performance.
//!
//! For number theoretic functions that depends on integer factorization, strongest primality
//! check will be used in factorization, since for these functions we prefer correctness
//! over speed.
//!

use crate::buffer::{NaiveBuffer, PrimeBufferExt};
use crate::factor::{one_line, pollard_rho, squfof, SQUFOF_MULTIPLIERS};
use crate::mint::SmallMint;
use crate::primality::{PrimalityBase, PrimalityRefBase};
use crate::tables::{
    MOEBIUS_ODD, SMALL_PRIMES, SMALL_PRIMES_NEXT, WHEEL_NEXT, WHEEL_PREV, WHEEL_SIZE,
};
#[cfg(feature = "big-table")]
use crate::tables::{SMALL_PRIMES_INV, ZETA_LOG_TABLE};
use crate::traits::{FactorizationConfig, Primality, PrimalityTestConfig, PrimalityUtils};
use crate::{BitTest, ExactRoots};
use num_integer::Roots;
#[cfg(feature = "big-table")]
use num_modular::DivExact;
use num_modular::{ModularCoreOps, ModularInteger, MontgomeryInt};
use num_traits::{CheckedAdd, FromPrimitive, Num, RefNum, ToPrimitive};
use rand::random;
use std::collections::BTreeMap;
use std::convert::TryFrom;

#[cfg(feature = "big-table")]
use crate::tables::{MILLER_RABIN_BASE32, MILLER_RABIN_BASE64};

/// Fast primality test on a u64 integer. It's based on
/// deterministic Miller-rabin tests. If target is larger than 2^64 or more
/// controlled primality tests are desired, please use [is_prime()]
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::is_prime64;
///
/// assert!(is_prime64(2));
/// assert!(is_prime64(13));
/// assert!(!is_prime64(1));
/// assert!(!is_prime64(15));
/// assert!(is_prime64(6_469_693_333));
/// ```
#[cfg(not(feature = "big-table"))]
pub fn is_prime64(target: u64) -> bool {
    // shortcuts
    if target < 2 {
        return false;
    }
    if target & 1 == 0 {
        return target == 2;
    }
    if let Ok(u) = u8::try_from(target) {
        // find in the prime list if the target is small enough
        return SMALL_PRIMES.binary_search(&u).is_ok();
    } else {
        // check remainder against the wheel table
        // this step eliminates any number that is not coprime to WHEEL_SIZE
        let pos = (target % WHEEL_SIZE as u64) as usize;
        if pos == 0 || WHEEL_NEXT[pos] < WHEEL_NEXT[pos - 1] {
            return false;
        }
    }

    // Then do a deterministic Miller-rabin test
    is_prime64_miller(target)
}

/// Very fast primality test on a u64 integer is a prime number. It's based on
/// deterministic Miller-rabin tests with hashing. if target is larger than 2^64 or more controlled
/// primality tests are desired, please use [`is_prime()`]
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::is_prime64;
///
/// assert!(is_prime64(2));
/// assert!(is_prime64(13));
/// assert!(!is_prime64(1));
/// assert!(!is_prime64(15));
/// assert!(is_prime64(6_469_693_333));
/// ```
#[cfg(feature = "big-table")]
#[must_use]
pub fn is_prime64(target: u64) -> bool {
    // shortcuts
    if target < 2 {
        return false;
    }
    if target & 1 == 0 {
        return target == 2;
    }

    // remove small factors
    if target < SMALL_PRIMES_NEXT {
        // find in the prime list if the target is small enough
        return SMALL_PRIMES.binary_search(&(target as u16)).is_ok();
    } else {
        // check remainder against the wheel table
        // this step eliminates any number that is not coprime to WHEEL_SIZE
        let pos = (target % u64::from(WHEEL_SIZE)) as usize;
        if pos == 0 || WHEEL_NEXT[pos] < WHEEL_NEXT[pos - 1] {
            return false;
        }
    }

    // Then do a deterministic Miller-rabin test
    is_prime64_miller(target)
}

// Primality test for u64 with only miller-rabin tests, used during factorization.
// It assumes the target is odd, not too small and cannot be divided small primes
#[cfg(not(feature = "big-table"))]
fn is_prime64_miller(target: u64) -> bool {
    // The collection of witnesses are from http://miller-rabin.appspot.com/
    if let Ok(u) = u32::try_from(target) {
        const WITNESS32: [u32; 3] = [2, 7, 61];
        let u = SmallMint::from(u);
        WITNESS32.iter().all(|&x| u.is_sprp(SmallMint::from(x)))
    } else {
        const WITNESS64: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
        let u = SmallMint::from(target);
        WITNESS64.iter().all(|&x| u.is_sprp(SmallMint::from(x)))
    }
}

#[cfg(feature = "big-table")]
fn is_prime32_miller(target: u32) -> bool {
    let h = u64::from(target);
    let h = ((h >> 16) ^ h).wrapping_mul(0x045d_9f3b);
    let h = ((h >> 16) ^ h).wrapping_mul(0x045d_9f3b);
    let h = ((h >> 16) ^ h) & 255;
    let u = SmallMint::from(target);
    u.is_sprp(SmallMint::from(u32::from(MILLER_RABIN_BASE32[h as usize])))
}

// Primality test for u64 with only miller-rabin tests, used during factorization.
// It assumes the target is odd, not too small and cannot be divided small primes
#[cfg(feature = "big-table")]
fn is_prime64_miller(target: u64) -> bool {
    if let Ok(u) = u32::try_from(target) {
        return is_prime32_miller(u);
    }

    let u = SmallMint::from(target);
    if !u.is_sprp(2.into()) {
        return false;
    }

    let h = target;
    let h = ((h >> 32) ^ h).wrapping_mul(0x045d_9f3b_3335_b369);
    let h = ((h >> 32) ^ h).wrapping_mul(0x0333_5b36_945d_9f3b);
    let h = ((h >> 32) ^ h) & 16383;
    let b = MILLER_RABIN_BASE64[h as usize];
    u.is_sprp((u64::from(b) & 4095).into()) && u.is_sprp((u64::from(b) >> 12).into())
}

/// Fast integer factorization on a u64 target. It's based on a selection of factorization methods.
/// if target is larger than 2^128 or more controlled primality tests are desired, please use [`factors()`][crate::buffer::PrimeBufferExt::factors].
///
/// The factorization can be quite faster under 2^64 because: 1) faster and deterministic primality check,
/// 2) efficient montgomery multiplication implementation of u64
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::factorize64;
/// use std::collections::BTreeMap;
/// use std::iter::FromIterator;
///
/// let fac = factorize64(4095);
/// assert_eq!(fac, BTreeMap::from_iter([(3, 2), (5, 1), (7, 1), (13, 1)]));
///
/// let fac = factorize64(123_456_789);
/// assert_eq!(fac, BTreeMap::from_iter([(3, 2), (3607, 1), (3803, 1)]));
/// ```
#[must_use]
pub fn factorize64(target: u64) -> BTreeMap<u64, usize> {
    // TODO: improve factorization performance
    // REF: http://flintlib.org/doc/ulong_extras.html#factorisation
    //      https://mathoverflow.net/questions/114018/fastest-way-to-factor-integers-260
    //      https://hal.inria.fr/inria-00188645v3/document
    //      https://github.com/coreutils/coreutils/blob/master/src/factor.c
    //      https://github.com/uutils/coreutils/blob/master/src/uu/factor/src/cli.rs
    //      https://github.com/elmomoilanen/prime-factorization
    //      https://github.com/radii/msieve
    //      https://github.com/zademn/facto-rs
    //      Pari/GP: ifac_crack
    let mut result = BTreeMap::new();

    // quick check on factors of 2
    let f2 = target.trailing_zeros();
    if f2 == 0 {
        if is_prime64(target) {
            result.insert(target, 1);
            return result;
        }
    } else {
        result.insert(2, f2 as usize);
    }

    // trial division using primes in the table
    let tsqrt = target.sqrt() + 1;

    let mut residual = target >> f2;
    let mut factored = false;

    #[cfg(not(feature = "big-table"))]
    for p in SMALL_PRIMES.iter().skip(1).map(|&v| v as u64) {
        if p > tsqrt {
            factored = true;
            break;
        }

        while residual % p == 0 {
            residual = residual / p;
            *result.entry(p).or_insert(0) += 1;
        }
        if residual == 1 {
            factored = true;
            break;
        }
    }

    #[cfg(feature = "big-table")]
    // divisibility check with pre-computed tables, see comments on SMALL_PRIMES_INV for reference
    for (p, &pinv) in SMALL_PRIMES
        .iter()
        .map(|&p| u64::from(p))
        .zip(SMALL_PRIMES_INV.iter())
        .skip(1)
    {
        // only need to test primes up to sqrt(target)
        if p > tsqrt {
            factored = true;
            break;
        }

        let mut exp: usize = 0;
        while let Some(q) = DivExact::div_exact(residual, p, &pinv) {
            exp += 1;
            residual = q;
        }
        if exp > 0 {
            result.insert(p, exp);
        }

        if residual == 1 {
            factored = true;
            break;
        }
    }

    if factored {
        if residual != 1 {
            result.insert(residual, 1);
        }
        return result;
    }

    // then try advanced methods to find a divisor util fully factored
    for (p, exp) in factorize64_advanced(&[(residual, 1usize)]) {
        *result.entry(p).or_insert(0) += exp;
    }
    result
}

// This function factorize all cofactors after some trivial division steps
pub(crate) fn factorize64_advanced(cofactors: &[(u64, usize)]) -> Vec<(u64, usize)> {
    let mut todo: Vec<_> = cofactors.to_vec();
    let mut factored: Vec<(u64, usize)> = Vec::new(); // prime factor, exponent

    while let Some((target, exp)) = todo.pop() {
        if is_prime64_miller(target) {
            factored.push((target, exp));
            continue;
        }

        // check perfect powers before other methods, this is required for SQUFOF
        // it suffices to check square and cubic if big-table is enabled, since fifth power of
        // the smallest prime that haven't been checked is 8167^5 > 2^64
        if let Some(d) = target.sqrt_exact() {
            todo.push((d, exp * 2));
            continue;
        }
        if let Some(d) = target.cbrt_exact() {
            todo.push((d, exp * 3));
            continue;
        }

        // try to find a divisor
        let mut i = 0usize;
        let mut max_iter_ratio = 1; // increase max_iter after factorization round
        let divisor = loop {
            // try various factorization method iteratively
            const NMETHODS: usize = 3;
            match i % NMETHODS {
                0 => {
                    // Pollard's rho (quick check)
                    let start = MontgomeryInt::new(random::<u64>(), &target);
                    let offset = start.convert(random::<u64>());
                    let max_iter = max_iter_ratio << (target.bits() / 6); // unoptimized heuristic
                    if let (Some(p), _) = pollard_rho(
                        &SmallMint::from(target),
                        start.into(),
                        offset.into(),
                        max_iter,
                    ) {
                        break p.value();
                    }
                }
                1 => {
                    // Hart's one-line (quick check)
                    let mul_target = target.checked_mul(480).unwrap_or(target);
                    let max_iter = max_iter_ratio << (mul_target.bits() / 6); // unoptimized heuristic
                    if let (Some(p), _) = one_line(&target, mul_target, max_iter) {
                        break p;
                    }
                }
                2 => {
                    // Shanks's squfof (main power)
                    let mut d = None;
                    for &k in &SQUFOF_MULTIPLIERS {
                        if let Some(mul_target) = target.checked_mul(u64::from(k)) {
                            let max_iter = max_iter_ratio * 2 * mul_target.sqrt().sqrt() as usize;
                            if let (Some(p), _) = squfof(&target, mul_target, max_iter) {
                                d = Some(p);
                                break;
                            }
                        }
                    }
                    if let Some(p) = d {
                        break p;
                    }
                }
                _ => unreachable!(),
            }
            i += 1;

            // increase max iterations after trying all methods
            if i % NMETHODS == 0 {
                max_iter_ratio *= 2;
            }
        };
        todo.push((divisor, exp));
        todo.push((target / divisor, exp));
    }
    factored
}

/// Fast integer factorization on a u128 target. It's based on a selection of factorization methods.
/// if target is larger than 2^128 or more controlled primality tests are desired, please use [`factors()`][crate::buffer::PrimeBufferExt::factors].
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::factorize128;
/// use std::collections::BTreeMap;
/// use std::iter::FromIterator;
///
/// let fac = factorize128(4095);
/// assert_eq!(fac, BTreeMap::from_iter([(3, 2), (5, 1), (7, 1), (13, 1)]));
///
/// let fac = factorize128(8167u128.pow(3));
/// assert_eq!(fac, BTreeMap::from_iter([(8167, 3)]));
/// ```
#[must_use]
pub fn factorize128(target: u128) -> BTreeMap<u128, usize> {
    // shortcut for u64
    if target < (1u128 << 64) {
        return factorize64(target as u64)
            .into_iter()
            .map(|(k, v)| (u128::from(k), v))
            .collect();
    }

    let mut result = BTreeMap::new();

    // quick check on factors of 2
    let f2 = target.trailing_zeros();
    if f2 != 0 {
        result.insert(2, f2 as usize);
    }
    let mut residual = target >> f2;

    // trial division using primes in the table
    // note that p^2 is never larger than target (at least 64 bits), so we don't need to shortcut trial division
    #[cfg(not(feature = "big-table"))]
    for p in SMALL_PRIMES.iter().skip(1).map(|&v| v as u128) {
        while residual % p == 0 {
            residual = residual / p;
            *result.entry(p).or_insert(0) += 1;
        }
        if residual == 1 {
            return result;
        }
    }

    #[cfg(feature = "big-table")]
    // divisibility check with pre-computed tables, see comments on SMALL_PRIMES_INV for reference
    for (p, &pinv) in SMALL_PRIMES
        .iter()
        .map(|&p| u64::from(p))
        .zip(SMALL_PRIMES_INV.iter())
        .skip(1)
    {
        let mut exp: usize = 0;
        while let Some(q) = DivExact::div_exact(residual, p, &pinv) {
            exp += 1;
            residual = q;
        }
        if exp > 0 {
            result.insert(u128::from(p), exp);
        }

        if residual == 1 {
            return result;
        }
    }

    // then try advanced methods to find a divisor util fully factored
    for (p, exp) in factorize128_advanced(&[(residual, 1usize)]) {
        *result.entry(p).or_insert(0) += exp;
    }
    result
}

pub(crate) fn factorize128_advanced(cofactors: &[(u128, usize)]) -> Vec<(u128, usize)> {
    let (mut todo128, mut todo64) = (Vec::new(), Vec::new()); // cofactors to be processed
    let mut factored: Vec<(u128, usize)> = Vec::new(); // prime factor, exponent
    for &(co, e) in cofactors {
        if let Ok(co64) = u64::try_from(co) {
            todo64.push((co64, e));
        } else {
            todo128.push((co, e));
        };
    }

    while let Some((target, exp)) = todo128.pop() {
        if is_prime(&SmallMint::from(target), Some(PrimalityTestConfig::bpsw())).probably() {
            factored.push((target, exp));
            continue;
        }

        // check perfect powers before other methods
        // it suffices to check 2, 3, 5, 7 power if big-table is enabled, since tenth power of
        // the smallest prime that haven't been checked is 8167^10 > 2^128
        if let Some(d) = target.sqrt_exact() {
            if let Ok(d64) = u64::try_from(d) {
                todo64.push((d64, exp * 2));
            } else {
                todo128.push((d, exp * 2));
            }
            continue;
        }
        if let Some(d) = target.cbrt_exact() {
            if let Ok(d64) = u64::try_from(d) {
                todo64.push((d64, exp * 3));
            } else {
                todo128.push((d, exp * 3));
            }
            continue;
        }
        // TODO: check 5-th, 7-th power

        // try to find a divisor
        let mut i = 0usize;
        let mut max_iter_ratio = 1;

        let divisor = loop {
            // try various factorization method iteratively, sort by time per iteration
            const NMETHODS: usize = 3;
            match i % NMETHODS {
                0 => {
                    // Pollard's rho
                    let start = MontgomeryInt::new(random::<u128>(), &target);
                    let offset = start.convert(random::<u128>());
                    let max_iter = max_iter_ratio << (target.bits() / 6); // unoptimized heuristic
                    if let (Some(p), _) = pollard_rho(
                        &SmallMint::from(target),
                        start.into(),
                        offset.into(),
                        max_iter,
                    ) {
                        break p.value();
                    }
                }
                1 => {
                    // Hart's one-line
                    let mul_target = target.checked_mul(480).unwrap_or(target);
                    let max_iter = max_iter_ratio << (mul_target.bits() / 6); // unoptimized heuristic
                    if let (Some(p), _) = one_line(&target, mul_target, max_iter) {
                        break p;
                    }
                }
                2 => {
                    // Shanks's squfof, try all mutipliers
                    let mut d = None;
                    for &k in &SQUFOF_MULTIPLIERS {
                        if let Some(mul_target) = target.checked_mul(u128::from(k)) {
                            let max_iter = max_iter_ratio * 2 * mul_target.sqrt().sqrt() as usize;
                            if let (Some(p), _) = squfof(&target, mul_target, max_iter) {
                                d = Some(p);
                                break;
                            }
                        }
                    }
                    if let Some(p) = d {
                        break p;
                    }
                }
                _ => unreachable!(),
            }
            i += 1;

            // increase max iterations after trying all methods
            if i % NMETHODS == 0 {
                max_iter_ratio *= 2;
            }
        };

        if let Ok(d64) = u64::try_from(divisor) {
            todo64.push((d64, exp));
        } else {
            todo128.push((divisor, exp));
        }
        let co = target / divisor;
        if let Ok(d64) = u64::try_from(co) {
            todo64.push((d64, exp));
        } else {
            todo128.push((co, exp));
        }
    }

    // forward 64 bit cofactors
    factored.extend(
        factorize64_advanced(&todo64)
            .into_iter()
            .map(|(p, exp)| (u128::from(p), exp)),
    );
    factored
}

/// Primality test
///
/// This function re-exports [`PrimeBufferExt::is_prime()`][crate::buffer::PrimeBufferExt::is_prime()] with a new [`NaiveBuffer`] instance
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::is_prime;
///
/// assert!(is_prime(&2u64, None).probably());
/// assert!(is_prime(&13u64, None).probably());
/// assert!(!is_prime(&15u64, None).probably());
/// ```
pub fn is_prime<T: PrimalityBase>(target: &T, config: Option<PrimalityTestConfig>) -> Primality
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    NaiveBuffer::new().is_prime(target, config)
}

/// Faillible factorization
///
/// This function re-exports [`PrimeBufferExt::factors()`][crate::buffer::PrimeBufferExt::factors()] with a new [`NaiveBuffer`] instance
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::factors;
///
/// let (fac, unfactored) = factors(60u64, None);
/// assert_eq!(fac[&2], 2);
/// assert_eq!(fac[&3], 1);
/// assert_eq!(fac[&5], 1);
/// assert!(unfactored.is_none());
/// ```
pub fn factors<T: PrimalityBase>(
    target: T,
    config: Option<FactorizationConfig>,
) -> (BTreeMap<T, usize>, Option<Vec<T>>)
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    NaiveBuffer::new().factors(target, config)
}

/// Infaillible factorization
///
/// This function re-exports [`PrimeBufferExt::factorize()`][crate::buffer::PrimeBufferExt::factorize()] with a new [`NaiveBuffer`] instance
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::factorize;
///
/// let fac = factorize(60u64);
/// assert_eq!(fac[&2], 2);
/// assert_eq!(fac[&3], 1);
/// assert_eq!(fac[&5], 1);
/// ```
pub fn factorize<T: PrimalityBase>(target: T) -> BTreeMap<T, usize>
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    NaiveBuffer::new().factorize(target)
}

/// Get a list of primes under a limit
///
/// This function re-exports [`NaiveBuffer::primes()`] and collect result as a vector.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::primes;
///
/// assert_eq!(primes(20), vec![2, 3, 5, 7, 11, 13, 17, 19]);
/// assert_eq!(primes(2), vec![2]);
/// assert!(primes(1).is_empty());
/// ```
#[must_use]
pub fn primes(limit: u64) -> Vec<u64> {
    NaiveBuffer::new().into_primes(limit).collect()
}

/// Get the first n primes
///
/// This function re-exports [`NaiveBuffer::nprimes()`] and collect result as a vector.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::nprimes;
///
/// assert_eq!(nprimes(5), vec![2, 3, 5, 7, 11]);
/// assert!(nprimes(0).is_empty());
/// ```
#[must_use]
pub fn nprimes(count: usize) -> Vec<u64> {
    NaiveBuffer::new().into_nprimes(count).collect()
}

/// Calculate and return the prime π function
///
/// This function re-exports [`NaiveBuffer::prime_pi()`]
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::prime_pi;
///
/// assert_eq!(prime_pi(10), 4);  // primes: 2, 3, 5, 7
/// assert_eq!(prime_pi(100), 25);
/// ```
#[must_use]
pub fn prime_pi(limit: u64) -> u64 {
    NaiveBuffer::new().prime_pi(limit)
}

/// Get the n-th prime (n counts from 1).
///
/// This function re-exports [`NaiveBuffer::nth_prime()`]
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::nth_prime;
///
/// assert_eq!(nth_prime(1), 2);
/// assert_eq!(nth_prime(5), 11);
/// assert_eq!(nth_prime(25), 97);
/// ```
#[must_use]
pub fn nth_prime(n: u64) -> u64 {
    NaiveBuffer::new().nth_prime(n)
}

/// Calculate the primorial function
///
/// Returns the product of the first `n` primes.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::primorial;
///
/// assert_eq!(primorial::<u64>(1), 2);       // 2
/// assert_eq!(primorial::<u64>(3), 30);      // 2 * 3 * 5
/// assert_eq!(primorial::<u64>(4), 210);     // 2 * 3 * 5 * 7
/// ```
#[must_use]
pub fn primorial<T: PrimalityBase + std::iter::Product>(n: usize) -> T {
    NaiveBuffer::new()
        .into_nprimes(n)
        .map(|p| T::from_u64(p).unwrap())
        .product()
}

/// This function calculate the Möbius `μ(n)` function of the input integer `n`
///
/// This function behaves like `moebius_factorized(factorize(target))`.
/// If the input integer is very hard to factorize, it's better to use
/// the [`factors()`] function to control how the factorization is done, and then call
/// [`moebius_factorized()`].
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::moebius;
///
/// assert_eq!(moebius(&1u64), 1);    // μ(1) = 1
/// assert_eq!(moebius(&2u64), -1);   // μ(p) = -1
/// assert_eq!(moebius(&4u64), 0);    // μ(p²) = 0
/// assert_eq!(moebius(&30u64), -1);  // μ(2·3·5) = -1 (odd number of prime factors)
/// assert_eq!(moebius(&6u64), 1);    // μ(2·3) = 1 (even number of prime factors)
/// ```
///
/// # Panics
/// if the factorization failed on target.
pub fn moebius<T: PrimalityBase>(target: &T) -> i8
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    // remove factor 2
    if target.is_even() {
        let two = T::one() + T::one();
        let four = &two + &two;
        if (target % four).is_zero() {
            return 0;
        } else {
            return -moebius(&(target / &two));
        }
    }

    // look up tables when input is smaller than 256
    if let Some(v) = (target - T::one()).to_u8() {
        let m = MOEBIUS_ODD[(v >> 6) as usize];
        let m = m & (3 << (v & 63));
        let m = m >> (v & 63);
        return m as i8 - 1;
    }

    // short cut for common primes
    let three_sq = T::from_u8(9).unwrap();
    let five_sq = T::from_u8(25).unwrap();
    let seven_sq = T::from_u8(49).unwrap();
    if (target % three_sq).is_zero()
        || (target % five_sq).is_zero()
        || (target % seven_sq).is_zero()
    {
        return 0;
    }

    // then try complete factorization
    moebius_factorized(&factorize(target.clone()))
}

/// This function calculate the Möbius `μ(n)` function given the factorization
/// result of `n`
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::{moebius_factorized, factorize};
///
/// assert_eq!(moebius_factorized(&factorize(30u64)), -1); // 30 = 2·3·5
/// assert_eq!(moebius_factorized(&factorize(12u64)), 0);  // 12 = 2²·3
/// assert_eq!(moebius_factorized(&factorize(6u64)), 1);   // 6 = 2·3
/// ```
#[must_use]
pub fn moebius_factorized<T>(factors: &BTreeMap<T, usize>) -> i8 {
    if factors.values().any(|exp| exp > &1) {
        0
    } else if factors.len() % 2 == 0 {
        1
    } else {
        -1
    }
}

/// Tests if the integer doesn't have any square number factor.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::is_square_free;
///
/// assert!(is_square_free(&30u64));   // 30 = 2·3·5
/// assert!(!is_square_free(&12u64));  // 12 = 2²·3
/// assert!(is_square_free(&1u64));
/// ```
///
/// # Panics
/// if the factorization failed on target.
pub fn is_square_free<T: PrimalityBase>(target: &T) -> bool
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    moebius(target) != 0
}

/// Returns the estimated bounds (low, high) of prime π function, such that
/// low <= π(target) <= high
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::prime_pi_bounds;
///
/// let (lo, hi) = prime_pi_bounds(&1_000_000u64);
/// // π(1_000_000) = 78498
/// assert!(lo <= 78498 && 78498 <= hi);
/// ```
///
/// # Reference:
/// - \[1] Dusart, Pierre. "Estimates of Some Functions Over Primes without R.H."
///   [arxiv:1002.0442](http://arxiv.org/abs/1002.0442). 2010.
/// - \[2] Dusart, Pierre. "Explicit estimates of some functions over primes."
///   The Ramanujan Journal 45.1 (2018): 227-251.
pub fn prime_pi_bounds<T: ToPrimitive + FromPrimitive>(target: &T) -> (T, T) {
    if let Some(x) = target.to_u64() {
        // use existing primes and return exact value
        if x <= u64::from(*SMALL_PRIMES.last().unwrap()) {
            #[cfg(not(feature = "big-table"))]
            let pos = SMALL_PRIMES.binary_search(&(x as u8));
            #[cfg(feature = "big-table")]
            let pos = SMALL_PRIMES.binary_search(&(x as u16));

            let n = match pos {
                Ok(p) => p + 1,
                Err(p) => p,
            };
            return (T::from_usize(n).unwrap(), T::from_usize(n).unwrap());
        }

        // use function approximation
        let n = x as f64;
        let ln = n.ln();
        let invln = ln.recip();

        let lo = match () {
            // [2] Collary 5.3
            () if x >= 468_049 => n / (ln - 1. - invln),
            // [2] Collary 5.2
            () if x >= 88789 => n * invln * (1. + invln * (1. + 2. * invln)),
            // [2] Collary 5.3
            () if x >= 5393 => n / (ln - 1.),
            // [2] Collary 5.2
            () if x >= 599 => n * invln * (1. + invln),
            // [2] Collary 5.2
            () => n * invln,
        };
        let hi = match () {
            // [2] Theorem 5.1, valid for x > 4e9, intersects at 7.3986e9
            () if x >= 7_398_600_000 => {
                n * invln * (1. + invln * (1. + invln * (2. + invln * 7.59)))
            }
            // [1] Theorem 6.9
            () if x >= 2_953_652_287 => n * invln * (1. + invln * (1. + invln * 2.334)),
            // [2] Collary 5.3, valid for x > 5.6, intersects at 5668
            () if x >= 467_345 => n / (ln - 1. - 1.2311 * invln),
            // [2] Collary 5.2, valid for x > 1, intersects at 29927
            () if x >= 29927 => n * invln * (1. + invln * (1. + invln * 2.53816)),
            // [2] Collary 5.3, valid for x > exp(1.112), intersects at 5668
            () if x >= 5668 => n / (ln - 1.112),
            // [2] Collary 5.2, valid for x > 1, intersects at 148
            () if x >= 148 => n * invln * (1. + invln * 1.2762),
            // [2] Collary 5.2, valid for x > 1
            () => 1.25506 * n * invln,
        };
        (T::from_f64(lo).unwrap(), T::from_f64(hi).unwrap())
    } else {
        let n = target.to_f64().unwrap();
        let ln = n.ln();
        let invln = ln.recip();

        // best bounds so far
        let lo = n / (ln - 1. - invln);
        let hi = n * invln * (1. + invln * (1. + invln * (2. + invln * 7.59)));
        (T::from_f64(lo).unwrap(), T::from_f64(hi).unwrap())
    }
}

/// Returns the estimated inclusive bounds (low, high) of the n-th prime. If the result
/// is larger than maximum of `T`, [None] will be returned.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::nth_prime_bounds;
///
/// let (lo, hi) = nth_prime_bounds(&10_000u64).unwrap();
/// // The 10000th prime is 104729
/// assert!(lo <= 104729 && 104729 <= hi);
/// ```
///
/// # Reference:
/// - \[1] Dusart, Pierre. "Estimates of Some Functions Over Primes without R.H."
///   arXiv preprint [arXiv:1002.0442](https://arxiv.org/abs/1002.0442) (2010).
/// - \[2] Rosser, J. Barkley, and Lowell Schoenfeld. "Approximate formulas for some
///   functions of prime numbers." Illinois Journal of Mathematics 6.1 (1962): 64-94.
/// - \[3] Dusart, Pierre. "The k th prime is greater than k (ln k+ ln ln k-1) for k≥ 2."
///   Mathematics of computation (1999): 411-415.
/// - \[4] Axler, Christian. ["New Estimates for the nth Prime Number."](https://www.emis.de/journals/JIS/VOL22/Axler/axler17.pdf)
///   Journal of Integer Sequences 22.2 (2019): 3.
/// - \[5] Axler, Christian. [Uber die Primzahl-Zählfunktion, die n-te Primzahl und verallgemeinerte Ramanujan-Primzahlen. Diss.](http://docserv.uniduesseldorf.de/servlets/DerivateServlet/Derivate-28284/pdfa-1b.pdf)
///   `PhD` thesis, Düsseldorf, 2013.
///
/// Note that some of the results might depend on the Riemann Hypothesis. If you find
/// any prime that doesn't fall in the bound, then it might be a big discovery!
pub fn nth_prime_bounds<T: ToPrimitive + FromPrimitive>(target: &T) -> Option<(T, T)> {
    if let Some(x) = target.to_usize() {
        if x == 0 {
            return Some((T::from_u8(0).unwrap(), T::from_u8(0).unwrap()));
        }

        // use existing primes and return exact value
        if x <= SMALL_PRIMES.len() {
            let p = SMALL_PRIMES[x - 1];

            #[cfg(not(feature = "big-table"))]
            return Some((T::from_u8(p).unwrap(), T::from_u8(p).unwrap()));

            #[cfg(feature = "big-table")]
            return Some((T::from_u16(p).unwrap(), T::from_u16(p).unwrap()));
        }

        // use function approximation
        let n = x as f64;
        let ln = n.ln();
        let lnln = ln.ln();

        let lo = match () {
            // [4] Theroem 4, valid for x >= 2, intersects as 3.172e5
            () if x >= 317_200 => {
                n * (ln + lnln - 1. + (lnln - 2.) / ln
                    - (lnln * lnln - 6. * lnln + 11.321) / (2. * ln * ln))
            }
            // [1] Proposition 6.7, valid for x >= 3, intersects at 3520
            () if x >= 3520 => n * (ln + lnln - 1. + (lnln - 2.1) / ln),
            // [3] title
            () => n * (ln + lnln - 1.),
        };
        let hi = match () {
            // [4] Theroem 1, valid for x >= 46254381
            () if x >= 46_254_381 => {
                n * (ln + lnln - 1. + (lnln - 2.) / ln
                    - (lnln * lnln - 6. * lnln + 10.667) / (2. * ln * ln))
            }
            // [5] Korollar 2.11, valid for x >= 8009824
            () if x >= 8_009_824 => {
                n * (ln + lnln - 1. + (lnln - 2.) / ln
                    - (lnln * lnln - 6. * lnln + 10.273) / (2. * ln * ln))
            }
            // [1] Proposition 6.6
            () if x >= 688_383 => n * (ln + lnln - 1. + (lnln - 2.) / ln),
            // [1] Lemma 6.5
            () if x >= 178_974 => n * (ln + lnln - 1. + (lnln - 1.95) / ln),
            // [3] in "Further Results"
            () if x >= 39017 => n * (ln + lnln - 0.9484),
            // [3] in "Further Results"
            () if x >= 27076 => n * (ln + lnln - 1. + (lnln - 1.8) / ln),
            // [2] Theorem 3, valid for x >= 20
            () => n * (ln + lnln - 0.5),
        };
        Some((T::from_f64(lo)?, T::from_f64(hi)?))
    } else {
        let n = target.to_f64().unwrap();
        let ln = n.ln();
        let lnln = ln.ln();

        // best bounds so far
        let lo = n
            * (ln + lnln - 1. + (lnln - 2.) / ln
                - (lnln * lnln - 6. * lnln + 11.321) / (2. * ln * ln));
        let hi = n
            * (ln + lnln - 1. + (lnln - 2.) / ln
                - (lnln * lnln - 6. * lnln + 10.667) / (2. * ln * ln));
        Some((T::from_f64(lo)?, T::from_f64(hi)?))
    }
}

/// Test if the target is a safe prime under [Sophie German's definition](https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes). It will use the
/// [strict primality test configuration][FactorizationConfig::strict()].
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::is_safe_prime;
///
/// assert!(is_safe_prime(&5u64).probably());   // (5-1)/2 = 2, prime
/// assert!(is_safe_prime(&7u64).probably());   // (7-1)/2 = 3, prime
/// assert!(is_safe_prime(&23u64).probably());  // (23-1)/2 = 11, prime
/// assert!(!is_safe_prime(&13u64).probably()); // (13-1)/2 = 6, not prime
/// ```
pub fn is_safe_prime<T: PrimalityBase>(target: &T) -> Primality
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    let buf = NaiveBuffer::new();
    let config = Some(PrimalityTestConfig::strict());

    // test (n-1)/2 first since its smaller
    let sophie_p = buf.is_prime(&(target >> 1), config);
    if matches!(sophie_p, Primality::No) {
        return sophie_p;
    }

    // and then test target itself
    let target_p = buf.is_prime(target, config);
    target_p & sophie_p
}

/// Find the first prime number larger than `target`. If the result causes an overflow,
/// then [None] will be returned
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::next_prime;
///
/// assert_eq!(next_prime(&13u32, None), Some(17));
/// assert_eq!(next_prime(&1000u32, None), Some(1009));
/// ```
#[cfg(not(feature = "big-table"))]
pub fn next_prime<T: PrimalityBase + CheckedAdd>(
    target: &T,
    config: Option<PrimalityTestConfig>,
) -> Option<T>
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    // first search in small primes
    if let Some(x) = target.to_u8() {
        return match SMALL_PRIMES.binary_search(&x) {
            Ok(pos) => {
                if pos + 1 == SMALL_PRIMES.len() {
                    T::from_u64(SMALL_PRIMES_NEXT)
                } else {
                    T::from_u8(SMALL_PRIMES[pos + 1])
                }
            }
            Err(pos) if pos < SMALL_PRIMES.len() => T::from_u8(SMALL_PRIMES[pos]),
            Err(_) => T::from_u64(SMALL_PRIMES_NEXT),
        };
    }

    // then moving along the wheel
    let mut i = (target % T::from_u8(WHEEL_SIZE).unwrap()).to_u8().unwrap();
    let mut t = target.clone();
    loop {
        let offset = WHEEL_NEXT[i as usize];
        t = t.checked_add(&T::from_u8(offset).unwrap())?;
        i = i.addm(offset, &WHEEL_SIZE);
        if is_prime(&t, config).probably() {
            break Some(t);
        }
    }
}

/// Find the first prime number larger than `target`. If the result causes an overflow,
/// then [None] will be returned
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::next_prime;
///
/// assert_eq!(next_prime(&13u32, None), Some(17));
/// assert_eq!(next_prime(&1000u32, None), Some(1009));
/// ```
#[cfg(feature = "big-table")]
pub fn next_prime<T: PrimalityBase + CheckedAdd>(
    target: &T,
    config: Option<PrimalityTestConfig>,
) -> Option<T>
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    // first search in small primes
    if target <= &T::from_u8(255).unwrap() // shortcut for T=u8
        || target < &T::from_u16(*SMALL_PRIMES.last().unwrap()).unwrap()
    {
        let next = match SMALL_PRIMES.binary_search(&target.to_u16().unwrap()) {
            Ok(pos) => SMALL_PRIMES[pos + 1],
            Err(pos) => SMALL_PRIMES[pos],
        };
        return T::from_u16(next);
    }

    // then moving along the wheel
    let mut i = (target % T::from_u16(WHEEL_SIZE).unwrap())
        .to_u16()
        .unwrap();
    let mut t = target.clone();
    loop {
        let offset = WHEEL_NEXT[i as usize];
        t = t.checked_add(&T::from_u8(offset).unwrap())?;
        i = i.addm(u16::from(offset), &WHEEL_SIZE);
        if is_prime(&t, config).probably() {
            break Some(t);
        }
    }
}

/// Find the first prime number smaller than `target`. If target is less than 3, then [None]
/// will be returned.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::prev_prime;
///
/// assert_eq!(prev_prime(&13u32, None), Some(11));
/// assert_eq!(prev_prime(&1000u32, None), Some(997));
/// assert_eq!(prev_prime(&2u32, None), None);
/// ```
#[cfg(not(feature = "big-table"))]
pub fn prev_prime<T: PrimalityBase>(target: &T, config: Option<PrimalityTestConfig>) -> Option<T>
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    if target <= &(T::one() + T::one()) {
        return None;
    }

    // first search in small primes
    if let Some(x) = target.to_u8() {
        let next = match SMALL_PRIMES.binary_search(&x) {
            Ok(pos) => SMALL_PRIMES[pos - 1],
            Err(pos) => SMALL_PRIMES[pos - 1],
        };
        return Some(T::from_u8(next).unwrap());
    }

    // then moving along the wheel
    let mut i = (target % T::from_u8(WHEEL_SIZE).unwrap()).to_u8().unwrap();
    let mut t = target.clone();
    loop {
        let offset = WHEEL_PREV[i as usize];
        t = t - T::from_u8(offset).unwrap();
        i = i.subm(offset, &WHEEL_SIZE);
        if is_prime(&t, config).probably() {
            break Some(t);
        }
    }
}

/// Find the first prime number smaller than `target`. If target is less than 3, then [None]
/// will be returned.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::prev_prime;
///
/// assert_eq!(prev_prime(&13u32, None), Some(11));
/// assert_eq!(prev_prime(&1000u32, None), Some(997));
/// assert_eq!(prev_prime(&2u32, None), None);
/// ```
#[cfg(feature = "big-table")]
pub fn prev_prime<T: PrimalityBase>(target: &T, config: Option<PrimalityTestConfig>) -> Option<T>
where
    for<'r> &'r T: PrimalityRefBase<T>,
{
    if target <= &(T::one() + T::one()) {
        return None;
    }

    // first search in small primes
    if target <= &T::from_u8(255).unwrap() // shortcut for u8
        || target < &T::from_u16(*SMALL_PRIMES.last().unwrap()).unwrap()
    {
        let next = match SMALL_PRIMES.binary_search(&target.to_u16().unwrap()) {
            Ok(pos) => SMALL_PRIMES[pos - 1],
            Err(pos) => SMALL_PRIMES[pos - 1],
        };
        return Some(T::from_u16(next).unwrap());
    }

    // then moving along the wheel
    let mut i = (target % T::from_u16(WHEEL_SIZE).unwrap())
        .to_u16()
        .unwrap();
    let mut t = target.clone();
    loop {
        let offset = WHEEL_PREV[i as usize];
        t = t - T::from_u8(offset).unwrap();
        i = i.subm(u16::from(offset), &WHEEL_SIZE);
        if is_prime(&t, config).probably() {
            break Some(t);
        }
    }
}

/// Estimate the value of prime π() function by averaging the estimated bounds.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::{prime_pi_est, prime_pi_bounds};
///
/// let est = prime_pi_est(&1_000_000u64);
/// let (lo, hi) = prime_pi_bounds(&1_000_000u64);
/// assert!(lo <= est && est <= hi);
/// ```
#[cfg(not(feature = "big-table"))]
pub fn prime_pi_est<T: Num + ToPrimitive + FromPrimitive>(target: &T) -> T {
    let (lo, hi) = prime_pi_bounds(target);
    (lo + hi) / T::from_u8(2).unwrap()
}

/// Estimate the value of prime `π()` function by Riemann's R function. The estimation
/// error is roughly of scale O(sqrt(x)log(x)).
///
/// Reference: <https://primes.utm.edu/howmany.html#better>
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::{prime_pi_est, prime_pi_bounds};
///
/// let est = prime_pi_est(&1_000_000u64);
/// let (lo, hi) = prime_pi_bounds(&1_000_000u64);
/// assert!(lo <= est && est <= hi);
/// ```
#[cfg(feature = "big-table")]
pub fn prime_pi_est<T: ToPrimitive + FromPrimitive>(target: &T) -> T {
    // shortcut
    if let Some(x) = target.to_u16() {
        if x <= { *SMALL_PRIMES.last().unwrap() } {
            let (lo, hi) = prime_pi_bounds(&x);
            debug_assert_eq!(lo, hi);
            return T::from_u16(lo).unwrap();
        }
    }

    // Gram expansion with logarithm arithmetics
    let lnln = target.to_f64().unwrap().ln().ln();
    let mut total = 0f64;
    let mut lnp = 0f64; // k*ln(ln(x))
    let mut lnfac = 0f64; // ln(k!)

    for k in 1usize..100 {
        lnp += lnln;
        let lnk = (k as f64).ln();
        lnfac += lnk;
        let lnzeta = if k > 64 { 0f64 } else { ZETA_LOG_TABLE[k - 1] };
        let t = lnp - lnk - lnfac - lnzeta;
        if t < -4. {
            // stop if the increment is too small
            break;
        }
        total += t.exp();
    }
    T::from_f64(total + 1f64).unwrap()
}

/// Estimate the value of nth prime by bisecting on [`prime_pi_est`].
/// If the result is larger than maximum of `T`, [None] will be returned.
///
/// # Examples
///
/// ```
/// use num_prime::nt_funcs::{nth_prime_est, nth_prime_bounds};
///
/// let est = nth_prime_est(&10_000u64).unwrap();
/// let (lo, hi) = nth_prime_bounds(&10_000u64).unwrap();
/// assert!(lo <= est && est <= hi);
/// ```
pub fn nth_prime_est<T: ToPrimitive + FromPrimitive + Num + PartialOrd>(target: &T) -> Option<T>
where
    for<'r> &'r T: RefNum<T>,
{
    let (mut lo, mut hi) = nth_prime_bounds(target)?;
    if lo == hi {
        return Some(lo);
    }

    while lo != &hi - T::from_u8(1).unwrap() {
        let x = (&lo + &hi) / T::from_u8(2).unwrap();
        let mid = prime_pi_est(&x);
        if &mid < target {
            lo = x;
        } else if &mid > target {
            hi = x;
        } else {
            return Some(x);
        }
    }
    Some(lo)
}

// TODO: More functions
// REF: http://www.numbertheory.org/gnubc/bc_programs.html
// REF: https://github.com/TilmanNeumann/java-math-library
// - is_smooth: checks if the smoothness bound is at least b
// - euler_phi: Euler's totient function
// - jordan_tot: Jordan's totient function
// Others include Louiville function, Mangoldt function, Dedekind psi function, Dickman rho function, etc..

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::SliceRandom, random};
    use std::iter::FromIterator;

    #[test]
    fn is_prime64_test() {
        // test small primes
        for x in 2..100 {
            assert_eq!(SMALL_PRIMES.contains(&x), is_prime64(u64::from(x)));
        }
        assert!(is_prime64(677));

        // from PR #7
        assert!(!is_prime64(9773));
        assert!(!is_prime64(13357));
        assert!(!is_prime64(18769));

        // some large primes
        assert!(is_prime64(6_469_693_333));
        assert!(is_prime64(13_756_265_695_458_089_029));
        assert!(is_prime64(13_496_181_268_022_124_907));
        assert!(is_prime64(10_953_742_525_620_032_441));
        assert!(is_prime64(17_908_251_027_575_790_097));

        // primes from examples in Bradley Berg's hash method
        assert!(is_prime64(480_194_653));
        assert!(!is_prime64(20_074_069));
        assert!(is_prime64(8_718_775_377_449));
        assert!(is_prime64(3_315_293_452_192_821_991));
        assert!(!is_prime64(8_651_776_913_431));
        assert!(!is_prime64(1_152_965_996_591_997_761));

        // false positives reported by JASory (#4)
        assert!(!is_prime64(600_437_059_821_397));
        assert!(!is_prime64(3_866_032_210_719_337));
        assert!(!is_prime64(4_100_599_722_623_587));

        // ensure no factor for 100 random primes
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let x = random();
            if !is_prime64(x) {
                continue;
            }
            assert_ne!(x % u64::from(*SMALL_PRIMES.choose(&mut rng).unwrap()), 0);
        }

        // create random composites
        for _ in 0..100 {
            let x = u64::from(random::<u32>());
            let y = u64::from(random::<u32>());
            assert!(!is_prime64(x * y));
        }
    }

    #[test]
    fn factorize64_test() {
        // some simple cases
        let fac4095 = BTreeMap::from_iter([(3, 2), (5, 1), (7, 1), (13, 1)]);
        let fac = factorize64(4095);
        assert_eq!(fac, fac4095);

        let fac123456789 = BTreeMap::from_iter([(3, 2), (3803, 1), (3607, 1)]);
        let fac = factorize64(123_456_789);
        assert_eq!(fac, fac123456789);

        let fac1_17 = BTreeMap::from_iter([(2_071_723, 1), (5_363_222_357, 1)]);
        let fac = factorize64(11_111_111_111_111_111);
        assert_eq!(fac, fac1_17);

        // perfect powers
        for exp in 2u32..5 {
            assert_eq!(
                factorize128(8167u128.pow(exp)),
                BTreeMap::from_iter([(8167, exp as usize)])
            );
        }

        // 100 random factorization tests
        for _ in 0..100 {
            let x = random();
            let fac = factorize64(x);
            let mut prod = 1;
            for (p, exp) in fac {
                assert!(
                    is_prime64(p),
                    "factorization result should have prime factors! (get {})",
                    p
                );
                prod *= p.pow(exp as u32);
            }
            assert_eq!(x, prod, "factorization check failed! ({x} != {prod})");
        }
    }

    #[test]
    fn factorize128_test() {
        // some simple cases
        let fac_primorial19 =
            BTreeMap::from_iter(SMALL_PRIMES.iter().take(19).map(|&p| (u128::from(p), 1)));
        let fac = factorize128(7_858_321_551_080_267_055_879_090);
        assert_eq!(fac, fac_primorial19);

        let fac_smallbig = BTreeMap::from_iter([(167, 1), (2_417_851_639_229_258_349_412_369, 1)]);
        let fac = factorize128(403_781_223_751_286_144_351_865_623);
        assert_eq!(fac, fac_smallbig);

        // perfect powers
        for exp in 5u32..10 {
            // 2^64 < 8167^5 < 8167^9 < 2^128
            assert_eq!(
                factorize128(8167u128.pow(exp)),
                BTreeMap::from_iter([(8167, exp as usize)])
            );
        }

        // random factorization tests
        for _ in 0..4 {
            let x = random::<u128>() >> 28; // test 100 bit numbers
            let fac = factorize128(x);
            let mut prod = 1;
            for (p, exp) in fac {
                assert!(
                    is_prime(&p, None).probably(),
                    "factorization result should have prime factors! (get {})",
                    p
                );
                prod *= p.pow(exp as u32);
            }
            assert_eq!(x, prod, "factorization check failed! ({x} != {prod})");
        }
    }

    #[test]
    fn is_safe_prime_test() {
        // OEIS:A005385
        let safe_primes = [
            5u16, 7, 11, 23, 47, 59, 83, 107, 167, 179, 227, 263, 347, 359, 383, 467, 479, 503,
            563, 587, 719, 839, 863, 887, 983, 1019, 1187, 1283, 1307, 1319, 1367, 1439, 1487,
            1523, 1619, 1823, 1907,
        ];
        for p in SMALL_PRIMES {
            #[allow(clippy::unnecessary_cast)]
            let p = p as u16;
            if p > 1500 {
                break;
            }
            assert_eq!(
                is_safe_prime(&p).probably(),
                safe_primes.iter().any(|v| &p == v)
            );
        }
    }

    #[test]
    fn moebius_test() {
        // test small examples
        let mu20: [i8; 20] = [
            1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0,
        ];
        for (i, &expected) in mu20.iter().enumerate() {
            assert_eq!(moebius(&(i + 1)), expected, "moebius on {i}");
        }

        // some square numbers
        assert_eq!(moebius(&1024u32), 0);
        assert_eq!(moebius(&(8081u32 * 8081)), 0);

        // sphenic numbers
        let sphenic3: [u8; 20] = [
            30, 42, 66, 70, 78, 102, 105, 110, 114, 130, 138, 154, 165, 170, 174, 182, 186, 190,
            195, 222,
        ]; // OEIS:A007304
        for &val in &sphenic3 {
            assert_eq!(moebius(&val), -1i8, "moebius on {val}");
        }
        let sphenic5: [u16; 23] = [
            2310, 2730, 3570, 3990, 4290, 4830, 5610, 6006, 6090, 6270, 6510, 6630, 7410, 7590,
            7770, 7854, 8610, 8778, 8970, 9030, 9282, 9570, 9690,
        ]; // OEIS:A046387
        for &val in sphenic5.iter().take(20) {
            assert_eq!(moebius(&val), -1i8, "moebius on {val}");
        }
    }

    #[test]
    fn prime_pi_bounds_test() {
        fn check(n: u64, pi: u64) {
            let (lo, hi) = prime_pi_bounds(&n);
            let est = prime_pi_est(&n);
            assert!(
                lo <= pi && pi <= hi,
                "fail to satisfy {} <= pi({}) = {} <= {}",
                lo,
                n,
                pi,
                hi
            );
            assert!(lo <= est && est <= hi);
        }

        // test with sieved primes
        let mut pb = NaiveBuffer::new();
        let mut last = 0;
        for (i, p) in pb.primes(100_000).copied().enumerate() {
            for j in last..p {
                check(j, i as u64);
            }
            last = p;
        }

        // test with some known cases with input as 10^n, OEIS:A006880
        let pow10_values = [
            0,
            4,
            25,
            168,
            1229,
            9592,
            78498,
            664_579,
            5_761_455,
            50_847_534,
            455_052_511,
            4_118_054_813,
            37_607_912_018,
            346_065_536_839,
            3_204_941_750_802,
            29_844_570_422_669,
            279_238_341_033_925,
            2_623_557_157_654_233,
        ];
        for (exponent, gt) in pow10_values.iter().enumerate() {
            let n = 10u64.pow(exponent as u32);
            check(n, *gt);
        }
    }

    #[test]
    fn nth_prime_bounds_test() {
        fn check(n: u64, p: u64) {
            let (lo, hi) = super::nth_prime_bounds(&n).unwrap();
            assert!(
                lo <= p && p <= hi,
                "fail to satisfy: {} <= {}-th prime = {} <= {}",
                lo,
                n,
                p,
                hi
            );
            let est = super::nth_prime_est(&n).unwrap();
            assert!(lo <= est && est <= hi);
        }

        // test with sieved primes
        let mut pb = NaiveBuffer::new();
        for (i, p) in pb.primes(100_000).copied().enumerate() {
            check(i as u64 + 1, p);
        }

        // test with some known cases with input as 10^n, OEIS:A006988
        let pow10_values = [
            2,
            29,
            541,
            7919,
            104_729,
            1_299_709,
            15_485_863,
            179_424_673,
            2_038_074_743,
            22_801_763_489,
            252_097_800_623,
            2_760_727_302_517,
            29_996_224_275_833,
            323_780_508_946_331,
            3_475_385_758_524_527,
            37_124_508_045_065_437,
        ];
        for (exponent, nth_prime) in pow10_values.iter().enumerate() {
            let n = 10u64.pow(exponent as u32);
            check(n, *nth_prime);
        }
    }

    #[test]
    fn prev_next_test() {
        assert_eq!(prev_prime(&2u32, None), None);

        // prime table boundary test
        assert_eq!(prev_prime(&257u16, None), Some(251));
        assert_eq!(next_prime(&251u16, None), Some(257));
        assert_eq!(next_prime(&251u8, None), None);
        assert_eq!(prev_prime(&8167u16, None), Some(8161));
        assert_eq!(next_prime(&8161u16, None), Some(8167));

        // OEIS:A077800
        let twine_primes: [(u32, u32); 8] = [
            (2, 3), // not exactly twine
            (3, 5),
            (5, 7),
            (11, 13),
            (17, 19),
            (29, 31),
            (41, 43),
            (617, 619),
        ];
        for (p1, p2) in twine_primes {
            assert_eq!(prev_prime(&p2, None).unwrap(), p1);
            assert_eq!(next_prime(&p1, None).unwrap(), p2);
        }

        let adj10_primes: [(u32, u32); 7] = [
            (7, 11),
            (97, 101),
            (997, 1009),
            (9973, 10007),
            (99991, 100_003),
            (999_983, 1_000_003),
            (9_999_991, 10_000_019),
        ];
        for (i, (p1, p2)) in adj10_primes.iter().enumerate() {
            assert_eq!(prev_prime(p2, None).unwrap(), *p1);
            assert_eq!(next_prime(p1, None).unwrap(), *p2);

            let pow = 10u32.pow((i + 1) as u32);
            assert_eq!(prev_prime(&pow, None).unwrap(), *p1);
            assert_eq!(next_prime(&pow, None).unwrap(), *p2);
        }
    }

    #[test]
    fn factors_overflow_test() {
        // Test for issue #23: multiplication overflow in one_line factorization
        // This should not panic in debug builds
        let problematic_number = 0x3ffffffffffffff8u64;
        let (factors_map, cofactors) = factors(problematic_number, None);

        // Verify that we get the correct factorization: 2^3 × 179951 × 3203431780337
        // The function should not panic due to overflow
        assert!(!factors_map.is_empty(), "Should find at least some factors");

        // Verify the product of all factors equals the original number
        let mut product = 1u64;
        for (factor, count) in &factors_map {
            product = product
                .checked_mul(factor.pow(*count as u32))
                .expect("Product computation should not overflow");
        }
        if let Some(ref remaining) = cofactors {
            for cofactor in remaining {
                product = product
                    .checked_mul(*cofactor)
                    .expect("Product computation should not overflow");
            }
        }
        assert_eq!(
            product, problematic_number,
            "Product of factors should equal original number"
        );
    }
}

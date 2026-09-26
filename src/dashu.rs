//! Pollard's rho over Montgomery arithmetic for [`UBig`].
//!
//! This mirrors [`crate::montgomery`], which serves the `num-bigint` backend:
//! the generic [`pollard_rho`][crate::factor::pollard_rho] pays a full
//! division per modular multiplication, while Montgomery form replaces them
//! with multiplication-only REDC steps. The reduction machinery comes from
//! `dashu-int`'s [`MontgomeryRepr`], which is also the reducer behind
//! [`UBigMint`][crate::detail::UBigMint].
//!
//! Only enabled when the `big-int` feature is absent: when both backends are
//! compiled in, the factorization split keeps using the original `num-bigint`
//! path for all types.

use dashu_base::BitTest as _;
use dashu_int::{monty::MontgomeryRepr, UBig};
use num_integer::Integer;
use num_traits::ToPrimitive as _;

use crate::traits::BitTest;

/// Pollard's rho with Brent's cycle detection, over Montgomery arithmetic.
///
/// Both walkers live in Montgomery form; their differences accumulate into
/// `prod`, whose gcd with `n` is taken once per batch. When the sequence
/// cycles without splitting `n`, the polynomial constant `c` moves on.
fn rho(n: &UBig) -> UBig {
    /// Differences accumulated into `prod` per gcd. A bigger batch trades
    /// steps wasted past the split for fewer of the gcds, which dominate.
    const BATCH: usize = 128;

    let ring = MontgomeryRepr::new(n.clone());
    let one = ring.reduce(UBig::ONE);
    // 2 in Montgomery form, the common starting point of both walkers.
    let start = ring.reduce(UBig::from(2u8));
    let zero = ring.reduce(UBig::ZERO);

    let mut tortoise = start.clone();
    let mut hare = start.clone();
    let mut prod = one.clone();

    // c starts at 1 rather than 0 because x^2 + 2 opens better than x^2 + 1
    // (~35% on the hard factorization benchmarks for the num-bigint path).
    let mut c: u64 = 1;
    // the polynomial constant in Montgomery form, recomputed on restarts only
    let mut add = ring.reduce(UBig::from(c));
    let mut steps = 0usize;
    loop {
        if tortoise == hare {
            // The sequence cycled without splitting n: start over under the
            // next polynomial, keeping what prod holds.
            c += 1;
            add = ring.reduce(UBig::from(c));
            tortoise = start.clone();
            hare = start.clone();
        }

        let next = &prod * &(&tortoise - &hare);
        // keep the previous product if the difference vanished (both walkers
        // met); the cycle branch above restarts under the next polynomial
        if next != zero {
            prod = next;
        }

        // The tortoise takes one step, the hare two.
        tortoise = &tortoise.sqr() + &add;
        hare = &(&hare.sqr() + &add).sqr() + &add;

        steps += 1;
        if steps == BATCH {
            steps = 0;
            // one REDC per batch converts the product back to plain form
            let gcd = prod.residue().gcd(n);
            if !gcd.is_one() {
                return gcd;
            }
        }
    }
}

/// If `x` is a perfect power, return its root and the exponent.
///
/// Pollard's rho needs about `sqrt(p)` iterations to split `p^k`, which is
/// hopeless for a large `p`, so these are peeled off beforehand.
fn perfect_power(x: &UBig) -> Option<(UBig, u32)> {
    let bits = x.bit_len() as u32;
    for e in 2..=bits {
        // A perfect power is a perfect power for a prime exponent too.
        if (2..).take_while(|d| d * d <= e).any(|d| e % d == 0) {
            continue;
        }
        let root = x.nth_root(e as usize);
        if root.is_one() {
            break;
        }
        if root.pow(e as usize) == *x {
            return Some((root, e));
        }
    }
    None
}

/// Widen an arbitrary integer into a [`UBig`], bit by bit.
///
/// This is only ever called on targets that do not fit in a `u128`, where the
/// cost is negligible next to the factorization that follows.
pub(crate) fn to_ubig<T: BitTest>(x: &T) -> UBig {
    let mut bytes = vec![0u8; (x.bits() + 7) / 8];
    for i in 0..x.bits() {
        if x.bit(i) {
            bytes[i / 8] |= 1 << (i % 8);
        }
    }
    UBig::from_le_bytes(&bytes)
}

/// Narrow a [`UBig`] back into the caller's integer type.
///
/// The value must fit in `T`'s range; this is only called on divisor results
/// of the factorization split, which divide the original (already-`T`) target.
pub(crate) fn from_ubig<T: Integer + Clone + num_traits::FromPrimitive>(x: &UBig) -> T {
    // fast path: the value fits a u64 (the common case for divisors found by
    // trial division on wide targets)
    if let Some(v) = x.to_u64() {
        return T::from_u64(v).expect("value fits in the caller's type");
    }

    let shift = T::from_u128(1u128 << 32).expect("multi-word targets are at least 64 bit wide");
    let bytes = x.to_le_bytes();
    let mut acc = T::zero();
    // the trailing chunk may be shorter than 4 bytes; pad it with zeros
    for chunk in bytes.rchunks(4) {
        let mut digit = [0u8; 4];
        digit[..chunk.len()].copy_from_slice(chunk);
        acc = acc * shift.clone() + T::from_u32(u32::from_le_bytes(digit)).unwrap();
    }
    acc
}

/// A non-trivial divisor of the odd composite `n`, or the factorization of a
/// perfect power as `(root, exponent)`.
pub(crate) enum Split {
    Divisor(UBig),
    Power(UBig, u32),
}

/// Split the odd composite `n`, which must be larger than `u128::MAX`.
pub(crate) fn divisor(n: &UBig) -> Split {
    match perfect_power(n) {
        Some((root, exp)) => Split::Power(root, exp),
        None => Split::Divisor(rho(n)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    fn parse(s: &str) -> UBig {
        s.parse().unwrap()
    }

    #[test]
    fn rho_finds_factor() {
        // 2^67 - 1 = 193707721 * 761838257287
        let n = parse("147573952589676412927");
        let d = rho(&n);
        assert!(d > UBig::one() && d < n);
        assert_eq!(&n % &d, UBig::ZERO);
    }

    #[test]
    fn divisor_splits_semiprime() {
        let n = parse("1180591625390335725871");
        match divisor(&n) {
            Split::Divisor(d) => {
                assert!(d > UBig::one() && d < n);
                assert_eq!(&n % &d, UBig::ZERO);
            }
            Split::Power(..) => panic!("not a perfect power"),
        }
    }

    #[test]
    fn perfect_power_detection() {
        // 34359738421^7, which Pollard's rho cannot split at all
        let base = parse("34359738421");
        let x = base.pow(7usize);
        assert_eq!(perfect_power(&x), Some((base, 7)));

        assert_eq!(perfect_power(&parse("1180591625390335725871")), None);
    }

    #[test]
    fn ubig_roundtrip() {
        let n = parse("123456789012345678901234567890123456789");
        let narrow: u128 = from_ubig(&n);
        assert_eq!(UBig::from(narrow), n);

        let narrow: u32 = from_ubig(&parse("42"));
        assert_eq!(narrow, 42);
    }
}

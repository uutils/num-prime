//! Pollard's rho over Montgomery arithmetic for arbitrary-precision integers.
//!
//! The generic [`pollard_rho`][crate::factor::pollard_rho] reduces through
//! [`ModularCoreOps`][num_modular::ModularCoreOps], which for [`BigUint`] means
//! a full division per modular multiplication. Keeping the modulus in
//! Montgomery form instead removes those divisions, which is worth roughly a
//! factor of five on the numbers where rho actually spends its time.

use core::cmp::Ordering;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{FromPrimitive, One};

use crate::traits::BitTest;

/// Montgomery arithmetic modulo an odd `n`, held as little-endian 64-bit limbs.
///
/// Values are plain residues in `[0, n)`; [`Montgomery::mulredc`] computes
/// `lhs * rhs * R^-1 mod n` rather than `lhs * rhs mod n`. Pollard's rho does
/// not care: the iteration stays a pseudo-random map, and the extra powers of
/// `R^-1` accumulated in the gcd product are units modulo `n`.
struct Montgomery {
    n: Vec<u64>,
    /// `-n^-1 mod 2^64`
    n0inv: u64,
}

/// `x^-1 mod 2^64`, for odd `x`, by Newton's iteration.
fn binv(x: u64) -> u64 {
    // x is its own inverse modulo 8, and each step doubles the correct bits.
    let mut y = x;
    for _ in 0..5 {
        y = y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y)));
    }
    y
}

fn to_limbs(x: &BigUint, len: usize) -> Vec<u64> {
    let mut limbs: Vec<u64> = x.iter_u64_digits().collect();
    limbs.resize(len, 0);
    limbs
}

fn from_limbs(limbs: &[u64]) -> BigUint {
    let mut bytes = Vec::with_capacity(limbs.len() * 8);
    for limb in limbs {
        bytes.extend_from_slice(&limb.to_le_bytes());
    }
    BigUint::from_bytes_le(&bytes)
}

impl Montgomery {
    /// `n` must be odd and larger than one.
    fn new(n: &BigUint) -> Self {
        let n: Vec<u64> = n.iter_u64_digits().collect();
        let n0inv = binv(n[0]).wrapping_neg();
        Montgomery { n, n0inv }
    }

    fn len(&self) -> usize {
        self.n.len()
    }

    /// Whether `x`, extended with `high` as its most significant limb, is `>= n`.
    fn geq(&self, x: &[u64], high: u64) -> bool {
        if high != 0 {
            return true;
        }
        for (a, b) in x.iter().zip(&self.n).rev() {
            match a.cmp(b) {
                Ordering::Equal => (),
                other => return other == Ordering::Greater,
            }
        }
        true
    }

    /// `x -= n`, dropping the borrow out of the most significant limb.
    fn sub_n(&self, x: &mut [u64]) {
        let mut borrow = 0u64;
        for (a, b) in x.iter_mut().zip(&self.n) {
            let (d, b1) = a.overflowing_sub(*b);
            let (d, b2) = d.overflowing_sub(borrow);
            *a = d;
            borrow = (b1 | b2) as u64;
        }
    }

    /// `out = lhs * rhs * R^-1 mod n`, by the CIOS variant of Montgomery
    /// multiplication. `acc` is scratch space of `n.len() + 2` limbs.
    fn mulredc(&self, lhs: &[u64], rhs: &[u64], out: &mut [u64], acc: &mut [u64]) {
        let len = self.len();
        for limb in acc.iter_mut() {
            *limb = 0;
        }

        for &rhs_i in &rhs[..len] {
            let rhs_i = rhs_i as u128;
            let mut carry = 0u128;
            for j in 0..len {
                let cur = acc[j] as u128 + lhs[j] as u128 * rhs_i + carry;
                acc[j] = cur as u64;
                carry = cur >> 64;
            }
            let cur = acc[len] as u128 + carry;
            acc[len] = cur as u64;
            acc[len + 1] = (cur >> 64) as u64;

            let quot = acc[0].wrapping_mul(self.n0inv) as u128;
            // The low limb of acc[0] + quot * n[0] is zero by construction of quot.
            let mut carry = (acc[0] as u128 + quot * self.n[0] as u128) >> 64;
            for j in 1..len {
                let cur = acc[j] as u128 + quot * self.n[j] as u128 + carry;
                acc[j - 1] = cur as u64;
                carry = cur >> 64;
            }
            let cur = acc[len] as u128 + carry;
            acc[len - 1] = cur as u64;
            acc[len] = acc[len + 1] + (cur >> 64) as u64;
        }

        out.copy_from_slice(&acc[..len]);
        // With lhs, rhs < n the CIOS result is below 2n, so one subtraction
        // normalizes it.
        if self.geq(out, acc[len]) {
            self.sub_n(out);
        }
    }

    /// `x = x + c mod n`, for `c` smaller than `n`.
    fn addc(&self, x: &mut [u64], c: u64) {
        let mut carry = c as u128;
        for limb in x.iter_mut() {
            let cur = *limb as u128 + carry;
            *limb = cur as u64;
            carry = cur >> 64;
        }
        if self.geq(x, carry as u64) {
            self.sub_n(x);
        }
    }

    /// `out = lhs + rhs mod n`.
    fn add(&self, lhs: &[u64], rhs: &[u64], out: &mut [u64]) {
        let mut carry = 0u128;
        for (i, out_i) in out.iter_mut().enumerate() {
            let cur = lhs[i] as u128 + rhs[i] as u128 + carry;
            *out_i = cur as u64;
            carry = cur >> 64;
        }
        if self.geq(out, carry as u64) {
            self.sub_n(out);
        }
    }

    /// `out = lhs - rhs mod n`.
    fn sub(&self, lhs: &[u64], rhs: &[u64], out: &mut [u64]) {
        let mut borrow = 0u64;
        for (i, out_i) in out.iter_mut().enumerate() {
            let (diff, borrow1) = lhs[i].overflowing_sub(rhs[i]);
            let (diff, borrow2) = diff.overflowing_sub(borrow);
            *out_i = diff;
            borrow = (borrow1 | borrow2) as u64;
        }
        if borrow != 0 {
            let mut carry = 0u128;
            for (out_i, n_i) in out.iter_mut().zip(&self.n) {
                let cur = *out_i as u128 + *n_i as u128 + carry;
                *out_i = cur as u64;
                carry = cur >> 64;
            }
        }
    }
}

/// Find a non-trivial divisor of the odd composite `n` with Pollard's rho.
///
/// `n` must be odd, larger than one, composite, and not a perfect power;
/// [`divisor`] establishes all of that. The search is unbounded: rho will
/// always split such an `n` eventually, so the only question is how long it
/// takes.
///
/// Floyd's cycle detection over `x -> x^2 + c`, with the differences
/// accumulated into a product so that a single gcd covers a whole batch of
/// them. Keeping the last non-zero product rather than the current one is what
/// makes that batch safe: the accumulator never reaches zero, so `gcd(prod, n)`
/// can never be `n`, and a gcd that is not one is already a proper divisor --
/// there is no batch to replay and no failure to recover from. The tortoise
/// catching the hare means the sequence cycled without splitting `n`, so `c`
/// moves on to the next polynomial.
///
/// Modelled on KACTL's `content/number-theory/Factor.h` (CC0-1.0), specialized
/// to Montgomery arithmetic and to a gcd over [`BigUint`].
fn pollard_rho(n: &BigUint) -> BigUint {
    rho(n).0
}

/// [`pollard_rho`], also reporting the polynomial constant that split `n`.
///
/// Only the divisor is of interest in anger; the tests use `c` to tell a split
/// found under the opening polynomial from one that needed a later.
fn rho(n: &BigUint) -> (BigUint, u64) {
    /// Differences accumulated into `prod` per gcd. A bigger batch trades
    /// steps wasted past the split for fewer of the gcds, which dominate.
    const BATCH: usize = 128;

    let mont = Montgomery::new(n);
    let len = mont.len();
    let mut scratch = vec![0u64; len + 2];
    // 1 in Montgomery form, i.e. R mod n.
    let one = to_limbs(&((BigUint::one() << (64 * len)) % n), len);

    let mut diff = vec![0u64; len];
    let mut next = vec![0u64; len];

    // Both walkers start at 2 in Montgomery form; prod accumulates the
    // differences whose gcd with n is taken once per batch.
    let mut tortoise = vec![0u64; len];
    mont.add(&one, &one, &mut tortoise);
    let start = tortoise.clone();
    let mut hare = tortoise.clone();
    let mut prod = one;

    // Both walkers start equal, so the opening pass through the cycled branch
    // below is what picks the first polynomial: c is a "none yet" sentinel
    // until then. It starts at 1 rather than 0 because x^2 + 2 opens better
    // than x^2 + 1 -- ~35% on the hard factorization benchmarks.
    let mut c = 1u64;
    let mut steps = 0usize;
    loop {
        if tortoise == hare {
            // The sequence cycled without splitting n: start over from the
            // same point under the next polynomial, keeping what prod holds.
            c += 1;
            tortoise.copy_from_slice(&start);
            hare.copy_from_slice(&start);
        }

        mont.sub(&tortoise, &hare, &mut diff);
        mont.mulredc(&prod, &diff, &mut next, &mut scratch);
        if next.iter().any(|&limb| limb != 0) {
            prod.copy_from_slice(&next);
        }

        // The tortoise takes one step, the hare two.
        mont.mulredc(&tortoise, &tortoise, &mut next, &mut scratch);
        core::mem::swap(&mut tortoise, &mut next);
        mont.addc(&mut tortoise, c);
        for _ in 0..2 {
            mont.mulredc(&hare, &hare, &mut next, &mut scratch);
            core::mem::swap(&mut hare, &mut next);
            mont.addc(&mut hare, c);
        }

        steps += 1;
        if steps == BATCH {
            steps = 0;
            let gcd = from_limbs(&prod).gcd(n);
            if !gcd.is_one() {
                return (gcd, c);
            }
        }
    }
}

/// If `x` is a perfect power, return its root and the exponent.
///
/// Pollard's rho needs about `sqrt(p)` iterations to split `p^k`, which is
/// hopeless for a large `p`, so these are peeled off beforehand.
fn perfect_power(x: &BigUint) -> Option<(BigUint, u32)> {
    let bits = x.bits() as u32;
    for e in 2..=bits {
        // A perfect power is a perfect power for a prime exponent too.
        if (2..).take_while(|d| d * d <= e).any(|d| e % d == 0) {
            continue;
        }
        let root = x.nth_root(e);
        if root.is_one() {
            break;
        }
        if root.pow(e) == *x {
            return Some((root, e));
        }
    }
    None
}

/// Widen an arbitrary integer into a [`BigUint`], bit by bit.
///
/// This is only ever called on targets that do not fit in a `u128`, where the
/// cost is negligible next to the factorization that follows.
pub(crate) fn to_biguint<T: BitTest>(x: &T) -> BigUint {
    let mut bytes = vec![0u8; (x.bits() + 7) / 8];
    for i in 0..x.bits() {
        if x.bit(i) {
            bytes[i / 8] |= 1 << (i % 8);
        }
    }
    BigUint::from_bytes_le(&bytes)
}

/// Narrow a [`BigUint`] back into the caller's integer type.
pub(crate) fn from_biguint<T: Integer + Clone + FromPrimitive>(x: &BigUint) -> T {
    let shift = T::from_u64(1 << 32).unwrap();
    let mut acc = T::zero();
    for digit in x.iter_u32_digits().rev() {
        acc = acc * shift.clone() + T::from_u32(digit).unwrap();
    }
    acc
}

/// A non-trivial divisor of the odd composite `n`, or the factorization of a
/// perfect power as `(root, exponent)`.
pub(crate) enum Split {
    Divisor(BigUint),
    Power(BigUint, u32),
}

/// Split the odd composite `n`, which must be larger than `u128::MAX`.
pub(crate) fn divisor(n: &BigUint) -> Split {
    match perfect_power(n) {
        Some((root, exp)) => Split::Power(root, exp),
        None => Split::Divisor(pollard_rho(n)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    fn parse(s: &str) -> BigUint {
        s.parse().unwrap()
    }

    fn check_divisor(s: &str) -> BigUint {
        let n = parse(s);
        match divisor(&n) {
            Split::Divisor(d) => {
                assert!(d > BigUint::one(), "trivial divisor of {}", n);
                assert!(d < n, "trivial divisor of {}", n);
                assert!((&n % &d).is_zero(), "{} does not divide {}", d, n);
                d
            }
            Split::Power(root, exp) => panic!("unexpected perfect power {}^{}", root, exp),
        }
    }

    /// The point of keeping the last non-zero product: when Floyd's walkers
    /// meet without having split `n`, the polynomial constant advances and the
    /// walk restarts, carrying `prod` over. Only small moduli cycle soon
    /// enough to reach that branch -- the wide ones this module is built for
    /// split long before their sequences close.
    #[test]
    fn advances_the_polynomial_when_the_sequence_cycles() {
        for n in [35u64, 1_000_025, 1_000_027] {
            let big = BigUint::from(n);
            let (d, c) = rho(&big);
            assert!(c > 2, "{} split under the opening polynomial", n);
            assert!(
                d > BigUint::one() && d < big,
                "trivial divisor {} of {}",
                d,
                n
            );
            assert!((&big % &d).is_zero(), "{} does not divide {}", d, n);
        }
    }

    /// The counterpart: a modulus of the size this module actually sees splits
    /// under the opening polynomial, without ever taking that branch.
    #[test]
    fn a_wide_semiprime_splits_under_the_opening_polynomial() {
        let (_, c) = rho(&parse("1180591625390335725871"));
        assert_eq!(c, 2);
    }

    #[test]
    fn binv_inverts_odd_words() {
        for x in [1u64, 3, 5, 0xffff_ffff_ffff_ffff, 0x9e37_79b9_7f4a_7c15] {
            assert_eq!(x.wrapping_mul(binv(x)), 1);
        }
    }

    #[test]
    fn limb_roundtrip() {
        let n = parse("340282366920938463463374607431768211507");
        assert_eq!(from_limbs(&to_limbs(&n, 4)), n);
    }

    #[test]
    fn biguint_roundtrip() {
        let n = parse("340282366920938463463374607431768211507");
        assert_eq!(to_biguint(&n), n);
        assert_eq!(from_biguint::<BigUint>(&n), n);
        let narrow: u128 = 340_282_366_920_938_463_463_374_607_431_768_211_455;
        assert_eq!(to_biguint(&narrow), BigUint::from(narrow));
        assert_eq!(from_biguint::<u128>(&BigUint::from(narrow)), narrow);
    }

    #[test]
    fn mulredc_matches_plain_arithmetic() {
        let n = parse("340282366920938463463374607431768211507");
        let mont = Montgomery::new(&n);
        let len = mont.len();
        let r = (BigUint::one() << (64 * len)) % &n;
        let r_inv = {
            // R^-1 mod n, by Fermat's little theorem (n is prime here).
            r.modpow(&(&n - BigUint::from(2u32)), &n)
        };
        let mut scratch = vec![0u64; len + 2];
        let mut out = vec![0u64; len];
        for (a, b) in [("2", "3"), ("123456789", "987654321"), ("0", "7")] {
            let (a, b) = (parse(a) % &n, parse(b) % &n);
            mont.mulredc(
                &to_limbs(&a, len),
                &to_limbs(&b, len),
                &mut out,
                &mut scratch,
            );
            assert_eq!(from_limbs(&out), (&a * &b * &r_inv) % &n, "{} * {}", a, b);
        }
    }

    #[test]
    fn add_sub_wrap_around_the_modulus() {
        let n = parse("340282366920938463463374607431768211507");
        let mont = Montgomery::new(&n);
        let len = mont.len();
        let a = &n - BigUint::from(1u32);
        let b = BigUint::from(5u32);
        let mut out = vec![0u64; len];

        mont.add(&to_limbs(&a, len), &to_limbs(&b, len), &mut out);
        assert_eq!(from_limbs(&out), (&a + &b) % &n);

        mont.sub(&to_limbs(&b, len), &to_limbs(&a, len), &mut out);
        assert_eq!(from_limbs(&out), (&b + &n - &a) % &n);

        let mut x = to_limbs(&a, len);
        mont.addc(&mut x, 5);
        assert_eq!(from_limbs(&x), (&a + &b) % &n);
    }

    #[test]
    fn splits_a_semiprime() {
        // 34359738421 * 34359738451
        let d = check_divisor("1180591625390335725871");
        assert!(d == parse("34359738421") || d == parse("34359738451"));
    }

    #[test]
    fn splits_a_product_of_thirteen_similar_primes() {
        check_divisor(
            "256192672085272469290287843204387360975152374284235599731951768269391636066386517575760286247162035537155995319918598846421204855240141082924971355328149",
        );
    }

    #[test]
    fn splits_a_square_free_number_with_a_tiny_factor() {
        // 3 * (2^127 - 1) -- one factor far smaller than the other
        let d = check_divisor("510423550381407695195061911147652317181");
        assert!(d == parse("3") || d == parse("170141183460469231731687303715884105727"));
    }

    #[test]
    fn detects_perfect_powers() {
        // 34359738421^5
        let n = parse("47890486021415120313827563670912728827215402664536101");
        match divisor(&n) {
            Split::Power(root, exp) => {
                assert_eq!(root, parse("34359738421"));
                assert_eq!(exp, 5);
            }
            Split::Divisor(d) => panic!("expected a perfect power, got {}", d),
        }
    }

    #[test]
    fn detects_a_square_of_a_composite() {
        // (34359738421 * 34359738451)^2
        let n = parse("1393796585941794802955558839641240458708641");
        match divisor(&n) {
            Split::Power(root, exp) => {
                assert_eq!(root, parse("1180591625390335725871"));
                assert_eq!(exp, 2);
            }
            Split::Divisor(d) => panic!("expected a perfect power, got {}", d),
        }
    }
}

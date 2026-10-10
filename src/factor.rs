//! Implementations for various factorization algorithms.
//!
//! Note general prime number field sieve is not planned to be implemented, since it's too complex
//!
//! See <https://web.archive.org/web/20110331180514/https://diamond.boisestate.edu/~liljanab/BOISECRYPTFall09/Jacobsen.pdf>
//! for a detailed comparison between different factorization algorithms

// XXX: make the factorization method resumable? Maybe let all of them returns a Future

#[cfg(feature = "big-table")]
use crate::tables::{SMALL_PRIMES, SMALL_PRIMES_INV};
use crate::traits::ExactRoots;
use num_integer::{Integer, Roots};
use num_modular::{DivExact, ModularCoreOps, ModularUnaryOps, PreModInv};
use num_traits::{CheckedAdd, CheckedMul, FromPrimitive, NumRef, PrimInt, RefNum, ToPrimitive};
use std::collections::BTreeMap;

/// Get the precomputed modular inverse of the prime at position `i` of the iterator.
///
/// The prime iterator is not guaranteed to follow [`SMALL_PRIMES`], so the alignment
/// is verified before the precomputed value is used. Returns `None` if the build
/// doesn't provide the precomputed inverses or if `p` is not covered by them.
#[cfg(feature = "big-table")]
#[inline]
fn small_prime_inv(i: usize, p: u64) -> Option<&'static PreModInv<u64>> {
    // the entry for 2 is a placeholder: factor 2 must be handled by bit tests
    if p != 2 && SMALL_PRIMES.get(i).is_some_and(|&q| u64::from(q) == p) {
        SMALL_PRIMES_INV.get(i)
    } else {
        None
    }
}

#[cfg(not(feature = "big-table"))]
#[inline]
fn small_prime_inv(_i: usize, _p: u64) -> Option<&'static PreModInv<u64>> {
    None
}

/// Residual of trial division that fits a single word.
///
/// The divisibility check by an odd prime is a multiplication against the
/// precomputed modular inverse ([`DivExact`]) when available, and falls back
/// to a plain remainder check otherwise.
trait WordResidual: PrimInt + From<u64> {
    /// Remove one instance of the odd prime `p` if it divides `self`.
    /// `pre` must be the precomputed inverse of `p` when given.
    fn div_exact_prime(self, p: u64, pre: Option<&PreModInv<u64>>) -> Option<Self>;
}

impl WordResidual for u64 {
    #[inline]
    fn div_exact_prime(self, p: u64, pre: Option<&PreModInv<u64>>) -> Option<Self> {
        match pre {
            Some(pre) => DivExact::div_exact(self, p, pre),
            None => (self % p == 0).then(|| self / p),
        }
    }
}

impl WordResidual for u128 {
    #[inline]
    fn div_exact_prime(self, p: u64, pre: Option<&PreModInv<u64>>) -> Option<Self> {
        match pre {
            // the 128-bit residual is handled as DoubleWord, the check costs
            // two multiplications instead of a software division
            Some(pre) => DivExact::div_exact(self, p, pre),
            None => (self % u128::from(p) == 0).then(|| self / u128::from(p)),
        }
    }
}

/// Run trial division on a residual that fits the single word type `W`.
///
/// `tsqrt` must be the square root bound derived from the original target (not
/// the shrinking residual), so that the `Ok`/`Err` split matches the wide path.
/// `inv_offset` is the position of the first prime of `primes` in the original
/// iterator, used to look up the precomputed inverses.
fn word_trial_division<W: WordResidual>(
    mut residual: W,
    primes: impl Iterator<Item = u64>,
    tsqrt: W,
    limit: Option<u64>,
    inv_offset: usize,
    result: &mut BTreeMap<u64, usize>,
) -> (bool, W) {
    let lim = match limit {
        Some(l) => tsqrt.min(<W as From<u64>>::from(l)),
        None => tsqrt,
    };

    let mut factored = false;
    for (i, p) in primes.enumerate() {
        if <W as From<u64>>::from(p) > tsqrt {
            factored = true;
        }
        if <W as From<u64>>::from(p) > lim {
            break;
        }

        let mut exp = 0usize;
        if p == 2 {
            // the precomputed inverses only cover odd primes
            let tz = residual.trailing_zeros();
            residual = residual >> (tz as usize);
            exp = tz as usize;
        } else {
            while let Some(q) = residual.div_exact_prime(p, small_prime_inv(inv_offset + i, p)) {
                residual = q;
                exp += 1;
            }
        }
        if exp > 0 {
            *result.entry(p).or_insert(0) += exp;
        }
        if residual == <W as From<u64>>::from(1) {
            factored = true;
            break;
        }
    }
    (factored, residual)
}

/// Run trial division on a residual that doesn't fit a `u128`.
///
/// The primes are grouped into batches whose product fits a `u64`. Since
/// `p | residual` iff `p | (residual mod batch_product)`, one division of the
/// wide residual per batch replaces one division per prime: the divisibility
/// checks run on the single-word remainder (via [`DivExact`] with the
/// precomputed inverses when available), and the residual itself is only
/// divided when a prime actually divides it.
fn wide_trial_division<T>(
    target: T,
    primes: impl Iterator<Item = u64>,
    tsqrt64: Option<u64>,
    tsqrt128: Option<u128>,
    limit: Option<u64>,
    result: &mut BTreeMap<u64, usize>,
) -> (bool, T)
where
    T: Integer + Clone + Roots + NumRef + FromPrimitive + ToPrimitive,
    for<'r> &'r T: RefNum<T>,
{
    let tsqrt = tsqrt64.unwrap_or(u64::MAX);
    let lim = tsqrt.min(limit.unwrap_or(u64::MAX));

    // the residual remainder for the current batch, recomputed after each hit.
    // note: mod_floor instead of rem, the Mint backend only supports the
    // remainder operator for odd divisors (it goes through Montgomery form)
    let word_residual = |residual: &T, m: &T| -> u64 {
        if residual < m {
            residual
                .to_u64()
                .expect("residual below the batch product fits u64")
        } else {
            residual
                .mod_floor(m)
                .to_u64()
                .expect("remainder below the batch product fits u64")
        }
    };

    let mut residual = target;
    let mut factored = false;
    let mut iter = primes;
    let mut pending: Option<(usize, u64)> = None; // prime that didn't fit the last batch
    let mut batch: Vec<(usize, u64)> = Vec::new();
    let mut pulled = 0usize; // number of primes taken from the iterator

    'outer: loop {
        // hand the residual over to the word loops once it fits a word
        let inv_offset = pending.as_ref().map_or(pulled, |&(pos, _)| pos);
        if let Some(r) = residual.to_u64() {
            let (f, q) = word_trial_division(
                r,
                pending.into_iter().map(|(_, p)| p).chain(&mut iter),
                tsqrt,
                limit,
                inv_offset,
                result,
            );
            return (factored || f, T::from_u64(q).unwrap());
        }
        if let Some(r) = residual.to_u128() {
            let (f, q) = word_trial_division(
                r,
                pending.into_iter().map(|(_, p)| p).chain(&mut iter),
                tsqrt128.unwrap_or(u128::MAX),
                limit,
                inv_offset,
                result,
            );
            return (factored || f, T::from_u128(q).unwrap());
        }

        // group the next primes while their product fits a u64, so that the
        // batch product can always be converted back through from_u64 (which
        // every FromPrimitive implementation must properly provide)
        batch.clear();
        let mut m: u64 = 1;
        let mut exhausted = false;
        let mut stop = false;
        loop {
            let (pos, p) = match pending.take() {
                Some(pp) => pp,
                None => match iter.next() {
                    Some(p) => {
                        pulled += 1;
                        (pulled - 1, p)
                    }
                    None => {
                        exhausted = true;
                        break;
                    }
                },
            };
            if p > tsqrt {
                factored = true;
            }
            if p > lim {
                stop = true;
                break;
            }
            match m.checked_mul(p) {
                Some(m2) => {
                    m = m2;
                    batch.push((pos, p));
                }
                None => {
                    pending = Some((pos, p));
                    break;
                }
            }
        }

        if !batch.is_empty() {
            let m_t = T::from_u64(m).expect("batch product is representable in T");
            let mut r = word_residual(&residual, &m_t);
            for &(pos, p) in batch.iter() {
                let divisible = if p == 2 {
                    r & 1 == 0
                } else {
                    match small_prime_inv(pos, p) {
                        Some(pre) => DivExact::div_exact(r, p, pre).is_some(),
                        None => r % p == 0,
                    }
                };
                if !divisible {
                    continue;
                }

                // peel all powers of p from the residual, div_rem computes
                // quotient and remainder in a single pass
                let p_t = T::from_u64(p).unwrap();
                let mut exp = 0usize;
                loop {
                    let (quo, rem) = residual.div_rem(&p_t);
                    if !rem.is_zero() {
                        break;
                    }
                    residual = quo;
                    exp += 1;
                }
                if exp > 0 {
                    *result.entry(p).or_insert(0) += exp;
                }

                if residual.is_one() {
                    factored = true;
                    break 'outer;
                }
                r = word_residual(&residual, &m_t);
            }
        }
        if exhausted || stop {
            break;
        }
    }
    (factored, residual)
}

/// Find factors by trial division, returns a tuple of the found factors and the residual.
///
/// The target is guaranteed fully factored only if bound * bound > target, where bound = max(primes).
/// The parameter limit additionally sets the maximum of primes to be tried.
/// The residual will be Ok(1) or Ok(p) if fully factored.
///
/// Divisibility checks run on single words whenever the residual fits one: with the
/// `big-table` feature they use the precomputed modular inverses (via [`DivExact`]),
/// otherwise plain remainder checks. For wider residuals, the primes are grouped into
/// batches whose product fits a `u64`, so that one division of the target per batch
/// replaces one division per prime, and the target is only divided by the primes that
/// actually divide it.
///
/// # Examples
///
/// ```
/// use num_prime::factor::trial_division;
///
/// let primes = vec![2, 3, 5, 7, 11, 13];
/// let (factors, residual) = trial_division(primes.into_iter(), 60u64, None);
/// assert_eq!(factors[&2], 2);
/// assert_eq!(factors[&3], 1);
/// assert_eq!(factors[&5], 1);
/// assert!(residual.is_ok());
/// ```
pub fn trial_division<
    I: Iterator<Item = u64>,
    T: Integer + Clone + Roots + NumRef + FromPrimitive + ToPrimitive,
>(
    primes: I,
    target: T,
    limit: Option<u64>,
) -> (BTreeMap<u64, usize>, Result<T, T>)
where
    for<'r> &'r T: RefNum<T>,
{
    let mut result = BTreeMap::new();

    // zero has no prime factorization, dividing it by primes would never end
    if target.is_zero() {
        return (result, Err(target));
    }

    let tsqrt = Roots::sqrt(&target) + T::one();
    let tsqrt64 = tsqrt.to_u64();
    let tsqrt128 = tsqrt.to_u128();

    // wide_trial_division hands the residual over to the word loops at its
    // first iteration when the target already fits a word
    let (factored, residual) =
        wide_trial_division(target, primes, tsqrt64, tsqrt128, limit, &mut result);

    if factored {
        (result, Ok(residual))
    } else {
        (result, Err(residual))
    }
}

/// Find factors using Pollard's rho algorithm with Brent's loop detection algorithm
///
/// The returned values are the factor and the count of passed iterations.
///
/// # Examples
///
/// ```
/// use num_prime::factor::pollard_rho;
///
/// let (factor, _iterations) = pollard_rho(&8051u16, 2, 1, 100);
/// assert_eq!(factor, Some(97));  // 8051 = 83 × 97
/// ```
pub fn pollard_rho<
    T: Integer
        + FromPrimitive
        + NumRef
        + Clone
        + for<'r> ModularCoreOps<&'r T, &'r T, Output = T>
        + for<'r> ModularUnaryOps<&'r T, Output = T>,
>(
    target: &T,
    start: T,
    offset: T,
    max_iter: usize,
) -> (Option<T>, usize)
where
    for<'r> &'r T: RefNum<T>,
{
    let mut a = start.clone();
    let mut b = start.clone();
    let mut z = T::one() % target; // accumulator for gcd

    // using Brent's loop detection, i = tortoise, j = hare
    let (mut i, mut j) = (0usize, 1usize);

    // backtracing states
    let mut s = start;
    let mut backtrace = false;

    while i < max_iter {
        i += 1;
        // Not `a.sqm(target)`: for arbitrary-precision types that is a modular
        // exponentiation, which costs far more than a single multiplication.
        a = a.clone().mulm(&a, target).addm(&offset, target);
        if a == b {
            return (None, i);
        }

        // gcd(n, -t) = gcd(n, t), so no abs-diff: ordering Montgomery forms
        // would need a residue() per walker, and `subm` cannot underflow.
        let diff = a.clone().subm(&b, target);
        z = z.mulm(&diff, target);
        if z.is_zero() {
            // the factor is missed by a combined GCD, do backtracing
            if backtrace {
                // ultimately failed
                return (None, i);
            } else {
                backtrace = true;
                a = std::mem::replace(&mut s, T::one()); // s is discarded
                z = T::one() % target; // clear gcd
                continue;
            }
        }

        // here we check gcd every 2^k steps or 128 steps
        // larger batch size leads to large overhead when backtracing.
        // reference: https://www.cnblogs.com/812-xiao-wen/p/10544546.html
        if i == j || i & 127 == 0 || backtrace {
            let d = z.gcd(target);
            if !d.is_one() && &d != target {
                return (Some(d), i);
            }

            // save state
            s = a.clone();
        }

        // when tortoise catches up with hare, let hare jump to the next stop
        if i == j {
            b = a.clone();
            j <<= 1;
        }
    }

    (None, i)
}

/// This function implements Shanks's square forms factorization (SQUFOF).
///
/// The input is usually multiplied by a multiplier, and the multiplied integer should be put in
/// the `mul_target` argument. The multiplier can be choosen from `SQUFOF_MULTIPLIERS`, or other square-free odd numbers.
/// The returned values are the factor and the count of passed iterations.
///
/// The max iteration can be choosed as 2*n^(1/4), based on Theorem 4.22 from \[1\].
///
/// # Examples
///
/// ```
/// use num_prime::factor::squfof;
///
/// let (factor, _iterations) = squfof(&11111u32, 11111u32, 100);
/// assert_eq!(factor, Some(41));  // 11111 = 41 × 271
/// ```
///
/// Reference: Gower, J., & Wagstaff Jr, S. (2008). Square form factorization.
/// In \[1\] [Mathematics of Computation](https://homes.cerias.purdue.edu/~ssw/gowerthesis804/wthe.pdf)
/// or \[2\] [his thesis](https://homes.cerias.purdue.edu/~ssw/gowerthesis804/wthe.pdf)
/// The code is from \[3\] [Rosetta code](https://rosettacode.org/wiki/Square_form_factorization)
pub fn squfof<T: Integer + NumRef + Clone + ExactRoots + std::fmt::Debug>(
    target: &T,
    mul_target: T,
    max_iter: usize,
) -> (Option<T>, usize)
where
    for<'r> &'r T: RefNum<T>,
{
    assert!(
        &mul_target.is_multiple_of(target),
        "mul_target should be multiples of target"
    );
    let rd = Roots::sqrt(&mul_target); // root of k*N

    /// Reduction operator for binary quadratic forms. It's equivalent to
    /// the one used in the `num-irrational` crate, in a little different form.
    ///
    /// This function reduces (a, b, c) = (qm1, p, q), updates qm1 and q, returns new p.
    #[inline]
    fn rho<T: Integer + Clone + NumRef>(rd: &T, p: &T, q: &mut T, qm1: &mut T) -> T
    where
        for<'r> &'r T: RefNum<T>,
    {
        let b = (rd + p).div_floor(&*q);
        let new_p = &b * &*q - p;
        let new_q = if p > &new_p {
            &*qm1 + b * (p - &new_p)
        } else {
            &*qm1 - b * (&new_p - p)
        };

        *qm1 = std::mem::replace(q, new_q);
        new_p
    }

    // forward loop, search principal cycle
    let (mut p, mut q, mut qm1) = (rd.clone(), &mul_target - &rd * &rd, T::one());
    if q.is_zero() {
        // shortcut for perfect square
        return (Some(rd), 0);
    }

    for i in 1..max_iter {
        p = rho(&rd, &p, &mut q, &mut qm1);
        if i.is_odd() {
            if let Some(rq) = q.sqrt_exact() {
                let b = (&rd - &p) / &rq;
                let mut u = b * &rq + &p;
                let (mut v, mut vm1) = ((&mul_target - &u * &u) / &rq, rq);

                // backward loop, search ambiguous cycle
                loop {
                    let new_u = rho(&rd, &u, &mut v, &mut vm1);
                    if new_u == u {
                        break;
                    } else {
                        u = new_u;
                    }
                }

                let d = target.gcd(&u);
                if d > T::one() && &d < target {
                    return (Some(d), i);
                }
            }
        }
    }
    (None, max_iter)
}

/// Good squfof multipliers sorted by efficiency descendingly, from Dana Jacobsen.
///
/// Note: square-free odd numbers are suitable as SQUFOF multipliers
pub const SQUFOF_MULTIPLIERS: [u16; 38] = [
    3 * 5 * 7 * 11,
    3 * 5 * 7,
    3 * 5 * 7 * 11 * 13,
    3 * 5 * 7 * 13,
    3 * 5 * 7 * 11 * 17,
    3 * 5 * 11,
    3 * 5 * 7 * 17,
    3 * 5,
    3 * 5 * 7 * 11 * 19,
    3 * 5 * 11 * 13,
    3 * 5 * 7 * 19,
    3 * 5 * 7 * 13 * 17,
    3 * 5 * 13,
    3 * 7 * 11,
    3 * 7,
    5 * 7 * 11,
    3 * 7 * 13,
    5 * 7,
    3 * 5 * 17,
    5 * 7 * 13,
    3 * 5 * 19,
    3 * 11,
    3 * 7 * 17,
    3,
    3 * 11 * 13,
    5 * 11,
    3 * 7 * 19,
    3 * 13,
    5,
    5 * 11 * 13,
    5 * 7 * 19,
    5 * 13,
    7 * 11,
    7,
    3 * 17,
    7 * 13,
    11,
    1,
];

/// William Hart's one line factorization algorithm for 64 bit integers.
///
/// The number to be factored could be multiplied by a smooth number (coprime to the target)
/// to speed up, put the multiplied number in the `mul_target` argument. A good multiplier given by Hart is 480.
/// `iters` determine the range for iterating the inner multiplier itself. The returned values are the factor
/// and the count of passed iterations.
///
///
/// The one line factorization algorithm is especially good at factoring semiprimes with form pq,
/// where p = `next_prime(c^a+d1`), p = `next_prime(c^b+d2`), a and b are close, and c, d1, d2 are small integers.
///
/// # Examples
///
/// ```
/// use num_prime::factor::one_line;
///
/// let (factor, _iterations) = one_line(&11111u32, 11111u32, 100);
/// assert_eq!(factor, Some(271));  // 11111 = 41 × 271
/// ```
///
/// Reference: Hart, W. B. (2012). A one line factoring algorithm. Journal of the Australian Mathematical Society, 92(1), 61-69. doi:10.1017/S1446788712000146
// TODO: add multipliers preset for one_line method?
pub fn one_line<T: Integer + NumRef + FromPrimitive + ExactRoots + CheckedAdd + CheckedMul>(
    target: &T,
    mul_target: T,
    max_iter: usize,
) -> (Option<T>, usize)
where
    for<'r> &'r T: RefNum<T>,
{
    assert!(
        &mul_target.is_multiple_of(target),
        "mul_target should be multiples of target"
    );

    let mut ikn = mul_target.clone();
    for i in 1..max_iter {
        let s = ikn.sqrt() + T::one(); // assuming target is not perfect square

        // Use checked multiplication to prevent overflow
        let s_squared = if let Some(result) = s.checked_mul(&s) {
            result
        } else {
            // If s*s would overflow, this method won't work for this range
            return (None, i);
        };
        let m = s_squared - &ikn;
        if let Some(t) = m.sqrt_exact() {
            let g = target.gcd(&(s - t));
            if !g.is_one() && &g != target {
                return (Some(g), i);
            }
        }

        // prevent overflow
        ikn = if let Some(n) = ikn.checked_add(&mul_target) {
            n
        } else {
            return (None, i);
        }
    }
    (None, max_iter)
}

// TODO: ECM, (self initialize) Quadratic sieve, Lehman's Fermat(https://en.wikipedia.org/wiki/Fermat%27s_factorization_method, n_factor_lehman)
// REF: https://pypi.org/project/primefac/
//      http://flintlib.org/doc/ulong_extras.html#factorisation
//      https://github.com/zademn/facto-rs/
//      https://github.com/elmomoilanen/prime-factorization
//      https://cseweb.ucsd.edu/~ethome/teaching/2022-cse-291-14/
#[cfg(test)]
mod tests {
    use super::*;
    use crate::mint::SmallMint;
    use num_modular::MontgomeryInt;
    use rand::random;

    #[test]
    fn pollard_rho_test() {
        assert_eq!(pollard_rho(&8051u16, 2, 1, 100).0, Some(97));
        assert!(matches!(pollard_rho(&8051u16, random(), 1, 100).0, Some(i) if i == 97 || i == 83));
        assert_eq!(pollard_rho(&455_459_u32, 2, 1, 100).0, Some(743));

        // Mint test
        for _ in 0..10 {
            let target = random::<u16>() | 1;
            let start = random::<u16>() % target;
            let offset = random::<u16>() % target;

            let expect = pollard_rho(&target, start, offset, 65536);
            let mint_result = pollard_rho(
                &SmallMint::from(target),
                MontgomeryInt::new(start, &target).into(),
                MontgomeryInt::new(offset, &target).into(),
                65536,
            );
            assert_eq!(expect.0, mint_result.0.map(|v| v.value()));
        }
    }

    #[test]
    fn squfof_test() {
        // case from wikipedia
        assert_eq!(squfof(&11111u32, 11111u32, 100).0, Some(41));

        // cases from https://rosettacode.org/wiki/Square_form_factorization
        let cases: Vec<u64> = vec![
            2501,
            12851,
            13289,
            75301,
            120_787,
            967_009,
            997_417,
            7_091_569,
            5_214_317,
            20_834_839,
            23_515_517,
            33_409_583,
            44_524_219,
            13_290_059,
            223_553_581,
            2_027_651_281,
            11_111_111_111,
            100_895_598_169,
            60_012_462_237_239,
            287_129_523_414_791,
            9_007_199_254_740_931,
            11_111_111_111_111_111,
            314_159_265_358_979_323,
            384_307_168_202_281_507,
            419_244_183_493_398_773,
            658_812_288_346_769_681,
            922_337_203_685_477_563,
            1_000_000_000_000_000_127,
            1_152_921_505_680_588_799,
            1_537_228_672_809_128_917,
            // this case should success at step 276, from https://rosettacode.org/wiki/Talk:Square_form_factorization
            4_558_849,
        ];
        for n in cases {
            let d = squfof(&n, n, 40000)
                .0
                .or(squfof(&n, 3 * n, 40000).0)
                .or(squfof(&n, 5 * n, 40000).0)
                .or(squfof(&n, 7 * n, 40000).0)
                .or(squfof(&n, 11 * n, 40000).0);
            assert!(d.is_some(), "{}", n);
        }
    }

    #[test]
    fn one_line_test() {
        assert_eq!(one_line(&11111u32, 11111u32, 100).0, Some(271));
    }

    // --- one_line with overflow via checked_add ---
    #[test]
    fn one_line_overflow() {
        // Use a u64 target large enough that repeated addition overflows
        let n = u64::MAX / 4 + 1; // ~4.6e18, adding 5 times overflows u64
        let result = one_line(&n, n, 1000);
        // Should return None (overflow triggered early exit via checked_add)
        assert!(result.0.is_none());
    }

    #[test]
    fn one_line_with_multiplier() {
        // Use multiplier 480 as recommended
        let n = 11111u32;
        let result = one_line(&n, n * 480, 100);
        assert!(result.0.is_some());
        let f = result.0.unwrap();
        assert!(n % f == 0 && f > 1 && f < n);
    }

    // --- trial_division with limit=None (no limit path) ---
    #[test]
    fn trial_division_no_limit() {
        let primes: Vec<u64> = vec![2, 3, 5, 7, 11, 13];
        let (factors, residual) = trial_division(primes.into_iter(), 2 * 3 * 5 * 7u64, None);
        assert!(residual.is_ok());
        assert_eq!(residual.unwrap(), 1);
        assert_eq!(factors[&2], 1);
        assert_eq!(factors[&3], 1);
        assert_eq!(factors[&5], 1);
        assert_eq!(factors[&7], 1);
    }

    // --- trial_division where residual is 1 (fully factored) ---
    #[test]
    fn trial_division_residual_one() {
        let primes: Vec<u64> = vec![2, 3, 5];
        let (factors, residual) = trial_division(primes.into_iter(), 60u64, Some(100));
        assert!(residual.is_ok());
        assert_eq!(residual.unwrap(), 1);
        assert_eq!(factors[&2], 2);
        assert_eq!(factors[&3], 1);
        assert_eq!(factors[&5], 1);
    }

    // --- trial_division where bound exceeds sqrt (factored=true with residual prime) ---
    #[test]
    fn trial_division_bound_exceeds_sqrt() {
        // 91 = 7 * 13. Primes up to 13 will factor it, and 13 > sqrt(91) ~ 9.5
        let primes: Vec<u64> = vec![2, 3, 5, 7, 11, 13];
        let (factors, residual) = trial_division(primes.into_iter(), 91u64, Some(100));
        assert!(residual.is_ok());
        // After dividing by 7, residual is 13, and bound > sqrt means factored
        assert_eq!(factors[&7], 1);
        assert_eq!(residual.unwrap(), 13);
    }

    #[test]
    fn trial_division_prime_target() {
        // 97 is prime. Primes up to 10 > sqrt(97) ~ 9.85, so factored=true
        let primes: Vec<u64> = vec![2, 3, 5, 7, 11];
        let (factors, residual) = trial_division(primes.into_iter(), 97u64, Some(100));
        assert!(residual.is_ok());
        assert!(factors.is_empty());
        assert_eq!(residual.unwrap(), 97);
    }

    // --- squfof with perfect square input ---
    #[test]
    fn squfof_perfect_square() {
        // Perfect square: q.is_zero() shortcut
        let result = squfof(&49u64, 49u64, 100);
        assert_eq!(result.0, Some(7));
        assert_eq!(result.1, 0); // should return immediately
    }

    #[test]
    fn squfof_perfect_square_large() {
        let n = 10201u64; // 101^2
        let result = squfof(&n, n, 100);
        assert_eq!(result.0, Some(101));
        assert_eq!(result.1, 0);
    }

    // --- pollard_rho with known backtracing scenario ---
    #[test]
    fn pollard_rho_various_starts() {
        // Test multiple start/offset combinations to increase path coverage
        let target = 8051u32;
        for start in [1u32, 2, 3, 5, 7, 11, 13] {
            for offset in [1u32, 2, 3, 5, 7] {
                let (result, _) = pollard_rho(&target, start, offset, 10000);
                if let Some(f) = result {
                    assert!(target % f == 0 && f > 1 && f < target);
                }
            }
        }
    }

    #[test]
    fn pollard_rho_loop_detection() {
        // Case where a == b (cycle detected) should return None
        // Start 0, offset 0: f(x) = x^2 + 0 mod n, starting from 0 => always 0, quick cycle
        let (result, _) = pollard_rho(&15u32, 0, 0, 100);
        // This should either find a factor or hit the cycle
        // Just verify it doesn't panic
        let _ = result;
    }

    // --- trial_division with small limit ---
    #[test]
    fn trial_division_limited() {
        // Limit smaller than sqrt means not fully factored
        let primes: Vec<u64> = vec![2, 3, 5, 7, 11, 13];
        // 1001 = 7 * 11 * 13, sqrt(1001) ~ 31.6
        // With limit 10, we can only find factor 7, then residual 143 = 11*13
        let (factors, residual) = trial_division(primes.into_iter(), 1001u64, Some(10));
        assert!(residual.is_err()); // not fully factored
        assert_eq!(factors[&7], 1);
        assert_eq!(residual.unwrap_err(), 143);
    }

    #[test]
    fn trial_division_primes_not_from_the_static_table() {
        // the prime list doesn't follow SMALL_PRIMES (unaligned or duplicated),
        // the precomputed inverses must not be misapplied on such iterators
        let primes: Vec<u64> = vec![3, 7, 5, 2, 11, 2, 13];
        // 2*3*5*7*11*13 = 30030
        let (factors, residual) = trial_division(primes.into_iter(), 30030u64, None);
        assert_eq!(residual, Ok(1));
        for p in [2, 3, 5, 7, 11, 13] {
            assert_eq!(factors[&p], 1, "exponent of {p}");
        }
    }

    #[test]
    fn trial_division_zero() {
        // zero has no prime factorization, it must not loop forever
        let primes: Vec<u64> = vec![2, 3, 5, 7];
        let (factors, residual) = trial_division(primes.into_iter(), 0u64, None);
        assert!(factors.is_empty());
        assert_eq!(residual.unwrap_err(), 0);
    }

    #[test]
    fn trial_division_u128() {
        // 3^41 doesn't fit a u64, the residual is checked as DoubleWord
        let n = 3u128.pow(41);
        let (factors, residual) = trial_division([2, 3, 5].into_iter(), n, None);
        assert_eq!(residual, Ok(1));
        assert_eq!(factors[&3], 41);

        // a limit below the smallest factor leaves the target unfactored
        let (factors, residual) = trial_division([2, 3, 5].into_iter(), n, Some(2));
        assert!(factors.is_empty());
        assert_eq!(residual, Err(n));
    }

    #[cfg(feature = "big-int")]
    #[test]
    fn trial_division_wide_biguint() {
        use crate::tables::SMALL_PRIMES;
        use num_bigint::BigUint;
        use num_traits::One;

        let primes = || SMALL_PRIMES.iter().map(|&p| u64::from(p));

        // a wide target built from repeated factors of the static table
        let mut n = BigUint::from(2u8).pow(90);
        n = &n * BigUint::from(3u8).pow(40);
        n = &n * BigUint::from(7u8).pow(11);
        n = &n * BigUint::from(241u8).pow(9);
        n = &n * BigUint::from(251u8).pow(9);
        assert!(n.to_u128().is_none());

        let (factors, residual) = trial_division(primes(), n, None);
        assert_eq!(residual, Ok(BigUint::one()));
        assert_eq!(factors[&2], 90);
        assert_eq!(factors[&3], 40);
        assert_eq!(factors[&7], 11);
        assert_eq!(factors[&241], 9);
        assert_eq!(factors[&251], 9);

        // a limit leaves the factors above it in the residual
        let n = BigUint::from(2u8).pow(90)
            * BigUint::from(3u8).pow(40)
            * BigUint::from(7u8).pow(11)
            * BigUint::from(241u8).pow(9)
            * BigUint::from(251u8).pow(9);
        let (factors, residual) = trial_division(primes(), n.clone(), Some(100));
        assert_eq!(
            residual,
            Err(BigUint::from(241u8).pow(9) * BigUint::from(251u8).pow(9))
        );
        assert_eq!(factors[&2], 90);
        assert_eq!(factors[&3], 40);
        assert_eq!(factors[&7], 11);

        // the residual drops below u64 in the middle of a batch: 2 and 251
        // are peeled from the wide target while the batch is still running,
        // leaving 3^39 which is re-reduced against the same batch product
        let m =
            BigUint::from(2u8).pow(64) * BigUint::from(251u8).pow(9) * BigUint::from(3u8).pow(39);
        let (factors, residual) = trial_division([2, 5, 251, 3].into_iter(), m, None);
        assert_eq!(residual, Ok(BigUint::one()));
        assert_eq!(factors[&2], 64);
        assert_eq!(factors[&3], 39);
        assert_eq!(factors[&251], 9);
        assert!(!factors.contains_key(&5));
    }
}

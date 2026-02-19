//! Implementations for various factorization algorithms.
//!
//! Note general prime number field sieve is not planned to be implemented, since it's too complex
//!
//! See <https://web.archive.org/web/20110331180514/https://diamond.boisestate.edu/~liljanab/BOISECRYPTFall09/Jacobsen.pdf>
//! for a detailed comparison between different factorization algorithms

// XXX: make the factorization method resumable? Maybe let all of them returns a Future

use crate::traits::ExactRoots;
use num_integer::{Integer, Roots};
use num_modular::{ModularCoreOps, ModularUnaryOps};
use num_traits::{CheckedAdd, FromPrimitive, NumRef, RefNum};
use std::collections::BTreeMap;

/// Find factors by trial division, returns a tuple of the found factors and the residual.
///
/// The target is guaranteed fully factored only if bound * bound > target, where bound = max(primes).
/// The parameter limit additionally sets the maximum of primes to be tried.
/// The residual will be Ok(1) or Ok(p) if fully factored.
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
///
/// TODO: implement fast check for small primes with `BigInts` in the precomputed table, and skip them in this function
pub fn trial_division<
    I: Iterator<Item = u64>,
    T: Integer + Clone + Roots + NumRef + FromPrimitive,
>(
    primes: I,
    target: T,
    limit: Option<u64>,
) -> (BTreeMap<u64, usize>, Result<T, T>)
where
    for<'r> &'r T: RefNum<T>,
{
    let tsqrt: T = Roots::sqrt(&target) + T::one();
    let limit = if let Some(l) = limit {
        tsqrt.clone().min(T::from_u64(l).unwrap())
    } else {
        tsqrt.clone()
    };

    let mut residual = target;
    let mut result = BTreeMap::new();
    let mut factored = false;
    for (p, pt) in primes.map(|p| (p, T::from_u64(p).unwrap())) {
        if pt > tsqrt {
            factored = true;
        }
        if pt > limit {
            break;
        }

        while residual.is_multiple_of(&pt) {
            residual = residual / &pt;
            *result.entry(p).or_insert(0) += 1;
        }
        if residual.is_one() {
            factored = true;
            break;
        }
    }

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
        a = a.sqm(target).addm(&offset, target);
        if a == b {
            return (None, i);
        }

        // FIXME: optimize abs_diff for montgomery form if we are going to use the abs_diff in the std lib
        let diff = if b > a { &b - &a } else { &a - &b }; // abs_diff
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
/// The max iteration can be choosed as 2*n^(1/4), based on Theorem 4.22 from [1].
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
/// In [1] [Mathematics of Computation](https://homes.cerias.purdue.edu/~ssw/gowerthesis804/wthe.pdf)
/// or [2] [his thesis](https://homes.cerias.purdue.edu/~ssw/gowerthesis804/wthe.pdf)
/// The code is from [3] [Rosetta code](https://rosettacode.org/wiki/Square_form_factorization)
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
pub fn one_line<T: Integer + NumRef + FromPrimitive + ExactRoots + CheckedAdd>(
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
        let m = &s * &s - &ikn;
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
        assert!(n.is_multiple_of(f) && f > 1 && f < n);
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
                    assert!(target.is_multiple_of(f) && f > 1 && f < target);
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
}

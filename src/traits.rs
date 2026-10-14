use core::default::Default;
use std::ops::{BitAnd, BitOr, Mul};

use either::Either;
use num_integer::{Integer, Roots};
use num_traits::Pow;

/// This trait support unified bit testing for (unsigned) integers
pub trait BitTest {
    /// Get the minimum required number of bits to represent this integer
    fn bits(&self) -> usize;

    /// Get the i-th bit of the integer, with i specified by `position`
    fn bit(&self, position: usize) -> bool;

    /// Get the number of trailing zeros in the integer
    fn trailing_zeros(&self) -> usize;
}

/// This enum describes the result of primality checks
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Primality {
    /// The number passes deterministic primality check.
    Yes,
    /// The number is a composite and failed at least one specific primality check.
    No,
    /// The number passes several probabilistic primality check.
    /// The associated float number carries the probability of the number being a prime
    /// (conditioned on that it's already a probable prime)
    Probable(f32),
}

impl Primality {
    /// Check whether the resule indicates that the number is
    /// (very) probably a prime. Return false only on [`Primality::No`]
    #[inline(always)]
    #[must_use]
    pub fn probably(self) -> bool {
        !matches!(self, Primality::No)
    }
}

impl BitAnd<Primality> for Primality {
    type Output = Primality;

    /// Combine two primality results by ensuring both numbers are prime
    fn bitand(self, rhs: Primality) -> Self::Output {
        match self {
            Primality::No => Primality::No,
            Primality::Yes => rhs,
            Primality::Probable(p) => match rhs {
                Primality::No => Primality::No,
                Primality::Yes => Primality::Probable(p),
                Primality::Probable(p2) => {
                    let combined = p.mul(p2);
                    Primality::Probable(combined)
                }
            },
        }
    }
}

impl BitOr<Primality> for Primality {
    type Output = Primality;

    /// Combine two primality results by ensuring either numbers is prime
    fn bitor(self, rhs: Primality) -> Self::Output {
        match self {
            Primality::No => rhs,
            Primality::Yes => Primality::Yes,
            Primality::Probable(p) => match rhs {
                Primality::No => Primality::Probable(p),
                Primality::Yes => Primality::Yes,
                Primality::Probable(p2) => Primality::Probable(1. - (1. - p) * (1. - p2)),
            },
        }
    }
}

/// Represents a configuration for a primality test
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct PrimalityTestConfig {
    // TODO: add option to divides small primes in the table
    //       and this option should be enabled if the probabilistic test is used for strict config
    /// Number of strong probable prime test, starting from base 2
    pub sprp_trials: usize,

    /// Number of strong probable prime test with random bases
    pub sprp_random_trials: usize,

    /// Whether perform strong lucas probable prime test (with automatically selected parameters)
    pub slprp_test: bool,

    /// Whether perform extra strong lucas probable prime test (with automatically selected parameters)
    pub eslprp_test: bool,
}

impl Default for PrimalityTestConfig {
    /// Create a defalt primality testing configuration. This config will eliminate most
    /// composites with little computation
    fn default() -> Self {
        Self {
            sprp_trials: 2,        // test base 2 and 3
            sprp_random_trials: 3, // choose other 3 random bases
            slprp_test: false,
            eslprp_test: false,
        }
    }
}

impl PrimalityTestConfig {
    /// Create a configuration with a very strong primality check. It's based on
    /// the **strongest deterministic primality testing** and some SPRP tests with
    /// random bases.
    #[must_use]
    pub fn strict() -> Self {
        let mut config = Self::bpsw();
        config.sprp_random_trials = 1;
        config
    }

    /// Create a configuration for Baillie-PSW test (base 2 SPRP test + SLPRP test)
    #[must_use]
    pub fn bpsw() -> Self {
        Self {
            sprp_trials: 1,
            sprp_random_trials: 0,
            slprp_test: true,
            eslprp_test: false,
        }
    }
}

/// Represents a configuration for integer factorization
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct FactorizationConfig {
    /// Config for testing if a factor is prime
    pub primality_config: PrimalityTestConfig,

    /// Prime limit of trial division, you also need to reserve the primes in the buffer
    /// if all primes under the limit are to be tested. `None` means using all available primes.
    pub td_limit: Option<u64>,

    /// Number of trials with Pollard's rho method
    pub rho_trials: usize,

    /// Offset added to the seed of the Pollard's rho generator. The seed is
    /// derived from the target, so a run is reproducible; advance this value
    /// to make a run split differently (the factorization retries do).
    pub rho_seed: u64,
}

impl Default for FactorizationConfig {
    /// Create a defalt primality testing configuration. This config will factorize
    /// most integers within decent time
    fn default() -> Self {
        const THRESHOLD_DEFAULT_TD: u64 = 1 << 14;
        Self {
            primality_config: PrimalityTestConfig::default(),
            td_limit: Some(THRESHOLD_DEFAULT_TD),
            rho_trials: 4,
            rho_seed: 0,
        }
    }
}

impl FactorizationConfig {
    /// Same as the default configuration but with strict primality check
    #[must_use]
    pub fn strict() -> Self {
        Self {
            primality_config: PrimalityTestConfig::strict(),
            ..Self::default()
        }
    }
}

// FIXME: backport to num_integer (see https://github.com/rust-num/num-traits/issues/233)
/// Extension on [`num_integer::Roots`] to support perfect power check on integers
pub trait ExactRoots: Roots + Pow<u32, Output = Self> + Clone {
    fn nth_root_exact(&self, n: u32) -> Option<Self> {
        let r = self.nth_root(n);
        if &r.clone().pow(n) == self {
            Some(r)
        } else {
            None
        }
    }
    fn sqrt_exact(&self) -> Option<Self> {
        self.nth_root_exact(2)
    }
    fn cbrt_exact(&self) -> Option<Self> {
        self.nth_root_exact(3)
    }
    fn is_nth_power(&self, n: u32) -> bool {
        self.nth_root_exact(n).is_some()
    }
    fn is_square(&self) -> bool {
        self.sqrt_exact().is_some()
    }
    fn is_cubic(&self) -> bool {
        self.cbrt_exact().is_some()
    }
}

// TODO: implement is_perfect_power, this could be used during factorization
//       to filter out perfect powers when factorize large integers
// REF: PARI/GP `Z_ispowerall`, `is_357_power`
//      FLINT `n_is_perfect_power235`, `fmpz_is_perfect_power`
//      GMP `mpz_perfect_power_p`

/// This trait represents a general data structure that stores primes.
///
/// It's recommended to store at least a bunch of small primes in the buffer
/// to make some of the algorithms more efficient.
pub trait PrimeBuffer<'a> {
    type PrimeIter: Iterator<Item = &'a u64>;

    /// Directly return an iterator of existing primes
    fn iter(&'a self) -> Self::PrimeIter;

    /// Generate primes until the largest prime in the buffer is equal or larger than limit
    fn reserve(&mut self, limit: u64);

    /// Get the largest primes in the list
    fn bound(&self) -> u64;

    /// Test if the number is in the buffer. If a number is not in the buffer,
    /// then it's either a composite or large than [`PrimeBuffer::bound()`]
    fn contains(&self, num: u64) -> bool;

    /// clear the prime buffer to save memory
    fn clear(&mut self);
}

/// This trait implements various primality testing algorithms
///
/// Reference:
/// - <http://ntheory.org/pseudoprimes.html>
pub trait PrimalityUtils: Integer + Clone {
    /// Test if the integer is a (Fermat) probable prime
    fn is_prp(&self, base: Self) -> bool;

    /// Test if the integer is a strong probable prime (based on Miller-Rabin test).
    fn is_sprp(&self, base: Self) -> bool;

    /// Do a Miller-Rabin test. The return value is a integer if it finds a factor of
    /// the integer, otherwise it reports the test result.
    fn test_sprp(&self, base: Self) -> Either<bool, Self>;

    /// Test if the integer is a Lucas probable prime
    /// If either of p, q is not specified, then we will use Selfridge's Method A to choose p, q
    fn is_lprp(&self, p: Option<usize>, q: Option<isize>) -> bool;

    /// Test if the integer is a strong Lucas probable prime
    /// If either of p, q is not specified, then we will use Selfridge's Method A to choose p, q
    fn is_slprp(&self, p: Option<usize>, q: Option<isize>) -> bool;

    /// Test if the integer is an extra strong Lucas probable prime
    /// If p is not specified, then first p starting from 3 such that Jacobi symbol is -1 will be chosen, which is sometimes refered as "Method C"
    fn is_eslprp(&self, p: Option<usize>) -> bool;

    // TODO: implement ECPP test
    // https://en.wikipedia.org/wiki/Elliptic_curve_primality

    // TODO: implement is_vprp (Lucas-V probable prime test)
    // https://arxiv.org/pdf/2006.14425.pdf
}

/// Supports random generation of primes
pub trait RandPrime<T> {
    /// Generate a random prime within the given bit size limit
    ///
    /// # Panics
    /// if the `bit_size` is 0 or it's larger than the bit width of the integer
    fn gen_prime(&mut self, bit_size: usize, config: Option<PrimalityTestConfig>) -> T;

    /// Generate a random prime with **exact** the given bit size
    ///
    /// # Panics
    /// if the `bit_size` is 0 or it's larger than the bit width of the integer
    fn gen_prime_exact(&mut self, bit_size: usize, config: Option<PrimalityTestConfig>) -> T;

    /// Generate a random (Sophie German) safe prime within the given bit size limit. The generated prime
    /// is guaranteed to pass the [`is_safe_prime`][crate::nt_funcs::is_safe_prime] test
    ///
    /// # Panics
    /// if the `bit_size` is 0 or it's larger than the bit width of the integer
    fn gen_safe_prime(&mut self, bit_size: usize) -> T;

    /// Generate a random (Sophie German) safe prime with the **exact** given bit size. The generated prime
    /// is guaranteed to pass the [`is_safe_prime`][crate::nt_funcs::is_safe_prime] test
    ///
    /// # Panics
    /// if the `bit_size` is 0 or it's larger than the bit width of the integer
    fn gen_safe_prime_exact(&mut self, bit_size: usize) -> T;
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Primality::probably() ---
    #[test]
    fn primality_probably() {
        assert!(Primality::Yes.probably());
        assert!(!Primality::No.probably());
        assert!(Primality::Probable(0.9).probably());
    }

    // --- Primality BitAnd: all 9 combinations ---
    #[test]
    fn primality_bitand_no_lhs() {
        assert_eq!(Primality::No & Primality::No, Primality::No);
        assert_eq!(Primality::No & Primality::Yes, Primality::No);
        assert_eq!(Primality::No & Primality::Probable(0.9), Primality::No);
    }

    #[test]
    fn primality_bitand_yes_lhs() {
        assert_eq!(Primality::Yes & Primality::No, Primality::No);
        assert_eq!(Primality::Yes & Primality::Yes, Primality::Yes);
        assert_eq!(
            Primality::Yes & Primality::Probable(0.8),
            Primality::Probable(0.8)
        );
    }

    #[test]
    fn primality_bitand_probable_lhs() {
        assert_eq!(Primality::Probable(0.9) & Primality::No, Primality::No);
        assert_eq!(
            Primality::Probable(0.9) & Primality::Yes,
            Primality::Probable(0.9)
        );
        // Probable & Probable => combined probability
        let result = Primality::Probable(0.8) & Primality::Probable(0.9);
        match result {
            Primality::Probable(p) => assert!((p - 0.72).abs() < 1e-6),
            _ => panic!("expected Probable"),
        }
    }

    // --- Primality BitOr: all 9 combinations ---
    #[test]
    fn primality_bitor_no_lhs() {
        assert_eq!(Primality::No | Primality::No, Primality::No);
        assert_eq!(Primality::No | Primality::Yes, Primality::Yes);
        assert_eq!(
            Primality::No | Primality::Probable(0.8),
            Primality::Probable(0.8)
        );
    }

    #[test]
    fn primality_bitor_yes_lhs() {
        assert_eq!(Primality::Yes | Primality::No, Primality::Yes);
        assert_eq!(Primality::Yes | Primality::Yes, Primality::Yes);
        assert_eq!(Primality::Yes | Primality::Probable(0.8), Primality::Yes);
    }

    #[test]
    fn primality_bitor_probable_lhs() {
        assert_eq!(
            Primality::Probable(0.9) | Primality::No,
            Primality::Probable(0.9)
        );
        assert_eq!(Primality::Probable(0.9) | Primality::Yes, Primality::Yes);
        // Probable | Probable => 1 - (1-p1)*(1-p2)
        let result = Primality::Probable(0.8) | Primality::Probable(0.9);
        match result {
            Primality::Probable(p) => assert!((p - 0.98).abs() < 1e-6),
            _ => panic!("expected Probable"),
        }
    }

    // --- PrimalityTestConfig constructors ---
    #[test]
    fn primality_test_config_default() {
        let c = PrimalityTestConfig::default();
        assert_eq!(c.sprp_trials, 2);
        assert_eq!(c.sprp_random_trials, 3);
        assert!(!c.slprp_test);
        assert!(!c.eslprp_test);
    }

    #[test]
    fn primality_test_config_bpsw() {
        let c = PrimalityTestConfig::bpsw();
        assert_eq!(c.sprp_trials, 1);
        assert_eq!(c.sprp_random_trials, 0);
        assert!(c.slprp_test);
        assert!(!c.eslprp_test);
    }

    #[test]
    fn primality_test_config_strict() {
        let c = PrimalityTestConfig::strict();
        assert_eq!(c.sprp_trials, 1);
        assert_eq!(c.sprp_random_trials, 1);
        assert!(c.slprp_test);
        assert!(!c.eslprp_test);
    }

    // --- FactorizationConfig constructors ---
    #[test]
    fn factorization_config_default() {
        let c = FactorizationConfig::default();
        assert_eq!(c.td_limit, Some(1 << 14));
        assert_eq!(c.rho_trials, 4);
    }

    #[test]
    fn factorization_config_strict() {
        let c = FactorizationConfig::strict();
        assert_eq!(c.td_limit, Some(1 << 14));
        assert_eq!(c.rho_trials, 4);
        // uses strict primality config
        assert_eq!(c.primality_config.sprp_trials, 1);
        assert_eq!(c.primality_config.sprp_random_trials, 1);
        assert!(c.primality_config.slprp_test);
    }

    // --- ExactRoots helper methods ---
    #[test]
    fn exact_roots_is_square() {
        assert!(16u64.is_square());
        assert!(!15u64.is_square());
        assert!(1u64.is_square());
        assert!(100u64.is_square());
        assert!(!99u64.is_square());
    }

    #[test]
    fn exact_roots_is_cubic() {
        assert!(27u64.is_cubic());
        assert!(!26u64.is_cubic());
        assert!(1u64.is_cubic());
        assert!(64u64.is_cubic());
    }

    #[test]
    fn exact_roots_is_nth_power() {
        assert!(256u64.is_nth_power(4));
        assert!(!255u64.is_nth_power(4));
    }

    #[test]
    fn exact_roots_sqrt_exact() {
        assert_eq!(49u64.sqrt_exact(), Some(7));
        assert_eq!(50u64.sqrt_exact(), None);
    }

    #[test]
    fn exact_roots_cbrt_exact() {
        assert_eq!(125u64.cbrt_exact(), Some(5));
        assert_eq!(126u64.cbrt_exact(), None);
    }
}

// #![doc = include_str!("../README.md")]

//! This crate provides utilities for prime related functionalities and some basic number theoretic functions:
//! - Primality testing
//!   - [Primality check][nt_funcs::is_prime]
//!   - [Deterministic primality check of `u64` integers][nt_funcs::is_prime64] (using a very fast hashing algorithm)
//!   - [Fermat probable prime test][PrimalityUtils::is_prp]
//!   - [Miller-rabin probable prime test][PrimalityUtils::is_sprp]
//!   - ([strong][PrimalityUtils::is_slprp]/[extra strong][PrimalityUtils::is_eslprp]) [Lucas probable prime test][PrimalityUtils::is_lprp]
//!   - [Baillie-PSW test][PrimalityTestConfig::bpsw]
//!   - [Sophie Germain safe prime test][nt_funcs::is_safe_prime]
//! - Primes generation and indexing
//!   - [A naive implementation of the sieve of Eratosthenes][buffer::NaiveBuffer]
//!   - [Unified API to support other prime generation backends][PrimeBuffer]
//!   - [Generate random (safe) primes][traits::RandPrime]
//!   - Find [previous prime][nt_funcs::prev_prime] / [next prime][nt_funcs::next_prime]
//! - [Integer factorization][nt_funcs::factors]
//!   - [Trial division][factor::trial_division]
//!   - [Pollard's rho algorithm][factor::pollard_rho]
//!   - [Shanks's square forms factorization (SQUFOF)][factor::squfof]
//!   - [Hart's one line algorithm][factor::one_line]
//!   - [Fast factorization of `u64` integers][nt_funcs::factorize64]
//! - Number theoretic functions
//!   - [Prime Pi function][nt_funcs::prime_pi], its [estimation](nt_funcs::prime_pi_est), and its [bounds](nt_funcs::prime_pi_bounds)
//!   - [Nth Prime][nt_funcs::nth_prime], its [estimation](nt_funcs::nth_prime_est), and its [bounds](nt_funcs::nth_prime_bounds)
//!   - [Moebius function][nt_funcs::moebius]
//!
//! # Usage
//! Most number theoretic functions can be found in [`nt_funcs`] module, while some
//! of them are implemented as member function of [`num_modular::ModularOps`] or [`PrimalityUtils`].
//!
//! Example code for primality testing and integer factorization:
//! ```rust
//! use num_prime::{PrimalityTestConfig, FactorizationConfig};
//! use num_prime::nt_funcs::{is_prime, factorize, factors};
//!
//! let p = 2u128.pow(89) - 1; // a prime number
//! assert!(is_prime(&p, None).probably()); // use default primality check config
//! assert!(is_prime(&p, Some(PrimalityTestConfig::bpsw())).probably()); // BPSW test
//!
//! let c = 2u128.pow(83) - 1; // a composite number
//! assert!(!is_prime(&c, None).probably());
//! let fac = factorize(c); // infallible factorization with default configuration
//! assert_eq!(fac.len(), 2); // 2^83-1 = 167 * 57912614113275649087721
//!
//! let config = FactorizationConfig::strict();
//! let (fac, rem) = factors(c, Some(config)); // fallible factorization with customized configuration
//! assert!(fac.len() == 2 && rem.is_none());
//! ```
//!
//! # Backends
//! This crate is built with modular integer type and prime generation backends.
//! Most functions support generic input types, and support for `num-bigint` is
//! also available (it's an optional feature). To make a new integer type supported
//! by this crate, the type has to implement [`detail::PrimalityBase`] and [`detail::PrimalityRefBase`].
//! For prime generation, there's a builtin implementation (see [buffer] module),
//! but you can also use other backends (such as `primal`) as long as it implements [`PrimeBuffer`].
//!
//! # Optional Features
//! - `big-int` (default): Enable this feature to support `num-bigint::BigUint` as integer inputs.
//! - `big-table` (default): Enable this feature to allow compiling large precomputed tables which
//!   could improve the speed of various functions with the cost of larger memory footprint.
//!

#![allow(clippy::redundant_clone)]

pub mod buffer;
pub mod factor;
pub mod nt_funcs;

mod integer;
mod mint;
mod primality;
mod rand;
mod tables;
mod traits;
mod util;

pub use traits::*;
pub mod detail {
    //! Implementation details for this crate.
    //!
    //! The structs and traits in this module are exposed for public use, although they are no
    //! designed for such usage. User-friendly is not a goal and backward-compatilibity is not
    //! strictly maintained here. Some traits in this module can be used to extend `num-prime`
    //! with new backends.
    pub use super::mint::{Mint, SmallMint};
    pub use super::primality::{LucasUtils, PrimalityBase, PrimalityRefBase};
    pub use super::tables::SMALL_PRIMES;
}

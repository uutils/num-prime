//! Implementations and extensions for [`PrimeBuffer`], which represents a container of primes
//!
//! In `num-prime`, there is no global instance to store primes, the user has to generate
//! and store the primes themselves. The trait [`PrimeBuffer`] defines a unified interface
//! for a prime number container. Some methods that can take advantage of pre-generated
//! primes will be implemented in the [`PrimeBufferExt`] trait.
//!
//! We also provide [`NaiveBuffer`] as a simple implementation of [`PrimeBuffer`] without any
//! external dependencies. The performance of the [`NaiveBuffer`] will not be extremely optimized,
//! but it will be efficient enough for most applications.
//!

use crate::factor::{pollard_rho, trial_division};
use crate::nt_funcs::{
    factorize128, is_prime64, next_prime, nth_prime_bounds, nth_prime_est, prev_prime,
};
use crate::primality::{PrimalityBase, PrimalityRefBase};
use crate::tables::{SMALL_PRIMES, SMALL_PRIMES_NEXT};
use crate::traits::{
    FactorizationConfig, Primality, PrimalityTestConfig, PrimalityUtils, PrimeBuffer,
};
use bitvec::{bitvec, prelude::Msb0};
use lru::LruCache;
use num_integer::Roots;
use rand::random;
use std::collections::BTreeMap;
use std::num::NonZeroUsize;

/// Extension functions that can utilize pre-generated primes
pub trait PrimeBufferExt: for<'a> PrimeBuffer<'a> {
    /// Test if an integer is a prime.
    ///
    /// For targets smaller than 2^64, the deterministic [`is_prime64`] will be used, otherwise
    /// the primality test algorithms can be specified by the `config` argument.
    ///
    /// The primality test can be either deterministic or probabilistic for large integers depending on the `config`.
    /// The return value is represented by the enum [Primality], which tells whether the primality test is deterministic
    /// or probabilistic.
    fn is_prime<T: PrimalityBase>(
        &self,
        target: &T,
        config: Option<PrimalityTestConfig>,
    ) -> Primality
    where
        for<'r> &'r T: PrimalityRefBase<T>,
    {
        // shortcuts
        if target.is_even() {
            return if target == &T::from_u8(2u8).unwrap() {
                Primality::Yes
            } else {
                Primality::No
            };
        }

        // do deterministic test if target is under 2^64
        if let Some(x) = target.to_u64() {
            return match is_prime64(x) {
                true => Primality::Yes,
                false => Primality::No,
            };
        }

        let config = config.unwrap_or_default();
        let mut probability = 1.;

        // miller-rabin test
        let mut witness_list: Vec<u64> = Vec::new();
        if config.sprp_trials > 0 {
            witness_list.extend(self.iter().take(config.sprp_trials));
            probability *= 1. - 0.25f32.powi(config.sprp_trials as i32);
        }
        if config.sprp_random_trials > 0 {
            for _ in 0..config.sprp_random_trials {
                // we have ensured target is larger than 2^64
                let mut w: u64 = rand::random();
                while witness_list.iter().any(|x| x == &w) {
                    w = rand::random();
                }
                witness_list.push(w);
            }
            probability *= 1. - 0.25f32.powi(config.sprp_random_trials as i32);
        }
        if !witness_list
            .into_iter()
            .all(|x| target.is_sprp(T::from_u64(x).unwrap()))
        {
            return Primality::No;
        }

        // lucas probable prime test
        if config.slprp_test {
            probability *= 1. - 4f32 / 15f32;
            if !target.is_slprp(None, None) {
                return Primality::No;
            }
        }
        if config.eslprp_test {
            probability *= 1. - 4f32 / 15f32;
            if !target.is_eslprp(None) {
                return Primality::No;
            }
        }

        Primality::Probable(probability)
    }

    /// Factorize an integer.
    ///
    /// For targets smaller than 2^64, the efficient [`crate::nt_funcs::factorize64`] will be used, otherwise
    /// the primality test and factorization algorithms can be specified by the `config` argument.
    ///
    /// The factorization result consists of two parts. The first is a map from prime factors to their exponents.
    /// If the factorization failed, the second part will be the remaining cofactors that are not factored, otherwise None
    /// is returned for the second part. It's ensured that the product of prime factors (and remaining cofactors if exist)
    /// is equal to the original target.
    fn factors<T: PrimalityBase>(
        &self,
        target: T,
        config: Option<FactorizationConfig>,
    ) -> (BTreeMap<T, usize>, Option<Vec<T>>)
    where
        for<'r> &'r T: PrimalityRefBase<T>,
    {
        // shortcut if the target is in u128 range
        if let Some(x) = target.to_u128() {
            let factors = factorize128(x)
                .into_iter()
                .map(|(k, v)| (T::from_u128(k).unwrap(), v))
                .collect();
            return (factors, None);
        }
        let config = config.unwrap_or_default();

        // test the existing primes
        let (result, factored) = trial_division(self.iter().copied(), target, config.td_limit);
        let mut result: BTreeMap<T, usize> = result
            .into_iter()
            .map(|(k, v)| (T::from_u64(k).unwrap(), v))
            .collect();

        // TODO: check is_perfect_power before other methods

        // find factors by dividing
        let mut failed = Vec::new();
        let mut config = config;
        config.td_limit = Some(0); // disable trial division when finding divisor
        match factored {
            Ok(res) => {
                if !res.is_one() {
                    result.insert(res, 1);
                }
            }
            Err(res) => {
                let mut todo = vec![res];
                while let Some(target) = todo.pop() {
                    if self
                        .is_prime(&target, Some(config.primality_config))
                        .probably()
                    {
                        *result.entry(target).or_insert(0) += 1;
                    } else if let Some(divisor) = self.divisor(&target, &mut config) {
                        todo.push(divisor.clone());
                        todo.push(target / divisor);
                    } else {
                        failed.push(target);
                    }
                }
            }
        };

        if failed.is_empty() {
            (result, None)
        } else {
            (result, Some(failed))
        }
    }

    /// Factorize an integer until all prime factors are found.
    ///
    /// This function will try to call [`PrimeBufferExt::factors`] function repeatedly until the target
    /// is fully factorized.
    fn factorize<T: PrimalityBase>(&self, target: T) -> BTreeMap<T, usize>
    where
        for<'r> &'r T: PrimalityRefBase<T>,
    {
        // TODO: prevent overhead of repeat trial division
        loop {
            let (result, remainder) = self.factors(target.clone(), None);
            if remainder.is_none() {
                break result;
            }
        }
    }

    /// Return a proper divisor of target (randomly), even works for very large numbers.
    /// Return `None` if no factor is found.
    ///
    /// Note: this method will not do a primality check
    fn divisor<T: PrimalityBase>(&self, target: &T, config: &mut FactorizationConfig) -> Option<T>
    where
        for<'r> &'r T: PrimalityRefBase<T>,
    {
        if matches!(config.td_limit, Some(0)) {
            // try to get a factor by trial division
            let tsqrt: T = Roots::sqrt(target) + T::one();
            let limit = if let Some(l) = config.td_limit {
                tsqrt.clone().min(T::from_u64(l).unwrap())
            } else {
                tsqrt.clone()
            };

            for p in self.iter().map(|p| T::from_u64(*p).unwrap()) {
                if p > tsqrt {
                    return None; // the number is a prime
                }
                if p > limit {
                    break;
                }
                if target.is_multiple_of(&p) {
                    return Some(p);
                }
            }
        }

        // try to get a factor using pollard_rho with 4x4 trials
        let below64 = target.to_u64().is_some();
        while config.rho_trials > 0 {
            let (start, offset) = if below64 {
                (
                    T::from_u8(random::<u8>()).unwrap() % target,
                    T::from_u8(random::<u8>()).unwrap() % target,
                )
            } else {
                (
                    T::from_u64(random::<u64>()).unwrap() % target,
                    T::from_u64(random::<u64>()).unwrap() % target,
                )
            };
            config.rho_trials -= 1;
            // TODO: change to a reasonable pollard rho limit
            // TODO: add other factorization methods
            if let (Some(p), _) = pollard_rho(target, start, offset, 1_048_576) {
                return Some(p);
            }
        }

        None
    }
}

impl<T> PrimeBufferExt for T where for<'a> T: PrimeBuffer<'a> {}

/// `NaiveBuffer` implements a very simple Sieve of Eratosthenes
pub struct NaiveBuffer {
    list: Vec<u64>, // list of found prime numbers
    next: u64, // all primes smaller than this value has to be in the prime list, should be an odd number
}

impl Default for NaiveBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl NaiveBuffer {
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        let list = SMALL_PRIMES.iter().map(|&p| u64::from(p)).collect();
        NaiveBuffer {
            list,
            next: SMALL_PRIMES_NEXT,
        }
    }
}

impl<'a> PrimeBuffer<'a> for NaiveBuffer {
    type PrimeIter = std::slice::Iter<'a, u64>;

    fn contains(&self, num: u64) -> bool {
        self.list.binary_search(&num).is_ok()
    }

    fn clear(&mut self) {
        self.list.truncate(16);
        self.list.shrink_to_fit();
        self.next = 55; // 16-th prime is 53
    }

    fn iter(&'a self) -> Self::PrimeIter {
        self.list.iter()
    }

    fn bound(&self) -> u64 {
        *self.list.last().unwrap()
    }

    fn reserve(&mut self, limit: u64) {
        let sieve_limit = (limit | 1) + 2; // make sure sieving limit is odd and larger than limit
        let current = self.next; // prevent borrowing self
        debug_assert!(current % 2 == 1);
        if sieve_limit < current {
            return;
        }

        // create sieve and filter with existing primes
        let mut sieve = bitvec![usize, Msb0; 0; ((sieve_limit - current) / 2) as usize];
        for p in self.list.iter().skip(1) {
            // skip pre-filtered 2
            let start = if p * p < current {
                p * ((current / p) | 1) // start from an odd factor
            } else {
                p * p
            };
            for multi in (start..sieve_limit).step_by(2 * (*p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // sieve with new primes
        for p in (current..Roots::sqrt(&sieve_limit) + 1).step_by(2) {
            for multi in (p * p..sieve_limit).step_by(2 * (p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // collect the sieve
        self.list
            .extend(sieve.iter_zeros().map(|x| (x as u64) * 2 + current));
        self.next = sieve_limit;
    }
}

impl NaiveBuffer {
    // FIXME: These functions could be implemented in the trait, but only after
    // RFC 2071 and https://github.com/cramertj/impl-trait-goals/issues/3

    /// Calculate the primorial function
    pub fn primorial<T: PrimalityBase + std::iter::Product>(&mut self, n: usize) -> T {
        self.nprimes(n).map(|&p| T::from_u64(p).unwrap()).product()
    }

    /// Returns all primes ≤ `limit`. The primes are sorted.
    // TODO: let primes return &[u64] instead of iterator, and create a separate iterator
    //       for endless prime iter. This can be a method in this trait, or standalone function,
    //       or implement as IntoIter. We can try to implement PrimeBuffer on primal first and see
    //       if it's reasonable to unifiy
    pub fn primes(&mut self, limit: u64) -> std::iter::Take<<Self as PrimeBuffer<'_>>::PrimeIter> {
        self.reserve(limit);
        let position = match self.list.binary_search(&limit) {
            Ok(p) => p + 1,
            Err(p) => p,
        }; // into_ok_or_err()
        self.list.iter().take(position)
    }

    /// Returns all primes ≤ `limit` and takes ownership. The primes are sorted.
    #[must_use]
    pub fn into_primes(mut self, limit: u64) -> std::vec::IntoIter<u64> {
        self.reserve(limit);
        let position = match self.list.binary_search(&limit) {
            Ok(p) => p + 1,
            Err(p) => p,
        }; // into_ok_or_err()
        self.list.truncate(position);
        self.list.into_iter()
    }

    /// Returns primes of certain amount counting from 2. The primes are sorted.
    pub fn nprimes(
        &mut self,
        count: usize,
    ) -> std::iter::Take<<Self as PrimeBuffer<'_>>::PrimeIter> {
        let (_, bound) = nth_prime_bounds(&(count as u64))
            .expect("Estimated size of the largest prime will be larger than u64 limit");
        self.reserve(bound);
        debug_assert!(self.list.len() >= count);
        self.list.iter().take(count)
    }

    /// Returns primes of certain amount counting from 2 and takes ownership. The primes are sorted.
    #[must_use]
    pub fn into_nprimes(mut self, count: usize) -> std::vec::IntoIter<u64> {
        let (_, bound) = nth_prime_bounds(&(count as u64))
            .expect("Estimated size of the largest prime will be larger than u64 limit");
        self.reserve(bound);
        debug_assert!(self.list.len() >= count);
        self.list.truncate(count);
        self.list.into_iter()
    }

    /// Get the n-th prime (n counts from 1).
    ///
    /// Theoretically the result can be larger than 2^64, but it will takes forever to
    /// calculate that so we just return `u64` instead of `Option<u64>` here.
    pub fn nth_prime(&mut self, n: u64) -> u64 {
        if n < self.list.len() as u64 {
            return self.list[n as usize - 1];
        }

        // Directly sieve if the limit is small
        const THRESHOLD_NTH_PRIME_SIEVE: u64 = 4096;
        if n <= THRESHOLD_NTH_PRIME_SIEVE {
            return *self.nprimes(n as usize).next_back().unwrap();
        }

        // Check primes starting from estimation
        let mut x = prev_prime(&nth_prime_est(&n).unwrap(), None).unwrap();
        let mut pi = self.prime_pi(x);

        while pi > n {
            x = prev_prime(&x, None).unwrap();
            pi -= 1;
        }
        while pi < n {
            x = next_prime(&x, None).unwrap();
            pi += 1;
        }
        x
    }

    /// Legendre's phi function, used as a helper function for [`Self::prime_pi`]
    pub fn prime_phi(&mut self, x: u64, a: usize, cache: &mut LruCache<(u64, usize), u64>) -> u64 {
        if a == 1 {
            return x.div_ceil(2);
        }
        if let Some(v) = cache.get(&(x, a)) {
            return *v;
        }
        let t1 = self.prime_phi(x, a - 1, cache);
        let pa = self.nth_prime(a as u64);
        let t2 = self.prime_phi(x / pa, a - 1, cache);
        let t = t1 - t2;
        cache.put((x, a), t);
        t
    }

    /// Calculate the prime π function, i.e. number of primes ≤ `limit`.
    ///
    /// Meissel-Lehmer method will be used if the input `limit` is large enough.
    pub fn prime_pi(&mut self, limit: u64) -> u64 {
        // Directly sieve if the limit is small
        const THRESHOLD_PRIME_PI_SIEVE: u64 = 38873; // 4096th prime
        if &limit <= self.list.last().unwrap() || limit <= THRESHOLD_PRIME_PI_SIEVE {
            self.reserve(limit);

            return match self.list.binary_search(&limit) {
                Ok(pos) => (pos + 1) as u64,
                Err(pos) => pos as u64,
            };
        }

        // Then use Meissel-Lehmer method.
        let b = limit.sqrt();
        let a = b.sqrt();
        let c = limit.cbrt();
        self.reserve(b);

        let a = self.prime_pi(a);
        let b = self.prime_pi(b);
        let c = self.prime_pi(c);

        let cache_cap = NonZeroUsize::new(a as usize).unwrap(); // a > 0 because limit > THRESHOLD_PRIME_PI_SIEVE
        let mut phi_cache = LruCache::new(cache_cap);
        let mut sum =
            self.prime_phi(limit, a as usize, &mut phi_cache) + (b + a - 2) * (b - a + 1) / 2;
        for i in (a + 1)..=b {
            let w = limit / self.nth_prime(i);
            sum -= self.prime_pi(w);
            if i <= c {
                let l = self.prime_pi(w.sqrt());
                sum += (l * (l - 1) - i * (i - 3)) / 2 - 1;
                for j in i..=l {
                    let pj = self.nth_prime(j);
                    sum -= self.prime_pi(w / pj);
                }
            }
        }
        sum
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mint::SmallMint;
    #[cfg(feature = "num-bigint")]
    use core::str::FromStr;
    #[cfg(feature = "num-bigint")]
    use num_bigint::BigUint;
    use rand::random;

    #[test]
    fn prime_generation_test() {
        const PRIME50: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
        const PRIME300: [u64; 62] = [
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
            181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
            277, 281, 283, 293,
        ];

        let mut pb = NaiveBuffer::new();
        assert_eq!(pb.primes(50).copied().collect::<Vec<_>>(), PRIME50);
        assert_eq!(pb.primes(300).copied().collect::<Vec<_>>(), PRIME300);

        // test when limit itself is a prime
        pb.clear();
        assert_eq!(pb.primes(293).copied().collect::<Vec<_>>(), PRIME300);
        pb = NaiveBuffer::new();
        assert_eq!(*pb.primes(257).next_back().unwrap(), 257); // boundary of small table
        pb = NaiveBuffer::new();
        assert_eq!(*pb.primes(8167).next_back().unwrap(), 8167); // boundary of large table
    }

    #[test]
    fn nth_prime_test() {
        let mut pb = NaiveBuffer::new();
        assert_eq!(pb.nth_prime(10000), 104_729);
        assert_eq!(pb.nth_prime(20000), 224_737);
        assert_eq!(pb.nth_prime(10000), 104_729); // use existing primes

        // Riemann zeta based, test on OEIS:A006988
        assert_eq!(pb.nth_prime(10u64.pow(4)), 104_729);
        assert_eq!(pb.nth_prime(10u64.pow(5)), 1_299_709);
        assert_eq!(pb.nth_prime(10u64.pow(6)), 15_485_863);
        assert_eq!(pb.nth_prime(10u64.pow(7)), 179_424_673);
    }

    #[test]
    fn prime_pi_test() {
        let mut pb = NaiveBuffer::new();
        assert_eq!(pb.prime_pi(8161), 1024); // 8161 is the 1024th prime
        assert_eq!(pb.prime_pi(10000), 1229);
        assert_eq!(pb.prime_pi(20000), 2262);
        assert_eq!(pb.prime_pi(38873), 4096);

        pb.clear(); // sieving from scratch
        assert_eq!(pb.prime_pi(8161), 1024);
        assert_eq!(pb.prime_pi(10000), 1229);
        assert_eq!(pb.prime_pi(20000), 2262);
        assert_eq!(pb.prime_pi(10000), 1229); // use existing primes

        // Meissel–Lehmer algorithm, test on OEIS:A006880
        assert_eq!(pb.prime_pi(10u64.pow(5)), 9592);
        assert_eq!(pb.prime_pi(10u64.pow(6)), 78498);
        assert_eq!(pb.prime_pi(10u64.pow(7)), 664_579);
        assert_eq!(pb.prime_pi(10u64.pow(8)), 5_761_455);
    }

    #[test]
    fn is_prime_test() {
        // test for is_prime
        let pb = NaiveBuffer::new();

        // some mersenne numbers
        assert_eq!(pb.is_prime(&(2u32.pow(19) - 1), None), Primality::Yes);
        assert_eq!(pb.is_prime(&(2u32.pow(23) - 1), None), Primality::No);
        assert!(matches!(
            pb.is_prime(&(2u128.pow(89) - 1), None),
            Primality::Probable(_)
        ));
        assert!(matches!(
            pb.is_prime(&SmallMint::from(2u128.pow(89) - 1), None),
            Primality::Probable(_)
        ));

        // test against small prime assertion
        for _ in 0..100 {
            let target = random::<u64>();
            assert_eq!(
                !is_prime64(target),
                matches!(
                    pb.is_prime(&target, Some(PrimalityTestConfig::bpsw())),
                    Primality::No
                )
            );
        }

        // test large numbers
        const P: u128 = 18_699_199_384_836_356_663; // https://golang.org/issue/638
        assert!(matches!(pb.is_prime(&P, None), Primality::Probable(_)));
        assert!(matches!(
            pb.is_prime(&P, Some(PrimalityTestConfig::bpsw())),
            Primality::Probable(_)
        ));
        assert!(matches!(
            pb.is_prime(&SmallMint::from(P), None),
            Primality::Probable(_)
        ));
        assert!(matches!(
            pb.is_prime(&SmallMint::from(P), Some(PrimalityTestConfig::bpsw())),
            Primality::Probable(_)
        ));

        const P2: u128 = 2_019_922_777_445_599_503_530_083;
        assert!(matches!(pb.is_prime(&P2, None), Primality::Probable(_)));
        assert!(matches!(
            pb.is_prime(&P2, Some(PrimalityTestConfig::bpsw())),
            Primality::Probable(_)
        ));
        assert!(matches!(
            pb.is_prime(&SmallMint::from(P2), None),
            Primality::Probable(_)
        ));
        assert!(matches!(
            pb.is_prime(&SmallMint::from(P2), Some(PrimalityTestConfig::bpsw())),
            Primality::Probable(_)
        ));

        #[cfg(feature = "num-bigint")]
        {
            let large_primes = [
                "98920366548084643601728869055592650835572950932266967461790948584315647051443",
                "94560208308847015747498523884063394671606671904944666360068158221458669711639",

                // http://primes.utm.edu/lists/small/small3.html
                "449417999055441493994709297093108513015373787049558499205492347871729927573118262811508386655998299074566974373711472560655026288668094291699357843464363003144674940345912431129144354948751003607115263071543163",
                "230975859993204150666423538988557839555560243929065415434980904258310530753006723857139742334640122533598517597674807096648905501653461687601339782814316124971547968912893214002992086353183070342498989426570593",
                "5521712099665906221540423207019333379125265462121169655563495403888449493493629943498064604536961775110765377745550377067893607246020694972959780839151452457728855382113555867743022746090187341871655890805971735385789993",
                "203956878356401977405765866929034577280193993314348263094772646453283062722701277632936616063144088173312372882677123879538709400158306567338328279154499698366071906766440037074217117805690872792848149112022286332144876183376326512083574821647933992961249917319836219304274280243803104015000563790123",
                // ECC primes: http://tools.ietf.org/html/draft-ladd-safecurves-02
                "3618502788666131106986593281521497120414687020801267626233049500247285301239",                                                                                  // Curve1174: 2^251-9
                "57896044618658097711785492504343953926634992332820282019728792003956564819949",                                                                                 // Curve25519: 2^255-19
                "9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576599",                                           // E-382: 2^382-105
                "42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472367",                                 // Curve41417: 2^414-17
                "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151", // E-521: 2^521-1

                // https://github.com/AtropineTears/num-primes/issues/1#issuecomment-934629597
                "169511182982703321453314585423962898651587669459838234386506572286328885534468792292646838949809616446341407457141008401355628947670484184607678853094537849610289912805960069455687743151708433319901176932959509872662610091644590437761688516626993416011399330087939042347256922771590903190536793274742859624657"
            ];
            for pstr in large_primes {
                assert!(
                    pb.is_prime(&BigUint::from_str(pstr).unwrap(), None)
                        .probably(),
                    "false negative prime {}",
                    pstr
                )
            }

            let large_composites = [
                "21284175091214687912771199898307297748211672914763848041968395774954376176754",
                "6084766654921918907427900243509372380954290099172559290432744450051395395951",
                "84594350493221918389213352992032324280367711247940675652888030554255915464401",
                "82793403787388584738507275144194252681",

                // Arnault, "Rabin-Miller Primality Test: Composite Numbers Which Pass It",
                // Mathematics of Computation, 64(209) (January 1995), pp. 335-361.
                "1195068768795265792518361315725116351898245581", // strong pseudoprime to prime bases 2 through 29
                // strong pseudoprime to all prime bases up to 200
                "8038374574536394912570796143419421081388376882875581458374889175222974273765333652186502336163960045457915042023603208766569966760987284043965408232928738791850869166857328267761771029389697739470167082304286871099974399765441448453411558724506334092790222752962294149842306881685404326457534018329786111298960644845216191652872597534901",
            ];
            for cstr in large_composites {
                assert!(
                    !pb.is_prime(
                        &BigUint::from_str(cstr).unwrap(),
                        Some(PrimalityTestConfig::bpsw())
                    )
                    .probably(),
                    "false positive prime {}",
                    cstr
                )
            }
        }
    }

    #[test]
    fn pb_factors_test() {
        #[cfg(feature = "num-bigint")]
        {
            let pb = NaiveBuffer::new();
            let m131 = BigUint::from(2u8).pow(131) - 1u8; // m131/263 is a large prime
            let (fac, r) = pb.factors(m131, None);
            assert!(fac.len() == 2 && r.is_none());
        }
    }

    // --- NaiveBuffer::clear() + re-reserve ---
    #[test]
    fn test_clear_and_re_reserve() {
        let mut pb = NaiveBuffer::new();
        pb.reserve(100);
        assert!(pb.bound() >= 100);
        assert!(pb.contains(97));
        pb.clear();
        // After clear, only 16 primes remain (up to 53)
        assert_eq!(pb.bound(), 53);
        assert!(!pb.contains(97)); // 97 should be gone
                                   // Re-reserve brings primes back
        pb.reserve(100);
        assert!(pb.bound() >= 100);
        assert!(pb.contains(97));
    }

    // --- into_primes() ---
    #[test]
    fn test_into_primes() {
        let pb = NaiveBuffer::new();
        let primes: Vec<u64> = pb.into_primes(20).collect();
        assert_eq!(primes, vec![2, 3, 5, 7, 11, 13, 17, 19]);
    }

    #[test]
    fn test_into_primes_exact_boundary() {
        let pb = NaiveBuffer::new();
        // 23 is a prime, should be included
        let primes: Vec<u64> = pb.into_primes(23).collect();
        assert_eq!(*primes.last().unwrap(), 23);
    }

    // --- into_nprimes() ---
    #[test]
    fn test_into_nprimes() {
        let pb = NaiveBuffer::new();
        let primes: Vec<u64> = pb.into_nprimes(10).collect();
        assert_eq!(primes.len(), 10);
        assert_eq!(primes[0], 2);
        assert_eq!(primes[9], 29);
    }

    // --- primorial() ---
    #[test]
    fn test_primorial() {
        let mut pb = NaiveBuffer::new();
        // primorial(4) = 2 * 3 * 5 * 7 = 210
        let result: u64 = pb.primorial(4);
        assert_eq!(result, 210);
        // primorial(1) = 2
        let result: u64 = pb.primorial(1);
        assert_eq!(result, 2);
    }

    // --- is_prime with eslprp config ---
    #[test]
    fn test_is_prime_eslprp_config() {
        let pb = NaiveBuffer::new();
        let config = PrimalityTestConfig {
            sprp_trials: 1,
            sprp_random_trials: 0,
            slprp_test: false,
            eslprp_test: true,
        };
        let p: u128 = 18_699_199_384_836_356_663;
        assert!(pb.is_prime(&p, Some(config)).probably());
    }

    // --- is_prime with strict config ---
    #[test]
    fn test_is_prime_strict_config() {
        let pb = NaiveBuffer::new();
        let p: u128 = 2_019_922_777_445_599_503_530_083;
        assert!(pb
            .is_prime(&p, Some(PrimalityTestConfig::strict()))
            .probably());

        // composite should fail
        let c: u128 = 2_019_922_777_445_599_503_530_083 * 3;
        assert!(!pb
            .is_prime(&c, Some(PrimalityTestConfig::strict()))
            .probably());
    }

    // --- factors() for u128 composites ---
    #[test]
    fn test_factors_u128() {
        let pb = NaiveBuffer::new();
        // Factor a u128 composite: 2^3 * 3^2 * 5 = 360
        let (factors, remainder) = pb.factors(360u128, None);
        assert!(remainder.is_none());
        assert_eq!(factors[&2], 3);
        assert_eq!(factors[&3], 2);
        assert_eq!(factors[&5], 1);
    }

    #[test]
    fn test_factors_u128_large() {
        let pb = NaiveBuffer::new();
        // 2^64 + 1 = 274177 * 67280421310721
        let n: u128 = (1u128 << 64) + 1;
        let (factors, remainder) = pb.factors(n, None);
        assert!(remainder.is_none());
        assert!(factors.contains_key(&274177u128));
    }

    // --- is_prime on even numbers ---
    #[test]
    fn test_is_prime_even() {
        let pb = NaiveBuffer::new();
        assert_eq!(pb.is_prime(&2u128, None), Primality::Yes);
        assert_eq!(pb.is_prime(&4u128, None), Primality::No);
    }

    // --- factors with strict config ---
    #[test]
    fn test_factors_with_strict_config() {
        let pb = NaiveBuffer::new();
        let (factors, remainder) = pb.factors(100u64, Some(FactorizationConfig::strict()));
        assert!(remainder.is_none());
        assert_eq!(factors[&2], 2);
        assert_eq!(factors[&5], 2);
    }
}

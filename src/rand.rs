use crate::mint::SmallMint;
use crate::nt_funcs::{is_prime, is_prime64, next_prime};
use crate::{PrimalityTestConfig, RandPrime};
#[cfg(feature = "num-bigint")]
use num_bigint::{BigUint, RandBigInt};
use rand::Rng;

macro_rules! impl_randprime_prim {
    ($($T:ty)*) => {$(
        impl<R: Rng> RandPrime<$T> for R {
            #[inline]
            fn gen_prime(&mut self, bit_size: usize, _: Option<PrimalityTestConfig>) -> $T {
                if bit_size > (<$T>::BITS as usize) {
                    panic!("The given bit size limit exceeded the capacity of the integer type!")
                }

                loop {
                    let t: $T = self.gen();
                    let t = (t >> (<$T>::BITS - bit_size as u32)) | 1; // filter even numbers
                    if is_prime64(t as u64) {
                        break t
                    } else if let Some(p) = next_prime(&t, None) {
                        // deterministic primality test will be used for integers under u64
                        break p
                    }
                }
            }

            #[inline]
            fn gen_prime_exact(&mut self, bit_size: usize, _: Option<PrimalityTestConfig>) -> $T {
                if bit_size > (<$T>::BITS as usize) {
                    panic!("The given bit size limit exceeded the capacity of the integer type!")
                }

                loop {
                    let t: $T = self.gen();
                    let t = (t >> (<$T>::BITS - bit_size as u32)) | 1 | (1 << (bit_size - 1));
                    if is_prime64(t as u64) {
                        break t
                    } else if let Some(p) = next_prime(&t, None) {
                        // deterministic primality test will be used for integers under u64
                        break p
                    }
                }
            }

            #[inline]
            fn gen_safe_prime(&mut self, bit_size: usize) -> $T {
                loop {
                    // deterministic primality test will be used for integers under u64
                    let p = self.gen_prime(bit_size, None);

                    // test (p-1)/2
                    if is_prime64((p >> 1) as u64) {
                        break p
                    }
                    // test 2p+1
                    if let Some(p2) = p.checked_mul(2).and_then(|v| v.checked_add(1)) {
                        if is_prime64(p2 as u64) {
                            break p2
                        }
                    }
                }
            }

            #[inline]
            fn gen_safe_prime_exact(&mut self, bit_size: usize) -> $T {
                loop {
                    // deterministic primality test will be used for integers under u64
                    let p: $T = self.gen_prime_exact(bit_size, None);

                    // test (p-1)/2
                    if is_prime64((p >> 1) as u64) {
                        break p
                    }
                }
            }
        }
    )*}
}
impl_randprime_prim!(u8 u16 u32 u64);

impl<R: Rng> RandPrime<u128> for R {
    #[inline]
    fn gen_prime(&mut self, bit_size: usize, config: Option<PrimalityTestConfig>) -> u128 {
        if bit_size > (u128::BITS as usize) {
            panic!("The given bit size limit exceeded the capacity of the integer type!")
        }

        loop {
            let t: u128 = self.gen();
            let t = (t >> (u128::BITS - bit_size as u32)) | 1; // filter even numbers
            if is_prime(&SmallMint::from(t), config).probably() {
                break t;
            } else if let Some(p) = next_prime(&t, None) {
                // deterministic primality test will be used for integers under u64
                break p;
            }
        }
    }

    #[inline]
    fn gen_prime_exact(&mut self, bit_size: usize, config: Option<PrimalityTestConfig>) -> u128 {
        if bit_size > (u128::BITS as usize) {
            panic!("The given bit size limit exceeded the capacity of the integer type!")
        }

        loop {
            let t: u128 = self.gen();
            let t = (t >> (u128::BITS - bit_size as u32)) | 1 | (1 << (bit_size - 1));
            if is_prime(&SmallMint::from(t), config).probably() {
                break t;
            } else if let Some(p) = next_prime(&t, None) {
                // deterministic primality test will be used for integers under u64
                break p;
            }
        }
    }

    #[inline]
    fn gen_safe_prime(&mut self, bit_size: usize) -> u128 {
        loop {
            let config = Some(PrimalityTestConfig::strict());
            let p = self.gen_prime(bit_size, config);
            if is_prime(&SmallMint::from(p >> 1), config).probably() {
                break p;
            }
            if let Some(p2) = p.checked_mul(2).and_then(|v| v.checked_add(1)) {
                if is_prime(&p2, config).probably() {
                    break p2;
                }
            }
        }
    }

    #[inline]
    fn gen_safe_prime_exact(&mut self, bit_size: usize) -> u128 {
        loop {
            let config = Some(PrimalityTestConfig::strict());
            let p = self.gen_prime_exact(bit_size, config);
            if is_prime(&SmallMint::from(p >> 1), config).probably() {
                break p;
            }
        }
    }
}

#[cfg(feature = "num-bigint")]
impl<R: Rng> RandPrime<BigUint> for R {
    #[inline]
    fn gen_prime(&mut self, bit_size: usize, config: Option<PrimalityTestConfig>) -> BigUint {
        loop {
            let mut t = self.gen_biguint(bit_size as u64);
            t.set_bit(0, true); // filter even numbers
            if is_prime(&t, config).probably() {
                break t;
            } else if let Some(p) = next_prime(&t, config) {
                break p;
            }
        }
    }

    #[inline]
    fn gen_prime_exact(&mut self, bit_size: usize, config: Option<PrimalityTestConfig>) -> BigUint {
        loop {
            let mut t = self.gen_biguint(bit_size as u64);
            t.set_bit(0, true); // filter even numbers
            t.set_bit(bit_size as u64 - 1, true);
            if is_prime(&t, config).probably() {
                break t;
            } else if let Some(p) = next_prime(&t, config) {
                break p;
            }
        }
    }

    #[inline]
    fn gen_safe_prime(&mut self, bit_size: usize) -> BigUint {
        let config = Some(PrimalityTestConfig::strict());
        let p = self.gen_prime(bit_size, config);
        if is_prime(&(&p >> 1u8), config).probably() {
            return p;
        }
        let p2 = (p << 1u8) + 1u8;
        if is_prime(&p2, config).probably() {
            return p2;
        }

        self.gen_safe_prime(bit_size)
    }

    #[inline]
    fn gen_safe_prime_exact(&mut self, bit_size: usize) -> BigUint {
        let config = Some(PrimalityTestConfig::strict());
        loop {
            let p: BigUint = self.gen_prime_exact(bit_size, config);
            if is_prime(&(&p >> 1u8), config).probably() {
                return p;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nt_funcs::is_safe_prime;

    #[test]
    fn rand_prime() {
        let mut rng = rand::thread_rng();

        // test random prime generation for each size
        let p: u8 = rng.gen_prime(8, None);
        assert!(is_prime64(p as u64));
        let p: u16 = rng.gen_prime(16, None);
        assert!(is_prime64(p as u64));
        let p: u32 = rng.gen_prime(32, None);
        assert!(is_prime64(p as u64));
        let p: u64 = rng.gen_prime(64, None);
        assert!(is_prime64(p));
        let p: u128 = rng.gen_prime(128, None);
        assert!(is_prime(&p, None).probably());

        // test random safe prime generation
        let p: u8 = rng.gen_safe_prime(8);
        assert!(is_safe_prime(&p).probably());
        let p: u32 = rng.gen_safe_prime(32);
        assert!(is_safe_prime(&p).probably());
        let p: u128 = rng.gen_safe_prime(128);
        assert!(is_safe_prime(&p).probably());

        #[cfg(feature = "num-bigint")]
        {
            let p: BigUint = rng.gen_prime(512, None);
            assert!(is_prime(&p, None).probably());
            let p: BigUint = rng.gen_safe_prime(192);
            assert!(is_safe_prime(&p).probably());
        }

        // test bit size limit
        let p: u16 = rng.gen_prime(12, None);
        assert!(p < (1 << 12));
        let p: u32 = rng.gen_prime(24, None);
        assert!(p < (1 << 24));
    }

    #[test]
    fn rand_prime_exact() {
        let mut rng = rand::thread_rng();

        // test exact size prime generation
        let p: u8 = rng.gen_prime_exact(8, None);
        assert!(is_prime64(p as u64));
        assert_eq!(p.leading_zeros(), 0);
        let p: u32 = rng.gen_prime_exact(32, None);
        assert!(is_prime64(p as u64));
        assert_eq!(p.leading_zeros(), 0);
        let p: u128 = rng.gen_prime_exact(128, None);
        assert!(is_prime(&p, None).probably());
        assert_eq!(p.leading_zeros(), 0);

        // test random safe prime generation
        let p: u8 = rng.gen_safe_prime_exact(8);
        assert!(is_safe_prime(&p).probably());
        assert_eq!(p.leading_zeros(), 0);
        let p: u32 = rng.gen_safe_prime_exact(32);
        assert!(is_safe_prime(&p).probably());
        assert_eq!(p.leading_zeros(), 0);
        let p: u128 = rng.gen_safe_prime_exact(128);
        assert!(is_safe_prime(&p).probably());
        assert_eq!(p.leading_zeros(), 0);

        #[cfg(feature = "num-bigint")]
        {
            let p: BigUint = rng.gen_prime_exact(192, None);
            assert!(is_prime(&p, None).probably());
            assert_eq!(p.bits(), 192);
            let p: BigUint = rng.gen_safe_prime_exact(192);
            assert!(is_safe_prime(&p).probably());
            assert_eq!(p.bits(), 192);
        }
    }
}

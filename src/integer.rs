//! Backend implementations for integers

use crate::tables::{CUBIC_MODULI, CUBIC_RESIDUAL, QUAD_MODULI, QUAD_RESIDUAL};
use crate::traits::{BitTest, ExactRoots};

#[cfg(feature = "num-bigint")]
use num_bigint::{BigInt, BigUint, ToBigInt};
#[cfg(feature = "num-bigint")]
use num_traits::{One, Signed, ToPrimitive, Zero};

macro_rules! impl_bittest_prim {
    ($($T:ty)*) => {$(
        impl BitTest for $T {
            #[inline]
            fn bits(&self) -> usize {
                (<$T>::BITS - self.leading_zeros()) as usize
            }
            #[inline]
            fn bit(&self, position: usize) -> bool {
                self & (1 << position) > 0
            }
            #[inline]
            fn trailing_zeros(&self) -> usize {
                <$T>::trailing_zeros(*self) as usize
            }
        }
    )*}
}
impl_bittest_prim!(u8 u16 u32 u64 u128 usize);

#[cfg(feature = "num-bigint")]
impl BitTest for BigUint {
    fn bit(&self, position: usize) -> bool {
        self.bit(position as u64)
    }
    fn bits(&self) -> usize {
        self.bits() as usize
    }
    #[inline]
    fn trailing_zeros(&self) -> usize {
        match self.trailing_zeros() {
            Some(zeros) => zeros as usize,
            None => 0,
        }
    }
}

macro_rules! impl_exactroot_prim {
    ($($T:ty)*) => {$(
        impl ExactRoots for $T {
            fn sqrt_exact(&self) -> Option<Self> {
                if self < &0 { return None; }
                let shift = self.trailing_zeros();

                // the general form of any square number is (2^(2m))(8N+1)
                if shift & 1 == 1 { return None; }
                if (self >> shift) & 7 != 1 { return None; }
                self.nth_root_exact(2)
            }
        }
    )*};
    // TODO: it might worth use QUAD_RESIDUE and CUBIC_RESIDUE for large size
    //       primitive integers, need benchmark
}
impl_exactroot_prim!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

#[cfg(feature = "num-bigint")]
impl ExactRoots for BigUint {
    fn sqrt_exact(&self) -> Option<Self> {
        // shortcuts
        if self.is_zero() {
            return Some(BigUint::zero());
        }
        if let Some(v) = self.to_u64() {
            return v.sqrt_exact().map(BigUint::from);
        }

        // check mod 2
        let shift = self.trailing_zeros().unwrap();
        if shift & 1 == 1 {
            return None;
        }
        if !((self >> shift) & BigUint::from(7u8)).is_one() {
            return None;
        }

        // check other moduli
        #[cfg(not(feature = "big-table"))]
        for (m, res) in QUAD_MODULI.iter().zip(QUAD_RESIDUAL) {
            // need to &63 since we have 65 in QUAD_MODULI
            if (res >> ((self % m).to_u8().unwrap() & 63)) & 1 == 0 {
                return None;
            }
        }
        #[cfg(feature = "big-table")]
        for (m, res) in QUAD_MODULI.iter().zip(QUAD_RESIDUAL) {
            let rem = (self % m).to_u16().unwrap();
            if (res[(rem / 64) as usize] >> (rem % 64)) & 1 == 0 {
                return None;
            }
        }

        self.nth_root_exact(2)
    }

    fn cbrt_exact(&self) -> Option<Self> {
        // shortcuts
        if self.is_zero() {
            return Some(BigUint::zero());
        }
        if let Some(v) = self.to_u64() {
            return v.cbrt_exact().map(BigUint::from);
        }

        // check mod 2
        let shift = self.trailing_zeros().unwrap();
        if shift % 3 != 0 {
            return None;
        }

        // check other moduli
        #[cfg(not(feature = "big-table"))]
        for (m, res) in CUBIC_MODULI.iter().zip(CUBIC_RESIDUAL) {
            if (res >> (self % m).to_u8().unwrap()) & 1 == 0 {
                return None;
            }
        }
        #[cfg(feature = "big-table")]
        for (m, res) in CUBIC_MODULI.iter().zip(CUBIC_RESIDUAL) {
            let rem = (self % m).to_u16().unwrap();
            if (res[(rem / 64) as usize] >> (rem % 64)) & 1 == 0 {
                return None;
            }
        }

        self.nth_root_exact(3)
    }
}

#[cfg(feature = "num-bigint")]
impl ExactRoots for BigInt {
    fn sqrt_exact(&self) -> Option<Self> {
        self.to_biguint()
            .and_then(|u| u.sqrt_exact())
            .and_then(|u| u.to_bigint())
    }
    fn cbrt_exact(&self) -> Option<Self> {
        self.magnitude()
            .cbrt_exact()
            .and_then(|u| u.to_bigint())
            .map(|v| if self.is_negative() { -v } else { v })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand;

    #[test]
    fn exact_root_test() {
        // some simple tests
        assert!(matches!(ExactRoots::sqrt_exact(&3u8), None));
        assert!(matches!(ExactRoots::sqrt_exact(&4u8), Some(2)));
        assert!(matches!(ExactRoots::sqrt_exact(&9u8), Some(3)));
        assert!(matches!(ExactRoots::sqrt_exact(&18u8), None));
        assert!(matches!(ExactRoots::sqrt_exact(&3i8), None));
        assert!(matches!(ExactRoots::sqrt_exact(&4i8), Some(2)));
        assert!(matches!(ExactRoots::sqrt_exact(&9i8), Some(3)));
        assert!(matches!(ExactRoots::sqrt_exact(&18i8), None));

        // test fast implementations of sqrt against nth_root
        for _ in 0..100 {
            let x = rand::random::<u32>();
            assert_eq!(
                ExactRoots::sqrt_exact(&x),
                ExactRoots::nth_root_exact(&x, 2)
            );
            assert_eq!(
                ExactRoots::cbrt_exact(&x),
                ExactRoots::nth_root_exact(&x, 3)
            );
            let x = rand::random::<i32>();
            assert_eq!(
                ExactRoots::cbrt_exact(&x),
                ExactRoots::nth_root_exact(&x, 3)
            );
        }
        // test perfect powers
        for _ in 0..100 {
            let x = rand::random::<u32>() as u64;
            assert!(matches!(ExactRoots::sqrt_exact(&(x * x)), Some(v) if v == x));
            let x = rand::random::<i16>() as i64;
            assert!(matches!(ExactRoots::cbrt_exact(&(x * x * x)), Some(v) if v == x));
        }
        // test non-perfect powers
        for _ in 0..100 {
            let x = rand::random::<u32>() as u64;
            let y = rand::random::<u32>() as u64;
            if x == y {
                continue;
            }
            assert!(ExactRoots::sqrt_exact(&(x * y)).is_none());
        }

        #[cfg(feature = "num-bigint")]
        {
            use num_bigint::RandBigInt;
            let mut rng = rand::thread_rng();
            // test fast implementations of sqrt against nth_root
            for _ in 0..10 {
                let x = rng.gen_biguint(150);
                assert_eq!(
                    ExactRoots::sqrt_exact(&x),
                    ExactRoots::nth_root_exact(&x, 2)
                );
                assert_eq!(
                    ExactRoots::cbrt_exact(&x),
                    ExactRoots::nth_root_exact(&x, 3)
                );
                let x = rng.gen_bigint(150);
                assert_eq!(
                    ExactRoots::cbrt_exact(&x),
                    ExactRoots::nth_root_exact(&x, 3)
                );
            }
            // test perfect powers
            for _ in 0..10 {
                let x = rng.gen_biguint(150);
                assert!(matches!(ExactRoots::sqrt_exact(&(&x * &x)), Some(v) if v == x));
                let x = rng.gen_biguint(150);
                assert!(
                    matches!(ExactRoots::cbrt_exact(&(&x * &x * &x)), Some(v) if v == x),
                    "failed at {}",
                    x
                );
            }
            // test non-perfect powers
            for _ in 0..10 {
                let x = rng.gen_biguint(150);
                let y = rng.gen_biguint(150);
                if x == y {
                    continue;
                }
                assert!(ExactRoots::sqrt_exact(&(x * y)).is_none());
            }
        }
    }
}

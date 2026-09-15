use crate::traits::{BitTest, ExactRoots, PrimalityUtils};
use either::Either;
use num_integer::{Integer, Roots};
use num_modular::{ModularCoreOps, ModularRefOps, ModularUnaryOps};
use num_traits::{FromPrimitive, NumRef, RefNum, ToPrimitive};

/// Utilities for the Lucas pseudoprime test
pub trait LucasUtils {
    /// Find Lucas sequence to n with modulo m, i.e. $U_{n+1}(P,Q)$ mod m and $V_{n+1}(P,Q)$
    fn lucasm(p: usize, q: isize, m: Self, n: Self) -> (Self, Self)
    where
        Self: Sized;

    /// Find proper parameters P and Q of Lucas pseudoprime test for n, such that Jacobi(D|n) is -1,
    /// using Selfridge's method (referred as method A by Baillie).
    fn pq_selfridge(n: &Self) -> (usize, isize);

    /// Find proper parameters P of extra strong Lucas pseudoprime test for n, such that Jacobi(D|n) is -1,
    /// using brute-force searching (referred as method C by Baillie)
    fn p_bruteforce(n: &Self) -> usize;
}

impl<T> LucasUtils for T
where
    T: Integer
        + FromPrimitive
        + ToPrimitive
        + NumRef
        + BitTest
        + ExactRoots
        + Clone
        + ModularRefOps,
    for<'r> &'r T:
        RefNum<T> + ModularUnaryOps<&'r T, Output = T> + ModularCoreOps<&'r T, &'r T, Output = T>,
{
    fn lucasm(p: usize, q: isize, m: Self, n: Self) -> (Self, Self) {
        // Reference: <https://en.wikipedia.org/wiki/Lucas_sequence>
        // and Peter Hackman, "Elementary Number Theory", section "L.XVII Scalar" <http://hackmat.se/kurser/TATM54/booktot.pdf>

        let p = T::from_usize(p).unwrap() % &m;
        let q = if q >= 0 {
            T::from_isize(q).unwrap() % &m
        } else {
            T::from_isize(-q).unwrap().negm(&m)
        };

        let mut uk = T::zero() % &m; // U(k), mod m for montgomery form
        let mut uk1 = T::one() % &m; // U(k+1)

        for i in (0..n.bits()).rev() {
            if n.bit(i) {
                // k' = 2k+1
                // U(k'+1) = U(2k+2) = PU(k+1)² - 2*QU(k+1)U(k)
                let uk1sq = (&uk1).sqm(&m);
                let t1 = (&p).mulm(&uk1sq, &m);
                let t2 = (&q).mulm(&uk1, &m).mulm(&uk, &m).dblm(&m);
                let new_uk1 = t1.subm(&t2, &m);
                // U(k') = U(2k+1) = U(k+1)² - QU(k)²
                let t1 = uk1sq;
                let t2 = (&q).mulm(&uk.sqm(&m), &m);
                let new_uk = t1.subm(&t2, &m);
                uk1 = new_uk1;
                uk = new_uk;
            } else {
                // k' = 2k
                // U(k'+1) = U(2k+1) = U(k+1)² - QU(k)²
                let uksq = (&uk).sqm(&m);
                let t1 = (&uk1).sqm(&m);
                let t2 = (&uksq).mulm(&q, &m);
                let new_uk1 = t1.subm(&t2, &m);
                // U(k') = U(2k) = 2U(k+1)U(k) - PU(k)²
                let t1 = uk1.mulm(&uk, &m).dblm(&m);
                let t2 = uksq.mulm(&p, &m);
                let new_uk = t1.subm(&t2, &m);
                uk1 = new_uk1;
                uk = new_uk;
            }
        }

        // V(k) = 2U(k+1) - PU(k)
        let vk = (&uk1).dblm(&m).subm(&p.mulm(&uk, &m), &m);
        (uk, vk)
    }

    fn pq_selfridge(n: &Self) -> (usize, isize) {
        let mut d = T::from_u8(5).unwrap();
        let mut neg = false;
        loop {
            // check if n is a square number after several trials
            if d == T::from_u8(13).unwrap() && (*n).is_square() {
                break (0, 0);
            }

            let sd = if neg { (&d).negm(n) } else { d.clone() };
            let j = sd.jacobi(n);
            if j == 0 && &d != n {
                break (0, 0);
            } // modification from Baillie, see https://oeis.org/A217120/a217120_1.txt
            if j == -1 {
                let d = if neg {
                    -d.to_isize().unwrap()
                } else {
                    d.to_isize().unwrap()
                };
                break (1, (1 - d) / 4);
            }

            d = d + T::from_u8(2).unwrap();
            neg = !neg;
        }
    }

    fn p_bruteforce(n: &Self) -> usize {
        let mut p: usize = 3;
        loop {
            // check if n is a square number after several trials
            if p == 10 && (*n).is_square() {
                break 0;
            }

            let d = T::from_usize(p * p - 4).unwrap();
            let j = d.jacobi(n);
            if j == 0 && &d != n {
                break 0;
            }
            if j == -1 {
                break p;
            }
            p += 1;
        }
    }
}

impl<T: Integer + NumRef + Clone + FromPrimitive + LucasUtils + BitTest + ModularRefOps>
    PrimalityUtils for T
where
    for<'r> &'r T:
        RefNum<T> + std::ops::Shr<usize, Output = T> + ModularUnaryOps<&'r T, Output = T>,
{
    #[inline]
    fn is_prp(&self, base: Self) -> bool {
        if self < &Self::one() {
            return false;
        }
        let tm1 = self - Self::one();
        base.powm(&tm1, self).is_one()
    }

    #[inline]
    fn is_sprp(&self, base: Self) -> bool {
        self.test_sprp(base).either(|v| v, |_| false)
    }

    fn test_sprp(&self, base: T) -> Either<bool, T> {
        if self <= &Self::one() {
            return Either::Left(false);
        }

        // find 2^shift*u + 1 = n
        let tm1 = self - T::one();
        let shift = tm1.trailing_zeros();
        let u = &tm1 >> shift;

        // prevent reduction if the input is in montgomery form
        let m1 = T::one() % self;
        let mm1 = (&m1).negm(self);

        let mut x = base.powm(&u, self);
        if x == m1 || x == mm1 {
            return Either::Left(true);
        }

        for _ in 0..shift {
            let y = (&x).sqm(self);
            if y == m1 {
                return Either::Right(self.gcd(&(x - T::one())));
            }
            if y == mm1 {
                return Either::Left(true);
            }
            x = y;
        }

        Either::Left(x == m1)
    }

    fn is_lprp(&self, p: Option<usize>, q: Option<isize>) -> bool {
        if self < &Self::one() {
            return false;
        }
        if self.is_even() {
            return false;
        }

        let (p, q) = match (p, q) {
            (Some(sp), Some(sq)) => (sp, sq),
            (_, _) => {
                let (sp, sq) = LucasUtils::pq_selfridge(self);
                if sp == 0 {
                    return false;
                }; // is a perfect power
                (sp, sq)
            }
        };

        let d = (p * p) as isize - 4 * q;
        let d = if d > 0 {
            Self::from_isize(d).unwrap()
        } else {
            Self::from_isize(-d).unwrap().negm(self)
        };
        let delta = match d.jacobi(self) {
            0 => self.clone(),
            -1 => self + Self::one(),
            1 => self - Self::one(),
            _ => unreachable!(),
        };
        let (u, _) = LucasUtils::lucasm(p, q, self.clone(), delta);
        u.is_zero()
    }

    fn is_slprp(&self, p: Option<usize>, q: Option<isize>) -> bool {
        if self < &Self::one() {
            return false;
        }
        if self.is_even() {
            return false;
        }

        let (p, q) = match (p, q) {
            (Some(sp), Some(sq)) => (sp, sq),
            (_, _) => {
                let (sp, sq) = LucasUtils::pq_selfridge(self);
                if sp == 0 {
                    return false;
                }; // is a perfect power
                (sp, sq)
            }
        };

        let d = (p * p) as isize - 4 * q;
        let d = if d > 0 {
            Self::from_isize(d).unwrap()
        } else {
            Self::from_isize(-d).unwrap().negm(self)
        };
        let delta = match d.jacobi(self) {
            0 => self.clone(),
            -1 => self + Self::one(),
            1 => self - Self::one(),
            _ => unreachable!(),
        };

        let shift = delta.trailing_zeros();
        let base = &delta >> shift;

        let (ud, vd) = LucasUtils::lucasm(p, q, self.clone(), base.clone());
        if ud.is_zero() || vd.is_zero() {
            return true;
        }

        // do first iteration to remove the sign on Q
        if shift == 0 {
            return false;
        }
        let mut qk = Self::from_isize(q.abs()).unwrap().powm(&base, self);
        // V(2k) = V(k)² - 2Q^k
        let mut vd = if q >= 0 {
            vd.sqm(self).subm(&(&qk).dblm(self), self)
        } else {
            vd.sqm(self).addm(&(&qk).dblm(self), self)
        };
        if vd.is_zero() {
            return true;
        }

        for _ in 1..shift {
            // V(2k) = V(k)² - 2Q^k
            qk = qk.sqm(self);
            vd = vd.sqm(self).subm(&(&qk).dblm(self), self);
            if vd.is_zero() {
                return true;
            }
        }
        false
    }

    fn is_eslprp(&self, p: Option<usize>) -> bool {
        if self < &Self::one() {
            return false;
        }
        if self.is_even() {
            return false;
        }

        let p = match p {
            Some(sp) => sp,
            None => {
                let sp = LucasUtils::p_bruteforce(self);
                if sp == 0 {
                    return false;
                }; // is a perfect power
                sp
            }
        };

        let d = (p * p) as isize - 4;
        let d = if d > 0 {
            Self::from_isize(d).unwrap()
        } else {
            Self::from_isize(-d).unwrap().negm(self)
        };
        let delta = match d.jacobi(self) {
            0 => self.clone(),
            -1 => self + Self::one(),
            1 => self - Self::one(),
            _ => unreachable!(),
        };

        let shift = delta.trailing_zeros();
        let base = &delta >> shift;

        let (ud, mut vd) = LucasUtils::lucasm(p, 1, self.clone(), base.clone());
        let two = Self::from_u8(2).unwrap();
        // U(d) = 0 or V(d) = ±2
        if ud.is_zero() && (vd == two || vd == self - &two) {
            return true;
        }
        if vd.is_zero() {
            return true;
        }

        for _ in 1..(shift - 1) {
            // V(2k) = V(k)² - 2
            vd = vd.sqm(self).subm(&two, self);
            if vd.is_zero() {
                return true;
            }
        }
        false
    }
}

/// A dummy trait for integer type. All types that implements this and [`PrimalityRefBase`]
/// will be supported by most functions in `num-primes`
pub trait PrimalityBase:
    Integer
    + Roots
    + NumRef
    + Clone
    + FromPrimitive
    + ToPrimitive
    + ExactRoots
    + BitTest
    + ModularRefOps
{
}
impl<
        T: Integer
            + Roots
            + NumRef
            + Clone
            + FromPrimitive
            + ToPrimitive
            + ExactRoots
            + BitTest
            + ModularRefOps,
    > PrimalityBase for T
{
}

/// A dummy trait for integer reference type. All types that implements this and [`PrimalityBase`]
/// will be supported by most functions in `num-primes`
pub trait PrimalityRefBase<Base>:
    RefNum<Base>
    + std::ops::Shr<usize, Output = Base>
    + for<'r> ModularUnaryOps<&'r Base, Output = Base>
    + for<'r> ModularCoreOps<&'r Base, &'r Base, Output = Base>
{
}
impl<T, Base> PrimalityRefBase<Base> for T where
    T: RefNum<Base>
        + std::ops::Shr<usize, Output = Base>
        + for<'r> ModularUnaryOps<&'r Base, Output = Base>
        + for<'r> ModularCoreOps<&'r Base, &'r Base, Output = Base>
{
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mint::SmallMint;
    use num_modular::{ModularAbs, ModularSymbols};
    use rand::random;

    #[cfg(feature = "num-bigint")]
    use num_bigint::BigUint;

    #[test]
    fn fermat_prp_test() {
        // 341 is the smallest pseudoprime for base 2
        assert!(341u16.is_prp(2));
        assert!(!340u16.is_prp(2));
        assert!(!105u16.is_prp(2));

        // Carmichael number 561 = 3*11*17 is fermat pseudoprime for any base coprime to 561
        for p in [2, 5, 7, 13, 19] {
            assert!(561u32.is_prp(p));
        }
    }

    #[test]
    fn sprp_test() {
        // strong pseudoprimes of base 2 (OEIS:A001262) under 10000
        let spsp: [u16; 5] = [2047, 3277, 4033, 4681, 8321];
        for psp in spsp {
            assert!(psp.is_sprp(2));
            assert!(SmallMint::from(psp).is_sprp(2.into())); // test Mint execution
        }

        // test cofactor return
        assert_eq!(341u16.test_sprp(2), Either::Right(31));
        assert_eq!(
            SmallMint::from(341u16).test_sprp(2.into()),
            Either::Right(31.into())
        );

        // one is not prime and must not pass the test
        assert_eq!(1u16.test_sprp(2), Either::Left(false));
        assert!(!1u16.is_sprp(2));
        #[cfg(feature = "num-bigint")]
        {
            assert!(!BigUint::from(1u8).is_sprp(BigUint::from(2u8)));
        }
    }

    #[test]
    fn lucas_mod_test() {
        // OEIS:A006190
        let p3qm1: [u64; 26] = [
            0,
            1,
            3,
            10,
            33,
            109,
            360,
            1189,
            3927,
            12970,
            42837,
            141_481,
            467_280,
            1_543_321,
            5_097_243,
            16_835_050,
            55_602_393,
            183_642_229,
            606_529_080,
            2_003_229_469,
            6_616_217_487,
            21_851_881_930,
            72_171_863_277,
            238_367_471_761,
            787_274_278_560,
            2_600_190_307_441,
        ];
        let m = random::<u16>();
        for (n, &p3qm1_val) in p3qm1.iter().enumerate().skip(2) {
            let (uk, _) = LucasUtils::lucasm(3, -1, u64::from(m), n as u64);
            assert_eq!(uk, p3qm1_val % u64::from(m));

            #[cfg(feature = "num-bigint")]
            {
                let (uk, _) = LucasUtils::lucasm(3, -1, BigUint::from(m), BigUint::from(n));
                assert_eq!(uk, BigUint::from(p3qm1_val % u64::from(m)));
            }
        }

        fn lucasm_naive(p: usize, q: isize, m: u16, n: u16) -> (u16, u16) {
            if n == 0 {
                return (0, 2);
            }

            let m = m as usize;
            let q = q.absm(&m);
            let (mut um1, mut u) = (0, 1); // U_{n-1}, U_{n}
            let (mut vm1, mut v) = (2, p % m); // V_{n-1}, V_{n}

            for _ in 1..n {
                let new_u = p.mulm(u, &m).subm(q.mulm(um1, &m), &m);
                um1 = u;
                u = new_u;

                let new_v = p.mulm(v, &m).subm(q.mulm(vm1, &m), &m);
                vm1 = v;
                v = new_v;
            }
            (u as u16, v as u16)
        }
        for _ in 0..10 {
            let n = u16::from(random::<u8>());
            let m = random::<u16>();
            let p = random::<u16>() as usize;
            let q = random::<i16>() as isize;
            assert_eq!(
                LucasUtils::lucasm(p, q, m, n),
                lucasm_naive(p, q, m, n),
                "failed with Lucas settings: p={p}, q={q}, m={m}, n={n}"
            );
        }
    }

    #[test]
    fn lucas_prp_test() {
        // Some known cases
        assert!(19u8.is_lprp(Some(3), Some(-1)));
        assert!(5u8.is_lprp(None, None));
        assert!(7u8.is_lprp(None, None));
        assert!(!9u8.is_lprp(None, None));
        assert!(!5719u16.is_lprp(None, None));
        assert!(!1239u16.is_eslprp(None));

        // least lucas pseudo primes for Q=-1 and Jacobi(D/n) = -1 (from Wikipedia)
        let plimit: [u16; 5] = [323, 35, 119, 9, 9];
        for (i, l) in plimit.iter().copied().enumerate() {
            let p = i + 1;
            assert!(l.is_lprp(Some(p), Some(-1)));

            // test four random numbers under limit
            for _ in 0..10 {
                let n = random::<u16>() % l;
                if n <= 3 || n.is_sprp(2) {
                    continue;
                } // skip real primes
                let d = (p * p + 4) as u16;
                if n.is_odd() && d.jacobi(&n) != -1 {
                    continue;
                }
                assert!(
                    !n.is_lprp(Some(p), Some(-1)),
                    "lucas prp test on {} with p = {}",
                    n,
                    p
                );
            }
        }

        // least strong lucas pseudoprimes for Q=-1 and Jacobi(D/n) = -1 (from Wikipedia)
        let plimit: [u16; 3] = [4181, 169, 119];
        for (i, l) in plimit.iter().copied().enumerate() {
            let p = i + 1;
            assert!(l.is_slprp(Some(p), Some(-1)));

            // test random numbers under limit
            for _ in 0..10 {
                let n = random::<u16>() % l;
                if n <= 3 || (n.is_sprp(2) && n.is_sprp(3)) {
                    continue;
                } // skip real primes
                let d = (p * p + 4) as u16;
                if n.is_odd() && d.jacobi(&n) != -1 {
                    continue;
                }
                assert!(
                    !n.is_slprp(Some(p), Some(-1)),
                    "strong lucas prp test on {} with p = {}",
                    n,
                    p
                );
            }
        }

        // lucas pseudoprimes (OEIS:A217120) under 10000
        let lpsp: [u16; 9] = [323, 377, 1159, 1829, 3827, 5459, 5777, 9071, 9179];
        for psp in lpsp {
            assert!(
                psp.is_lprp(None, None),
                "lucas prp test on pseudoprime {}",
                psp
            );
        }
        for _ in 0..50 {
            let n = random::<u16>() % 10000;
            if n <= 3 || (n.is_sprp(2) && n.is_sprp(3)) {
                continue;
            } // skip real primes
            if lpsp.iter().any(|x| x == &n) {
                continue;
            } // skip pseudoprimes
            assert!(!n.is_lprp(None, None), "lucas prp test on {}", n);
        }

        // strong lucas pseudoprimes (OEIS:A217255) under 10000
        let slpsp: [u16; 2] = [5459, 5777];
        for psp in slpsp {
            assert!(
                psp.is_slprp(None, None),
                "strong lucas prp test on pseudoprime {}",
                psp
            );
        }
        for _ in 0..50 {
            let n = random::<u16>() % 10000;
            if n <= 3 || (n.is_sprp(2) && n.is_sprp(3)) {
                continue;
            } // skip real primes
            if slpsp.iter().any(|x| x == &n) {
                continue;
            } // skip pseudoprimes
            assert!(!n.is_slprp(None, None), "strong lucas prp test on {}", n);
        }

        // extra strong lucas pseudoprimes (OEIS:A217719) under 10000
        let eslpsp: [u16; 3] = [989, 3239, 5777];
        for psp in eslpsp {
            assert!(
                psp.is_eslprp(None),
                "extra strong lucas prp test on pseudoprime {}",
                psp
            );
        }
        for _ in 0..50 {
            let n = random::<u16>() % 10000;
            if n <= 3 || (n.is_sprp(2) && n.is_sprp(3)) {
                continue;
            } // skip real primes
            if eslpsp.iter().any(|x| x == &n) {
                continue;
            } // skip pseudoprimes
            assert!(!n.is_eslprp(None), "extra strong lucas prp test on {}", n);
        }
    }
}

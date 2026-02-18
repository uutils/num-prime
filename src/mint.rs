//! Wrapper of integer to makes it efficient in modular arithmetics but still have the same
//! API of normal integers.

use core::ops::{Add, Div, Mul, Neg, Rem, Shr, Sub};
use either::{Either, Left, Right};
use num_integer::{Integer, Roots};
use num_modular::{
    ModularCoreOps, ModularInteger, ModularPow, ModularSymbols, ModularUnaryOps, Montgomery,
    ReducedInt, Reducer,
};
use num_traits::{FromPrimitive, Num, One, Pow, ToPrimitive, Zero};

use crate::{BitTest, ExactRoots};

/// Integer with fast modular arithmetics support, based on [`MontgomeryInt`] under the hood
///
/// This struct only designed to be working with this crate. Most binary operators assume that
/// the modulus of two operands (when in montgomery form) are the same, and most implicit conversions
/// between conventional form and montgomery form will be forbidden
#[derive(Debug, Clone, Copy)]
pub struct Mint<T: Integer, R: Reducer<T>>(Either<T, ReducedInt<T, R>>);

impl<T: Integer, R: Reducer<T>> From<T> for Mint<T, R> {
    #[inline(always)]
    fn from(v: T) -> Self {
        Self(Left(v))
    }
}
impl<T: Integer, R: Reducer<T>> From<ReducedInt<T, R>> for Mint<T, R> {
    #[inline(always)]
    fn from(v: ReducedInt<T, R>) -> Self {
        Self(Right(v))
    }
}

#[inline(always)]
fn left_only<T: Integer, R: Reducer<T>>(lhs: Mint<T, R>, rhs: Mint<T, R>) -> (T, T) {
    match (lhs.0, rhs.0) {
        (Left(v1), Left(v2)) => (v1, v2),
        (_, _) => unreachable!(),
    }
}

#[inline(always)]
fn left_ref_only<'a, T: Integer, R: Reducer<T>>(
    lhs: &'a Mint<T, R>,
    rhs: &'a Mint<T, R>,
) -> (&'a T, &'a T) {
    match (&lhs.0, &rhs.0) {
        (Left(v1), Left(v2)) => (v1, v2),
        (_, _) => unreachable!(),
    }
}

macro_rules! forward_binops_left_ref_only {
    ($method:ident) => {
        #[inline(always)]
        fn $method(&self, other: &Self) -> Self {
            let (v1, v2) = left_ref_only(self, other);
            Self(Left(v1.$method(v2)))
        }
    };
    ($method:ident => $return:ty) => {
        #[inline(always)]
        fn $method(&self, other: &Self) -> $return {
            let (v1, v2) = left_ref_only(self, other);
            v1.$method(v2)
        }
    };
}

macro_rules! forward_uops_ref {
    ($method:ident => $return:ty) => {
        #[inline(always)]
        fn $method(&self) -> $return {
            match &self.0 {
                Left(v) => v.$method(),
                Right(m) => m.residue().$method(),
            }
        }
    };
}

impl<T: Integer + Clone, R: Reducer<T>> PartialEq for Mint<T, R> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Left(v1), Left(v2)) => v1 == v2,
            (Right(v1), Right(v2)) => v1 == v2,
            (_, _) => unreachable!(), // force optimization of equality test
        }
    }
}
impl<T: Integer + Clone, R: Reducer<T>> Eq for Mint<T, R> {}

impl<T: Integer + Clone, R: Reducer<T> + Clone> PartialOrd for Mint<T, R> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: Integer + Clone, R: Reducer<T> + Clone> Ord for Mint<T, R> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (&self.0, &other.0) {
            (Left(v1), Left(v2)) => v1.cmp(v2),
            (Left(v1), Right(v2)) => v1.cmp(&v2.residue()),
            (Right(v1), Left(v2)) => v1.residue().cmp(v2),
            (Right(v1), Right(v2)) => v1.residue().cmp(&v2.residue()),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> Mint<T, R> {
    #[inline(always)]
    pub fn value(&self) -> T {
        match &self.0 {
            Left(v) => v.clone(),
            Right(m) => m.residue(),
        }
    }
}

// forward binary operators by converting result to MontgomeryInt whenever possible
macro_rules! forward_binops_right {
    (impl $imp:ident, $method:ident) => {
        impl<T: Integer + Clone, R: Reducer<T> + Clone> $imp for Mint<T, R> {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                Self(match (self.0, rhs.0) {
                    (Left(v1), Left(v2)) => Left(v1.$method(v2)),
                    (Left(v1), Right(v2)) => Right(v2.convert(v1).$method(v2)),
                    (Right(v1), Left(v2)) => {
                        let v2 = v1.convert(v2);
                        Right(v1.$method(v2))
                    }
                    (Right(v1), Right(v2)) => Right(v1.$method(v2)),
                })
            }
        }

        impl<T: Integer + Clone + for<'r> $imp<&'r T, Output = T>, R: Reducer<T> + Clone>
            $imp<&Self> for Mint<T, R>
        {
            type Output = Mint<T, R>;
            #[inline]
            fn $method(self, rhs: &Self) -> Self::Output {
                Mint(match (self.0, &rhs.0) {
                    (Left(v1), Left(v2)) => Left(v1.$method(v2)),
                    (Left(v1), Right(v2)) => Right(v2.convert(v1).$method(v2)),
                    (Right(v1), Left(v2)) => {
                        let v2 = v1.convert(v2.clone());
                        Right(v1.$method(v2))
                    }
                    (Right(v1), Right(v2)) => Right(v1.$method(v2)),
                })
            }
        }

        impl<T: Integer + Clone, R: Reducer<T> + Clone> $imp<Mint<T, R>> for &Mint<T, R> {
            type Output = Mint<T, R>;
            // FIXME: additional clone here due to https://github.com/rust-lang/rust/issues/39959
            // (same for ref & ref operation below, and those for Div and Rem)
            #[inline]
            fn $method(self, rhs: Mint<T, R>) -> Self::Output {
                Mint(match (&self.0, rhs.0) {
                    (Left(v1), Left(v2)) => Left(v1.clone().$method(v2)),
                    (Left(v1), Right(v2)) => Right(v2.convert(v1.clone()).$method(v2)),
                    (Right(v1), Left(v2)) => {
                        let v2 = v1.convert(v2);
                        Right(v1.clone().$method(v2))
                    }
                    (Right(v1), Right(v2)) => Right(v1.$method(v2)),
                })
            }
        }
        impl<
                'a,
                'b,
                T: Integer + Clone + for<'r> $imp<&'r T, Output = T>,
                R: Reducer<T> + Clone,
            > $imp<&'b Mint<T, R>> for &'a Mint<T, R>
        {
            type Output = Mint<T, R>;
            #[inline]
            fn $method(self, rhs: &Mint<T, R>) -> Self::Output {
                Mint(match (&self.0, &rhs.0) {
                    (Left(v1), Left(v2)) => Left(v1.clone().$method(v2)),
                    (Left(v1), Right(v2)) => Right(v2.convert(v1.clone()).$method(v2)),
                    (Right(v1), Left(v2)) => {
                        let v2 = v1.convert(v2.clone());
                        Right(v1.clone().$method(v2))
                    }
                    (Right(v1), Right(v2)) => Right(v1.$method(v2)),
                })
            }
        }
    };
}

forward_binops_right!(impl Add, add);
forward_binops_right!(impl Sub, sub);
forward_binops_right!(impl Mul, mul);

impl<T: Integer + Clone, R: Reducer<T>> Div for Mint<T, R> {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        let (v1, v2) = left_only(self, rhs);
        Self(Left(v1.div(v2)))
    }
}
impl<T: Integer + Clone + for<'r> Div<&'r T, Output = T>, R: Reducer<T>> Div<&Self> for Mint<T, R> {
    type Output = Self;

    #[inline]
    fn div(self, rhs: &Self) -> Self::Output {
        match (self.0, &rhs.0) {
            (Left(v1), Left(v2)) => Self(Left(v1.div(v2))),
            (_, _) => unreachable!(),
        }
    }
}
impl<T: Integer + Clone, R: Reducer<T>> Div<Mint<T, R>> for &Mint<T, R> {
    type Output = Mint<T, R>;

    #[inline]
    fn div(self, rhs: Mint<T, R>) -> Self::Output {
        match (&self.0, rhs.0) {
            (Left(v1), Left(v2)) => Mint(Left(v1.clone().div(v2))),
            (_, _) => unreachable!(),
        }
    }
}
impl<T: Integer + Clone + for<'r> Div<&'r T, Output = T>, R: Reducer<T>> Div<&Mint<T, R>>
    for &Mint<T, R>
{
    type Output = Mint<T, R>;
    #[inline]
    fn div(self, rhs: &Mint<T, R>) -> Self::Output {
        match (&self.0, &rhs.0) {
            (Left(v1), Left(v2)) => Mint(Left(v1.clone().div(v2))),
            (_, _) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> Rem for Mint<T, R> {
    type Output = Self;

    #[inline]
    fn rem(self, rhs: Self) -> Self::Output {
        match (self.0, rhs.0) {
            (Left(v1), Left(v2)) => Self(Right(ReducedInt::new(v1, &v2))),
            (Right(v1), Left(v2)) => {
                debug_assert!(v1.modulus() == v2);
                Self(Right(v1))
            }
            (_, _) => unreachable!(),
        }
    }
}
impl<T: Integer + Clone, R: Reducer<T> + Clone> Rem<&Self> for Mint<T, R> {
    type Output = Self;

    #[inline]
    fn rem(self, rhs: &Self) -> Self::Output {
        match (self.0, &rhs.0) {
            (Left(v1), Left(v2)) => Self(Right(ReducedInt::new(v1, v2))),
            (Right(v1), Left(v2)) => {
                debug_assert!(&v1.modulus() == v2);
                Self(Right(v1))
            }
            (_, _) => unreachable!(),
        }
    }
}
impl<T: Integer + Clone, R: Reducer<T> + Clone> Rem<Mint<T, R>> for &Mint<T, R> {
    type Output = Mint<T, R>;

    #[inline]
    fn rem(self, rhs: Mint<T, R>) -> Self::Output {
        match (&self.0, rhs.0) {
            (Left(v1), Left(v2)) => Mint(Right(ReducedInt::new(v1.clone(), &v2))),
            (Right(v1), Left(v2)) => {
                debug_assert!(v1.modulus() == v2);
                Mint(Right(v1.clone()))
            }
            (_, _) => unreachable!(),
        }
    }
}
impl<T: Integer + Clone, R: Reducer<T> + Clone> Rem<&Mint<T, R>> for &Mint<T, R> {
    type Output = Mint<T, R>;

    #[inline]
    fn rem(self, rhs: &Mint<T, R>) -> Self::Output {
        match (&self.0, &rhs.0) {
            (Left(v1), Left(v2)) => Mint(Right(ReducedInt::new(v1.clone(), v2))),
            (Right(v1), Left(v2)) => {
                debug_assert!(&v1.modulus() == v2);
                Mint(Right(v1.clone()))
            }
            (_, _) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> Zero for Mint<T, R> {
    #[inline(always)]
    fn zero() -> Self {
        Self(Left(T::zero()))
    }
    #[inline(always)]
    fn is_zero(&self) -> bool {
        match &self.0 {
            Left(v) => v.is_zero(),
            Right(m) => m.is_zero(),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> One for Mint<T, R> {
    #[inline(always)]
    fn one() -> Self {
        Self(Left(T::one()))
    }
    forward_uops_ref!(is_one => bool);
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> Num for Mint<T, R> {
    type FromStrRadixErr = <T as Num>::FromStrRadixErr;

    #[inline(always)]
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        T::from_str_radix(str, radix).map(|v| Self(Left(v)))
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> Integer for Mint<T, R> {
    forward_binops_left_ref_only!(div_floor);
    forward_binops_left_ref_only!(mod_floor);
    forward_binops_left_ref_only!(lcm);
    forward_binops_left_ref_only!(is_multiple_of => bool);
    forward_uops_ref!(is_even => bool);
    forward_uops_ref!(is_odd => bool);

    #[inline(always)]
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        let (v1, v2) = left_ref_only(self, other);
        let (q, r) = v1.div_rem(v2);
        (Self(Left(q)), Self(Left(r)))
    }
    #[inline(always)]
    fn gcd(&self, other: &Self) -> Self {
        Self(Left(match (&self.0, &other.0) {
            (Left(v1), Left(v2)) => v1.gcd(v2),
            (Right(v1), Left(v2)) => v1.residue().gcd(v2),
            (Left(v1), Right(v2)) => v1.gcd(&v2.residue()),
            (Right(v1), Right(v2)) => v1.residue().gcd(&v2.residue()),
        }))
    }
}

impl<T: Integer + Clone + Roots, R: Reducer<T> + Clone> Roots for Mint<T, R> {
    #[inline]
    fn nth_root(&self, n: u32) -> Self {
        match &self.0 {
            Left(v) => Self(Left(v.nth_root(n))),
            Right(_) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone + FromPrimitive, R: Reducer<T>> FromPrimitive for Mint<T, R> {
    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        T::from_f64(n).map(|v| Self(Left(v)))
    }
    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        T::from_i64(n).map(|v| Self(Left(v)))
    }
    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        T::from_u64(n).map(|v| Self(Left(v)))
    }
}

impl<T: Integer + Clone + ToPrimitive, R: Reducer<T> + Clone> ToPrimitive for Mint<T, R> {
    #[inline]
    fn to_f64(&self) -> Option<f64> {
        match &self.0 {
            Left(v) => v.to_f64(),
            Right(m) => m.residue().to_f64(),
        }
    }
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        match &self.0 {
            Left(v) => v.to_i64(),
            Right(m) => m.residue().to_i64(),
        }
    }
    #[inline]
    fn to_u64(&self) -> Option<u64> {
        match &self.0 {
            Left(v) => v.to_u64(),
            Right(m) => m.residue().to_u64(),
        }
    }
}

impl<T: Integer + Clone + Pow<u32, Output = T>, R: Reducer<T>> Pow<u32> for Mint<T, R> {
    type Output = Self;
    #[inline]
    fn pow(self, rhs: u32) -> Self::Output {
        match self.0 {
            Left(v) => Self(Left(v.pow(rhs))),
            Right(_) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone + ExactRoots, R: Reducer<T> + Clone> ExactRoots for Mint<T, R> {
    #[inline]
    fn nth_root_exact(&self, n: u32) -> Option<Self> {
        match &self.0 {
            Left(v) => v.nth_root_exact(n).map(|v| Self(Left(v))),
            Right(_) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone + BitTest, R: Reducer<T>> BitTest for Mint<T, R> {
    #[inline]
    fn bit(&self, position: usize) -> bool {
        match &self.0 {
            Left(v) => v.bit(position),
            Right(_) => unreachable!(),
        }
    }
    #[inline]
    fn bits(&self) -> usize {
        match &self.0 {
            Left(v) => v.bits(),
            Right(_) => unreachable!(),
        }
    }
    #[inline]
    fn trailing_zeros(&self) -> usize {
        match &self.0 {
            Left(v) => v.trailing_zeros(),
            Right(_) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone + Shr<usize, Output = T>, R: Reducer<T>> Shr<usize> for Mint<T, R> {
    type Output = Self;
    #[inline]
    fn shr(self, rhs: usize) -> Self::Output {
        match self.0 {
            Left(v) => Self(Left(v >> rhs)),
            Right(_) => unreachable!(),
        }
    }
}
impl<T: Integer + Clone + Shr<usize, Output = T>, R: Reducer<T>> Shr<usize> for &Mint<T, R> {
    type Output = Mint<T, R>;
    #[inline]
    fn shr(self, rhs: usize) -> Self::Output {
        match &self.0 {
            Left(v) => Mint(Left(v.clone() >> rhs)),
            Right(_) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> ModularCoreOps<&Self, &Self> for Mint<T, R> {
    type Output = Self;
    #[inline]
    fn addm(self, rhs: &Self, m: &Self) -> Self::Output {
        match (self.0, &rhs.0, &m.0) {
            (Right(v1), Right(v2), Left(m)) => {
                debug_assert!(&v1.modulus() == m && &v2.modulus() == m);
                Self(Right(v1 + v2))
            }
            (_, _, _) => unreachable!(),
        }
    }
    #[inline]
    fn subm(self, rhs: &Self, m: &Self) -> Self::Output {
        match (self.0, &rhs.0, &m.0) {
            (Right(v1), Right(v2), Left(m)) => {
                debug_assert!(&v1.modulus() == m && &v2.modulus() == m);
                Self(Right(v1 - v2))
            }
            (_, _, _) => unreachable!(),
        }
    }
    #[inline]
    fn mulm(self, rhs: &Self, m: &Self) -> Self::Output {
        match (self.0, &rhs.0, &m.0) {
            (Right(v1), Right(v2), Left(m)) => {
                debug_assert!(&v1.modulus() == m && &v2.modulus() == m);
                Self(Right(v1 * v2))
            }
            (_, _, _) => unreachable!(),
        }
    }
}
impl<'b, T: Integer + Clone, R: Reducer<T> + Clone> ModularCoreOps<&'b Mint<T, R>, &'b Mint<T, R>>
    for &Mint<T, R>
{
    type Output = Mint<T, R>;
    #[inline]
    fn addm(self, rhs: &Mint<T, R>, m: &Mint<T, R>) -> Self::Output {
        match (&self.0, &rhs.0, &m.0) {
            (Right(v1), Right(v2), Left(m)) => {
                debug_assert!(&v1.modulus() == m && &v2.modulus() == m);
                Mint(Right(v1 + v2))
            }
            (_, _, _) => unreachable!(),
        }
    }
    #[inline]
    fn subm(self, rhs: &Mint<T, R>, m: &Mint<T, R>) -> Self::Output {
        match (&self.0, &rhs.0, &m.0) {
            (Right(v1), Right(v2), Left(m)) => {
                debug_assert!(&v1.modulus() == m && &v2.modulus() == m);
                Mint(Right(v1 - v2))
            }
            (_, _, _) => unreachable!(),
        }
    }
    #[inline]
    fn mulm(self, rhs: &Mint<T, R>, m: &Mint<T, R>) -> Self::Output {
        match (&self.0, &rhs.0, &m.0) {
            (Right(v1), Right(v2), Left(m)) => {
                debug_assert!(&v1.modulus() == m && &v2.modulus() == m);
                Mint(Right(v1 * v2))
            }
            (_, _, _) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> ModularUnaryOps<&Self> for Mint<T, R> {
    type Output = Self;
    #[inline]
    fn negm(self, m: &Self) -> Self::Output {
        Self(Right(match (self.0, &m.0) {
            (Left(v), Left(m)) => ReducedInt::new(v, m).neg(),
            (Right(v), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.neg()
            }
            (_, Right(_)) => unreachable!(),
        }))
    }
    fn invm(self, _: &Self) -> Option<Self::Output> {
        unreachable!() // not used in this crate
    }
    #[inline]
    fn dblm(self, m: &Self) -> Self::Output {
        Self(Right(match (self.0, &m.0) {
            (Left(v), Left(m)) => ReducedInt::new(v, m).double(),
            (Right(v), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.double()
            }
            (_, Right(_)) => unreachable!(),
        }))
    }
    #[inline]
    fn sqm(self, m: &Self) -> Self::Output {
        Self(Right(match (self.0, &m.0) {
            (Left(v), Left(m)) => ReducedInt::new(v, m).square(),
            (Right(v), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.square()
            }
            (_, Right(_)) => unreachable!(),
        }))
    }
}
impl<T: Integer + Clone, R: Reducer<T> + Clone> ModularUnaryOps<&Mint<T, R>> for &Mint<T, R> {
    type Output = Mint<T, R>;
    #[inline]
    fn negm(self, m: &Mint<T, R>) -> Self::Output {
        Mint(Right(match (&self.0, &m.0) {
            (Left(v), Left(m)) => ReducedInt::new(v.clone(), m).neg(),
            (Right(v), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.clone().neg()
            }
            (_, Right(_)) => unreachable!(),
        }))
    }
    fn invm(self, _: &Mint<T, R>) -> Option<Self::Output> {
        unreachable!() // not used in this crate
    }
    #[inline]
    fn dblm(self, m: &Mint<T, R>) -> Self::Output {
        Mint(Right(match (&self.0, &m.0) {
            (Left(v), Left(m)) => ReducedInt::new(v.clone(), m).double(),
            (Right(v), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.clone().double()
            }
            (_, Right(_)) => unreachable!(),
        }))
    }
    #[inline]
    fn sqm(self, m: &Mint<T, R>) -> Self::Output {
        Mint(Right(match (&self.0, &m.0) {
            (Left(v), Left(m)) => ReducedInt::new(v.clone(), m).square(),
            (Right(v), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.clone().square()
            }
            (_, Right(_)) => unreachable!(),
        }))
    }
}

impl<T: Integer + Clone + for<'r> ModularSymbols<&'r T>, R: Reducer<T> + Clone>
    ModularSymbols<&Self> for Mint<T, R>
{
    #[inline]
    fn checked_jacobi(&self, n: &Self) -> Option<i8> {
        match (&self.0, &n.0) {
            (Left(a), Left(n)) => a.checked_jacobi(n),
            (Right(a), Left(n)) => a.residue().checked_jacobi(n),
            (_, Right(_)) => unreachable!(),
        }
    }
    #[inline]
    fn checked_legendre(&self, n: &Self) -> Option<i8> {
        match (&self.0, &n.0) {
            (Left(a), Left(n)) => a.checked_legendre(n),
            (Right(a), Left(n)) => a.residue().checked_legendre(n),
            (_, Right(_)) => unreachable!(),
        }
    }
    #[inline]
    fn kronecker(&self, n: &Self) -> i8 {
        match (&self.0, &n.0) {
            (Left(a), Left(n)) => a.kronecker(n),
            (Right(a), Left(n)) => a.residue().kronecker(n),
            (_, Right(_)) => unreachable!(),
        }
    }
}

impl<T: Integer + Clone, R: Reducer<T> + Clone> ModularPow<&Self, &Self> for Mint<T, R> {
    type Output = Self;
    #[inline]
    fn powm(self, exp: &Self, m: &Self) -> Self::Output {
        Self(Right(match (self.0, &exp.0, &m.0) {
            (Left(v), Left(e), Left(m)) => ReducedInt::new(v, m).pow(&e.clone()),
            (Right(v), Left(e), Left(m)) => {
                debug_assert!(&v.modulus() == m);
                v.pow(&e.clone())
            }
            (_, _, _) => unreachable!(),
        }))
    }
}

pub type SmallMint<T> = Mint<T, Montgomery<T>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basics() {
        let a: SmallMint<u32> = 19.into();
        let b: SmallMint<u32> = 8.into();
        assert_eq!(a + b, 27.into());
    }
}

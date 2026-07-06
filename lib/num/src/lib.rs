#![doc = include_str!("../README.md")]

use std::{cmp::Ordering, fmt::Debug, marker::PhantomData};

use ndext::ops::*;

use crate::arch::{AsBytesMut, AsBytesRef, BytesFn, BytesLen, Offset, word::Single};

pub mod arch;
pub mod long;
pub mod prime;

macro_rules! num_impl {
    (@signed [$($signed:ty > $unsigned:ty),+] $(,)?) => {
        $(num_impl!(@impl $signed, $signed, $unsigned);)+
        $(num_impl!(@signed $signed, $unsigned);)+
    };
    (@unsigned [$($unsigned:ty > $signed:ty),+] $(,)?) => {
        $(num_impl!(@impl $unsigned, $signed, $unsigned);)+
        $(num_impl!(@unsigned $unsigned, $signed);)+
    };
    (@impl $primitive:ty, $signed:ty, $unsigned:ty $(,)?) => {
        impl NumFn for $primitive {
            #[inline]
            fn is_odd(&self) -> bool {
                self & 1 == 1
            }

            #[inline]
            fn is_even(&self) -> bool {
                self & 1 == 0
            }

            #[inline]
            fn write_odd(&mut self) -> &mut Self {
                *self |= 1;
                self
            }

            #[inline]
            fn write_even(&mut self) -> &mut Self {
                *self &= !1;
                self
            }

            #[inline]
            fn write_alt(&mut self) -> &mut Self {
                *self ^= 1;
                self
            }
        }

        impl Num for $primitive {
            type Signed = $signed;
            type Unsigned = $unsigned;

            #[inline]
            fn as_signed(&self) -> Self::Signed {
                *self as Self::Signed
            }

            #[inline]
            fn as_unsigned(&self) -> Self::Unsigned {
                *self as Self::Unsigned
            }
        }

        impl NdRand for $primitive {}

        impl NdPow for $primitive {}

        impl NdGcd for $primitive {}

        impl NdGcdChecked for $primitive {}

        impl Zero for $primitive {
            const ZERO: Self = 0;
        }

        impl One for $primitive {
            const ONE: Self = 1;
        }

        impl Min for $primitive {
            const MIN: Self = Self::MIN;
        }

        impl Max for $primitive {
            const MAX: Self = Self::MAX;
        }

        impl LeCt for $primitive {}
        impl GeCt for $primitive {}

        impl SignCt for $primitive {}
        impl CmpCt for $primitive {}

        impl MinCt for $primitive {}
        impl MaxCt for $primitive {}

        impl SelectCt for $primitive {
            #[inline(never)]
            fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
                let lhs_mask = Self::from_ne_bytes([mask; (Self::BYTES) as usize]);
                let rhs_mask = Self::from_ne_bytes([!mask; (Self::BYTES) as usize]);

                lhs & lhs_mask | rhs & rhs_mask
            }
        }

        impl PowCt for $primitive {}
    };
    (@signed $signed:ty, $unsigned:ty $(,)?) => {
        impl NumSigned for $signed {}

        impl IsZeroCt for $signed {
            #[inline(never)]
            fn is_zero_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct(any)
            }
        }

        impl IsOneCt for $signed {
            #[inline(never)]
            fn is_one_ct(&self) -> MaskCt {
                let val = *self as $unsigned;
                let val = val ^ 1;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct(any)
            }
        }

        impl IsPosCt for $signed {
            #[inline(never)]
            fn is_pos_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let neg = val >> (Self::BITS - 1);
                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);

                let neg = neg as MaskCt;
                let any = any as MaskCt;

                inv_ct(neg) & dir_ct(any)
            }
        }

        impl IsNegCt for $signed {
            #[inline(never)]
            fn is_neg_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let neg = val >> (Self::BITS - 1);
                let neg = neg as MaskCt;

                dir_ct(neg)
            }
        }

        impl EqCt for $signed {
            #[inline(never)]
            fn eq_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let any = lhs ^ rhs;
                let any = (any | any.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct(any)
            }
        }

        impl LtCt for $signed {
            #[inline(never)]
            fn lt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let lt = (lhs.wrapping_sub(rhs) >> (Self::BITS - 1)) as MaskCt;

                let lhs_neg = (lhs >> (Self::BITS - 1)) as MaskCt;
                let rhs_neg = (rhs >> (Self::BITS - 1)) as MaskCt;

                let xor = lhs_neg ^ rhs_neg;
                let res = xor & lhs_neg | !xor & lt;

                dir_ct(res)
            }
        }

        impl GtCt for $signed {
            #[inline(never)]
            fn gt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let gt = (rhs.wrapping_sub(lhs) >> (Self::BITS - 1)) as MaskCt;

                let lhs_neg = (lhs >> (Self::BITS - 1)) as MaskCt;
                let rhs_neg = (rhs >> (Self::BITS - 1)) as MaskCt;

                let xor = lhs_neg ^ rhs_neg;
                let res = xor & rhs_neg | !xor & gt;

                dir_ct(res)
            }
        }

        impl PosxCt for $signed {
            #[inline]
            fn posx_ct(&self) -> Self {
                let pos = *self;
                let neg = (!self).wrapping_add(1);

                SelectCt::select_ct(&pos, &neg, self.is_pos_ct())
            }
        }

        impl NegxCt for $signed {
            #[inline]
            fn negx_ct(&self) -> Self {
                let pos = *self;
                let neg = (!self).wrapping_add(1);

                SelectCt::select_ct(&pos, &neg, self.is_neg_ct())
            }
        }
    };
    (@unsigned $unsigned:ty, $signed:ty $(,)?) => {
        impl NumUnsigned for $unsigned {
            #[inline]
            fn order(&self) -> usize {
                self.ilog2() as usize
            }

            #[inline]
            fn log(&self) -> Self {
                self.ilog2() as $unsigned
            }

            #[inline]
            fn sqrt(&self) -> Self {
                self.isqrt() as $unsigned
            }
        }

        impl IsZeroCt for $unsigned {
            #[inline(never)]
            fn is_zero_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct(any)
            }
        }

        impl IsOneCt for $unsigned {
            #[inline(never)]
            fn is_one_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = ((val ^ 1) | (val ^ 1).wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct(any)
            }
        }

        impl IsPosCt for $unsigned {
            #[inline(never)]
            fn is_pos_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                dir_ct(any)
            }
        }

        impl IsNegCt for $unsigned {
            #[inline(never)]
            fn is_neg_ct(&self) -> MaskCt {
                MaskCt::ZERO
            }
        }

        impl EqCt for $unsigned {
            #[inline(never)]
            fn eq_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let any = lhs ^ rhs;
                let any = (any | any.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct(any)
            }
        }

        impl LtCt for $unsigned {
            #[inline(never)]
            fn lt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let lt = (lhs.wrapping_sub(rhs) >> (Self::BITS - 1)) as MaskCt;

                let lhs_bit = (lhs >> (Self::BITS - 1)) as MaskCt;
                let rhs_bit = (rhs >> (Self::BITS - 1)) as MaskCt;

                let xor = lhs_bit ^ rhs_bit;
                let res = xor & rhs_bit | !xor & lt;

                dir_ct(res)
            }
        }

        impl GtCt for $unsigned {
            #[inline(never)]
            fn gt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let gt = (rhs.wrapping_sub(lhs) >> (Self::BITS - 1)) as MaskCt;

                let lhs_bit = (lhs >> (Self::BITS - 1)) as MaskCt;
                let rhs_bit = (rhs >> (Self::BITS - 1)) as MaskCt;

                let xor = lhs_bit ^ rhs_bit;
                let res = xor & lhs_bit | !xor & gt;

                dir_ct(res)
            }
        }
    };
}

macro_rules! dir_from {
    ([$($primitive:ty),+ $(,)?]) => {
        $(dir_from!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl From<$primitive> for Dir {
            #[inline]
            fn from(value: $primitive) -> Self {
                match value.cmp(&0) {
                    Ordering::Less => Dir::NEG,
                    Ordering::Equal => Dir::POS,
                    Ordering::Greater => Dir::POS,
                }
            }
        }
    };
}

macro_rules! sign_from {
    ([$($primitive:ty),+ $(,)?]) => {
        $(sign_from!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl From<$primitive> for Sign {
            #[inline]
            fn from(value: $primitive) -> Self {
                match value.cmp(&0) {
                    Ordering::Less => Sign::NEG,
                    Ordering::Equal => Sign::ZERO,
                    Ordering::Greater => Sign::POS,
                }
            }
        }
    };
}

/// Number with Range.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: Num)]
pub struct Ranged<N: Num, R: Range<N>>(N, PhantomData<R>);

/// Number with Width.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdRand)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[ndfwd::def(self.0 with N: IsZeroCt)]
#[ndfwd::def(self.0 with N: IsOneCt)]
#[ndfwd::def(self.0 with N: IsPosCt)]
#[ndfwd::def(self.0 with N: IsNegCt)]
#[ndfwd::def(self.0 with N: EqCt)]
#[ndfwd::def(self.0 with N: LtCt)]
#[ndfwd::def(self.0 with N: GtCt)]
#[ndfwd::def(self.0 with N: LeCt)]
#[ndfwd::def(self.0 with N: GeCt)]
#[ndfwd::def(self.0 with N: SignCt)]
#[ndfwd::def(self.0 with N: CmpCt)]
#[ndfwd::def(self.0 with N: MinCt)]
#[ndfwd::def(self.0 with N: MaxCt)]
#[ndfwd::def(self.0 with N: PosxCt)]
#[ndfwd::def(self.0 with N: NegxCt)]
#[ndfwd::def(self.0 with N: SelectCt)]
#[ndfwd::def(self.0 with N: PowCt!)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Width<N: Num + NumUnsigned + BytesLen + BytesFn, const BITS: usize>(N);

/// Number with Modulus.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Modular<N: Num + NumUnsigned, M: Modulus<N>>(N, PhantomData<M>);

/// Number direction (positive/negative).
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Dir {
    /// Positive number variant.
    #[default]
    POS = 1,

    /// Negative number variant.
    NEG = -1,
}

/// Number sign (positive/negative/zero).
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    /// Zero number variant.
    #[default]
    ZERO = 0,

    /// Negative number variant.
    NEG = -1,

    /// Positive number variant.
    POS = 1,
}

/// Const-time mask.
///
/// For more info, see [crate-level](crate) documentation.
pub type MaskCt = u8;

/// Const-time relation.
///
/// For more info, see [crate-level](crate) documentation.
pub type RelCt = i8;

/// Creates random number.
///
/// Convenience wrapper over [`NdRand`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn rand<N: NdRand, Rng: rand::Rng>(order: usize, rng: &mut Rng) -> N {
    N::nd_rand(order, rng)
}

/// Calculates Greatest Common Divisor of two numbers with default semantics.
///
/// Convenience wrapper over [`NdGcd`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn gcd<N: NdGcd>(lhs: N, rhs: N) -> N {
    N::nd_gcd(lhs, rhs)
}

/// Calculates Greatest Common Divisor Extended of two numbers with default semantics.
///
/// Convenience wrapper over [`NdGcd`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn gcde<N: NdGcd>(lhs: N, rhs: N) -> (N, N, N) {
    N::nd_gcde(lhs, rhs)
}

/// Calculates Least Common Multiple of two numbers with default semantics.
///
/// Convenience wrapper over [`NdGcd`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn lcm<N: NdGcd>(lhs: N, rhs: N) -> N {
    N::nd_lcm(lhs, rhs)
}

/// Calculates Greatest Common Divisor of two numbers with checked semantics.
///
/// Convenience wrapper over [`NdGcdChecked`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn gcd_checked<N: NdGcdChecked>(lhs: N, rhs: N) -> Option<N> {
    N::nd_gcd_checked(lhs, rhs)
}

/// Calculates Greatest Common Divisor Extended of two numbers with checked semantics.
///
/// Convenience wrapper over [`NdGcdChecked`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn gcde_checked<N: NdGcdChecked>(lhs: N, rhs: N) -> Option<(N, N, N)> {
    N::nd_gcde_checked(lhs, rhs)
}

/// Calculates Least Common Multiple of two numbers with checked semantics.
///
/// Convenience wrapper over [`NdGcdChecked`].
///
/// For more info, see [crate-level](crate) documentation.
#[inline]
pub fn lcm_checked<N: NdGcdChecked>(lhs: N, rhs: N) -> Option<N> {
    N::nd_lcm_checked(lhs, rhs)
}

#[allow(unused)]
trait NdForward {}

/// Numbers functions.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumFn:
    Sized + Default + Clone + PartialEq + Eq + PartialOrd + Ord + NdOps<All = Self> + NdOpsAssign + ZeroFn + OneFn
{
    /// Checks number is odd.
    fn is_odd(&self) -> bool;

    /// Checks number is even.
    fn is_even(&self) -> bool;

    /// Writes odd number.
    #[ndfwd::as_self]
    fn write_odd(&mut self) -> &mut Self;

    /// Writes even number.
    #[ndfwd::as_self]
    fn write_even(&mut self) -> &mut Self;

    /// Alters odd/even number.
    #[ndfwd::as_self]
    fn write_alt(&mut self) -> &mut Self;

    /// Writes odd number.
    #[inline]
    #[ndfwd::as_into]
    fn into_odd(mut self) -> Self {
        self.write_odd();
        self
    }

    /// Writes even number.
    #[inline]
    #[ndfwd::as_into]
    fn into_even(mut self) -> Self {
        self.write_even();
        self
    }

    /// Alters odd/even number.
    #[inline]
    #[ndfwd::as_into]
    fn into_alt(mut self) -> Self {
        self.write_alt();
        self
    }
}

/// Number with static allocation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait Num: NumFn + Zero + One + Copy {
    /// Checks `size_of::<Self>() == size_of::<Self::Signed>`.
    #[allow(unused)]
    const CHECK_SIGNED: () = assert!(std::mem::size_of::<Self>() == std::mem::size_of::<Self::Signed>());

    /// Checks `size_of::<Self>() == size_of::<Self::Unsigned>`.
    #[allow(unused)]
    const CHECK_UNSIGNED: () = assert!(std::mem::size_of::<Self>() == std::mem::size_of::<Self::Unsigned>());

    /// Checks `size_of::<Self::Signed>() == size_of::<Self::Unsigned>`.
    #[allow(unused)]
    const CHECK_ASSOCIATED: () = assert!(std::mem::size_of::<Self::Signed>() == std::mem::size_of::<Self::Unsigned>());

    /// Signed counterpart of the same size.
    type Signed: Num + NumSigned;

    /// Unsigned counterpart of the same size.
    type Unsigned: Num + NumUnsigned;

    /// Num to `Self::Signed`.
    fn as_signed(&self) -> Self::Signed;

    /// Num to `Self::Unsigned`.
    fn as_unsigned(&self) -> Self::Unsigned;
}

/// Number with dynamic allocation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumDyn: NumFn {}

/// Number with sign.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumSigned: NumFn + From<i8> {}

/// Number without sign.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumUnsigned: NumFn + From<u8> {
    /// Order of number.
    ///
    /// Represents position of the most significant bit.
    fn order(&self) -> usize;

    /// Logarithm (base 2) of number.
    #[ndfwd::as_into]
    fn log(&self) -> Self;

    /// Square root of number.
    #[ndfwd::as_into]
    fn sqrt(&self) -> Self;
}

/// Number with const-time functions.
///
/// For more info, see [crate-level](crate) documentation.
pub trait NumCt: Num + EqCt + CmpCt + SignCt {}

/// Random generation functions.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NdRand: NumFn + BytesFn {
    /// Creates random number.
    ///
    /// Order represents position of the most significant bit.
    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn nd_rand<Rng: rand::Rng>(order: usize, rng: &mut Rng) -> Self {
        if order == 0 {
            return Self::default();
        }

        let order = order.min(Self::BYTES);
        let len = order.div_ceil(u8::BITS as usize);
        let idx = order.div_ceil(u8::BITS as usize) - 1;

        let shift = order % u8::BITS as usize;
        let mask = u8::MAX.unbounded_shr(u8::BITS - shift as u32);
        let bit = 1u8 << shift;

        let mut res = Self::default();

        let bytes = &mut res.as_bytes_mut()[..len];

        rng.fill_bytes(bytes);

        bytes[idx] &= mask;
        bytes[idx] |= bit;

        res
    }
}

/// Power functions.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NdPow: NumFn {
    /// Calculates `self ^ exp`.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    #[inline]
    #[ndfwd::as_into]
    fn nd_pow(self, mut exp: Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            if exp.is_odd() {
                Self::nd_mul_assign(&mut res, &acc);
            }

            let tmp = acc.clone();

            Self::nd_mul_assign(&mut acc, &tmp);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }

    /// Calculates `self ^ exp % rem`.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    #[inline]
    #[ndfwd::as_into]
    fn nd_powrem(self, mut exp: Self, rem: &Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            if exp.is_odd() {
                Self::nd_mul_assign(&mut res, &acc);
                Self::nd_rem_assign(&mut res, rem);
            }

            let tmp = acc.clone();

            Self::nd_mul_assign(&mut acc, &tmp);
            Self::nd_rem_assign(&mut acc, rem);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }
}

/// GCD/GCDE/LCM functions with default semantics.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NdGcd: NumFn {
    /// Calculates Greatest Common Divisor of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NdGcdChecked`] for checked semantics.
    #[inline]
    #[ndfwd::as_into]
    fn nd_gcd(mut lhs: Self, mut rhs: Self) -> Self {
        let zero = Self::zero();

        while rhs != zero {
            let rem = Self::nd_rem(&lhs, &rhs);

            lhs = rhs;
            rhs = rem;
        }

        lhs
    }

    /// Calculates Greatest Common Divisor Extended of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NdGcdChecked`] for checked semantics.
    #[inline]
    #[ndfwd::as_expr(|(r, x, y)| (Self::from(r), Self::from(x), Self::from(y)))]
    fn nd_gcde(lhs: Self, rhs: Self) -> (Self, Self, Self) {
        let zero = Self::zero();
        let one = Self::one();

        let mut r0 = lhs;
        let mut r1 = rhs;
        let mut x0 = one.clone();
        let mut x1 = zero.clone();
        let mut y0 = zero.clone();
        let mut y1 = one.clone();

        while r1 != zero {
            let div = Self::nd_div(&r0, &r1);

            let r = Self::nd_sub(&r0, &Self::nd_mul(&div, &r1));
            let x = Self::nd_sub(&x0, &Self::nd_mul(&div, &x1));
            let y = Self::nd_sub(&y0, &Self::nd_mul(&div, &y1));

            r0 = r1;
            r1 = r;

            x0 = x1;
            x1 = x;

            y0 = y1;
            y1 = y;
        }

        (r0, x0, y0)
    }

    /// Calculates Least Common Multiple of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NdGcdChecked`] for checked semantics.
    #[inline]
    #[ndfwd::as_into]
    fn nd_lcm(lhs: Self, rhs: Self) -> Self {
        let val = Self::nd_gcd(lhs.clone(), rhs.clone());
        let val = Self::nd_div(&lhs, &val);

        Self::nd_mul(&val, &rhs)
    }
}

/// GCD/GCDE/LCM functions with checked semantics.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NdGcdChecked: NumFn + NdOpsChecked<All = Self> {
    /// Calculates Greatest Common Divisor of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[inline]
    #[ndfwd::as_map(Self::from)]
    fn nd_gcd_checked(mut lhs: Self, mut rhs: Self) -> Option<Self> {
        let zero = Self::zero();

        while rhs != zero {
            let rem = Self::nd_rem_checked(&lhs, &rhs)?;

            lhs = rhs;
            rhs = rem;
        }

        Some(lhs)
    }

    /// Calculates Greatest Common Divisor Extended of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[inline]
    #[ndfwd::as_map(|(r, x, y)| (Self::from(r), Self::from(x), Self::from(y)))]
    fn nd_gcde_checked(lhs: Self, rhs: Self) -> Option<(Self, Self, Self)> {
        let zero = Self::zero();
        let one = Self::one();

        let mut r0 = lhs;
        let mut r1 = rhs;
        let mut x0 = one.clone();
        let mut x1 = zero.clone();
        let mut y0 = zero.clone();
        let mut y1 = one.clone();

        while r1 != zero {
            let div = Self::nd_div(&r0, &r1);

            let r = Self::nd_sub_checked(&r0, &Self::nd_mul_checked(&div, &r1)?)?;
            let x = Self::nd_sub_checked(&x0, &Self::nd_mul_checked(&div, &x1)?)?;
            let y = Self::nd_sub_checked(&y0, &Self::nd_mul_checked(&div, &y1)?)?;

            r0 = r1;
            r1 = r;

            x0 = x1;
            x1 = x;

            y0 = y1;
            y1 = y;
        }

        Some((r0, x0, y0))
    }

    /// Calculates Least Common Multiple of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[inline]
    #[ndfwd::as_map(Self::from)]
    fn nd_lcm_checked(lhs: Self, rhs: Self) -> Option<Self> {
        let val = Self::nd_gcd_checked(lhs.clone(), rhs.clone())?;
        let val = Self::nd_div_checked(&lhs, &val)?;

        Self::nd_mul_checked(&val, &rhs)
    }
}

/// Range for [`Ranged`] numbers.
///
/// For more info, see [crate-level](crate) documentation.
pub trait Range<N: Num>: Default + Debug + Clone {
    /// Range inclusive minimum.
    const MIN: N;

    /// Range inclusive maximum.
    const MAX: N;
}

/// Modulus for [`Modular`] numbers.
///
/// For more info, see [crate-level](crate) documentation.
pub trait Modulus<N: Num>: Default + Debug + Clone + Copy {
    /// Modulus for arithmetics.
    const MOD: N;
}

/// Zero with static allocation.
///
/// For more info, see [crate-level](crate) documentation.
pub trait Zero {
    /// Zero value.
    const ZERO: Self;
}

/// One with static allocation.
///
/// For more info, see [crate-level](crate) documentation.
pub trait One {
    /// One value.
    const ONE: Self;
}

/// Minimum with static allocation.
///
/// For more info, see [crate-level](crate) documentation.
pub trait Min {
    /// Minimum value.
    const MIN: Self;
}

/// Maximum with static allocation.
///
/// For more info, see [crate-level](crate) documentation.
pub trait Max {
    /// Maximum value.
    const MAX: Self;
}

/// Zero with dynamic allocation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait ZeroFn {
    /// Returns zero value.
    #[ndfwd::as_into]
    fn zero() -> Self;
}

/// One with dynamic allocation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait OneFn {
    /// Returns one value.
    #[ndfwd::as_into]
    fn one() -> Self;
}

/// Minimum with dynamic allocation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait MinFn {
    /// Returns minimum value.
    #[ndfwd::as_into]
    fn min() -> Self;
}

/// Maximum with dynamic allocation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait MaxFn {
    /// Returns maximum value.
    #[ndfwd::as_into]
    fn max() -> Self;
}

/// Const-time equality comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait EqCt {
    /// Const-time equality function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs != rhs`.
    /// - `MaskCt::MAX` => `lhs == rhs`.
    fn eq_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait CmpCt: EqCt + LtCt + GtCt {
    /// Const-time comparison function.
    ///
    /// # Returns
    ///
    /// - `-1` => `lhs < rhs`
    /// - `0` => `lhs == rhs`.
    /// - `1` => `lhs > rhs`
    #[inline]
    fn cmp_ct(&self, other: &Self) -> RelCt {
        let lt = self.lt_ct(other) as RelCt;
        let gt = self.gt_ct(other) as RelCt;

        lt | gt & 1
    }
}

/// Const-time sign.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait SignCt: IsZeroCt + IsPosCt + IsNegCt {
    /// Const-time sign function.
    ///
    /// # Returns
    ///
    /// - `-1` => `lhs < 0`
    /// - `0` => `lhs == 0`.
    /// - `1` => `lhs > 0`
    #[inline]
    fn sign_ct(&self) -> RelCt {
        let pos = self.is_pos_ct() as RelCt;
        let neg = self.is_neg_ct() as RelCt;

        pos & 1 | neg
    }
}

/// Const-time equality with zero comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait IsZeroCt {
    /// Const-time equality with zero function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `value != 0`.
    /// - `MaskCt::MAX` => `value == 0`.
    fn is_zero_ct(&self) -> MaskCt;
}

/// Const-time equality with one comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait IsOneCt {
    /// Const-time equality with one function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `value != 0`.
    /// - `MaskCt::MAX` => `value == 0`.
    fn is_one_ct(&self) -> MaskCt;
}

/// Const-time greater-then-zero comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait IsPosCt {
    /// Const-time greater-then-zero function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs > 0`.
    /// - `MaskCt::MAX` => `lhs <= 0`.
    fn is_pos_ct(&self) -> MaskCt;
}

/// Const-time less-then-zero comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait IsNegCt {
    /// Const-time less-then-zero function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs >= 0`.
    /// - `MaskCt::MAX` => `lhs < 0`.
    fn is_neg_ct(&self) -> MaskCt;
}

/// Const-time less-then comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait LtCt {
    /// Const-time less-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs >= rhs`.
    /// - `MaskCt::MAX` => `lhs < rhs`.
    fn lt_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time greater-then comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait GtCt {
    /// Const-time greater-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs <= rhs`.
    /// - `MaskCt::MAX` => `lhs > rhs`.
    fn gt_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time less-or-equal-then comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait LeCt: EqCt + LtCt + GtCt {
    /// Const-time less-or-equal-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs > rhs`.
    /// - `MaskCt::MAX` => `lhs <= rhs`.
    #[inline]
    fn le_ct(&self, other: &Self) -> MaskCt {
        !self.gt_ct(other)
    }
}

/// Const-time greater-or-equal-then comparison.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait GeCt: EqCt + LtCt + GtCt {
    /// Const-time greater-or-equal-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs < rhs`.
    /// - `MaskCt::MAX` => `lhs >= rhs`.
    #[inline]
    fn ge_ct(&self, other: &Self) -> MaskCt {
        !self.lt_ct(other)
    }
}

/// Const-time minimum value.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait MinCt: Copy + EqCt + LtCt + GtCt + SelectCt {
    /// Const-time minimum function.
    #[inline]
    #[ndfwd::as_into]
    fn min_ct(&self, other: &Self) -> Self {
        SelectCt::select_ct(self, other, self.lt_ct(other))
    }
}

/// Const-time maximum value.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait MaxCt: Copy + EqCt + LtCt + GtCt + SelectCt {
    /// Const-time maximum function.
    #[inline]
    #[ndfwd::as_into]
    fn max_ct(&self, other: &Self) -> Self {
        SelectCt::select_ct(self, other, self.gt_ct(other))
    }
}

/// Const-time positive absolute value.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait PosxCt {
    /// Const-time positive absolute function.
    #[ndfwd::as_into]
    fn posx_ct(&self) -> Self;
}

/// Const-time positive absolute value.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NegxCt {
    /// Const-time negative absolute function.
    #[ndfwd::as_into]
    fn negx_ct(&self) -> Self;
}

/// Const-time select value.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait SelectCt {
    /// Const-time select function.
    ///
    /// # Returns
    ///
    /// `lhs & mask | rhs & !mask`
    ///
    /// `mask` is repeated to match `size_of::<Self>()`.
    #[ndfwd::as_into]
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self;
}

/// Const-time power functions.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait PowCt: Num + SelectCt {
    /// Calculates `self ^ exp` in const-time.
    ///
    /// For true const-time, use via [`Wrapping`] or [`Relaxed`].
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    #[inline]
    #[ndfwd::as_into]
    fn pow_ct(self, mut exp: Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            let val = Self::nd_mul(&res, &acc);

            res = SelectCt::select_ct(&res, &val, [0, MaskCt::MAX][exp.is_even() as usize]);

            let tmp = acc;

            Self::nd_mul_assign(&mut acc, &tmp);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }

    /// Calculates `self ^ exp % rem` in const-time.
    ///
    /// For true const-time, use via [`Wrapping`] or [`Relaxed`].
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    #[inline]
    #[ndfwd::as_into]
    fn powrem_ct(self, mut exp: Self, rem: &Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            let val = Self::nd_mul(&res, &acc);
            let val = Self::nd_rem(&val, rem);

            res = SelectCt::select_ct(&res, &val, [0, MaskCt::MAX][exp.is_even() as usize]);

            let tmp = acc;

            Self::nd_mul_assign(&mut acc, &tmp);
            Self::nd_rem_assign(&mut acc, rem);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }
}

num_impl!(@signed [i8 > u8, i16 > u16, i32 > u32, i64 > u64, i128 > u128, isize > usize]);
num_impl!(@unsigned [u8 > i8, u16 > i16, u32 > i32, u64 > i64, u128 > i128, usize > isize]);

dir_from!([i8, i16, i32, i64, i128, isize]);
dir_from!([u8, u16, u32, u64, u128, usize]);

sign_from!([i8, i16, i32, i64, i128, isize]);
sign_from!([u8, u16, u32, u64, u128, usize]);

impl<N: Num, R: Range<N>> From<N> for Ranged<N, R> {
    #[inline]
    fn from(value: N) -> Self {
        if value < R::MIN {
            return Self(R::MIN, PhantomData);
        }

        if value > R::MAX {
            return Self(R::MAX, PhantomData);
        }

        Self(value, PhantomData)
    }
}

impl<N: Num + NumUnsigned + BytesLen + BytesFn, const BITS: usize> From<N> for Width<N, BITS> {
    #[inline]
    fn from(value: N) -> Self {
        Self(value).normalized()
    }
}

impl<N: Num + NumUnsigned, M: Modulus<N>> From<N> for Modular<N, M> {
    #[inline]
    fn from(value: N) -> Self {
        Self(value, PhantomData).normalized()
    }
}

ndops::def! { @stdbin (lhs: Sign, rhs: Sign) -> Sign, [* (lhs as i8) * (rhs as i8)] }
ndops::def! { @stdbin (lhs:  Dir, rhs:  Dir) ->  Dir, [* (lhs as i8) * (rhs as i8)] }

#[ndfwd::def(self.0 with &'num N: arch::BytesLen)]
#[ndfwd::def(self.0 with &'num N: arch::BytesFn)]
#[ndfwd::def(self.0 with &'num N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with &'num N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with &'num N: NumFn!)]
#[ndfwd::def(self.0 with &'num N: Num!)]
#[ndfwd::def(self.0 with &'num N: NumSigned)]
#[ndfwd::def(self.0 with &'num N: NumUnsigned)]
#[ndfwd::def(self.0 with &'num N: NdRand!)]
#[ndfwd::def(self.0 with &'num N: NdPow!)]
#[ndfwd::def(self.0 with &'num N: NdGcd!)]
#[ndfwd::def(self.0 with &'num N: NdGcdChecked!)]
#[ndfwd::def(self.0 with &'num N: IsZeroCt)]
#[ndfwd::def(self.0 with &'num N: IsOneCt)]
#[ndfwd::def(self.0 with &'num N: IsPosCt)]
#[ndfwd::def(self.0 with &'num N: IsNegCt)]
#[ndfwd::def(self.0 with &'num N: EqCt)]
#[ndfwd::def(self.0 with &'num N: LtCt)]
#[ndfwd::def(self.0 with &'num N: GtCt)]
#[ndfwd::def(self.0 with &'num N: LeCt)]
#[ndfwd::def(self.0 with &'num N: GeCt)]
#[ndfwd::def(self.0 with &'num N: SignCt)]
#[ndfwd::def(self.0 with &'num N: CmpCt)]
#[ndfwd::def(self.0 with &'num N: MinCt)]
#[ndfwd::def(self.0 with &'num N: MaxCt)]
#[ndfwd::def(self.0 with &'num N: PosxCt)]
#[ndfwd::def(self.0 with &'num N: NegxCt)]
#[ndfwd::def(self.0 with &'num N: SelectCt)]
#[ndfwd::def(self.0 with &'num N: PowCt!)]
impl<'num, N> NdForward for Ref<'num, N> {}

#[ndfwd::def(self.0 with &'num mut N: arch::BytesLen)]
#[ndfwd::def(self.0 with &'num mut N: arch::BytesFn)]
#[ndfwd::def(self.0 with &'num mut N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with &'num mut N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with &'num mut N: NumFn!)]
#[ndfwd::def(self.0 with &'num mut N: Num!)]
#[ndfwd::def(self.0 with &'num mut N: NumSigned)]
#[ndfwd::def(self.0 with &'num mut N: NumUnsigned)]
#[ndfwd::def(self.0 with &'num mut N: NdRand!)]
#[ndfwd::def(self.0 with &'num mut N: NdPow!)]
#[ndfwd::def(self.0 with &'num mut N: NdGcd!)]
#[ndfwd::def(self.0 with &'num mut N: NdGcdChecked!)]
#[ndfwd::def(self.0 with &'num mut N: IsZeroCt)]
#[ndfwd::def(self.0 with &'num mut N: IsOneCt)]
#[ndfwd::def(self.0 with &'num mut N: IsPosCt)]
#[ndfwd::def(self.0 with &'num mut N: IsNegCt)]
#[ndfwd::def(self.0 with &'num mut N: EqCt)]
#[ndfwd::def(self.0 with &'num mut N: LtCt)]
#[ndfwd::def(self.0 with &'num mut N: GtCt)]
#[ndfwd::def(self.0 with &'num mut N: LeCt)]
#[ndfwd::def(self.0 with &'num mut N: GeCt)]
#[ndfwd::def(self.0 with &'num mut N: SignCt)]
#[ndfwd::def(self.0 with &'num mut N: CmpCt)]
#[ndfwd::def(self.0 with &'num mut N: MinCt)]
#[ndfwd::def(self.0 with &'num mut N: MaxCt)]
#[ndfwd::def(self.0 with &'num mut N: PosxCt)]
#[ndfwd::def(self.0 with &'num mut N: NegxCt)]
#[ndfwd::def(self.0 with &'num mut N: SelectCt)]
#[ndfwd::def(self.0 with &'num mut N: PowCt!)]
impl<'num, N> NdForward for Mut<'num, N> {}

#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumSigned)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdRand!)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[ndfwd::def(self.0 with N: IsZeroCt)]
#[ndfwd::def(self.0 with N: IsOneCt)]
#[ndfwd::def(self.0 with N: IsPosCt)]
#[ndfwd::def(self.0 with N: IsNegCt)]
#[ndfwd::def(self.0 with N: EqCt)]
#[ndfwd::def(self.0 with N: LtCt)]
#[ndfwd::def(self.0 with N: GtCt)]
#[ndfwd::def(self.0 with N: LeCt)]
#[ndfwd::def(self.0 with N: GeCt)]
#[ndfwd::def(self.0 with N: SignCt)]
#[ndfwd::def(self.0 with N: CmpCt)]
#[ndfwd::def(self.0 with N: MinCt)]
#[ndfwd::def(self.0 with N: MaxCt)]
#[ndfwd::def(self.0 with N: PosxCt)]
#[ndfwd::def(self.0 with N: NegxCt)]
#[ndfwd::def(self.0 with N: SelectCt)]
#[ndfwd::def(self.0 with N: PowCt!)]
impl<N> NdForward for Strict<N> {}

#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumSigned)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdRand!)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[ndfwd::def(self.0 with N: IsZeroCt)]
#[ndfwd::def(self.0 with N: IsOneCt)]
#[ndfwd::def(self.0 with N: IsPosCt)]
#[ndfwd::def(self.0 with N: IsNegCt)]
#[ndfwd::def(self.0 with N: EqCt)]
#[ndfwd::def(self.0 with N: LtCt)]
#[ndfwd::def(self.0 with N: GtCt)]
#[ndfwd::def(self.0 with N: LeCt)]
#[ndfwd::def(self.0 with N: GeCt)]
#[ndfwd::def(self.0 with N: SignCt)]
#[ndfwd::def(self.0 with N: CmpCt)]
#[ndfwd::def(self.0 with N: MinCt)]
#[ndfwd::def(self.0 with N: MaxCt)]
#[ndfwd::def(self.0 with N: PosxCt)]
#[ndfwd::def(self.0 with N: NegxCt)]
#[ndfwd::def(self.0 with N: SelectCt)]
#[ndfwd::def(self.0 with N: PowCt!)]
impl<N> NdForward for Wrapping<N> {}

#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumSigned)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdRand!)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[ndfwd::def(self.0 with N: IsZeroCt)]
#[ndfwd::def(self.0 with N: IsOneCt)]
#[ndfwd::def(self.0 with N: IsPosCt)]
#[ndfwd::def(self.0 with N: IsNegCt)]
#[ndfwd::def(self.0 with N: EqCt)]
#[ndfwd::def(self.0 with N: LtCt)]
#[ndfwd::def(self.0 with N: GtCt)]
#[ndfwd::def(self.0 with N: LeCt)]
#[ndfwd::def(self.0 with N: GeCt)]
#[ndfwd::def(self.0 with N: SignCt)]
#[ndfwd::def(self.0 with N: CmpCt)]
#[ndfwd::def(self.0 with N: MinCt)]
#[ndfwd::def(self.0 with N: MaxCt)]
#[ndfwd::def(self.0 with N: PosxCt)]
#[ndfwd::def(self.0 with N: NegxCt)]
#[ndfwd::def(self.0 with N: SelectCt)]
#[ndfwd::def(self.0 with N: PowCt!)]
impl<N> NdForward for Saturating<N> {}

#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumSigned)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdRand!)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[ndfwd::def(self.0 with N: IsZeroCt)]
#[ndfwd::def(self.0 with N: IsOneCt)]
#[ndfwd::def(self.0 with N: IsPosCt)]
#[ndfwd::def(self.0 with N: IsNegCt)]
#[ndfwd::def(self.0 with N: EqCt)]
#[ndfwd::def(self.0 with N: LtCt)]
#[ndfwd::def(self.0 with N: GtCt)]
#[ndfwd::def(self.0 with N: LeCt)]
#[ndfwd::def(self.0 with N: GeCt)]
#[ndfwd::def(self.0 with N: SignCt)]
#[ndfwd::def(self.0 with N: CmpCt)]
#[ndfwd::def(self.0 with N: MinCt)]
#[ndfwd::def(self.0 with N: MaxCt)]
#[ndfwd::def(self.0 with N: PosxCt)]
#[ndfwd::def(self.0 with N: NegxCt)]
#[ndfwd::def(self.0 with N: SelectCt)]
#[ndfwd::def(self.0 with N: PowCt!)]
impl<N> NdForward for Unbounded<N> {}

#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: arch::AsBytesRef)]
#[ndfwd::def(self.0 with N: arch::AsBytesMut)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumSigned)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[ndfwd::def(self.0 with N: NdRand!)]
#[ndfwd::def(self.0 with N: NdPow!)]
#[ndfwd::def(self.0 with N: NdGcd!)]
#[ndfwd::def(self.0 with N: NdGcdChecked!)]
#[ndfwd::def(self.0 with N: IsZeroCt)]
#[ndfwd::def(self.0 with N: IsOneCt)]
#[ndfwd::def(self.0 with N: IsPosCt)]
#[ndfwd::def(self.0 with N: IsNegCt)]
#[ndfwd::def(self.0 with N: EqCt)]
#[ndfwd::def(self.0 with N: LtCt)]
#[ndfwd::def(self.0 with N: GtCt)]
#[ndfwd::def(self.0 with N: LeCt)]
#[ndfwd::def(self.0 with N: GeCt)]
#[ndfwd::def(self.0 with N: SignCt)]
#[ndfwd::def(self.0 with N: CmpCt)]
#[ndfwd::def(self.0 with N: MinCt)]
#[ndfwd::def(self.0 with N: MaxCt)]
#[ndfwd::def(self.0 with N: PosxCt)]
#[ndfwd::def(self.0 with N: NegxCt)]
#[ndfwd::def(self.0 with N: SelectCt)]
#[ndfwd::def(self.0 with N: PowCt!)]
impl<N> NdForward for Relaxed<N> {}

impl<N: Zero> Zero for Strict<N> {
    const ZERO: Self = Strict(N::ZERO);
}

impl<N: One> One for Strict<N> {
    const ONE: Self = Strict(N::ONE);
}

impl<N: Min> Min for Strict<N> {
    const MIN: Self = Strict(N::MIN);
}

impl<N: Max> Max for Strict<N> {
    const MAX: Self = Strict(N::MAX);
}

impl<N: Zero> Zero for Wrapping<N> {
    const ZERO: Self = Wrapping(N::ZERO);
}

impl<N: One> One for Wrapping<N> {
    const ONE: Self = Wrapping(N::ONE);
}

impl<N: Min> Min for Wrapping<N> {
    const MIN: Self = Wrapping(N::MIN);
}

impl<N: Max> Max for Wrapping<N> {
    const MAX: Self = Wrapping(N::MAX);
}

impl<N: Zero> Zero for Saturating<N> {
    const ZERO: Self = Saturating(N::ZERO);
}

impl<N: One> One for Saturating<N> {
    const ONE: Self = Saturating(N::ONE);
}

impl<N: Min> Min for Saturating<N> {
    const MIN: Self = Saturating(N::MIN);
}

impl<N: Max> Max for Saturating<N> {
    const MAX: Self = Saturating(N::MAX);
}

impl<N: Zero> Zero for Unbounded<N> {
    const ZERO: Self = Unbounded(N::ZERO);
}

impl<N: One> One for Unbounded<N> {
    const ONE: Self = Unbounded(N::ONE);
}

impl<N: Min> Min for Unbounded<N> {
    const MIN: Self = Unbounded(N::MIN);
}

impl<N: Max> Max for Unbounded<N> {
    const MAX: Self = Unbounded(N::MAX);
}

impl<N: Zero> Zero for Relaxed<N> {
    const ZERO: Self = Relaxed(N::ZERO);
}

impl<N: One> One for Relaxed<N> {
    const ONE: Self = Relaxed(N::ONE);
}

impl<N: Min> Min for Relaxed<N> {
    const MIN: Self = Relaxed(N::MIN);
}

impl<N: Max> Max for Relaxed<N> {
    const MAX: Self = Relaxed(N::MAX);
}

impl<N: Num + NumUnsigned + BytesLen + BytesFn, const BITS: usize> BytesLen for Width<N, BITS> {
    const BITS: usize = BITS;
    const BYTES: usize = BITS.div_ceil(8);
}

impl<N: Num + NumUnsigned + BytesLen + BytesFn, const BITS: usize> Width<N, BITS> {
    #[allow(unused)]
    const CHECK: () = assert!(0 < BITS && BITS <= N::BITS);

    #[inline]
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    #[inline]
    pub(crate) fn normalize(&mut self) -> &mut Self {
        if N::BITS <= BITS {
            return self;
        }

        let bits = N::BITS - BITS;
        let div = bits / Single::BITS as usize;
        let rem = bits % Single::BITS as usize;

        for idx in 0..div {
            self.write_bitand(0, Offset::Right((idx + 1) * BITS));
        }

        self.write_bitand(Single::MAX.unbounded_shr(rem as u32), Offset::Right((div + 1) * BITS));
        self
    }
}

impl<N: Num + NumUnsigned, M: Modulus<N>> Modular<N, M> {
    #[inline]
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    #[inline]
    pub(crate) fn normalize(&mut self) -> &mut Self {
        N::nd_rem_assign(&mut self.0, &M::MOD);

        self
    }
}

impl<Any: Zero> ZeroFn for Any {
    #[inline]
    fn zero() -> Self {
        Any::ZERO
    }
}

impl<Any: One> OneFn for Any {
    #[inline]
    fn one() -> Self {
        Any::ONE
    }
}

impl<Any: Min> MinFn for Any {
    #[inline]
    fn min() -> Self {
        Any::MIN
    }
}

impl<Any: Max> MaxFn for Any {
    #[inline]
    fn max() -> Self {
        Any::MAX
    }
}

#[inline]
fn dir_ct(val: MaskCt) -> MaskCt {
    MaskCt::ZERO.wrapping_sub(val)
}

#[inline]
fn inv_ct(val: MaskCt) -> MaskCt {
    !MaskCt::ZERO.wrapping_sub(val)
}

#[inline]
fn eq_ct<N: Num + NdOpsWrapping<All = N> + NdOpsAssignWrapping>(lhs: &N, rhs: &N) {
    todo!()
}

#[inline]
fn cmp_ct<N: Num + NdOpsWrapping<All = N> + NdOpsAssignWrapping>(lhs: &N, rhs: &N) {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 48).filter(|&val| val < u64::MAX).map(|val| val + 1)) [
            (u64::nd_gcd(val, 0), val),
            (u64::nd_gcd(0, val), val),
            (u64::nd_gcd(val, 1), 1),
            (u64::nd_gcd(1, val), 1),
            (u64::nd_gcd(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            (u64::nd_gcd(lhs, rhs), u64::nd_gcd(rhs, lhs)),
            (lhs % u64::nd_gcd(lhs, rhs), 0),
            (rhs % u64::nd_gcd(lhs, rhs), 0),
            (u64::nd_gcd(lhs, rhs) * u64::nd_lcm(lhs, rhs), lhs * rhs),
            {
                let res = u64::nd_gcd(lhs, rhs);

                (u64::nd_gcd(lhs / res, rhs / res), 1)
            },
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 6,
            rhs in 1..=1 << 6,
              k in 1..=1 << 6,
        ) [
            (u64::nd_gcd(k * lhs, k * rhs), k * u64::nd_gcd(lhs, rhs)),
        ] }
    }

    #[test]
    fn gcde() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 48).filter(|&val| val < i64::MAX).map(|val| val + 1)) [
            (i64::nd_gcde(val, 0), (val, 1, 0)),
            (i64::nd_gcde(0, val), (val, 0, 1)),
            (i64::nd_gcde(val, 1), (1, 0, 1)),
            (i64::nd_gcde(1, val), (1, 1, 0)),
            (i64::nd_gcde(val, val), (val, 0, 1)),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            (i64::nd_gcde(lhs, rhs).0, i64::nd_gcde(rhs, lhs).0),
            (lhs % i64::nd_gcde(lhs, rhs).0, 0),
            (rhs % i64::nd_gcde(lhs, rhs).0, 0),
            (i64::nd_gcde(lhs, rhs).0 * i64::nd_lcm(lhs, rhs), lhs * rhs),
            {
                let res = i64::nd_gcde(lhs, rhs).0;

                (i64::nd_gcde(lhs / res, rhs / res).0, 1)
            },
            {
                let res = i64::nd_gcde(lhs, rhs);

                (lhs * res.1 + rhs * res.2, res.0)
            }
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 6,
            rhs in 1..=1 << 6,
              k in 1..=1 << 6,
        ) [
            (i64::nd_gcde(k * lhs, k * rhs).0, k * i64::nd_gcde(lhs, rhs).0),
        ] }
    }

    #[test]
    fn lcm() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 48).filter(|&val| val < u64::MAX).map(|val| val + 1)) [
            (u64::nd_lcm(val, 0), 0),
            (u64::nd_lcm(0, val), 0),
            (u64::nd_lcm(val, 1), val),
            (u64::nd_lcm(1, val), val),
            (u64::nd_lcm(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            (u64::nd_lcm(lhs, rhs), u64::nd_lcm(rhs, lhs)),
            (u64::nd_lcm(lhs, rhs) % lhs, 0),
            (u64::nd_lcm(lhs, rhs) % rhs, 0),
            (u64::nd_lcm(lhs, rhs) * u64::nd_gcd(lhs, rhs), lhs * rhs),
            {
                let res = u64::nd_lcm(lhs, rhs);

                (u64::nd_gcd(res / lhs, res / rhs), 1)
            },
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 6,
            rhs in 1..=1 << 6,
              k in 1..=1 << 6,
        ) [
            (u64::nd_lcm(k * lhs, k * rhs), k * u64::nd_lcm(lhs, rhs)),
        ] }
    }

    #[test]
    fn pow() {
        const EXP: u64 = ndassert::prime!(8);
        const MOD: u64 = ndassert::prime!(32);

        for value in ndassert::range!(u32, 24).map(|x| x as u64) {
            let mut acc = Wrapping(1u64);

            for exp in 0..EXP {
                assert_eq!(acc, Wrapping(value).nd_pow(Wrapping(exp)));

                acc *= Wrapping(value);
            }
        }

        for value in ndassert::range!(u32, 24).map(|x| x as u64) {
            let mut acc = Wrapping(1u64);

            for exp in 0..EXP {
                assert_eq!(acc, Wrapping(value).nd_powrem(Wrapping(exp), &Wrapping(MOD)));

                acc *= Wrapping(value);
                acc %= Wrapping(MOD);
            }
        }
    }

    #[test]
    fn ranged() {}

    #[test]
    fn width() {}

    #[test]
    fn modular() {}

    #[test]
    fn cmp_ct() {
        #![allow(clippy::absurd_extreme_comparisons)]
        #![allow(unused_comparisons)]

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            rhs in ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
        ) [
            (lhs.is_zero_ct(), MaskCt::MAX * (lhs == 0)   as MaskCt),
            (lhs.is_one_ct(),  MaskCt::MAX * (lhs == 1)   as MaskCt),
            (lhs.is_pos_ct(),  MaskCt::MAX * (lhs >  0)   as MaskCt),
            (lhs.is_neg_ct(),  MaskCt::MAX * (lhs <  0)   as MaskCt),
            (lhs.eq_ct(&rhs),  MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs.lt_ct(&rhs),  MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs.gt_ct(&rhs),  MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs.le_ct(&rhs),  MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs.ge_ct(&rhs),  MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs.sign_ct(),    lhs.cmp(&0)   as RelCt),
            (lhs.cmp_ct(&rhs), lhs.cmp(&rhs) as RelCt),
            (lhs.min_ct(&rhs), lhs.min(rhs)),
            (lhs.max_ct(&rhs), lhs.max(rhs)),
            (lhs.posx_ct(),    lhs.wrapping_abs()),
            (lhs.negx_ct(),    lhs.wrapping_abs().wrapping_neg()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(u64, 56, 1).chain([0, 1]),
        ) [
            (lhs.is_zero_ct(), MaskCt::MAX * (lhs == 0)   as MaskCt),
            (lhs.is_one_ct(),  MaskCt::MAX * (lhs == 1)   as MaskCt),
            (lhs.is_pos_ct(),  MaskCt::MAX * (lhs >  0)   as MaskCt),
            (lhs.is_neg_ct(),  MaskCt::MAX * (lhs <  0)   as MaskCt),
            (lhs.eq_ct(&rhs),  MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs.lt_ct(&rhs),  MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs.gt_ct(&rhs),  MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs.le_ct(&rhs),  MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs.ge_ct(&rhs),  MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs.sign_ct(),    lhs.cmp(&0)   as RelCt),
            (lhs.cmp_ct(&rhs), lhs.cmp(&rhs) as RelCt),
            (lhs.min_ct(&rhs), lhs.min(rhs)),
            (lhs.max_ct(&rhs), lhs.max(rhs)),
        ] }
    }

    #[test]
    fn pow_ct() {
        const EXP: u64 = ndassert::prime!(8);
        const MOD: u64 = ndassert::prime!(32);

        for value in ndassert::range!(u32, 24).map(|x| x as u64) {
            let mut acc = Wrapping(1u64);

            for exp in 0..EXP {
                assert_eq!(acc, Wrapping(value).pow_ct(Wrapping(exp)));

                acc *= Wrapping(value);
            }
        }

        for value in ndassert::range!(u32, 24).map(|x| x as u64) {
            let mut acc = Wrapping(1u64);

            for exp in 0..EXP {
                assert_eq!(acc, Wrapping(value).powrem_ct(Wrapping(exp), &Wrapping(MOD)));

                acc *= Wrapping(value);
                acc %= Wrapping(MOD);
            }
        }
    }
}

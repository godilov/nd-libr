#![doc = include_str!("../README.md")]

use std::{cmp::Ordering, fmt::Debug, marker::PhantomData};

use ndext::ops::*;
use zerocopy::IntoBytes;

use crate::arch::{BytesFn, BytesLen, Offset, word::Single};

pub mod arch;
pub mod long;
pub mod prime;

macro_rules! dir_ct {
    ($expr:expr) => {
        MaskCt::ZERO.wrapping_sub($expr)
    };
}

macro_rules! inv_ct {
    ($expr:expr) => {
        !MaskCt::ZERO.wrapping_sub($expr)
    };
}

macro_rules! num_impl {
    (@signed [$($primitive:ty > $unsigned:ty),+] $(,)?) => {
        $(num_impl!(@impl $primitive, $primitive, $unsigned);)+
        $(num_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty > $signed:ty),+] $(,)?) => {
        $(num_impl!(@impl $primitive, $signed, $primitive);)+
        $(num_impl!(@unsigned $primitive);)+
    };
    (@impl $primitive:ty, $signed:ty, $unsigned:ty $(,)?) => {
        impl BytesLen for $primitive {
            const BITS: usize = Self::BITS as usize;
            const BYTES: usize = Self::BITS as usize / 8;
        }

        impl BytesFn for $primitive {
            #[inline]
            fn as_bytes_ref(&self) -> &[u8] {
                self.as_bytes()
            }

            #[inline]
            fn as_bytes_mut(&mut self) -> &mut [u8] {
                self.as_mut_bytes()
            }

            #[inline]
            fn read(&self, offset: Offset) -> Single {
                let offset = match offset {
                    Offset::Left(val) => val as u32,
                    Offset::Right(val) => Self::BITS.saturating_sub(val as u32),
                };

                self.unbounded_shr(offset) as Single
            }

            #[inline]
            fn write_bitor(&mut self, mask: Single, offset: Offset) -> &mut Self {
                let offset = match offset {
                    Offset::Left(val) => val as u32,
                    Offset::Right(val) => Self::BITS.saturating_sub(val as u32),
                };

                *self |= (mask as Self).unbounded_shl(offset);
                self
            }

            #[inline]
            fn write_bitand(&mut self, mask: Single, offset: Offset) -> &mut Self {
                use std::ops::Not;

                let offset = match offset {
                    Offset::Left(val) => val as u32,
                    Offset::Right(val) => Self::BITS.saturating_sub(val as u32),
                };

                *self &= (mask.not() as Self).unbounded_shl(offset).not();
                self
            }

            #[inline]
            fn write_bitxor(&mut self, mask: Single, offset: Offset) -> &mut Self {
                let offset = match offset {
                    Offset::Left(val) => val as u32,
                    Offset::Right(val) => Self::BITS.saturating_sub(val as u32),
                };

                *self ^= (mask as Self).unbounded_shl(offset);
                self
            }
        }

        impl NumFn for $primitive {
            type Signed = $signed;
            type Unsigned = $unsigned;

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

        impl NumPow for $primitive {}

        impl NumGcd for $primitive {}

        impl NumGcdChecked for $primitive {}

        impl Num for $primitive {}

        impl NumRand for $primitive {}

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
    };
    (@signed $primitive:ty $(,)?) => {
        impl NumSigned for $primitive {}
    };
    (@unsigned $primitive:ty $(,)?) => {
        impl NumUnsigned for $primitive {
            #[inline]
            fn order(&self) -> usize {
                self.ilog2() as usize
            }

            #[inline]
            fn log(&self) -> Self {
                self.ilog2() as $primitive
            }

            #[inline]
            fn sqrt(&self) -> Self {
                self.isqrt() as $primitive
            }
        }
    };
}

#[cfg(feature = "const-time")]
macro_rules! num_ct_impl {
    (@signed [$($signed:ty > $unsigned:ty),+ $(,)?]) => {
        $(num_ct_impl!(@signed $signed > $unsigned);)+
    };
    (@unsigned [$($unsigned:ty),+ $(,)?]) => {
        $(num_ct_impl!(@unsigned $unsigned);)+
    };
    (@signed $signed:ty > $unsigned:ty $(,)?) => {
        impl OneCt for $signed {
            #[inline(never)]
            fn one_ct(&self) -> MaskCt {
                let val = *self as $unsigned;
                let val = val ^ 1;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct!(any)
            }
        }

        impl ZeroCt for $signed {
            #[inline(never)]
            fn zero_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct!(any)
            }
        }

        impl PosCt for $signed {
            #[inline(never)]
            fn pos_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let neg = val >> (Self::BITS - 1);
                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);

                let neg = neg as MaskCt;
                let any = any as MaskCt;

                inv_ct!(neg) & dir_ct!(any)
            }
        }

        impl NegCt for $signed {
            #[inline(never)]
            fn neg_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let neg = val >> (Self::BITS - 1);
                let neg = neg as MaskCt;

                dir_ct!(neg)
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

                inv_ct!(any)
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

                dir_ct!(res)
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

                dir_ct!(res)
            }
        }

        impl AbsCt for $signed {
            #[inline]
            fn abs_ct(&self) -> Self {
                SelectCt::select_ct(self, &self.wrapping_abs(), self.pos_ct())
            }
        }

        num_ct_impl!(@select $signed);
    };
    (@unsigned $unsigned:ty $(,)?) => {
        impl OneCt for $unsigned {
            #[inline(never)]
            fn one_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = ((val ^ 1) | (val ^ 1).wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct!(any)
            }
        }

        impl ZeroCt for $unsigned {
            #[inline(never)]
            fn zero_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                inv_ct!(any)
            }
        }

        impl PosCt for $unsigned {
            #[inline(never)]
            fn pos_ct(&self) -> MaskCt {
                let val = *self as $unsigned;

                let any = (val | val.wrapping_neg()) >> (Self::BITS - 1);
                let any = any as MaskCt;

                dir_ct!(any)
            }
        }

        impl NegCt for $unsigned {
            #[inline(never)]
            fn neg_ct(&self) -> MaskCt {
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

                inv_ct!(any)
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

                dir_ct!(res)
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

                dir_ct!(res)
            }
        }

        num_ct_impl!(@select $unsigned);
    };
    (@select $primitive:ty $(,)?) => {
        impl SelectCt for $primitive {
            #[inline(never)]
            fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
                let lhs_mask = Self::from_ne_bytes([mask; (Self::BYTES) as usize]);
                let rhs_mask = Self::from_ne_bytes([!mask; (Self::BYTES) as usize]);

                lhs & lhs_mask | rhs & rhs_mask
            }
        }
    };
}

macro_rules! sign_from {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
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
    (@unsigned $primitive:ty $(,)?) => {
        impl From<$primitive> for Sign {
            #[inline]
            fn from(value: $primitive) -> Self {
                match value {
                    0 => Sign::ZERO,
                    _ => Sign::POS,
                }
            }
        }
    };
}

/// Number with Strict operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: NumPow!)]
#[ndfwd::def(self.0 with N: NumGcd!)]
#[ndfwd::def(self.0 with N: NumGcdChecked!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumRand!)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Strict<N>(pub N);

/// Number with Wrapping operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: NumPow!)]
#[ndfwd::def(self.0 with N: NumGcd!)]
#[ndfwd::def(self.0 with N: NumGcdChecked!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumRand!)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Wrapping<N>(pub N);

/// Number with Saturating operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: NumPow!)]
#[ndfwd::def(self.0 with N: NumGcd!)]
#[ndfwd::def(self.0 with N: NumGcdChecked!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumRand!)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Saturating<N>(pub N);

/// Number with Unbounded operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: arch::BytesLen)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: NumFn!)]
#[ndfwd::def(self.0 with N: NumPow!)]
#[ndfwd::def(self.0 with N: NumGcd!)]
#[ndfwd::def(self.0 with N: NumGcdChecked!)]
#[ndfwd::def(self.0 with N: Num!)]
#[ndfwd::def(self.0 with N: NumRand!)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Unbounded<N>(pub N);

/// Number within Range.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: Num)]
pub struct Ranged<N: Num, R: Range<N>>(pub N, pub PhantomData<R>);

/// Number with specified binary width.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: arch::BytesFn)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumPow!)]
#[ndfwd::def(self.0 with N: NumGcd!)]
#[ndfwd::def(self.0 with N: NumGcdChecked!)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumRand)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Width<N: Num + NumUnsigned + BytesLen + BytesFn, const BITS: usize>(pub N);

/// Number with specified modulus.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::iter(self.0 with N)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumPow!)]
#[ndfwd::def(self.0 with N: NumGcd!)]
#[ndfwd::def(self.0 with N: NumGcdChecked!)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Modular<N: Num + NumUnsigned, M: Modulus<N>>(pub N, pub PhantomData<M>);

/// Number sign.
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

/// Mask for Const-time operations.
#[cfg(feature = "const-time")]
pub type MaskCt = u8;

/// Relation for Const-time operations.
#[cfg(feature = "const-time")]
pub type RelCt = i8;

/// Numbers functions.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumFn:
    Sized + Default + Clone + PartialEq + Eq + PartialOrd + Ord + NdOps<All = Self> + NdOpsAssign + ZeroFn + OneFn
{
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
    type Signed;

    /// Unsigned counterpart of the same size.
    type Unsigned;

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

/// Numbers with power functions.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumPow: NumFn {
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

            let val = acc.clone();

            Self::nd_mul_assign(&mut acc, &val);
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

            let val = acc.clone();

            Self::nd_mul_assign(&mut acc, &val);
            Self::nd_rem_assign(&mut acc, rem);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }
}

/// Numbers with GCD/GCDE/LCM functions with default semantics.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumGcd: NumFn {
    /// Calculates Greatest Common Divisor of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NumGcdChecked`] for checked semantics.
    #[inline]
    #[ndfwd::as_into]
    fn gcd(mut lhs: Self, mut rhs: Self) -> Self {
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
    /// See [`NumGcdChecked`] for checked semantics.
    #[inline]
    #[ndfwd::as_expr(|(r, x, y)| (Self::from(r), Self::from(x), Self::from(y)))]
    fn gcde(lhs: Self, rhs: Self) -> (Self, Self, Self) {
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
    /// See [`NumGcdChecked`] for checked semantics.
    #[inline]
    #[ndfwd::as_into]
    fn lcm(lhs: Self, rhs: Self) -> Self {
        let val = Self::gcd(lhs.clone(), rhs.clone());
        let val = Self::nd_div(&lhs, &val);

        Self::nd_mul(&val, &rhs)
    }
}

/// Numbers with GCD/GCDE/LCM functions with checked semantics.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumGcdChecked: NumFn + NdOpsChecked<All = Self> {
    /// Calculates Greatest Common Divisor of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[inline]
    #[ndfwd::as_map(Self::from)]
    fn gcd_checked(mut lhs: Self, mut rhs: Self) -> Option<Self> {
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
    fn gcde_checked(lhs: Self, rhs: Self) -> Option<(Self, Self, Self)> {
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
    fn lcm_checked(lhs: Self, rhs: Self) -> Option<Self> {
        let val = Self::gcd_checked(lhs.clone(), rhs.clone())?;
        let val = Self::nd_div_checked(&lhs, &val)?;

        Self::nd_mul_checked(&val, &rhs)
    }
}

/// Numbers with random generation functions.
#[ndfwd::decl]
pub trait NumRand: NumFn + BytesFn {
    /// Creates random number.
    ///
    /// Order represents position of the most significant bit.
    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn rand_num<Rng: rand::Rng>(order: usize, rng: &mut Rng) -> Self {
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

/// Number with static allocation.
#[ndfwd::decl]
pub trait Num: NumFn + Zero + One + Copy {}

/// Number with dynamic allocation.
#[ndfwd::decl]
pub trait NumDyn: NumFn {}

/// Number with sign.
#[ndfwd::decl]
pub trait NumSigned: NumFn + From<i8> {}

/// Number without sign.
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

/// Range for [`Ranged`] numbers.
pub trait Range<N: Num>: Default + Debug + Clone {
    /// Range inclusive minimum.
    const MIN: N;

    /// Range inclusive maximum.
    const MAX: N;
}

/// Modulus for [`Modular`] numbers.
pub trait Modulus<N: Num>: Default + Debug + Clone + Copy {
    /// Modulus for arithmetics.
    const MOD: N;
}

/// Zero with static allocation.
pub trait Zero {
    /// Zero value.
    const ZERO: Self;
}

/// One with static allocation.
pub trait One {
    /// One value.
    const ONE: Self;
}

/// Minimum with static allocation.
pub trait Min {
    /// Minimum value.
    const MIN: Self;
}

/// Maximum with static allocation.
pub trait Max {
    /// Maximum value.
    const MAX: Self;
}

/// Zero with dynamic allocation.
#[ndfwd::decl]
pub trait ZeroFn {
    /// Returns zero value.
    #[ndfwd::as_into]
    fn zero() -> Self;
}

/// One with dynamic allocation.
#[ndfwd::decl]
pub trait OneFn {
    /// Returns one value.
    #[ndfwd::as_into]
    fn one() -> Self;
}

/// Minimum with dynamic allocation.
#[ndfwd::decl]
pub trait MinFn {
    /// Returns minimum value.
    #[ndfwd::as_into]
    fn min() -> Self;
}

/// Maximum with dynamic allocation.
#[ndfwd::decl]
pub trait MaxFn {
    /// Returns maximum value.
    #[ndfwd::as_into]
    fn max() -> Self;
}

/// Const-time equality with one comparison.
#[cfg(feature = "const-time")]
#[ndfwd::decl]
pub trait OneCt {
    /// Const-time equality with one function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `value != 0`.
    /// - `MaskCt::MAX` => `value == 0`.
    fn one_ct(&self) -> MaskCt;
}

/// Const-time equality with zero comparison.
#[cfg(feature = "const-time")]
#[ndfwd::decl]
pub trait ZeroCt {
    /// Const-time equality with zero function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `value != 0`.
    /// - `MaskCt::MAX` => `value == 0`.
    fn zero_ct(&self) -> MaskCt;
}

/// Const-time greater-then-zero comparison.
#[cfg(feature = "const-time")]
#[ndfwd::decl]
pub trait PosCt {
    /// Const-time greater-then-zero function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs > 0`.
    /// - `MaskCt::MAX` => `lhs <= 0`.
    fn pos_ct(&self) -> MaskCt;
}

/// Const-time less-then-zero comparison.
#[cfg(feature = "const-time")]
#[ndfwd::decl]
pub trait NegCt {
    /// Const-time less-then-zero function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs >= 0`.
    /// - `MaskCt::MAX` => `lhs < 0`.
    fn neg_ct(&self) -> MaskCt;
}

/// Const-time equality comparison.
#[cfg(feature = "const-time")]
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

/// Const-time less-then comparison.
#[cfg(feature = "const-time")]
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
#[cfg(feature = "const-time")]
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
/// Auto-implemented for all types with [`GtCt`].
#[cfg(feature = "const-time")]
pub trait LeCt {
    /// Const-time less-or-equal-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs > rhs`.
    /// - `MaskCt::MAX` => `lhs <= rhs`.
    fn le_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time greater-or-equal-then comparison.
///
/// Auto-implemented for all types with [`LtCt`].
#[cfg(feature = "const-time")]
pub trait GeCt {
    /// Const-time greater-or-equal-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs < rhs`.
    /// - `MaskCt::MAX` => `lhs >= rhs`.
    fn ge_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time sign.
///
/// Auto-implemented for all types with [`ZeroCt`], [`PosCt`], [`NegCt`].
#[cfg(feature = "const-time")]
pub trait SignCt {
    /// Const-time sign function.
    ///
    /// # Returns
    ///
    /// - `-1` => `lhs < 0`
    /// - `0` => `lhs == 0`.
    /// - `1` => `lhs > 0`
    fn sign_ct(&self) -> RelCt;
}

/// Const-time comparison.
///
/// Auto-implemented for all types with [`EqCt`], [`LtCt`], [`GtCt`].
#[cfg(feature = "const-time")]
pub trait CmpCt {
    /// Const-time comparison function.
    ///
    /// # Returns
    ///
    /// - `-1` => `lhs < rhs`
    /// - `0` => `lhs == rhs`.
    /// - `1` => `lhs > rhs`
    fn cmp_ct(&self, other: &Self) -> RelCt;
}

/// Const-time minimum value.
///
/// Auto-implemented for all types with [`LtCt`], [`SelectCt`].
#[cfg(feature = "const-time")]
pub trait MinCt: Copy {
    /// Const-time minimum function.
    fn min_ct(&self, other: &Self) -> Self;
}

/// Const-time maximum value.
///
/// Auto-implemented for all types with [`GtCt`], [`SelectCt`].
#[cfg(feature = "const-time")]
pub trait MaxCt: Copy {
    /// Const-time maximum function.
    fn max_ct(&self, other: &Self) -> Self;
}

/// Const-time absolute value.
#[cfg(feature = "const-time")]
pub trait AbsCt: Copy {
    /// Const-time absolute function.
    fn abs_ct(&self) -> Self;
}

/// Const-time select value.
#[cfg(feature = "const-time")]
#[ndfwd::decl]
pub trait SelectCt: Copy {
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

num_impl!(@signed [i8 > u8, i16 > u16, i32 > u32, i64 > u64, i128 > u128, isize > usize]);
num_impl!(@unsigned [u8 > i8, u16 > i16, u32 > i32, u64 > i64, u128 > i128, usize > isize]);

#[cfg(feature = "const-time")]
num_ct_impl!(@signed [i8 > u8, i16 > u16, i32 > u32, i64 > u64, i128 > u128, isize > usize]);

#[cfg(feature = "const-time")]
num_ct_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

impl<N> From<N> for Strict<N> {
    #[inline]
    fn from(value: N) -> Self {
        Self(value)
    }
}

impl<N> From<N> for Wrapping<N> {
    #[inline]
    fn from(value: N) -> Self {
        Self(value)
    }
}

impl<N> From<N> for Saturating<N> {
    #[inline]
    fn from(value: N) -> Self {
        Self(value)
    }
}

impl<N> From<N> for Unbounded<N> {
    #[inline]
    fn from(value: N) -> Self {
        Self(value)
    }
}

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

ndops::def! { @stdbin (lhs: Sign, rhs: Sign) -> Sign, [* (lhs as i8) * (rhs as i8)] }

ndops::fwd! { @ndun <N> (value: &Strict<N>) -> Strict<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - with @strict where        [N: NdNegStrict             <N, Type = N>],
    - @checked where            [N: NdNegChecked            <N, Type = N>],
    - @overflowing where        [N: NdNegOverflowing        <N, Type = N>],
] }

ndops::fwd! { @ndun <N> (value: &Wrapping<N>) -> Wrapping<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - with @wrapping where      [N: NdNegWrapping           <N, Type = N>],
    - @checked where            [N: NdNegChecked            <N, Type = N>],
    - @overflowing where        [N: NdNegOverflowing        <N, Type = N>],
] }

ndops::fwd! { @ndun <N> (value: &Saturating<N>) -> Saturating<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - with @saturating where    [N: NdNegSaturating         <N, Type = N>],
    - @checked where            [N: NdNegChecked            <N, Type = N>],
    - @overflowing where        [N: NdNegOverflowing        <N, Type = N>],
] }

ndops::fwd! { @ndun <N> (value: &Unbounded<N>) -> Unbounded<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - where                     [N: NdNeg                   <N, Type = N>],
    - @checked where            [N: NdNegChecked            <N, Type = N>],
    - @strict where             [N: NdNegStrict             <N, Type = N>],
    - @wrapping where           [N: NdNegWrapping           <N, Type = N>],
    - @saturating where         [N: NdNegSaturating         <N, Type = N>],
    - @overflowing where        [N: NdNegOverflowing        <N, Type = N>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Strict<Lhs>, rhs: &Strict<Rhs>) -> Strict<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + with @strict where        [Lhs: NdAddStrict           <Lhs, Rhs, Type = T>],
    - with @strict where        [Lhs: NdSubStrict           <Lhs, Rhs, Type = T>],
    * with @strict where        [Lhs: NdMulStrict           <Lhs, Rhs, Type = T>],
    / with @strict where        [Lhs: NdDivStrict           <Lhs, Rhs, Type = T>],
    % with @strict where        [Lhs: NdRemStrict           <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
    + @checked where            [Lhs: NdAddChecked          <Lhs, Rhs, Type = T>],
    - @checked where            [Lhs: NdSubChecked          <Lhs, Rhs, Type = T>],
    * @checked where            [Lhs: NdMulChecked          <Lhs, Rhs, Type = T>],
    / @checked where            [Lhs: NdDivChecked          <Lhs, Rhs, Type = T>],
    % @checked where            [Lhs: NdRemChecked          <Lhs, Rhs, Type = T>],
    + @overflowing where        [Lhs: NdAddOverflowing      <Lhs, Rhs, Type = T>],
    - @overflowing where        [Lhs: NdSubOverflowing      <Lhs, Rhs, Type = T>],
    * @overflowing where        [Lhs: NdMulOverflowing      <Lhs, Rhs, Type = T>],
    / @overflowing where        [Lhs: NdDivOverflowing      <Lhs, Rhs, Type = T>],
    % @overflowing where        [Lhs: NdRemOverflowing      <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Strict<Lhs>, rhs: Rhs) -> Strict<T>, (Lhs) (&lhs.0) (rhs) [
    << with @strict where       [Lhs: NdShlStrict           <Lhs, Rhs, Type = T>],
    >> with @strict where       [Lhs: NdShrStrict           <Lhs, Rhs, Type = T>],
    << @checked where           [Lhs: NdShlChecked          <Lhs, Rhs, Type = T>],
    >> @checked where           [Lhs: NdShrChecked          <Lhs, Rhs, Type = T>],
    << @overflowing where       [Lhs: NdShlOverflowing      <Lhs, Rhs, Type = T>],
    >> @overflowing where       [Lhs: NdShrOverflowing      <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Wrapping<Lhs>, rhs: &Wrapping<Rhs>) -> Wrapping<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + with @wrapping where      [Lhs: NdAddWrapping         <Lhs, Rhs, Type = T>],
    - with @wrapping where      [Lhs: NdSubWrapping         <Lhs, Rhs, Type = T>],
    * with @wrapping where      [Lhs: NdMulWrapping         <Lhs, Rhs, Type = T>],
    / with @wrapping where      [Lhs: NdDivWrapping         <Lhs, Rhs, Type = T>],
    % with @wrapping where      [Lhs: NdRemWrapping         <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
    + @checked where            [Lhs: NdAddChecked          <Lhs, Rhs, Type = T>],
    - @checked where            [Lhs: NdSubChecked          <Lhs, Rhs, Type = T>],
    * @checked where            [Lhs: NdMulChecked          <Lhs, Rhs, Type = T>],
    / @checked where            [Lhs: NdDivChecked          <Lhs, Rhs, Type = T>],
    % @checked where            [Lhs: NdRemChecked          <Lhs, Rhs, Type = T>],
    + @overflowing where        [Lhs: NdAddOverflowing      <Lhs, Rhs, Type = T>],
    - @overflowing where        [Lhs: NdSubOverflowing      <Lhs, Rhs, Type = T>],
    * @overflowing where        [Lhs: NdMulOverflowing      <Lhs, Rhs, Type = T>],
    / @overflowing where        [Lhs: NdDivOverflowing      <Lhs, Rhs, Type = T>],
    % @overflowing where        [Lhs: NdRemOverflowing      <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Wrapping<Lhs>, rhs: Rhs) -> Wrapping<T>, (Lhs) (&lhs.0) (rhs) [
    << where                    [Lhs: NdShl                 <Lhs, Rhs, Type = T>],
    >> where                    [Lhs: NdShr                 <Lhs, Rhs, Type = T>],
    << @checked where           [Lhs: NdShlChecked          <Lhs, Rhs, Type = T>],
    >> @checked where           [Lhs: NdShrChecked          <Lhs, Rhs, Type = T>],
    << @overflowing where       [Lhs: NdShlOverflowing      <Lhs, Rhs, Type = T>],
    >> @overflowing where       [Lhs: NdShrOverflowing      <Lhs, Rhs, Type = T>],
    << @unbounded where         [Lhs: NdShlUnbounded        <Lhs, Rhs, Type = T>],
    >> @unbounded where         [Lhs: NdShrUnbounded        <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Saturating<Lhs>, rhs: &Saturating<Rhs>) -> Saturating<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + with @saturating where    [Lhs: NdAddSaturating       <Lhs, Rhs, Type = T>],
    - with @saturating where    [Lhs: NdSubSaturating       <Lhs, Rhs, Type = T>],
    * with @saturating where    [Lhs: NdMulSaturating       <Lhs, Rhs, Type = T>],
    / with @saturating where    [Lhs: NdDivSaturating       <Lhs, Rhs, Type = T>],
    % with @saturating where    [Lhs: NdRemSaturating       <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
    + @checked where            [Lhs: NdAddChecked          <Lhs, Rhs, Type = T>],
    - @checked where            [Lhs: NdSubChecked          <Lhs, Rhs, Type = T>],
    * @checked where            [Lhs: NdMulChecked          <Lhs, Rhs, Type = T>],
    / @checked where            [Lhs: NdDivChecked          <Lhs, Rhs, Type = T>],
    % @checked where            [Lhs: NdRemChecked          <Lhs, Rhs, Type = T>],
    + @overflowing where        [Lhs: NdAddOverflowing      <Lhs, Rhs, Type = T>],
    - @overflowing where        [Lhs: NdSubOverflowing      <Lhs, Rhs, Type = T>],
    * @overflowing where        [Lhs: NdMulOverflowing      <Lhs, Rhs, Type = T>],
    / @overflowing where        [Lhs: NdDivOverflowing      <Lhs, Rhs, Type = T>],
    % @overflowing where        [Lhs: NdRemOverflowing      <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Saturating<Lhs>, rhs: Rhs) -> Saturating<T>, (Lhs) (&lhs.0) (rhs) [
    << where                    [Lhs: NdShl                 <Lhs, Rhs, Type = T>],
    >> where                    [Lhs: NdShr                 <Lhs, Rhs, Type = T>],
    << @checked where           [Lhs: NdShlChecked          <Lhs, Rhs, Type = T>],
    >> @checked where           [Lhs: NdShrChecked          <Lhs, Rhs, Type = T>],
    << @overflowing where       [Lhs: NdShlOverflowing      <Lhs, Rhs, Type = T>],
    >> @overflowing where       [Lhs: NdShrOverflowing      <Lhs, Rhs, Type = T>],
    << @unbounded where         [Lhs: NdShlUnbounded        <Lhs, Rhs, Type = T>],
    >> @unbounded where         [Lhs: NdShrUnbounded        <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Unbounded<Lhs>, rhs: &Unbounded<Rhs>) -> Unbounded<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + where                     [Lhs: NdAdd                 <Lhs, Rhs, Type = T>],
    - where                     [Lhs: NdSub                 <Lhs, Rhs, Type = T>],
    * where                     [Lhs: NdMul                 <Lhs, Rhs, Type = T>],
    / where                     [Lhs: NdDiv                 <Lhs, Rhs, Type = T>],
    % where                     [Lhs: NdRem                 <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
    + @checked where            [Lhs: NdAddChecked          <Lhs, Rhs, Type = T>],
    - @checked where            [Lhs: NdSubChecked          <Lhs, Rhs, Type = T>],
    * @checked where            [Lhs: NdMulChecked          <Lhs, Rhs, Type = T>],
    / @checked where            [Lhs: NdDivChecked          <Lhs, Rhs, Type = T>],
    % @checked where            [Lhs: NdRemChecked          <Lhs, Rhs, Type = T>],
    + @strict where             [Lhs: NdAddStrict           <Lhs, Rhs, Type = T>],
    - @strict where             [Lhs: NdSubStrict           <Lhs, Rhs, Type = T>],
    * @strict where             [Lhs: NdMulStrict           <Lhs, Rhs, Type = T>],
    / @strict where             [Lhs: NdDivStrict           <Lhs, Rhs, Type = T>],
    % @strict where             [Lhs: NdRemStrict           <Lhs, Rhs, Type = T>],
    + @wrapping where           [Lhs: NdAddWrapping         <Lhs, Rhs, Type = T>],
    - @wrapping where           [Lhs: NdSubWrapping         <Lhs, Rhs, Type = T>],
    * @wrapping where           [Lhs: NdMulWrapping         <Lhs, Rhs, Type = T>],
    / @wrapping where           [Lhs: NdDivWrapping         <Lhs, Rhs, Type = T>],
    % @wrapping where           [Lhs: NdRemWrapping         <Lhs, Rhs, Type = T>],
    + @saturating where         [Lhs: NdAddSaturating       <Lhs, Rhs, Type = T>],
    - @saturating where         [Lhs: NdSubSaturating       <Lhs, Rhs, Type = T>],
    * @saturating where         [Lhs: NdMulSaturating       <Lhs, Rhs, Type = T>],
    / @saturating where         [Lhs: NdDivSaturating       <Lhs, Rhs, Type = T>],
    % @saturating where         [Lhs: NdRemSaturating       <Lhs, Rhs, Type = T>],
    + @overflowing where        [Lhs: NdAddOverflowing      <Lhs, Rhs, Type = T>],
    - @overflowing where        [Lhs: NdSubOverflowing      <Lhs, Rhs, Type = T>],
    * @overflowing where        [Lhs: NdMulOverflowing      <Lhs, Rhs, Type = T>],
    / @overflowing where        [Lhs: NdDivOverflowing      <Lhs, Rhs, Type = T>],
    % @overflowing where        [Lhs: NdRemOverflowing      <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Unbounded<Lhs>, rhs: Rhs) -> Unbounded<T>, (Lhs) (&lhs.0) (rhs) [
    << with @unbounded where    [Lhs: NdShlUnbounded        <Lhs, Rhs, Type = T>],
    >> with @unbounded where    [Lhs: NdShrUnbounded        <Lhs, Rhs, Type = T>],
    << @checked where           [Lhs: NdShlChecked          <Lhs, Rhs, Type = T>],
    >> @checked where           [Lhs: NdShrChecked          <Lhs, Rhs, Type = T>],
    << @overflowing where       [Lhs: NdShlOverflowing      <Lhs, Rhs, Type = T>],
    >> @overflowing where       [Lhs: NdShrOverflowing      <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Strict<Lhs>, rhs: &Strict<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += with @strict where       [Lhs: NdAddAssignStrict     <Lhs, Rhs>],
    -= with @strict where       [Lhs: NdSubAssignStrict     <Lhs, Rhs>],
    *= with @strict where       [Lhs: NdMulAssignStrict     <Lhs, Rhs>],
    /= with @strict where       [Lhs: NdDivAssignStrict     <Lhs, Rhs>],
    %= with @strict where       [Lhs: NdRemAssignStrict     <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Strict<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= with @strict where      [Lhs: NdShlAssignStrict     <Lhs, Rhs>],
    >>= with @strict where      [Lhs: NdShrAssignStrict     <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Wrapping<Lhs>, rhs: &Wrapping<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += with @wrapping where     [Lhs: NdAddAssignWrapping   <Lhs, Rhs>],
    -= with @wrapping where     [Lhs: NdSubAssignWrapping   <Lhs, Rhs>],
    *= with @wrapping where     [Lhs: NdMulAssignWrapping   <Lhs, Rhs>],
    /= with @wrapping where     [Lhs: NdDivAssignWrapping   <Lhs, Rhs>],
    %= with @wrapping where     [Lhs: NdRemAssignWrapping   <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Wrapping<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where                   [Lhs: NdShlAssign           <Lhs, Rhs>],
    >>= where                   [Lhs: NdShrAssign           <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Saturating<Lhs>, rhs: &Saturating<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += with @saturating where   [Lhs: NdAddAssignSaturating <Lhs, Rhs>],
    -= with @saturating where   [Lhs: NdSubAssignSaturating <Lhs, Rhs>],
    *= with @saturating where   [Lhs: NdMulAssignSaturating <Lhs, Rhs>],
    /= with @saturating where   [Lhs: NdDivAssignSaturating <Lhs, Rhs>],
    %= with @saturating where   [Lhs: NdRemAssignSaturating <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Saturating<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where                   [Lhs: NdShlAssign           <Lhs, Rhs>],
    >>= where                   [Lhs: NdShrAssign           <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Unbounded<Lhs>, rhs: &Unbounded<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where                    [Lhs: NdAddAssign           <Lhs, Rhs>],
    -= where                    [Lhs: NdSubAssign           <Lhs, Rhs>],
    *= where                    [Lhs: NdMulAssign           <Lhs, Rhs>],
    /= where                    [Lhs: NdDivAssign           <Lhs, Rhs>],
    %= where                    [Lhs: NdRemAssign           <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
    += @strict where            [Lhs: NdAddAssignStrict     <Lhs, Rhs>],
    -= @strict where            [Lhs: NdSubAssignStrict     <Lhs, Rhs>],
    *= @strict where            [Lhs: NdMulAssignStrict     <Lhs, Rhs>],
    /= @strict where            [Lhs: NdDivAssignStrict     <Lhs, Rhs>],
    %= @strict where            [Lhs: NdRemAssignStrict     <Lhs, Rhs>],
    += @wrapping where          [Lhs: NdAddAssignWrapping   <Lhs, Rhs>],
    -= @wrapping where          [Lhs: NdSubAssignWrapping   <Lhs, Rhs>],
    *= @wrapping where          [Lhs: NdMulAssignWrapping   <Lhs, Rhs>],
    /= @wrapping where          [Lhs: NdDivAssignWrapping   <Lhs, Rhs>],
    %= @wrapping where          [Lhs: NdRemAssignWrapping   <Lhs, Rhs>],
    += @saturating where        [Lhs: NdAddAssignSaturating <Lhs, Rhs>],
    -= @saturating where        [Lhs: NdSubAssignSaturating <Lhs, Rhs>],
    *= @saturating where        [Lhs: NdMulAssignSaturating <Lhs, Rhs>],
    /= @saturating where        [Lhs: NdDivAssignSaturating <Lhs, Rhs>],
    %= @saturating where        [Lhs: NdRemAssignSaturating <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Unbounded<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= with @unbounded where   [Lhs: NdShlAssignUnbounded  <Lhs, Rhs>],
    >>= with @unbounded where   [Lhs: NdShrAssignUnbounded  <Lhs, Rhs>],
] }

ndops::fwd! { @stdun <N> (*value: &Strict<N>) -> Strict<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - with @strict where        [N: NdNegStrict             <N, Type = N>],
] }

ndops::fwd! { @stdun <N> (*value: &Wrapping<N>) -> Wrapping<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - with @wrapping where      [N: NdNegWrapping           <N, Type = N>],
] }

ndops::fwd! { @stdun <N> (*value: &Saturating<N>) -> Saturating<N>, (N) (&value.0) [
    ! where                     [N: NdNot                   <N, Type = N>],
    - with @saturating where    [N: NdNegSaturating         <N, Type = N>],
] }

ndops::fwd! { @stdun <N> (*value: &Unbounded<N>) -> Unbounded<N>, (N) (&value.0) [
    - where                     [N: NdNeg                   <N, Type = N>],
    ! where                     [N: NdNot                   <N, Type = N>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Strict<Lhs>, *rhs: &Strict<Rhs>) -> Strict<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + with @strict where        [Lhs: NdAddStrict           <Lhs, Rhs, Type = T>],
    - with @strict where        [Lhs: NdSubStrict           <Lhs, Rhs, Type = T>],
    * with @strict where        [Lhs: NdMulStrict           <Lhs, Rhs, Type = T>],
    / with @strict where        [Lhs: NdDivStrict           <Lhs, Rhs, Type = T>],
    % with @strict where        [Lhs: NdRemStrict           <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Strict<Lhs>, rhs: Rhs) -> Strict<T>, (Lhs) (&lhs.0) (rhs) [
    << with @strict where       [Lhs: NdShlStrict           <Lhs, Rhs, Type = T>],
    >> with @strict where       [Lhs: NdShrStrict           <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Wrapping<Lhs>, *rhs: &Wrapping<Rhs>) -> Wrapping<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + with @wrapping where      [Lhs: NdAddWrapping         <Lhs, Rhs, Type = T>],
    - with @wrapping where      [Lhs: NdSubWrapping         <Lhs, Rhs, Type = T>],
    * with @wrapping where      [Lhs: NdMulWrapping         <Lhs, Rhs, Type = T>],
    / with @wrapping where      [Lhs: NdDivWrapping         <Lhs, Rhs, Type = T>],
    % with @wrapping where      [Lhs: NdRemWrapping         <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Wrapping<Lhs>, rhs: Rhs) -> Wrapping<T>, (Lhs) (&lhs.0) (rhs) [
    << where                    [Lhs: NdShl                 <Lhs, Rhs, Type = T>],
    >> where                    [Lhs: NdShr                 <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Saturating<Lhs>, *rhs: &Saturating<Rhs>) -> Saturating<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + with @saturating where    [Lhs: NdAddSaturating       <Lhs, Rhs, Type = T>],
    - with @saturating where    [Lhs: NdSubSaturating       <Lhs, Rhs, Type = T>],
    * with @saturating where    [Lhs: NdMulSaturating       <Lhs, Rhs, Type = T>],
    / with @saturating where    [Lhs: NdDivSaturating       <Lhs, Rhs, Type = T>],
    % with @saturating where    [Lhs: NdRemSaturating       <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Saturating<Lhs>, rhs: Rhs) -> Saturating<T>, (Lhs) (&lhs.0) (rhs) [
    << where                    [Lhs: NdShl                 <Lhs, Rhs, Type = T>],
    >> where                    [Lhs: NdShr                 <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Unbounded<Lhs>, *rhs: &Unbounded<Rhs>) -> Unbounded<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + where                     [Lhs: NdAdd                 <Lhs, Rhs, Type = T>],
    - where                     [Lhs: NdSub                 <Lhs, Rhs, Type = T>],
    * where                     [Lhs: NdMul                 <Lhs, Rhs, Type = T>],
    / where                     [Lhs: NdDiv                 <Lhs, Rhs, Type = T>],
    % where                     [Lhs: NdRem                 <Lhs, Rhs, Type = T>],
    | where                     [Lhs: NdBitOr               <Lhs, Rhs, Type = T>],
    & where                     [Lhs: NdBitAnd              <Lhs, Rhs, Type = T>],
    ^ where                     [Lhs: NdBitXor              <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Unbounded<Lhs>, rhs: Rhs) -> Unbounded<T>, (Lhs) (&lhs.0) (rhs) [
    << with @unbounded where    [Lhs: NdShlUnbounded        <Lhs, Rhs, Type = T>],
    >> with @unbounded where    [Lhs: NdShrUnbounded        <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Strict<Lhs>, *rhs: &Strict<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += with @strict where       [Lhs: NdAddAssignStrict     <Lhs, Rhs>],
    -= with @strict where       [Lhs: NdSubAssignStrict     <Lhs, Rhs>],
    *= with @strict where       [Lhs: NdMulAssignStrict     <Lhs, Rhs>],
    /= with @strict where       [Lhs: NdDivAssignStrict     <Lhs, Rhs>],
    %= with @strict where       [Lhs: NdRemAssignStrict     <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Strict<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= with @strict where      [Lhs: NdShlAssignStrict     <Lhs, Rhs>],
    >>= with @strict where      [Lhs: NdShrAssignStrict     <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Wrapping<Lhs>, *rhs: &Wrapping<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += with @wrapping where     [Lhs: NdAddAssignWrapping   <Lhs, Rhs>],
    -= with @wrapping where     [Lhs: NdSubAssignWrapping   <Lhs, Rhs>],
    *= with @wrapping where     [Lhs: NdMulAssignWrapping   <Lhs, Rhs>],
    /= with @wrapping where     [Lhs: NdDivAssignWrapping   <Lhs, Rhs>],
    %= with @wrapping where     [Lhs: NdRemAssignWrapping   <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Wrapping<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where                   [Lhs: NdShlAssign           <Lhs, Rhs>],
    >>= where                   [Lhs: NdShrAssign           <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Saturating<Lhs>, *rhs: &Saturating<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += with @saturating where   [Lhs: NdAddAssignSaturating <Lhs, Rhs>],
    -= with @saturating where   [Lhs: NdSubAssignSaturating <Lhs, Rhs>],
    *= with @saturating where   [Lhs: NdMulAssignSaturating <Lhs, Rhs>],
    /= with @saturating where   [Lhs: NdDivAssignSaturating <Lhs, Rhs>],
    %= with @saturating where   [Lhs: NdRemAssignSaturating <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Saturating<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where                   [Lhs: NdShlAssign           <Lhs, Rhs>],
    >>= where                   [Lhs: NdShrAssign           <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Unbounded<Lhs>, *rhs: &Unbounded<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where                    [Lhs: NdAddAssign           <Lhs, Rhs>],
    -= where                    [Lhs: NdSubAssign           <Lhs, Rhs>],
    *= where                    [Lhs: NdMulAssign           <Lhs, Rhs>],
    /= where                    [Lhs: NdDivAssign           <Lhs, Rhs>],
    %= where                    [Lhs: NdRemAssign           <Lhs, Rhs>],
    |= where                    [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                    [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                    [Lhs: NdBitXorAssign        <Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Unbounded<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= with @unbounded where   [Lhs: NdShlAssignUnbounded  <Lhs, Rhs>],
    >>= with @unbounded where   [Lhs: NdShrAssignUnbounded  <Lhs, Rhs>],
] }

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

#[cfg(feature = "const-time")]
impl<Any: GtCt> LeCt for Any {
    #[inline(never)]
    fn le_ct(&self, other: &Self) -> MaskCt {
        !self.gt_ct(other)
    }
}

#[cfg(feature = "const-time")]
impl<Any: LtCt> GeCt for Any {
    #[inline(never)]
    fn ge_ct(&self, other: &Self) -> MaskCt {
        !self.lt_ct(other)
    }
}

#[cfg(feature = "const-time")]
impl<Any: ZeroCt + PosCt + NegCt> SignCt for Any {
    #[inline(never)]
    fn sign_ct(&self) -> RelCt {
        let pos = self.pos_ct() as RelCt;
        let neg = self.neg_ct() as RelCt;

        pos & 1 | neg
    }
}

#[cfg(feature = "const-time")]
impl<Any: EqCt + LtCt + GtCt> CmpCt for Any {
    #[inline(never)]
    fn cmp_ct(&self, other: &Self) -> RelCt {
        let lt = self.lt_ct(other) as RelCt;
        let gt = self.gt_ct(other) as RelCt;

        lt | gt & 1
    }
}

#[cfg(feature = "const-time")]
impl<Any: LtCt + SelectCt> MinCt for Any {
    #[inline]
    fn min_ct(&self, other: &Self) -> Self {
        SelectCt::select_ct(self, other, self.lt_ct(other))
    }
}

#[cfg(feature = "const-time")]
impl<Any: GtCt + SelectCt> MaxCt for Any {
    #[inline]
    fn max_ct(&self, other: &Self) -> Self {
        SelectCt::select_ct(self, other, self.gt_ct(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 48).map(|val| val + 1)) [
            (u64::gcd(val, 0), val),
            (u64::gcd(0, val), val),
            (u64::gcd(val, 1), 1),
            (u64::gcd(1, val), 1),
            (u64::gcd(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            (u64::gcd(lhs, rhs), u64::gcd(rhs, lhs)),
            (lhs % u64::gcd(lhs, rhs), 0),
            (rhs % u64::gcd(lhs, rhs), 0),
            (u64::gcd(lhs, rhs) * u64::lcm(lhs, rhs), lhs * rhs),
            {
                let res = u64::gcd(lhs, rhs);

                (u64::gcd(lhs / res, rhs / res), 1)
            },
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 6,
            rhs in 1..=1 << 6,
              k in 1..=1 << 6,
        ) [
            (u64::gcd(k * lhs, k * rhs), k * u64::gcd(lhs, rhs)),
        ] }
    }

    #[test]
    fn gcde() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 48).map(|val| val + 1)) [
            (i64::gcde(val, 0), (val, 1, 0)),
            (i64::gcde(0, val), (val, 0, 1)),
            (i64::gcde(val, 1), (1, 0, 1)),
            (i64::gcde(1, val), (1, 1, 0)),
            (i64::gcde(val, val), (val, 0, 1)),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            (i64::gcde(lhs, rhs).0, i64::gcde(rhs, lhs).0),
            (lhs % i64::gcde(lhs, rhs).0, 0),
            (rhs % i64::gcde(lhs, rhs).0, 0),
            (i64::gcde(lhs, rhs).0 * i64::lcm(lhs, rhs), lhs * rhs),
            {
                let res = i64::gcde(lhs, rhs).0;

                (i64::gcde(lhs / res, rhs / res).0, 1)
            },
            {
                let res = i64::gcde(lhs, rhs);

                (lhs * res.1 + rhs * res.2, res.0)
            }
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 6,
            rhs in 1..=1 << 6,
              k in 1..=1 << 6,
        ) [
            (i64::gcde(k * lhs, k * rhs).0, k * i64::gcde(lhs, rhs).0),
        ] }
    }

    #[test]
    fn lcm() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 48).map(|val| val + 1)) [
            (u64::lcm(val, 0), 0),
            (u64::lcm(0, val), 0),
            (u64::lcm(val, 1), val),
            (u64::lcm(1, val), val),
            (u64::lcm(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            (u64::lcm(lhs, rhs), u64::lcm(rhs, lhs)),
            (u64::lcm(lhs, rhs) % lhs, 0),
            (u64::lcm(lhs, rhs) % rhs, 0),
            (u64::lcm(lhs, rhs) * u64::gcd(lhs, rhs), lhs * rhs),
            {
                let res = u64::lcm(lhs, rhs);

                (u64::gcd(res / lhs, res / rhs), 1)
            },
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 6,
            rhs in 1..=1 << 6,
              k in 1..=1 << 6,
        ) [
            (u64::lcm(k * lhs, k * rhs), k * u64::lcm(lhs, rhs)),
        ] }
    }

    #[test]
    fn pow() {
        const EXP: u64 = ndassert::prime!(8);

        for value in ndassert::range!(u32, 24).map(|x| x as u64) {
            let mut acc = Wrapping(1u64);

            for exp in 0..EXP {
                assert_eq!(acc, Wrapping(value).nd_pow(Wrapping(exp)));

                acc *= Wrapping(value);
            }
        }
    }

    #[test]
    fn powrem() {
        const EXP: u64 = ndassert::prime!(8);
        const MOD: u64 = ndassert::prime!(32);

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
    fn strict() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ndassert::catch!(Strict(lhs) + Strict(rhs), Strict(lhs.strict_add(rhs))),
            ndassert::catch!(Strict(lhs) - Strict(rhs), Strict(lhs.strict_sub(rhs))),
            ndassert::catch!(Strict(lhs) * Strict(rhs), Strict(lhs.strict_mul(rhs))),
            ndassert::catch!(Strict(lhs) / Strict(rhs), Strict(lhs.strict_div(rhs))),
            ndassert::catch!(Strict(lhs) % Strict(rhs), Strict(lhs.strict_rem(rhs))),

            (Strict(lhs) | Strict(rhs), Strict(lhs | rhs)),
            (Strict(lhs) & Strict(rhs), Strict(lhs & rhs)),
            (Strict(lhs) ^ Strict(rhs), Strict(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ndassert::catch!(Strict(lhs) << rhs, Strict(lhs.strict_shl(rhs as u32))),
            ndassert::catch!(Strict(lhs) >> rhs, Strict(lhs.strict_shr(rhs as u32))),
        ] }
    }

    #[test]
    fn strict_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ndassert::catch!({ let mut val = Strict(lhs); val += Strict(rhs); val }, Strict(lhs.strict_add(rhs))),
            ndassert::catch!({ let mut val = Strict(lhs); val -= Strict(rhs); val }, Strict(lhs.strict_sub(rhs))),
            ndassert::catch!({ let mut val = Strict(lhs); val *= Strict(rhs); val }, Strict(lhs.strict_mul(rhs))),
            ndassert::catch!({ let mut val = Strict(lhs); val /= Strict(rhs); val }, Strict(lhs.strict_div(rhs))),
            ndassert::catch!({ let mut val = Strict(lhs); val %= Strict(rhs); val }, Strict(lhs.strict_rem(rhs))),

            ({ let mut val = Strict(lhs); val |= Strict(rhs); val }, Strict(lhs | rhs)),
            ({ let mut val = Strict(lhs); val &= Strict(rhs); val }, Strict(lhs & rhs)),
            ({ let mut val = Strict(lhs); val ^= Strict(rhs); val }, Strict(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ndassert::catch!({ let mut val = Strict(lhs); val <<= rhs; val }, Strict(lhs.strict_shl(rhs as u32))),
            ndassert::catch!({ let mut val = Strict(lhs); val >>= rhs; val }, Strict(lhs.strict_shr(rhs as u32))),
        ] }
    }

    #[test]
    fn wrapping() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (Wrapping(lhs) + Wrapping(rhs), Wrapping(lhs.wrapping_add(rhs))),
            (Wrapping(lhs) - Wrapping(rhs), Wrapping(lhs.wrapping_sub(rhs))),
            (Wrapping(lhs) * Wrapping(rhs), Wrapping(lhs.wrapping_mul(rhs))),
            (Wrapping(lhs) / Wrapping(rhs), Wrapping(lhs.wrapping_div(rhs))),
            (Wrapping(lhs) % Wrapping(rhs), Wrapping(lhs.wrapping_rem(rhs))),
            (Wrapping(lhs) | Wrapping(rhs), Wrapping(lhs | rhs)),
            (Wrapping(lhs) & Wrapping(rhs), Wrapping(lhs & rhs)),
            (Wrapping(lhs) ^ Wrapping(rhs), Wrapping(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ndassert::catch!(Wrapping(lhs) << rhs, Wrapping(lhs << rhs)),
            ndassert::catch!(Wrapping(lhs) >> rhs, Wrapping(lhs >> rhs)),
        ] }
    }

    #[test]
    fn wrapping_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ({ let mut val = Wrapping(lhs); val += Wrapping(rhs); val }, Wrapping(lhs.wrapping_add(rhs))),
            ({ let mut val = Wrapping(lhs); val -= Wrapping(rhs); val }, Wrapping(lhs.wrapping_sub(rhs))),
            ({ let mut val = Wrapping(lhs); val *= Wrapping(rhs); val }, Wrapping(lhs.wrapping_mul(rhs))),
            ({ let mut val = Wrapping(lhs); val /= Wrapping(rhs); val }, Wrapping(lhs.wrapping_div(rhs))),
            ({ let mut val = Wrapping(lhs); val %= Wrapping(rhs); val }, Wrapping(lhs.wrapping_rem(rhs))),
            ({ let mut val = Wrapping(lhs); val |= Wrapping(rhs); val }, Wrapping(lhs | rhs)),
            ({ let mut val = Wrapping(lhs); val &= Wrapping(rhs); val }, Wrapping(lhs & rhs)),
            ({ let mut val = Wrapping(lhs); val ^= Wrapping(rhs); val }, Wrapping(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ndassert::catch!({ let mut val = Wrapping(lhs); val <<= rhs; val }, Wrapping(lhs << rhs)),
            ndassert::catch!({ let mut val = Wrapping(lhs); val >>= rhs; val }, Wrapping(lhs >> rhs)),
        ] }
    }

    #[test]
    fn saturating() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (Saturating(lhs) + Saturating(rhs), Saturating(lhs.saturating_add(rhs))),
            (Saturating(lhs) - Saturating(rhs), Saturating(lhs.saturating_sub(rhs))),
            (Saturating(lhs) * Saturating(rhs), Saturating(lhs.saturating_mul(rhs))),
            (Saturating(lhs) / Saturating(rhs), Saturating(lhs.saturating_div(rhs))),
            (Saturating(lhs) % Saturating(rhs), Saturating(lhs.wrapping_rem(rhs))),
            (Saturating(lhs) | Saturating(rhs), Saturating(lhs | rhs)),
            (Saturating(lhs) & Saturating(rhs), Saturating(lhs & rhs)),
            (Saturating(lhs) ^ Saturating(rhs), Saturating(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ndassert::catch!(Saturating(lhs) << rhs, Saturating(lhs << rhs)),
            ndassert::catch!(Saturating(lhs) >> rhs, Saturating(lhs >> rhs)),
        ] }
    }

    #[test]
    fn saturating_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ({ let mut val = Saturating(lhs); val += Saturating(rhs); val }, Saturating(lhs.saturating_add(rhs))),
            ({ let mut val = Saturating(lhs); val -= Saturating(rhs); val }, Saturating(lhs.saturating_sub(rhs))),
            ({ let mut val = Saturating(lhs); val *= Saturating(rhs); val }, Saturating(lhs.saturating_mul(rhs))),
            ({ let mut val = Saturating(lhs); val /= Saturating(rhs); val }, Saturating(lhs.saturating_div(rhs))),
            ({ let mut val = Saturating(lhs); val %= Saturating(rhs); val }, Saturating(lhs.wrapping_rem(rhs))),
            ({ let mut val = Saturating(lhs); val |= Saturating(rhs); val }, Saturating(lhs | rhs)),
            ({ let mut val = Saturating(lhs); val &= Saturating(rhs); val }, Saturating(lhs & rhs)),
            ({ let mut val = Saturating(lhs); val ^= Saturating(rhs); val }, Saturating(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ndassert::catch!({ let mut val = Saturating(lhs); val <<= rhs; val }, Saturating(lhs << rhs)),
            ndassert::catch!({ let mut val = Saturating(lhs); val >>= rhs; val }, Saturating(lhs >> rhs)),
        ] }
    }

    #[test]
    fn unbounded() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ndassert::catch!(Unbounded(lhs) + Unbounded(rhs), Unbounded(lhs + rhs)),
            ndassert::catch!(Unbounded(lhs) - Unbounded(rhs), Unbounded(lhs - rhs)),
            ndassert::catch!(Unbounded(lhs) * Unbounded(rhs), Unbounded(lhs * rhs)),
            ndassert::catch!(Unbounded(lhs) / Unbounded(rhs), Unbounded(lhs / rhs)),
            ndassert::catch!(Unbounded(lhs) % Unbounded(rhs), Unbounded(lhs % rhs)),

            (Unbounded(lhs) | Unbounded(rhs), Unbounded(lhs | rhs)),
            (Unbounded(lhs) & Unbounded(rhs), Unbounded(lhs & rhs)),
            (Unbounded(lhs) ^ Unbounded(rhs), Unbounded(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            (Unbounded(lhs) << rhs, Unbounded(lhs.unbounded_shl(rhs as u32))),
            (Unbounded(lhs) >> rhs, Unbounded(lhs.unbounded_shr(rhs as u32))),
        ] }
    }

    #[test]
    fn unbounded_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ndassert::catch!({ let mut val = Unbounded(lhs); val += Unbounded(rhs); val }, Unbounded(lhs + rhs)),
            ndassert::catch!({ let mut val = Unbounded(lhs); val -= Unbounded(rhs); val }, Unbounded(lhs - rhs)),
            ndassert::catch!({ let mut val = Unbounded(lhs); val *= Unbounded(rhs); val }, Unbounded(lhs * rhs)),
            ndassert::catch!({ let mut val = Unbounded(lhs); val /= Unbounded(rhs); val }, Unbounded(lhs / rhs)),
            ndassert::catch!({ let mut val = Unbounded(lhs); val %= Unbounded(rhs); val }, Unbounded(lhs % rhs)),

            ({ let mut val = Unbounded(lhs); val |= Unbounded(rhs); val }, Unbounded(lhs | rhs)),
            ({ let mut val = Unbounded(lhs); val &= Unbounded(rhs); val }, Unbounded(lhs & rhs)),
            ({ let mut val = Unbounded(lhs); val ^= Unbounded(rhs); val }, Unbounded(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ({ let mut val = Unbounded(lhs); val <<= rhs; val }, Unbounded(lhs.unbounded_shl(rhs as u32))),
            ({ let mut val = Unbounded(lhs); val >>= rhs; val }, Unbounded(lhs.unbounded_shr(rhs as u32))),
        ] }
    }

    #[test]
    fn ranged() {}

    #[test]
    fn width() {}

    #[test]
    fn modular() {}

    #[cfg(feature = "const-time")]
    #[test]
    fn cmp_ct() {
        #![allow(clippy::absurd_extreme_comparisons)]
        #![allow(unused_comparisons)]

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(i64, 56, 1).chain([0, 1]),
        ) [
            (lhs.one_ct(), MaskCt::MAX * (lhs == 1) as MaskCt),
            (lhs.zero_ct(), MaskCt::MAX * (lhs == 0) as MaskCt),
            (lhs.pos_ct(), MaskCt::MAX * (lhs > 0) as MaskCt),
            (lhs.neg_ct(), MaskCt::MAX * (lhs < 0) as MaskCt),
            (lhs.eq_ct(&rhs), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs.lt_ct(&rhs), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs.gt_ct(&rhs), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs.le_ct(&rhs), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs.ge_ct(&rhs), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs.sign_ct(), lhs.cmp(&0) as RelCt),
            (lhs.cmp_ct(&rhs), lhs.cmp(&rhs) as RelCt),
            (lhs.min_ct(&rhs), lhs.min(rhs)),
            (lhs.max_ct(&rhs), lhs.max(rhs)),
            (lhs.abs_ct(), lhs.abs()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(u64, 56, 1).chain([0, 1]),
        ) [
            (lhs.one_ct(), MaskCt::MAX * (lhs == 1) as MaskCt),
            (lhs.zero_ct(), MaskCt::MAX * (lhs == 0) as MaskCt),
            (lhs.pos_ct(), MaskCt::MAX * (lhs > 0) as MaskCt),
            (lhs.neg_ct(), MaskCt::MAX * (lhs < 0) as MaskCt),
            (lhs.eq_ct(&rhs), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs.lt_ct(&rhs), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs.gt_ct(&rhs), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs.le_ct(&rhs), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs.ge_ct(&rhs), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs.sign_ct(), lhs.cmp(&0) as RelCt),
            (lhs.cmp_ct(&rhs), lhs.cmp(&rhs) as RelCt),
            (lhs.min_ct(&rhs), lhs.min(rhs)),
            (lhs.max_ct(&rhs), lhs.max(rhs)),
        ] }
    }
}

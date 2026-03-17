#![doc = include_str!("../docs/arch.md")]

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};

use ndext::ops::*;
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::*;

macro_rules! word_def {
    (($single:ty, $double:ty), { $($tokens:tt)* } $(,)?) => {
        pub type Single = $single;
        pub type Double = $double;

        $($tokens)*
    };
}

macro_rules! word_impl {
    ([$($primitive:ty),+ $(,)?]) => {
        $(word_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
#[rustfmt::skip]
        impl Word for $primitive {
            const BITS: usize = Self::BITS as usize;
            const BYTES: usize = Self::BITS as usize / 8;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            fn from_usize(value: usize) -> Self {
                value as Self
            }

            fn from_single(value: Single) -> Self {
                value as Self
            }

            fn from_double(value: Double) -> Self {
                value as Self
            }

            fn as_usize(self) -> usize {
                self as usize
            }

            fn as_single(self) -> Single {
                self as Single
            }

            fn as_double(self) -> Double {
                self as Double
            }

            fn order(self) -> usize {
                self.ilog2() as usize
            }

            fn is_pow2(self) -> bool {
                (self & (self - 1) == 0) && self != 0
            }
        }
    };
}

pub mod word {
    use super::*;

    #[cfg(all(target_pointer_width = "64", not(test)))]
    word_def!((u64, u128), {
        pub(crate) const DEC_RADIX: Double = 10_000_000_000_000_000_000;
        pub(crate) const DEC_WIDTH: u8 = 19;

        pub(crate) const OCT_RADIX: Double = 1 << 63;
        pub(crate) const OCT_WIDTH: u8 = 21;

        word_impl!([u8, u16, u32, u64, usize]);
    });

    #[cfg(all(target_pointer_width = "32", not(test)))]
    word_def!((u32, u64), {
        pub(crate) const DEC_RADIX: Double = 1_000_000_000;
        pub(crate) const DEC_WIDTH: u8 = 9;

        pub(crate) const OCT_RADIX: Double = 1 << 30;
        pub(crate) const OCT_WIDTH: u8 = 10;

        word_impl!([u8, u16, u32, usize]);
    });

    #[cfg(test)]
    word_def!((u8, u16), {
        pub(crate) const DEC_RADIX: Double = 100;
        pub(crate) const DEC_WIDTH: u8 = 2;

        pub(crate) const OCT_RADIX: Double = 1 << 6;
        pub(crate) const OCT_WIDTH: u8 = 2;

        word_impl!([u8]);
    });

    pub const MAX: Single = Single::MAX;
    pub const MIN: Single = Single::MIN;
    pub const BITS: usize = Single::BITS as usize;
    pub const BYTES: usize = Single::BITS as usize / 8;
    pub const RADIX: Double = Single::MAX as Double + 1;

    #[rustfmt::skip]
    pub trait Word: Clone + Copy
        + PartialEq + Eq
        + PartialOrd + Ord
        + Debug + Display + Binary + Octal + LowerHex + UpperHex
        + FromBytes + IntoBytes + Immutable
    {
        const BITS: usize;
        const BYTES: usize;
        const ZERO: Self;
        const ONE: Self;

        fn from_usize(value: usize) -> Self;
        fn from_single(value: Single) -> Self;
        fn from_double(value: Double) -> Self;

        fn as_usize(self) -> usize;
        fn as_single(self) -> Single;
        fn as_double(self) -> Double;

        fn order(self) -> usize;

        fn is_pow2(self) -> bool;
    }

    pub trait WordsIterator: Clone + Iterator + ExactSizeIterator
    where
        <Self as Iterator>::Item: Word,
    {
    }

    impl<Iter> WordsIterator for Iter
    where
        Iter: Clone + Iterator + ExactSizeIterator,
        Iter::Item: Word,
    {
    }
}

#[ndarch::align]
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::NumFnChecked)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumExt)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned<T>(pub T);

impl<T> From<T> for Aligned<T> {
    fn from(value: T) -> Self {
        Aligned(value)
    }
}

ndops::fwd! { @ndun <T> (value: &Aligned<T>) -> Aligned<T>, (T) (&value.0) [
    ! where [T: NdNot<Type = T>],
    - where [T: NdNeg<Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned<Lhs>, rhs: &Aligned<Rhs>) -> Aligned<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + where [Lhs: NdAdd   <Lhs, Rhs, Type = T>],
    - where [Lhs: NdSub   <Lhs, Rhs, Type = T>],
    * where [Lhs: NdMul   <Lhs, Rhs, Type = T>],
    / where [Lhs: NdDiv   <Lhs, Rhs, Type = T>],
    % where [Lhs: NdRem   <Lhs, Rhs, Type = T>],
    | where [Lhs: NdBitOr <Lhs, Rhs, Type = T>],
    & where [Lhs: NdBitAnd<Lhs, Rhs, Type = T>],
    ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned<Lhs>, rhs: Rhs) -> Aligned<T>, (Lhs) (&lhs.0) (rhs) [
    << where [Lhs: NdShl<Lhs, Rhs, Type = T>],
    >> where [Lhs: NdShr<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, rhs: &Aligned<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where [Lhs: NdAddAssign   <Lhs, Rhs>],
    -= where [Lhs: NdSubAssign   <Lhs, Rhs>],
    *= where [Lhs: NdMulAssign   <Lhs, Rhs>],
    /= where [Lhs: NdDivAssign   <Lhs, Rhs>],
    %= where [Lhs: NdRemAssign   <Lhs, Rhs>],
    |= where [Lhs: NdBitOrAssign <Lhs, Rhs>],
    &= where [Lhs: NdBitAndAssign<Lhs, Rhs>],
    ^= where [Lhs: NdBitXorAssign<Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where [Lhs: NdShlAssign<Lhs, Rhs>],
    >>= where [Lhs: NdShrAssign<Lhs, Rhs>],
] }

ndops::fwd! { @stdun <T> (*value: &Aligned<T>) -> Aligned<T>, (T) (&value.0) [
    - where [T: NdNeg<T, Type = T>],
    ! where [T: NdNot<T, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>, *rhs: &Aligned<Rhs>) -> Aligned<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + where [Lhs: NdAdd   <Lhs, Rhs, Type = T>],
    - where [Lhs: NdSub   <Lhs, Rhs, Type = T>],
    * where [Lhs: NdMul   <Lhs, Rhs, Type = T>],
    / where [Lhs: NdDiv   <Lhs, Rhs, Type = T>],
    % where [Lhs: NdRem   <Lhs, Rhs, Type = T>],
    | where [Lhs: NdBitOr <Lhs, Rhs, Type = T>],
    & where [Lhs: NdBitAnd<Lhs, Rhs, Type = T>],
    ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>, rhs: Rhs) -> Aligned<T>, (Lhs) (&lhs.0) (rhs) [
    << where [Lhs: NdShl<Lhs, Rhs, Type = T>],
    >> where [Lhs: NdShr<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, *rhs: &Aligned<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where [Lhs: NdAddAssign   <Lhs, Rhs>],
    -= where [Lhs: NdSubAssign   <Lhs, Rhs>],
    *= where [Lhs: NdMulAssign   <Lhs, Rhs>],
    /= where [Lhs: NdDivAssign   <Lhs, Rhs>],
    %= where [Lhs: NdRemAssign   <Lhs, Rhs>],
    |= where [Lhs: NdBitOrAssign <Lhs, Rhs>],
    &= where [Lhs: NdBitAndAssign<Lhs, Rhs>],
    ^= where [Lhs: NdBitXorAssign<Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where [Lhs: NdShlAssign<Lhs, Rhs>],
    >>= where [Lhs: NdShrAssign<Lhs, Rhs>],
] }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::long::{S64, U64};

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn std() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 48).map(S64::from)) [
            (*Aligned(val), val),
            (*Aligned(Aligned(val)), Aligned(val)),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(u64, 48).map(U64::from)) [
            (*Aligned(val), val),
            (*Aligned(Aligned(val)), Aligned(val)),
        ] }
    }

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn cmp() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56).map(S64::from),
            rhs in ndassert::range!(i64, 56).map(S64::from),
        ) [
            (Aligned(lhs).eq (&Aligned(rhs)), lhs.eq (&rhs)),
            (Aligned(lhs).cmp(&Aligned(rhs)), lhs.cmp(&rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56).map(U64::from),
            rhs in ndassert::range!(u64, 56).map(U64::from),
        ) [
            (Aligned(lhs).eq (&Aligned(rhs)), lhs.eq (&rhs)),
            (Aligned(lhs).cmp(&Aligned(rhs)), lhs.cmp(&rhs)),
        ] }
    }

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn fmt() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 48).map(S64::from)) [
            (format!("{:}",   Aligned(val)), format!("{:}",   val)),
            (format!("{:b}",  Aligned(val)), format!("{:b}",  val)),
            (format!("{:o}",  Aligned(val)), format!("{:o}",  val)),
            (format!("{:x}",  Aligned(val)), format!("{:x}",  val)),
            (format!("{:X}",  Aligned(val)), format!("{:X}",  val)),
            (format!("{:#}",  Aligned(val)), format!("{:#}",  val)),
            (format!("{:#b}", Aligned(val)), format!("{:#b}", val)),
            (format!("{:#o}", Aligned(val)), format!("{:#o}", val)),
            (format!("{:#x}", Aligned(val)), format!("{:#x}", val)),
            (format!("{:#X}", Aligned(val)), format!("{:#X}", val)),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(u64, 48).map(U64::from)) [
            (format!("{:}",   Aligned(val)), format!("{:}",   val)),
            (format!("{:b}",  Aligned(val)), format!("{:b}",  val)),
            (format!("{:o}",  Aligned(val)), format!("{:o}",  val)),
            (format!("{:x}",  Aligned(val)), format!("{:x}",  val)),
            (format!("{:X}",  Aligned(val)), format!("{:X}",  val)),
            (format!("{:#}",  Aligned(val)), format!("{:#}",  val)),
            (format!("{:#b}", Aligned(val)), format!("{:#b}", val)),
            (format!("{:#o}", Aligned(val)), format!("{:#o}", val)),
            (format!("{:#x}", Aligned(val)), format!("{:#x}", val)),
            (format!("{:#X}", Aligned(val)), format!("{:#X}", val)),
        ] }
    }

    #[test]
    fn ops() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1).map(S64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1).map(S64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1).map(U64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1).map(U64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 48).map(S64::from),
            rhs in 0..128,
        ) [
            (Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            (Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 48).map(U64::from),
            rhs in 0..128,
        ) [
            (Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            (Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }
    }

    #[test]
    fn ops_assign() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1).map(S64::from),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1).map(U64::from),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 48).map(S64::from),
            rhs in 0..128,
        ) [
            ({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 48).map(U64::from),
            rhs in 0..128,
        ) [
            ({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }
    }
}

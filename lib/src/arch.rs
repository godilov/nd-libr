use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};

use ndproc::*;
use rand::Rng;
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::{num::*, ops::*};

macro_rules! word_def {
    (($single:ty, $double:ty), { $($body:tt)* } $(,)?) => {
        pub type Single = $single;
        pub type Double = $double;

        $($body)*
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
    pub const BYTES: usize = Single::BITS as usize / u8::BITS as usize;
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

#[align]
#[forward_std(self.0 with T)]
#[forward_cmp(self.0 with T)]
#[forward_fmt(self.0 with T)]
#[forward_def(self.0 with T: crate::num::Num            where T: Num,           for<'s> &'s T: Ops<Type = T>)]
#[forward_def(self.0 with T: crate::num::NumExtension   where T: NumExtension,  for<'s> &'s T: Ops<Type = T>)]
#[forward_def(self.0 with T: crate::num::Signed         where T: Signed,        for<'s> &'s T: Ops<Type = T>)]
#[forward_def(self.0 with T: crate::num::Unsigned       where T: Unsigned,      for<'s> &'s T: Ops<Type = T>)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned<T>(pub T);

impl<T> From<T> for Aligned<T> {
    fn from(value: T) -> Self {
        Aligned(value)
    }
}

// ops_impl!(@bin <T> |*a: &Aligned<T>, *b: &Aligned<T>| -> Aligned::<T>,
// + ext {
//     (& &) Aligned(&a.0 + &b.0) where for<'t> &'t T: Add<&'t T, Output = T>;
//     (& _) Aligned(&a.0 + b.0) where for<'t> &'t T: Add<T, Output = T>;
//     (_ &) Aligned(a.0 + &b.0) where for<'t> T: Add<&'t T, Output = T>;
//     (_ _) Aligned(a.0 + b.0) where T: Add<T, Output = T>;
// });

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};

use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::bytes::word::*;

macro_rules! word_def {
    (($single:ty, $double:ty)) => {
        pub mod word {
            use super::*;

            pub type Single = $single;
            pub type Double = $double;

            pub const MAX: Single = Single::MAX;
            pub const MIN: Single = Single::MIN;
            pub const BITS: usize = Single::BITS as usize;
            pub const BYTES: usize = Single::BITS as usize / u8::BITS as usize;

    #[rustfmt::skip]
            pub trait Word: Clone + Copy
                + PartialEq + Eq
                + PartialOrd + Ord
                + Debug + Display + Binary + Octal + LowerHex + UpperHex
                + FromBytes + IntoBytes + Immutable
            {
                type Single: Clone + Copy;
                type Double: Clone + Copy + From<Self::Single>;

                const BITS: usize;
                const BYTES: usize;
                const ZERO: Self;
                const ONE: Self;

                fn from_single(value: Single) -> Self;
                fn from_double(value: Double) -> Self;

                fn as_single(self) -> Single;
                fn as_double(self) -> Double;

                fn order(self) -> usize;

                fn is_pow2(self) -> bool;
            }
        }
    };
}

#[cfg(all(target_pointer_width = "64", not(test)))]
word_def!((u64, u128));

#[cfg(all(target_pointer_width = "32", not(test)))]
word_def!((u32, u64));

#[cfg(test)]
word_def!((u8, u16));

pub struct Bytes<const L: usize>([Single; L]);

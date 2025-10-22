#![allow(unused)]
#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Display, Formatter, LowerHex, Octal, UpperHex, Write},
    str::FromStr,
};

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use thiserror::Error;
use zerocopy::{IntoBytes, transmute};

use crate::{
    num::{
        long::{digit::*, radix::*, uops::*},
        *,
    },
    ops::*,
};

#[macro_export]
macro_rules! signed {
    ($bits:expr) => {
        $crate::num::long::Signed<{ ($bits as usize).div_ceil($crate::num::long::digit::BITS as usize) }>
    };
}

#[macro_export]
macro_rules! unsigned {
    ($bits:expr) => {
        $crate::num::long::Unsigned<{ ($bits as usize).div_ceil($crate::num::long::digit::BITS as usize) }>
    };
}

macro_rules! digit_impl {
    ($primitive:ty, [$half:ty, $single:ty, $double:ty] $(,)?) => {
#[rustfmt::skip]
        impl Digit for $primitive {
            type Half = $half;
            type Single = $single;
            type Double = $double;

            const BITS: usize = Self::BITS as usize;
            const BYTES: usize = Self::BITS as usize / 8;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            fn from_half(value: Half) -> Self {
                value as Self
            }

            fn from_single(value: Single) -> Self {
                value as Self
            }

            fn from_double(value: Double) -> Self {
                value as Self
            }

            fn as_half(self) -> Half {
                self as Half
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

macro_rules! digits_impl {
    (($half:ty, $single:ty, $double:ty), ($dec_radix:expr, $dec_width:expr), ($oct_radix:expr, $oct_width:expr), { $($body:tt)* }) => {
        pub mod digit {
            use zerocopy::{FromBytes, IntoBytes};

            use super::*;

            pub type Half = $half;
            pub type Single = $single;
            pub type Double = $double;

            pub(super) const MAX: Single = Single::MAX;
            pub(super) const MIN: Single = Single::MIN;
            pub(super) const BITS: usize = Single::BITS as usize;
            pub(super) const BYTES: usize = Single::BITS as usize / u8::BITS as usize;
            pub(super) const RADIX: Double = Single::MAX as Double + 1;

            pub(super) const DEC_RADIX: Double = $dec_radix;
            pub(super) const DEC_WIDTH: u8 = $dec_width;

            pub(super) const OCT_RADIX: Double = $oct_radix;
            pub(super) const OCT_WIDTH: u8 = $oct_width;

            pub trait Digit: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + FromBytes + IntoBytes {
                type Half: Clone + Copy;
                type Single: Clone + Copy + From<Self::Half>;
                type Double: Clone + Copy + From<Self::Single>;

                const BITS: usize;
                const BYTES: usize;
                const ZERO: Self;
                const ONE: Self;

                fn from_half(value: Half) -> Self;
                fn from_single(value: Single) -> Self;
                fn from_double(value: Double) -> Self;

                fn as_half(self) -> Half;
                fn as_single(self) -> Single;
                fn as_double(self) -> Double;

                fn order(self) -> usize;

                fn is_pow2(self) -> bool;
            }

            pub trait DigitsIterator:
                Clone + Iterator<Item = <Self as DigitsIterator>::Item> + DoubleEndedIterator + ExactSizeIterator
            {
                type Item: Digit;
            }

            $($body)*
        }
    };
}

macro_rules! sign_from {
    (@unsigned [$($primitive:ty),+]) => {
        $(sign_from!(@unsigned $primitive);)+
    };
    (@signed [$($primitive:ty),+]) => {
        $(sign_from!(@signed $primitive);)+
    };
    (@unsigned $primitive:ty) => {
        impl From<$primitive> for Sign {
            fn from(value: $primitive) -> Self {
                if value == 0 { Sign::ZERO } else { Sign::POS }
            }
        }
    };
    (@signed $primitive:ty) => {
        impl From<$primitive> for Sign {
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

macro_rules! long_from {
    (@signed [$($primitive:ty),+]) => {
        $(long_from!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+]) => {
        $(long_from!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Signed<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_bytes_arr(&bytes, if value >= 0 { 0 } else { MAX });

                Self(res)
            }
        }
    };
    (@unsigned $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Unsigned<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_bytes_arr(&bytes, 0);

                Self(res)
            }
        }
    };
}

macro_rules! long_from_const {
    (@signed [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(long_from_const!(@signed $fn, $primitive);)+
    };
    (@unsigned [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(long_from_const!(@unsigned $fn, $primitive);)+
    };
    (@signed $fn:ident, $primitive:ty) => {
        pub const fn $fn(mut val: $primitive) -> Self {
            let default = if val >= 0 { 0 } else { MAX };

            let mut val = val.abs_diff(0);
            let mut idx = 0;
            let mut res = [default; L];

            while val > 0 {
                res[idx] = val as Single;
                idx += 1;
                val = val.unbounded_shr(BITS as u32);
            }

            Self(res)
        }
    };
    (@unsigned $fn:ident, $primitive:ty) => {
        pub const fn $fn(mut val: $primitive) -> Self {
            let mut idx = 0;
            let mut res = [0; L];

            while val > 0 {
                res[idx] = val as Single;
                idx += 1;
                val = val.unbounded_shr(BITS as u32);
            }

            Self(res)
        }
    };
}

macro_rules! try_from_digits_validate {
    ($digits:expr, $radix:expr) => {{
        if $radix.as_single() < 2 {
            return Err(TryFromDigitsError::InvalidRadix {
                radix: $radix.as_single() as usize,
            });
        }

        if let Some(digit) = $digits.find(|&digit| digit >= $radix) {
            return Err(TryFromDigitsError::InvalidDigits {
                digit: digit.as_single() as usize,
                radix: $radix.as_single() as usize,
            });
        }

        Ok(())
    }};
}

macro_rules! from_digits_bin_impl {
    ($digits:expr, $len:expr, $exp:expr) => {{
        let bits = $exp as usize;
        let mask = (1 << BITS) - 1;
        let len = ($len * bits + BITS - 1) / BITS;

        let mut acc = 0;
        let mut shl = 0;
        let mut idx = 0;
        let mut res = [0; L];

        for digit in $digits {
            acc |= digit.as_double() << shl;
            shl += bits;
            res[idx] = (acc & mask) as Single;

            if shl >= BITS {
                if idx + 1 == L {
                    break;
                }

                acc >>= BITS;
                shl -= BITS;
                idx += 1;
                res[idx] = (acc & mask) as Single;
            }
        }

        res
    }};
}

macro_rules! from_digits_impl {
    ($digits:expr, $radix:expr) => {{
        let mut idx = 0;
        let mut res = [0; L];

        for digit in $digits {
            let mut acc = digit.as_double();

            for ptr in res.iter_mut().take(idx + 1) {
                acc += *ptr as Double * $radix.as_double();

                *ptr = acc as Single;

                acc >>= BITS;
            }

            if idx < L && res[idx] > 0 {
                idx += 1;
            }
        }

        res
    }};
}

#[cfg(all(target_pointer_width = "64", not(test)))]
digits_impl!((u32, u64, u128), (10_000_000_000_000_000_000, 19), (Double::ONE << 63, 21), {
    digit_impl!(u8, [u8, u8, u16]);
    digit_impl!(u16, [u8, u16, u32]);
    digit_impl!(u32, [u16, u32, u64]);
    digit_impl!(u64, [u32, u64, u128]);
});

#[cfg(all(target_pointer_width = "32", not(test)))]
digits_impl!((u16, u32, u64), (1_000_000_000, 9), (Double::ONE << 30, 10), {
    digit_impl!(u8, [u8, u8, u16]);
    digit_impl!(u16, [u8, u16, u32]);
    digit_impl!(u32, [u16, u32, u64]);
});

#[cfg(test)]
digits_impl!((u8, u16, u32), (100, 2), (Double::ONE << 6, 2), {
    digit_impl!(u8, [u8, u8, u16]);
    digit_impl!(u16, [u8, u16, u32]);
});

pub mod radix {
    use super::*;

    pub struct Dec;
    pub struct Bin;
    pub struct Oct;
    pub struct Hex;
    pub struct Radix {
        pub(super) prefix: &'static str,
        pub(super) value: Double,
        pub(super) width: u8,
    }

    impl Dec {
        pub const PREFIX: &str = "";
        pub const RADIX: Double = DEC_RADIX;
        pub const WIDTH: u8 = DEC_WIDTH;
    }

    impl Bin {
        pub const PREFIX: &str = "0b";
        pub const RADIX: Double = RADIX;
        pub const WIDTH: u8 = BITS as u8;
    }

    impl Oct {
        pub const PREFIX: &str = "0o";
        pub const RADIX: Double = OCT_RADIX;
        pub const WIDTH: u8 = OCT_WIDTH;
    }

    impl Hex {
        pub const PREFIX: &str = "0x";
        pub const RADIX: Double = RADIX;
        pub const WIDTH: u8 = BITS as u8 / 4;
    }

    impl From<Dec> for Radix {
        fn from(_: Dec) -> Self {
            Self {
                prefix: Dec::PREFIX,
                value: Dec::RADIX,
                width: Dec::WIDTH,
            }
        }
    }

    impl From<Bin> for Radix {
        fn from(_: Bin) -> Self {
            Self {
                prefix: Bin::PREFIX,
                value: Bin::RADIX,
                width: Bin::WIDTH,
            }
        }
    }

    impl From<Oct> for Radix {
        fn from(_: Oct) -> Self {
            Self {
                prefix: Oct::PREFIX,
                value: Oct::RADIX,
                width: Oct::WIDTH,
            }
        }
    }

    impl From<Hex> for Radix {
        fn from(_: Hex) -> Self {
            Self {
                prefix: Hex::PREFIX,
                value: Hex::RADIX,
                width: Hex::WIDTH,
            }
        }
    }
}

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);
long_from!(@signed [i8, i16, i32, i64, i128, isize]);
long_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromStrError {
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error("Found invalid symbol '{ch}' during parsing from string of radix '{radix}'")]
    InvalidSymbol { ch: char, radix: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
    #[error("Found invalid digit '{digit}' during parsing from slice of radix '{radix}'")]
    InvalidDigits { digit: usize, radix: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryIntoDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signed<const L: usize>(pub [Single; L]);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unsigned<const L: usize>(pub [Single; L]);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SignedFixed<const L: usize>(pub [Single; L], pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsignedFixed<const L: usize>(pub [Single; L], pub usize);

struct SignedDyn(Vec<Single>, Sign);

struct UnsignedDyn(Vec<Single>);

struct SignedFixedDyn(Vec<Single>, Sign, usize);

struct UnsignedFixedDyn(Vec<Single>, usize);

pub struct DigitsBinIter<'digits, const L: usize, D: Digit> {
    digits: &'digits [Single; L],
    bits: usize,
    mask: Double,
    len: usize,
    acc: Double,
    shl: usize,
    idx: usize,
    val: D,
}

pub struct DigitsIter<'digits, const L: usize, D: Digit> {
    digits: &'digits mut [Single; L],
    radix: D,
    len: usize,
}

pub type S128 = signed!(128);
pub type S192 = signed!(192);
pub type S256 = signed!(256);
pub type S384 = signed!(384);
pub type S512 = signed!(512);
pub type S768 = signed!(768);
pub type S1024 = signed!(1024);
pub type S1536 = signed!(1536);
pub type S2048 = signed!(2048);
pub type S3072 = signed!(3072);
pub type S4096 = signed!(4096);
pub type S6144 = signed!(6144);
pub type S8192 = signed!(8192);

pub type U128 = unsigned!(128);
pub type U192 = unsigned!(192);
pub type U256 = unsigned!(256);
pub type U384 = unsigned!(384);
pub type U512 = unsigned!(512);
pub type U768 = unsigned!(768);
pub type U1024 = unsigned!(1024);
pub type U1536 = unsigned!(1536);
pub type U2048 = unsigned!(2048);
pub type U3072 = unsigned!(3072);
pub type U4096 = unsigned!(4096);
pub type U6144 = unsigned!(6144);
pub type U8192 = unsigned!(8192);

impl<const L: usize> Default for Signed<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> Default for Unsigned<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> From<&[u8]> for Signed<L> {
    fn from(value: &[u8]) -> Self {
        Self::from_bytes(value)
    }
}

impl<const L: usize> From<&[u8]> for Unsigned<L> {
    fn from(value: &[u8]) -> Self {
        Self::from_bytes(value)
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(s)
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(s)
    }
}

impl<const L: usize> FromIterator<u8> for Signed<L> {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self::from_bytes_iter(iter.into_iter())
    }
}

impl<const L: usize> FromIterator<u8> for Unsigned<L> {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self::from_bytes_iter(iter.into_iter())
    }
}

impl<const L: usize> From<Signed<L>> for Unsigned<L> {
    fn from(value: Signed<L>) -> Self {
        Self(value.0)
    }
}

impl<const L: usize> From<Unsigned<L>> for Signed<L> {
    fn from(value: Unsigned<L>) -> Self {
        Self(value.0)
    }
}

impl<const L: usize> AsRef<[u8]> for Signed<L> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const L: usize> AsRef<[u8]> for Unsigned<L> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const L: usize> AsMut<[u8]> for Signed<L> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl<const L: usize> AsMut<[u8]> for Unsigned<L> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl<const L: usize> Display for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = try_into_digits(*self.with_sign(Sign::POS).digits(), Dec::RADIX as Single).unwrap_or_default();

        write_long(f, Dec.into(), &digits, get_sign(self.digits(), self.sign()), write_dec)
    }
}

impl<const L: usize> Display for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = try_into_digits(*self.digits(), Dec::RADIX as Single).unwrap_or_default();

        write_long(f, Dec.into(), &digits, get_sign(self.digits(), self.sign()), write_dec)
    }
}

impl<const L: usize> Binary for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long_arr(f, Bin.into(), self.digits(), get_sign(self.digits(), Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long_arr(f, Bin.into(), self.digits(), get_sign(self.digits(), Sign::POS), write_bin)
    }
}

impl<const L: usize> Octal for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = try_into_digits_bin(self.digits(), Oct::RADIX.order() as u8).unwrap_or_default();

        write_long(f, Oct.into(), &digits, get_sign(self.digits(), Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = try_into_digits_bin(self.digits(), Oct::RADIX.order() as u8).unwrap_or_default();

        write_long(f, Oct.into(), &digits, get_sign(self.digits(), Sign::POS), write_oct)
    }
}

impl<const L: usize> LowerHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long_arr(f, Hex.into(), self.digits(), get_sign(self.digits(), Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long_arr(f, Hex.into(), self.digits(), get_sign(self.digits(), Sign::POS), write_lhex)
    }
}

impl<const L: usize> UpperHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long_arr(f, Hex.into(), self.digits(), get_sign(self.digits(), Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long_arr(f, Hex.into(), self.digits(), get_sign(self.digits(), Sign::POS), write_uhex)
    }
}

impl<const L: usize> Signed<L> {
    long_from_const!(@signed [
        (from_i8, i8),
        (from_i16, i16),
        (from_i32, i32),
        (from_i64, i64),
        (from_i128, i128),
        (from_isize, isize),
    ]);

    long_from_const!(@unsigned [
        (from_u8, u8),
        (from_u16, u16),
        (from_u32, u32),
        (from_u64, u64),
        (from_u128, u128),
        (from_usize, usize),
    ]);

    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        Self(from_bytes(bytes.as_ref()))
    }

    pub fn from_bytes_iter<Bytes: Iterator<Item = u8>>(bytes: Bytes) -> Self {
        Self(from_bytes_iter(bytes))
    }

    pub fn try_from_str(s: &str) -> Result<Self, TryFromStrError> {
        try_from_str(s).map(Self)
    }

    pub fn try_from_digits(digits: impl AsRef<[u8]>, radix: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits(digits.as_ref(), radix).map(Self)
    }

    pub fn try_from_digits_bin(digits: impl AsRef<[u8]>, exp: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits_bin(digits.as_ref(), exp).map(Self)
    }

    pub fn try_from_digits_iter<Digits: DigitsIterator<Item = u8>>(
        digits: Digits,
        radix: u8,
    ) -> Result<Self, TryFromDigitsError> {
        try_from_digits_iter(digits, radix).map(Self)
    }

    pub fn try_from_digits_bin_iter<Digits: DigitsIterator<Item = u8>>(
        digits: Digits,
        exp: u8,
    ) -> Result<Self, TryFromDigitsError> {
        try_from_digits_bin_iter(digits, exp).map(Self)
    }

    pub fn try_into_digits(self, radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits(self.0, radix)
    }

    pub fn try_into_digits_bin(&self, exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits_bin(&self.0, exp)
    }

    pub fn try_into_digits_iter(&mut self, radix: u8) -> Result<DigitsIter<'_, L, u8>, TryIntoDigitsError> {
        try_into_digits_iter(&mut self.0, radix)
    }

    pub fn try_into_digits_bin_iter(&self, exp: u8) -> Result<DigitsBinIter<'_, L, u8>, TryIntoDigitsError> {
        try_into_digits_bin_iter(&self.0, exp)
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn digits(&self) -> &[Single; L] {
        &self.0
    }

    pub fn sign(&self) -> Sign {
        if self.0 == [0; L] {
            return Sign::ZERO;
        }

        if self.0[L - 1] >> (BITS - 1) == 0 {
            Sign::POS
        } else {
            Sign::NEG
        }
    }

    pub fn with_sign(mut self, sign: Sign) -> Self {
        let s = self.sign();

        if s == Sign::ZERO {
            return self;
        }

        if sign == Sign::ZERO {
            return Self::default();
        }

        if sign != s {
            neg_mut(&mut self.0);
        }

        self
    }

    pub fn with_neg(mut self) -> Self {
        neg_mut(&mut self.0);

        self
    }
}

impl<const L: usize> Unsigned<L> {
    long_from_const!(@unsigned [
        (from_u8, u8),
        (from_u16, u16),
        (from_u32, u32),
        (from_u64, u64),
        (from_u128, u128),
        (from_usize, usize),
    ]);

    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        Self(from_bytes(bytes.as_ref()))
    }

    pub fn from_bytes_iter<Bytes: Iterator<Item = u8>>(bytes: Bytes) -> Self {
        Self(from_bytes_iter(bytes))
    }

    pub fn try_from_str(s: &str) -> Result<Self, TryFromStrError> {
        try_from_str(s).map(Self)
    }

    pub fn try_from_digits(digits: impl AsRef<[u8]>, radix: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits(digits.as_ref(), radix).map(Self)
    }

    pub fn try_from_digits_bin(digits: impl AsRef<[u8]>, exp: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits_bin(digits.as_ref(), exp).map(Self)
    }

    pub fn try_from_digits_iter<Digits: DigitsIterator<Item = u8>>(
        digits: Digits,
        radix: u8,
    ) -> Result<Self, TryFromDigitsError> {
        try_from_digits_iter(digits, radix).map(Self)
    }

    pub fn try_from_digits_bin_iter<Digits: DigitsIterator<Item = u8>>(
        digits: Digits,
        exp: u8,
    ) -> Result<Self, TryFromDigitsError> {
        try_from_digits_bin_iter(digits, exp).map(Self)
    }

    pub fn try_into_digits(self, radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits(self.0, radix)
    }

    pub fn try_into_digits_bin(&self, exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits_bin(&self.0, exp)
    }

    pub fn try_into_digits_iter(&mut self, radix: u8) -> Result<DigitsIter<'_, L, u8>, TryIntoDigitsError> {
        try_into_digits_iter(&mut self.0, radix)
    }

    pub fn try_into_digits_bin_iter(&self, exp: u8) -> Result<DigitsBinIter<'_, L, u8>, TryIntoDigitsError> {
        try_into_digits_bin_iter(&self.0, exp)
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn digits(&self) -> &[Single; L] {
        &self.0
    }

    pub fn sign(&self) -> Sign {
        get_sign_arr(&self.0, Sign::POS)
    }
}

impl<'digits, const L: usize, D: Digit> Iterator for DigitsBinIter<'digits, L, D> {
    type Item = D;

    fn next(&mut self) -> Option<Self::Item> {
        if self.digits.len() == self.idx {
            return None;
        }

        if self.shl >= self.bits {
            self.acc >>= self.bits;
            self.shl -= self.bits;
            self.val = D::from_double(self.acc & self.mask);

            return Some(self.val);
        }

        self.acc |= (self.digits[self.idx] as Double) << self.shl;
        self.shl += BITS;
        self.idx += 1;
        self.val = D::from_double(self.acc & self.mask);

        Some(self.val)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'digits, const L: usize, D: Digit> Iterator for DigitsIter<'digits, L, D> {
    type Item = D;

    fn next(&mut self) -> Option<Self::Item> {
        let mut any = 0;
        let mut acc = 0;

        for digit in self.digits.iter_mut().rev() {
            any |= *digit;
            acc = (acc << BITS) | *digit as Double;

            *digit = (acc / self.radix.as_double()) as Single;

            acc %= self.radix.as_double();
        }

        if any == 0 {
            return None;
        }

        Some(D::from_double(acc))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'digits, const L: usize, D: Digit> ExactSizeIterator for DigitsBinIter<'digits, L, D> {}
impl<'digits, const L: usize, D: Digit> ExactSizeIterator for DigitsIter<'digits, L, D> {}

fn from_bytes<const L: usize>(bytes: &[u8]) -> [Single; L] {
    let len = bytes.len().min(BYTES * L);

    let mut res = [0; L];

    res.as_mut_bytes()[..len].copy_from_slice(&bytes[..len]);

    res.iter_mut().for_each(|ptr| *ptr = (*ptr as Single).to_le());
    res
}

fn from_bytes_arr<const L: usize, const N: usize>(bytes: &[u8; N], default: Single) -> [Single; L] {
    let len = bytes.len().min(BYTES * L);

    let mut res = [default; L];

    res.as_mut_bytes()[..len].copy_from_slice(&bytes[..len]);

    res.iter_mut().for_each(|ptr| *ptr = (*ptr as Single).to_le());
    res
}

fn from_bytes_iter<const L: usize, Bytes: Iterator<Item = u8>>(bytes: Bytes) -> [Single; L] {
    let mut res = [0; L];

    res.as_mut_bytes().iter_mut().zip(bytes).for_each(|(dst, src)| *dst = src);

    res.iter_mut().for_each(|ptr| *ptr = (*ptr as Single).to_le());
    res
}

fn try_from_str_validate(s: &str, radix: u8) -> Result<(), TryFromStrError> {
    if let Some(ch) = s.chars().find(|&ch| {
        let byte = ch as u8;

        match ch {
            '0'..='9' => byte - b'0' >= radix,
            'a'..='f' => byte - b'a' + 10 >= radix,
            'A'..='F' => byte - b'A' + 10 >= radix,
            '_' => false,
            _ => false,
        }
    }) {
        return Err(TryFromStrError::InvalidSymbol { ch, radix });
    }

    Ok(())
}

fn try_into_digits_validate<D: Digit>(radix: D) -> Result<(), TryIntoDigitsError> {
    if radix.as_single() < 2 {
        return Err(TryIntoDigitsError::InvalidRadix {
            radix: radix.as_single() as usize,
        });
    }

    Ok(())
}

fn try_from_str_bin<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], TryFromStrError> {
    try_from_str_validate(s, 1 << exp)?;

    let mut res = from_digits_bin_impl!(s.bytes().rev().filter_map(get_digit_from_byte), s.len(), exp);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn try_from_digits_bin<const L: usize, D: Digit>(digits: &[D], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
    if exp >= D::BITS as u8 {
        return Err(TryFromDigitsError::InvalidExponent { exp });
    }

    try_from_digits_validate!(digits.iter().copied(), D::from_single(1 << exp))?;

    let res = from_digits_bin_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn try_from_digits_bin_iter<const L: usize, D: Digit, Digits: DigitsIterator<Item = D>>(
    digits: Digits,
    exp: u8,
) -> Result<[Single; L], TryFromDigitsError> {
    if exp >= D::BITS as u8 {
        return Err(TryFromDigitsError::InvalidExponent { exp });
    }

    try_from_digits_validate!(digits.clone(), D::from_single(1 << exp))?;

    let res = from_digits_bin_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn try_into_digits_bin<const L: usize, D: Digit>(digits: &[Single; L], exp: u8) -> Result<Vec<D>, TryIntoDigitsError> {
    if exp >= D::BITS as u8 {
        return Err(TryIntoDigitsError::InvalidExponent { exp });
    }

    try_into_digits_validate(D::from_single(1 << exp))?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![D::ZERO; len + 1];

    for &digit in digits {
        acc |= (digit as Double) << shl;
        shl += BITS;
        res[idx] = D::from_double(acc & mask);

        while shl >= bits {
            acc >>= bits;
            shl -= bits;
            idx += 1;
            res[idx] = D::from_double(acc & mask);
        }
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn try_into_digits_bin_iter<const L: usize, D: Digit>(
    digits: &[Single; L],
    exp: u8,
) -> Result<DigitsBinIter<'_, L, D>, TryIntoDigitsError> {
    if exp >= D::BITS as u8 {
        return Err(TryIntoDigitsError::InvalidExponent { exp });
    }

    try_into_digits_validate(D::from_single(1 << exp))?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let len = (digits.len() * BITS + bits - 1) / bits;

    Ok(DigitsBinIter {
        digits,
        bits,
        mask,
        len,
        acc: 0,
        shl: 0,
        idx: 0,
        val: D::ZERO,
    })
}

fn try_from_str<const L: usize>(s: &str) -> Result<[Single; L], TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;

    if radix.is_pow2() {
        return try_from_str_bin(s, radix.order() as u8, sign);
    }

    try_from_str_validate(s, radix)?;

    let mut res = from_digits_impl!(s.bytes().filter_map(get_digit_from_byte), radix);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn try_from_digits<const L: usize, D: Digit>(digits: &[D], radix: D) -> Result<[Single; L], TryFromDigitsError> {
    if radix.is_pow2() {
        return try_from_digits_bin(digits, radix.order() as u8);
    }

    try_from_digits_validate!(digits.iter().copied(), radix)?;

    let res = from_digits_impl!(digits.iter().rev(), radix);

    Ok(res)
}

fn try_from_digits_iter<const L: usize, D: Digit, Digits: DigitsIterator<Item = D>>(
    digits: Digits,
    radix: D,
) -> Result<[Single; L], TryFromDigitsError> {
    if radix.is_pow2() {
        return try_from_digits_bin_iter(digits, radix.order() as u8);
    }

    try_from_digits_validate!(digits.clone(), radix)?;

    let res = from_digits_impl!(digits.rev(), radix);

    Ok(res)
}

fn try_into_digits<const L: usize, D: Digit>(mut digits: [Single; L], radix: D) -> Result<Vec<D>, TryIntoDigitsError> {
    if radix.is_pow2() {
        return try_into_digits_bin(&digits, radix.order() as u8);
    }

    try_into_digits_validate(radix)?;

    let bits = radix.order();
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut idx = 0;
    let mut res = vec![D::ZERO; len + 1];

    loop {
        let mut any = 0;
        let mut acc = 0;

        for digit in digits.iter_mut().rev() {
            any |= *digit;
            acc = (acc << BITS) | *digit as Double;

            *digit = (acc / radix.as_double()) as Single;

            acc %= radix.as_double();
        }

        if any == 0 {
            break;
        }

        res[idx] = D::from_double(acc);
        idx += 1;
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn try_into_digits_iter<const L: usize, D: Digit>(
    digits: &mut [Single; L],
    radix: D,
) -> Result<DigitsIter<'_, L, D>, TryIntoDigitsError> {
    try_into_digits_validate(radix)?;

    let bits = radix.order();
    let len = (digits.len() * BITS + bits - 1) / bits;

    Ok(DigitsIter { digits, radix, len })
}

fn write_dec(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$}")
}

fn write_bin(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$b}")
}

fn write_oct(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$o}")
}

fn write_lhex(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$x}")
}

fn write_uhex(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$X}")
}

fn write_long<F: Fn(&mut String, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    radix: Radix,
    digits: &[Single],
    sign: Sign,
    func: F,
) -> std::fmt::Result {
    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", radix.prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let len = get_len(digits);

    let mut buf = String::with_capacity(len * radix.width as usize);

    for &digit in digits[..len].iter().rev() {
        func(&mut buf, digit, radix.width as usize)?;
    }

    let offset = buf.as_bytes().iter().take_while(|&byte| byte == &b'0').count();

    write!(fmt, "{}{}{}", sign, radix.prefix, &buf[offset..])
}

fn write_long_arr<const L: usize, F: Fn(&mut String, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    radix: Radix,
    digits: &[Single; L],
    sign: Sign,
    func: F,
) -> std::fmt::Result {
    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", radix.prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let len = get_len_arr(digits);

    let mut buf = String::with_capacity(len * radix.width as usize);

    for &digit in digits[..len].iter().rev() {
        func(&mut buf, digit, radix.width as usize)?;
    }

    let offset = buf.as_bytes().iter().take_while(|&byte| byte == &b'0').count();

    write!(fmt, "{}{}{}", sign, radix.prefix, &buf[offset..])
}

fn get_sign_from_str(s: &str) -> Result<(&str, Sign), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    let val = match &s[..1] {
        "+" => (&s[1..], Sign::POS),
        "-" => (&s[1..], Sign::NEG),
        _ => (s, Sign::POS),
    };

    Ok(val)
}

fn get_radix_from_str(s: &str) -> Result<(&str, u8), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    if s.len() < 2 {
        return Ok((s, 10));
    }

    let val = match &s[..2] {
        "0x" | "0X" => (&s[2..], 16),
        "0o" | "0O" => (&s[2..], 8),
        "0b" | "0B" => (&s[2..], 2),
        _ => (s, 10),
    };

    Ok(val)
}

fn get_digit_from_byte(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn get_len<D: Digit>(digits: &[D]) -> usize {
    for (i, digit) in digits.iter().enumerate().rev() {
        if digit != &D::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_len_arr<D: Digit, const L: usize>(digits: &[D; L]) -> usize {
    for (i, digit) in digits.iter().enumerate().rev() {
        if digit != &D::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_sign<D: Digit>(digits: &[D], sign: Sign) -> Sign {
    if !is_zero(digits) { sign } else { Sign::ZERO }
}

fn get_sign_arr<D: Digit, const L: usize>(digits: &[D; L], sign: Sign) -> Sign {
    if digits != &[D::ZERO; L] { sign } else { Sign::ZERO }
}

fn is_zero<D: Digit>(digits: &[D]) -> bool {
    digits.iter().all(|digit| digit == &D::ZERO)
}

fn is_non_zero<D: Digit>(digits: &[D]) -> bool {
    digits.iter().any(|digit| digit != &D::ZERO)
}

mod uops {
    use super::*;

    pub(super) fn pos<const L: usize>(digits: [Single; L]) -> [Single; L] {
        digits
    }

    pub(super) fn pos_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        digits
    }

    pub(super) fn neg<const L: usize>(digits: [Single; L]) -> [Single; L] {
        inc(not(digits))
    }

    pub(super) fn neg_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(digits);
        inc_mut(digits);

        digits
    }

    pub(super) fn not<const L: usize>(digits: [Single; L]) -> [Single; L] {
        digits.iter().map(|&digit| !digit).collect_with([0; L])
    }

    pub(super) fn not_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        digits.iter_mut().for_each(|digit| *digit = !*digit);
        digits
    }

    pub(super) fn inc<const L: usize>(mut digits: [Single; L]) -> [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = *ptr as Double + acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }

    pub(super) fn inc_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = *ptr as Double + acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }

    pub(super) fn dec<const L: usize>(mut digits: [Single; L]) -> [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = RADIX + *ptr as Double - acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }

    pub(super) fn dec_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = RADIX + *ptr as Double - acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }
}

pub mod asm {
    use super::*;

    const L: usize = 4096 / BITS;
    const N: usize = 256 / BITS;

    #[inline(never)]
    pub fn from_bytes_(bytes: &[u8]) -> [Single; L] {
        from_bytes(bytes)
    }

    #[inline(never)]
    pub fn from_bytes_arr_(bytes: &[u8; N]) -> [Single; L] {
        from_bytes_arr(bytes, 0)
    }

    #[inline(never)]
    pub fn try_from_str_(s: &str) -> Result<[Single; L], TryFromStrError> {
        try_from_str(s)
    }

    #[inline(never)]
    pub fn try_from_digits_(digits: &[u8], radix: u8) -> Result<[Single; L], TryFromDigitsError> {
        try_from_digits(digits, radix)
    }

    #[inline(never)]
    pub fn try_into_digits_(digits: [Single; L], radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits(digits, radix)
    }

    #[inline(never)]
    pub fn try_from_str_bin_(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], TryFromStrError> {
        try_from_str_bin(s, exp, sign)
    }

    #[inline(never)]
    pub fn try_from_digits_bin_(digits: &[u8], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
        try_from_digits_bin(digits, exp)
    }

    #[inline(never)]
    pub fn try_into_digits_bin_(digits: &[Single; L], exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits_bin(digits, exp)
    }

    #[inline(never)]
    pub fn neg_(digits: [Single; L]) -> [Single; L] {
        neg(digits)
    }

    #[inline(never)]
    pub fn not_(digits: [Single; L]) -> [Single; L] {
        not(digits)
    }

    #[inline(never)]
    pub fn inc_(digits: [Single; L]) -> [Single; L] {
        inc(digits)
    }

    #[inline(never)]
    pub fn dec_(digits: [Single; L]) -> [Single; L] {
        dec(digits)
    }

    #[inline(never)]
    pub fn neg_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        neg_mut(digits)
    }

    #[inline(never)]
    pub fn not_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(digits)
    }

    #[inline(never)]
    pub fn inc_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        inc_mut(digits)
    }

    #[inline(never)]
    pub fn dec_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        dec_mut(digits)
    }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat;

    use anyhow::Result;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use zerocopy::transmute;

    use super::*;

    type S64 = signed!(64);
    type U64 = unsigned!(64);

    const PRIMES_48BIT: [usize; 2] = [281_415_416_265_077, 281_397_419_487_323];

    #[test]
    fn from_primitives() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i128;
            let nval = -pval;

            assert_eq!(S64::from(pval), S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(S64::from(nval), S64 { 0: neg(transmute!(bytes)) });
            assert_eq!(U64::from(val), U64 { 0: pos(transmute!(bytes)) });
        }
    }

    #[test]
    fn from_bytes() {
        assert_eq!(S64::from_bytes([]), S64::default());
        assert_eq!(U64::from_bytes([]), U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_eq!(S64::from_bytes(bytes), S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(U64::from_bytes(bytes), U64 { 0: pos(transmute!(bytes)) });
        }
    }

    #[test]
    fn try_from_str() -> Result<()> {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i64;
            let nval = -(val as i64);

            let pos_dec = format!("{pval:#}");
            let pos_bin = format!("{pval:#b}");
            let pos_oct = format!("{pval:#o}");
            let pos_hex = format!("{pval:#x}");

            let neg_dec = format!("{nval:#}");
            let neg_bin = format!("{nval:#b}");
            let neg_oct = format!("{nval:#o}");
            let neg_hex = format!("{nval:#x}");

            let dec = format!("{val:#}");
            let bin = format!("{val:#b}");
            let oct = format!("{val:#o}");
            let hex = format!("{val:#x}");

            assert_eq!(pos_dec.parse::<S64>()?, S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(pos_bin.parse::<S64>()?, S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(pos_oct.parse::<S64>()?, S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(pos_hex.parse::<S64>()?, S64 { 0: pos(transmute!(bytes)) });

            assert_eq!(neg_dec.parse::<S64>()?, S64 { 0: neg(transmute!(bytes)) });
            assert_eq!(neg_bin.parse::<S64>()?, S64 { 0: neg(transmute!(bytes)) });
            assert_eq!(neg_oct.parse::<S64>()?, S64 { 0: neg(transmute!(bytes)) });
            assert_eq!(neg_hex.parse::<S64>()?, S64 { 0: neg(transmute!(bytes)) });

            assert_eq!(dec.parse::<U64>()?, U64 { 0: pos(transmute!(bytes)) });
            assert_eq!(bin.parse::<U64>()?, U64 { 0: pos(transmute!(bytes)) });
            assert_eq!(oct.parse::<U64>()?, U64 { 0: pos(transmute!(bytes)) });
            assert_eq!(hex.parse::<U64>()?, U64 { 0: pos(transmute!(bytes)) });
        }

        Ok(())
    }

    #[test]
    fn try_from_digits() -> Result<()> {
        assert_eq!(S64::try_from_digits([], 251)?, S64::default());
        assert_eq!(U64::try_from_digits([], 251)?, U64::default());

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                assert_eq!(S64::try_from_digits(digits, radix)?, S64 { 0: pos(transmute!(bytes)) });
                assert_eq!(U64::try_from_digits(digits, radix)?, U64 { 0: pos(transmute!(bytes)) });
            }
        }

        Ok(())
    }

    #[test]
    fn try_into_digits() -> Result<()> {
        assert_eq!(S64::try_from_digits([], 251)?.try_into_digits(251)?, vec![]);
        assert_eq!(U64::try_from_digits([], 251)?.try_into_digits(251)?, vec![]);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::try_from_digits(digits, radix)?
                        .try_into_digits(radix)?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );

                assert!(
                    U64::try_from_digits(digits, radix)?
                        .try_into_digits(radix)?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn to_str() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i64;
            let nval = -(val as i64);

            let pos_dec = format!("{pval:#}");
            let pos_bin = format!("{pval:#b}");
            let pos_oct = format!("{pval:#o}");
            let pos_hex = format!("{pval:#x}");

            let neg_dec = format!("{nval:#}");
            let neg_bin = format!("{nval:#b}");
            let neg_oct = format!("{nval:#o}");
            let neg_hex = format!("{nval:#x}");

            let dec = format!("{val:#}");
            let bin = format!("{val:#b}");
            let oct = format!("{val:#o}");
            let hex = format!("{val:#x}");

            assert_eq!(format!("{:#}", S64 { 0: pos(transmute!(bytes)) }), pos_dec);
            assert_eq!(format!("{:#b}", S64 { 0: pos(transmute!(bytes)) }), pos_bin);
            assert_eq!(format!("{:#o}", S64 { 0: pos(transmute!(bytes)) }), pos_oct);
            assert_eq!(format!("{:#x}", S64 { 0: pos(transmute!(bytes)) }), pos_hex);

            assert_eq!(format!("{:#}", S64 { 0: neg(transmute!(bytes)) }), neg_dec);
            assert_eq!(format!("{:#b}", S64 { 0: neg(transmute!(bytes)) }), neg_bin);
            assert_eq!(format!("{:#o}", S64 { 0: neg(transmute!(bytes)) }), neg_oct);
            assert_eq!(format!("{:#x}", S64 { 0: neg(transmute!(bytes)) }), neg_hex);

            assert_eq!(format!("{:#}", U64 { 0: pos(transmute!(bytes)) }), dec);
            assert_eq!(format!("{:#b}", U64 { 0: pos(transmute!(bytes)) }), bin);
            assert_eq!(format!("{:#o}", U64 { 0: pos(transmute!(bytes)) }), oct);
            assert_eq!(format!("{:#x}", U64 { 0: pos(transmute!(bytes)) }), hex);
        }
    }
}

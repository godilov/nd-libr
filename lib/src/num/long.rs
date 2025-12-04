#![allow(unused)]
#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex, Write as _},
    io::{Cursor, Write as _},
    iter::{once, repeat},
    marker::PhantomData,
    str::FromStr,
};

use ndproc::ops_impl;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use thiserror::Error;
use zerocopy::{FromBytes, Immutable, IntoBytes, transmute, transmute_mut, transmute_ref};

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

macro_rules! digit_def {
    ($id:ident) => {
#[rustfmt::skip]
        pub trait $id: Clone + Copy
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
    };
}

macro_rules! digit_impl {
    ($id:ident, $primitive:ty, [$single:ty, $double:ty] $(,)?) => {
#[rustfmt::skip]
        impl $id for $primitive {
            type Single = $single;
            type Double = $double;

            const BITS: usize = Self::BITS as usize;
            const BYTES: usize = Self::BITS as usize / 8;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            fn from_single(value: Single) -> Self {
                value as Self
            }

            fn from_double(value: Double) -> Self {
                value as Self
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
    (($single:ty, $double:ty), ($dec_radix:expr, $dec_width:expr), ($oct_radix:expr, $oct_width:expr), { $($body:tt)* }) => {
        pub mod digit {
            use super::*;

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

            digit_def!(Digit);
            digit_def!(DigitExt);

            pub trait DigitsIterator: Clone + Iterator + ExactSizeIterator
            where
                <Self as Iterator>::Item: Digit,
            {
            }

            impl<Iter> DigitsIterator for Iter
            where
                Iter: Clone + Iterator + ExactSizeIterator,
                Iter::Item: Digit,
            {
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
                let res = from_arr(&bytes, if value >= 0 { 0 } else { MAX });

                Self(res)
            }
        }
    };
    (@unsigned $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Unsigned<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr(&bytes, 0);

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

macro_rules! from_digits_validate {
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

macro_rules! inc_impl {
    ($digits:expr) => {{
        let mut digits = $digits;
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = *ptr as Double + acc as Double;

            *ptr = digit as Single;

            acc = digit / RADIX;

            if acc == 0 {
                break;
            }
        }

        digits
    }};
}

macro_rules! dec_impl {
    ($digits:expr) => {{
        let mut digits = $digits;
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = RADIX + *ptr as Double - acc as Double;

            *ptr = digit as Single;

            acc = (digit < RADIX) as Double;

            if acc == 0 {
                break;
            }
        }

        digits
    }};
}

macro_rules! add_long_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).scan(0, |acc, (a, b)| {
            let val = a as Double + b as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
}

macro_rules! sub_long_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).scan(0, |acc, (a, b)| {
            let val = RADIX + a as Double - b as Double - *acc;

            *acc = (val < RADIX) as Double;

            Some(val as Single)
        })
    };
}

macro_rules! add_single_impl {
    ($a:expr, $b:expr) => {
        $a.scan($b as Double, |acc, a| {
            let val = a as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
    (@overflow $a:expr, $b:expr) => {
        $a.fold($b as Double, |acc, a| {
            let val = a as Double + acc;

            val / RADIX
        })
    };
}

macro_rules! sub_single_impl {
    ($a:expr, $b:expr) => {
        $a.scan($b as Double, |acc, a| {
            let val = RADIX + a as Double - *acc;

            *acc = (val < RADIX) as Double;

            Some(val as Single)
        })
    };
}

macro_rules! mul_single_impl {
    ($a:expr, $b:expr) => {
        $a.scan(0, |acc, a| {
            let val = a as Double * $b as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
    (@overflow $a:expr, $b:expr) => {
        $a.fold(0, |acc, a| {
            let val = a as Double * $b as Double + acc;

            val / RADIX
        })
    };
}

macro_rules! add_long_mut_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).fold(0, |acc, (ptr, val)| {
            let v = *ptr as Double + val as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! sub_long_mut_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).fold(0, |acc, (ptr, val)| {
            let v = RADIX + *ptr as Double - val as Double - acc;

            *ptr = v as Single;

            (v < RADIX) as Double
        });
    };
}

macro_rules! add_single_mut_impl {
    ($a:expr, $b:expr) => {
        $a.fold($b as Double, |acc, ptr| {
            let v = *ptr as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! sub_single_mut_impl {
    ($a:expr, $b:expr) => {
        $a.fold($b as Double, |acc, ptr| {
            let v = RADIX + *ptr as Double - acc;

            *ptr = v as Single;

            (v < RADIX) as Double
        });
    };
}

macro_rules! mul_single_mut_impl {
    ($a:expr, $b:expr) => {
        $a.fold(0, |acc, ptr| {
            let v = *ptr as Double * $b as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! div_long_impl {
    ($a:expr, $b:expr) => {{
        let mut div = $a;
        let mut rem = [0; L];

        for val in div.iter_mut().rev() {
            cycle!(rem, *val);

            let digit = search!(@upper 0, RADIX, |m: Double| {
                if mul_single_impl!(@overflow $b, m) > 0 {
                    return Ordering::Greater;
                }

                let mul = mul_single_impl!($b, m).collect_with([0; L]);

                mul.iter()
                    .copied()
                    .rev()
                    .zip(rem.iter().copied().rev())
                    .map(|(x, y)| x.cmp(&y))
                    .find(|&ord| ord != Ordering::Equal)
                    .unwrap_or(Ordering::Equal)
            });

            let digit = digit.saturating_sub(1) as Single;

            *val = digit;

            if digit > 0 {
                let rem_iter = rem.iter_mut();
                let mul_iter = mul_single_impl!($b, digit);

                sub_long_mut_impl!(rem_iter, mul_iter);
            }
        }

        (div, rem)
    }};
}

macro_rules! div_single_impl {
    ($a:expr, $b:expr) => {{
        let mut div = $a;
        let mut rem = 0 as Double;

        for val in div.iter_mut().rev() {
            rem <<= BITS;
            rem |= *val as Double;

            let digit = search!(@upper 0, RADIX, |m: Double| { (m * $b as Double).cmp(&rem) });
            let digit = digit.saturating_sub(1) as Single;

            *val = digit;
            rem -= digit as Double * $b as Double;
        }

        (div, rem)
    }};
}

macro_rules! shl_impl {
    ($digits:expr, $digits_ret:expr, $shift:expr, $default:expr, |$val:ident: $ty:ty| { $($fn:tt)+ }) => {{
        let shift = $shift;
        let offset = shift / BITS;
        let shl = shift % BITS;
        let shr = BITS - shl;

        if offset >= L {
            return (|$val: $ty| { $($fn)+ })($digits_ret);
        }

        let mut res = $digits;

        for idx in ((offset + 1).min(L)..L).rev() {
            let idx_h = idx - offset;
            let idx_l = idx - offset - 1;

            let val_h = res[idx_h].checked_shl(shl as u32).unwrap_or(0);
            let val_l = res[idx_l].checked_shr(shr as u32).unwrap_or(0);

            res[idx] = val_h | val_l;
        }

        let val_h = res[0].checked_shl(shl as u32).unwrap_or(0);
        let val_l = $default.checked_shr(shr as u32).unwrap_or(0);

        res[offset] = val_h | val_l;

        res.iter_mut().take(offset).for_each(|ptr| *ptr = $default);
        res
    }};
}

macro_rules! shr_impl {
    ($digits:expr, $digits_ret:expr, $shift:expr, $default:expr, |$val:ident: $ty:ty| { $($fn:tt)+ }) => {{
        let shift = $shift;
        let offset = shift / BITS;
        let shr = shift % BITS;
        let shl = BITS - shr;

        if offset >= L {
            return (|$val: $ty| { $($fn)+ })($digits_ret);
        }

        let mut res = $digits;

        for idx in 0..(L - offset).saturating_sub(1) {
            let idx_h = idx + offset + 1;
            let idx_l = idx + offset;

            let val_h = res[idx_h].checked_shl(shl as u32).unwrap_or(0);
            let val_l = res[idx_l].checked_shr(shr as u32).unwrap_or(0);

            res[idx] = val_h | val_l;
        }

        let val_h = $default.checked_shl(shl as u32).unwrap_or(0);
        let val_l = res[L - 1].checked_shr(shr as u32).unwrap_or(0);

        res[L - offset - 1] = val_h | val_l;

        res.iter_mut().skip(L - offset).for_each(|ptr| *ptr = $default);
        res
    }};
}

macro_rules! cycle {
    ($arr:expr, $val:expr) => {{
        for i in (1..$arr.len()).rev() {
            $arr[i] = $arr[i - 1];
        }

        $arr[0] = $val;
    }};
}

macro_rules! search {
    (@lower $l:expr, $r:expr, |$m:ident: $ty:ty| { $($fn:tt)+ }) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match (|$m: $ty| { $($fn)+ })(m) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => r = m,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
    (@upper $l:expr, $r:expr, |$m:ident: $ty:ty| { $($fn:tt)+ }) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match (|$m: $ty| { $($fn)+ })(m) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
}

#[cfg(all(target_pointer_width = "64", not(test)))]
digits_impl!(
    (u64, u128),
    (10_000_000_000_000_000_000, 19),
    (<Double as DigitExt>::ONE << 63, 21),
    {
        digit_impl!(Digit, u8, [u8, u16]);
        digit_impl!(Digit, u16, [u16, u32]);
        digit_impl!(Digit, u32, [u32, u64]);
        digit_impl!(Digit, u64, [u64, u128]);
        digit_impl!(Digit, usize, [u64, u128]);

        digit_impl!(DigitExt, u128, [u128, u128]);
    }
);

#[cfg(all(target_pointer_width = "32", not(test)))]
digits_impl!((u32, u64), (1_000_000_000, 9), (<Double as DigitExt>::ONE << 30, 10), {
    digit_impl!(Digit, u8, [u8, u16]);
    digit_impl!(Digit, u16, [u16, u32]);
    digit_impl!(Digit, u32, [u32, u64]);
    digit_impl!(Digit, usize, [u32, u64]);

    digit_impl!(DigitExt, u64, [u32, u64, u128]);
    digit_impl!(DigitExt, u128, [u64, u128, u128]);
});

#[cfg(test)]
digits_impl!((u8, u16), (100, 2), (<Double as DigitExt>::ONE << 6, 2), {
    digit_impl!(Digit, u8, [u8, u16]);

    digit_impl!(DigitExt, u16, [u16, u32]);
    digit_impl!(DigitExt, u32, [u32, u64]);
    digit_impl!(DigitExt, u64, [u64, u128]);
    digit_impl!(DigitExt, u128, [u128, u128]);
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
        pub const EXP: u8 = RADIX.ilog2() as u8;
        pub const PREFIX: &str = "0b";
        pub const RADIX: Double = RADIX;
        pub const WIDTH: u8 = BITS as u8;
    }

    impl Oct {
        pub const EXP: u8 = OCT_RADIX.ilog2() as u8;
        pub const PREFIX: &str = "0o";
        pub const RADIX: Double = OCT_RADIX;
        pub const WIDTH: u8 = OCT_WIDTH;
    }

    impl Hex {
        pub const EXP: u8 = RADIX.ilog2() as u8;
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
pub enum TryToDigitsError {
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryIntoDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedDyn(Vec<Single>, Sign);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsignedDyn(Vec<Single>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedFixedDyn(Vec<Single>, Sign, usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsignedFixedDyn(Vec<Single>, usize);

#[derive(Debug, Clone)]
pub struct DigitsIter<'digits, const L: usize, D: Digit> {
    digits: &'digits [Single; L],
    bits: usize,
    mask: Double,
    cnt: usize,
    len: usize,
    acc: Double,
    shl: usize,
    idx: usize,
    _phantom: PhantomData<D>,
}

#[derive(Debug, Clone)]
pub struct DigitsArbIter<const L: usize, D: Digit> {
    digits: [Single; L],
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

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);
long_from!(@signed [i8, i16, i32, i64, i128, isize]);
long_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

impl From<TryToDigitsError> for TryIntoDigitsError {
    fn from(value: TryToDigitsError) -> Self {
        match value {
            TryToDigitsError::InvalidExponent { exp } => Self::InvalidRadix { radix: exp.order() },
        }
    }
}

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

impl<const L: usize, const N: usize, D: Digit> From<&[D; N]> for Signed<L> {
    fn from(value: &[D; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, const N: usize, D: Digit> From<&[D; N]> for Unsigned<L> {
    fn from(value: &[D; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, D: Digit> From<&[D]> for Signed<L> {
    fn from(value: &[D]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, D: Digit> From<&[D]> for Unsigned<L> {
    fn from(value: &[D]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, D: Digit> FromIterator<D> for Signed<L> {
    fn from_iter<T: IntoIterator<Item = D>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize, D: Digit> FromIterator<D> for Unsigned<L> {
    fn from_iter<T: IntoIterator<Item = D>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_arb(s).map(Self)
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_arb(s).map(Self)
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
        let iter = match self.with_sign(Sign::POS).into_digits_iter(Dec::RADIX as Single) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_long_iter(f, Dec.into(), iter, get_sign(&self.0, self.sign()), write_dec)
    }
}

impl<const L: usize> Display for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.into_digits_iter(Dec::RADIX as Single) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_long_iter(f, Dec.into(), iter, get_sign(&self.0, self.sign()), write_dec)
    }
}

impl<const L: usize> Binary for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long(f, Bin.into(), &self.0, get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long(f, Bin.into(), &self.0, get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Octal for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(Oct::EXP) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_long_iter(f, Oct.into(), iter, get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(Oct::EXP) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_long_iter(f, Oct.into(), iter, get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> LowerHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long(f, Hex.into(), &self.0, get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long(f, Hex.into(), &self.0, get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> UpperHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long(f, Hex.into(), &self.0, get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write_long(f, Hex.into(), &self.0, get_sign(&self.0, Sign::POS), write_uhex)
    }
}

ops_impl!(@bin |a: Sign, b: Sign| -> Sign, * Sign::from((a as i8) * (b as i8)));

ops_impl!(@bin <const L: usize> |*a: &Signed<L>, *b: &Signed<L>| -> Signed::<L>,
    + Signed::<L>(add_long(&a.0, &b.0)),
    - Signed::<L>(sub_long(&a.0, &b.0)),
    * Signed::<L>(mul_long(&a.0, &b.0)),
    / Signed::<L>(div_long(&a.abs().0, &b.abs().0).0).with_sign(a.sign() * b.sign()),
    % Signed::<L>(div_long(&a.abs().0, &b.abs().0).1).with_sign(a.sign()),
    | Signed::<L>(bit_long(&a.0, &b.0, |aop, bop| aop | bop)),
    & Signed::<L>(bit_long(&a.0, &b.0, |aop, bop| aop & bop)),
    ^ Signed::<L>(bit_long(&a.0, &b.0, |aop, bop| aop ^ bop)));

ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, *b: &Unsigned<L>| -> Unsigned::<L>,
    + Unsigned::<L>(add_long(&a.0, &b.0)),
    - Unsigned::<L>(sub_long(&a.0, &b.0)),
    * Unsigned::<L>(mul_long(&a.0, &b.0)),
    / Unsigned::<L>(div_long(&a.0, &b.0).0),
    % Unsigned::<L>(div_long(&a.0, &b.0).1),
    | Unsigned::<L>(bit_long(&a.0, &b.0, |aop, bop| aop | bop)),
    & Unsigned::<L>(bit_long(&a.0, &b.0, |aop, bop| aop & bop)),
    ^ Unsigned::<L>(bit_long(&a.0, &b.0, |aop, bop| aop ^ bop)));

ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: usize| -> Signed::<L>,
    << Signed::<L>(shl_signed(&a.0, b)),
    >> Signed::<L>(shr_signed(&a.0, b)));

ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: usize| -> Unsigned::<L>,
    << Unsigned::<L>(shl(&a.0, b, 0)),
    >> Unsigned::<L>(shr(&a.0, b, 0)));

ops_impl!(@mut <const L: usize> |a: &mut Signed<L>, *b: &Signed<L>|,
    += add_long_mut(&mut a.0, &b.0),
    -= sub_long_mut(&mut a.0, &b.0),
    *= mul_long_mut(&mut a.0, &b.0),
    /= { *a = Signed::<L>(div_long(&a.abs().0, &b.abs().0).0).with_sign(a.sign() * b.sign()); },
    %= { *a = Signed::<L>(div_long(&a.abs().0, &b.abs().0).1).with_sign(a.sign()); },
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: &mut Unsigned<L>, *b: &Unsigned<L>|,
    += add_long_mut(&mut a.0, &b.0),
    -= sub_long_mut(&mut a.0, &b.0),
    *= mul_long_mut(&mut a.0, &b.0),
    /= div_long_mut(&mut a.0, &b.0),
    %= rem_long_mut(&mut a.0, &b.0),
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: &mut Signed<L>, b: usize|,
    <<= { shl_signed_mut(&mut a.0, b); },
    >>= { shr_signed_mut(&mut a.0, b); });

ops_impl!(@mut <const L: usize> |a: &mut Unsigned<L>, b: usize|,
    <<= { shl_mut(&mut a.0, b, 0); },
    >>= { shr_mut(&mut a.0, b, 0); });

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

    pub fn from_digits<D: Digit>(digits: impl AsRef<[D]>, exp: u8) -> Result<Self, TryFromDigitsError> {
        from_digits(digits.as_ref(), exp).map(Self)
    }

    pub fn from_digits_iter<D: Digit, Digits: DigitsIterator<Item = D>>(
        digits: Digits,
        exp: u8,
    ) -> Result<Self, TryFromDigitsError> {
        from_digits_iter(digits, exp).map(Self)
    }

    pub fn from_digits_arb<D: Digit>(digits: impl AsRef<[D]>, radix: D) -> Result<Self, TryFromDigitsError> {
        from_digits_arb(digits.as_ref(), radix).map(Self)
    }

    pub fn from_digits_arb_iter<D: Digit, Digits: DigitsIterator<Item = D> + DoubleEndedIterator>(
        digits: Digits,
        radix: D,
    ) -> Result<Self, TryFromDigitsError> {
        from_digits_arb_iter(digits, radix).map(Self)
    }

    pub fn to_digits<D: Digit>(&self, exp: u8) -> Result<Vec<D>, TryToDigitsError> {
        to_digits(&self.0, exp)
    }

    pub fn to_digits_iter<D: Digit>(&self, exp: u8) -> Result<DigitsIter<'_, L, D>, TryToDigitsError> {
        to_digits_iter(&self.0, exp)
    }

    pub fn into_digits<D: Digit>(self, radix: D) -> Result<Vec<D>, TryIntoDigitsError> {
        into_digits(self.0, radix)
    }

    pub fn into_digits_iter<D: Digit>(self, radix: D) -> Result<DigitsArbIter<L, D>, TryIntoDigitsError> {
        into_digits_iter(self.0, radix)
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn sign(&self) -> Sign {
        sign(&self.0)
    }

    pub fn abs(&self) -> Unsigned<L> {
        match self.sign() {
            Sign::ZERO => Unsigned::<L>(self.0),
            Sign::NEG => Unsigned::<L>(neg(&self.0)),
            Sign::POS => Unsigned::<L>(self.0),
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

    pub fn from_digits<D: Digit>(digits: impl AsRef<[D]>, exp: u8) -> Result<Self, TryFromDigitsError> {
        from_digits(digits.as_ref(), exp).map(Self)
    }

    pub fn from_digits_iter<D: Digit, Digits: DigitsIterator<Item = D>>(
        digits: Digits,
        exp: u8,
    ) -> Result<Self, TryFromDigitsError> {
        from_digits_iter(digits, exp).map(Self)
    }

    pub fn from_digits_arb<D: Digit>(digits: impl AsRef<[D]>, radix: D) -> Result<Self, TryFromDigitsError> {
        from_digits_arb(digits.as_ref(), radix).map(Self)
    }

    pub fn from_digits_arb_iter<D: Digit, Digits: DigitsIterator<Item = D> + DoubleEndedIterator>(
        digits: Digits,
        radix: D,
    ) -> Result<Self, TryFromDigitsError> {
        from_digits_arb_iter(digits, radix).map(Self)
    }

    pub fn to_digits<D: Digit>(&self, exp: u8) -> Result<Vec<D>, TryToDigitsError> {
        to_digits(&self.0, exp)
    }

    pub fn to_digits_iter<D: Digit>(&self, exp: u8) -> Result<DigitsIter<'_, L, D>, TryToDigitsError> {
        to_digits_iter(&self.0, exp)
    }

    pub fn into_digits<D: Digit>(self, radix: D) -> Result<Vec<D>, TryIntoDigitsError> {
        into_digits(self.0, radix)
    }

    pub fn into_digits_iter<D: Digit>(self, radix: D) -> Result<DigitsArbIter<L, D>, TryIntoDigitsError> {
        into_digits_iter(self.0, radix)
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn sign(&self) -> Sign {
        get_sign(&self.0, Sign::POS)
    }
}

impl<'digits, const L: usize, D: Digit> ExactSizeIterator for DigitsIter<'digits, L, D> {}
impl<'digits, const L: usize, D: Digit> Iterator for DigitsIter<'digits, L, D> {
    type Item = D;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.cnt {
            if self.acc == 0 {
                return None;
            }

            let val = self.acc;

            self.acc >>= self.bits;
            self.shl = self.shl.saturating_sub(self.bits);

            return Some(D::from_double(val & self.mask));
        }

        if self.shl < self.bits {
            self.acc |= (self.digits[self.idx] as Double) << self.shl;
            self.shl += BITS;
            self.idx += 1;
        }

        let val = self.acc;

        self.acc >>= self.bits;
        self.shl -= self.bits;

        Some(D::from_double(val & self.mask))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<const L: usize, D: Digit> ExactSizeIterator for DigitsArbIter<L, D> {}
impl<const L: usize, D: Digit> Iterator for DigitsArbIter<L, D> {
    type Item = D;

    fn next(&mut self) -> Option<Self::Item> {
        let radix = self.radix.as_double();

        let mut any = 0;
        let mut acc = 0;

        for digit in self.digits.iter_mut().rev() {
            any |= *digit;
            acc = (acc << BITS) | *digit as Double;

            *digit = (acc / radix) as Single;

            acc %= radix;
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

fn from_arr<const L: usize, const N: usize, D: Digit>(arr: &[D; N], default: Single) -> [Single; L] {
    let len = N.min(L * BYTES / D::BYTES);

    let mut res = [default; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [D])[..len].copy_from_slice(&arr[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [D]).reverse();
    });

    res
}

fn from_slice<const L: usize, D: Digit>(slice: &[D]) -> [Single; L] {
    let len = slice.len().min(L * BYTES / D::BYTES);

    let mut res = [0; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [D])[..len].copy_from_slice(&slice[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [D]).reverse();
    });

    res
}

fn from_iter<const L: usize, D: Digit, Iter: Iterator<Item = D>>(iter: Iter) -> [Single; L] {
    let mut res = [0; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [D])
        .iter_mut()
        .zip(iter)
        .for_each(|(ptr, val)| *ptr = val);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [D]).reverse();
    });

    res
}

fn from_str_validate(s: &str, radix: u8) -> Result<(), TryFromStrError> {
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

fn to_digits_validate<D: Digit>(exp: u8) -> Result<(), TryToDigitsError> {
    if exp == 0 || exp >= D::BITS as u8 {
        return Err(TryToDigitsError::InvalidExponent { exp });
    }

    Ok(())
}

fn into_digits_validate<D: Digit>(radix: D) -> Result<(), TryIntoDigitsError> {
    let radix = radix.as_single() as usize;

    if radix < 2 {
        return Err(TryIntoDigitsError::InvalidRadix { radix });
    }

    Ok(())
}

fn from_digits<const L: usize, D: Digit>(digits: &[D], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
    if exp >= D::BITS as u8 {
        return Err(TryFromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate!(digits.iter().copied(), D::from_single(1 << exp))?;

    let res = from_digits_bin_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn from_digits_iter<const L: usize, D: Digit, Digits: DigitsIterator<Item = D>>(
    digits: Digits,
    exp: u8,
) -> Result<[Single; L], TryFromDigitsError> {
    if exp >= D::BITS as u8 {
        return Err(TryFromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate!(digits.clone(), D::from_single(1 << exp))?;

    let res = from_digits_bin_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn from_str<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], TryFromStrError> {
    from_str_validate(s, 1 << exp)?;

    let mut res = from_digits_bin_impl!(s.bytes().rev().filter_map(get_digit_from_byte), s.len(), exp);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn from_digits_arb<const L: usize, D: Digit>(digits: &[D], radix: D) -> Result<[Single; L], TryFromDigitsError> {
    if radix.is_pow2() {
        return from_digits(digits, radix.order() as u8);
    }

    from_digits_validate!(digits.iter().copied(), radix)?;

    let res = from_digits_impl!(digits.iter().rev(), radix);

    Ok(res)
}

fn from_digits_arb_iter<const L: usize, D: Digit, Digits: DigitsIterator<Item = D> + DoubleEndedIterator>(
    digits: Digits,
    radix: D,
) -> Result<[Single; L], TryFromDigitsError> {
    if radix.is_pow2() {
        return from_digits_iter(digits, radix.order() as u8);
    }

    from_digits_validate!(digits.clone(), radix)?;

    let res = from_digits_impl!(digits.rev(), radix);

    Ok(res)
}

fn from_str_arb<const L: usize>(s: &str) -> Result<[Single; L], TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;

    if radix.is_pow2() {
        return from_str(s, radix.order() as u8, sign);
    }

    from_str_validate(s, radix)?;

    let mut res = from_digits_impl!(s.bytes().filter_map(get_digit_from_byte), radix);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn to_digits<const L: usize, D: Digit>(digits: &[Single; L], exp: u8) -> Result<Vec<D>, TryToDigitsError> {
    to_digits_validate::<D>(exp)?;

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

    res.truncate(get_len_slice(&res));

    Ok(res)
}

fn to_digits_iter<const L: usize, D: Digit>(
    digits: &[Single; L],
    exp: u8,
) -> Result<DigitsIter<'_, L, D>, TryToDigitsError> {
    to_digits_validate::<D>(exp)?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let cnt = get_len(digits);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsIter {
        digits,
        bits,
        mask,
        cnt,
        len,
        acc: 0,
        shl: 0,
        idx: 0,
        _phantom: PhantomData,
    })
}

fn into_digits<const L: usize, D: Digit>(mut digits: [Single; L], radix: D) -> Result<Vec<D>, TryIntoDigitsError> {
    if radix.is_pow2() {
        return Ok(to_digits(&digits, radix.order() as u8)?);
    }

    into_digits_validate(radix)?;

    let radix = radix.as_double();
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

            *digit = (acc / radix) as Single;

            acc %= radix;
        }

        if any == 0 {
            break;
        }

        res[idx] = D::from_double(acc);
        idx += 1;
    }

    res.truncate(get_len_slice(&res));

    Ok(res)
}

fn into_digits_iter<const L: usize, D: Digit>(
    digits: [Single; L],
    radix: D,
) -> Result<DigitsArbIter<L, D>, TryIntoDigitsError> {
    into_digits_validate(radix)?;

    let bits = radix.order();
    let cnt = get_len(&digits);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsArbIter { digits, radix, len })
}

fn write_dec(mut cursor: Cursor<&mut [u8]>, mut digit: Single, width: usize) -> std::fmt::Result {
    cursor.write_fmt(format_args!("{digit:0width$}"));

    Ok(())
}

#[allow(clippy::unnecessary_cast)]
fn write_bin(cursor: Cursor<&mut [u8]>, mut digit: Single, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (digit % 2) as u8;
        digit /= 2;
    }

    Ok(())
}

#[allow(clippy::unnecessary_cast)]
fn write_oct(cursor: Cursor<&mut [u8]>, mut digit: Single, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (digit % 8) as u8;
        digit /= 8;
    }

    Ok(())
}

fn write_lhex(cursor: Cursor<&mut [u8]>, mut digit: Single, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[(digit % 16) as usize];
        digit /= 16;
    }

    Ok(())
}

fn write_uhex(cursor: Cursor<&mut [u8]>, mut digit: Single, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D', b'E', b'F',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[(digit % 16) as usize];
        digit /= 16;
    }

    Ok(())
}

fn write_long<const L: usize, F: Fn(Cursor<&mut [u8]>, Single, usize) -> std::fmt::Result>(
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

    let prefix = radix.prefix;
    let width = radix.width as usize;
    let len = get_len(digits);

    let mut buf = vec![b'0'; len * width];

    for (i, &digit) in digits[..len].iter().enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), digit, width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, radix.prefix, str)
}

fn write_long_iter<Digits: DigitsIterator, F: Fn(Cursor<&mut [u8]>, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    radix: Radix,
    digits: Digits,
    sign: Sign,
    func: F,
) -> std::fmt::Result
where
    <Digits as Iterator>::Item: Digit,
{
    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", radix.prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let prefix = radix.prefix;
    let width = radix.width as usize;
    let len = digits.len();

    let mut buf = vec![b'0'; len * width];

    for (i, digit) in digits.enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), digit.as_single(), width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, prefix, str)
}

fn add_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
    add_long_impl!(a.iter().copied(), b.iter().copied()).collect_with([0; L])
}

fn sub_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
    sub_long_impl!(a.iter().copied(), b.iter().copied()).collect_with([0; L])
}

fn mul_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
    let mut res = [0; L];

    for (idx, x) in b.iter().enumerate() {
        let res_iter = res.iter_mut().skip(idx);
        let mul_iter = mul_single_impl!(a.iter().copied(), *x);

        add_long_mut_impl!(res_iter, mul_iter);
    }

    res
}

fn div_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> ([Single; L], [Single; L]) {
    div_long_impl!(*a, b.iter().copied())
}

fn bit_long<const L: usize, F>(a: &[Single; L], b: &[Single; L], f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    a.iter()
        .copied()
        .zip(b.iter().copied())
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

fn add_single<const L: usize>(a: &[Single; L], b: Single) -> [Single; L] {
    add_single_impl!(a.iter().copied(), b).collect_with([0; L])
}

fn sub_single<const L: usize>(a: &[Single; L], b: Single) -> [Single; L] {
    sub_single_impl!(a.iter().copied(), b).collect_with([0; L])
}

fn mul_single<const L: usize>(a: &[Single; L], b: Single) -> [Single; L] {
    mul_single_impl!(a.iter().copied(), b).collect_with([0; L])
}

fn div_single<const L: usize>(a: &[Single; L], b: Single) -> ([Single; L], [Single; L]) {
    let (div, rem) = div_single_impl!(*a, b);

    (div, from_arr(&rem.to_le_bytes(), 0))
}

fn bitop_single<const L: usize, F>(a: &[Single; L], b: Single, f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    a.iter()
        .copied()
        .zip(once(b).chain(repeat(0)))
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

fn add_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    add_long_mut_impl!(a.iter_mut(), b.iter().copied());
}

fn sub_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    sub_long_mut_impl!(a.iter_mut(), b.iter().copied());
}

fn mul_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    *a = mul_long(a, b);
}

fn div_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    div_long_impl!(a, b.iter().copied());
}

fn rem_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    let (_, rem) = div_long_impl!(*a, b.iter().copied());

    *a = rem;
}

fn bit_long_mut<const L: usize, F>(a: &mut [Single; L], b: &[Single; L], f: F)
where
    F: Fn(Single, Single) -> Single,
{
    a.iter_mut().zip(b.iter().copied()).for_each(|(ptr, val)| *ptr = f(*ptr, val));
}

fn add_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    add_single_mut_impl!(a.iter_mut(), b);
}

fn sub_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    sub_single_mut_impl!(a.iter_mut(), b);
}

fn mul_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    mul_single_mut_impl!(a.iter_mut(), b);
}

fn div_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    div_single_impl!(a, b);
}

fn rem_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    let (_, rem) = div_single_impl!(*a, b);

    *a = from_arr(&rem.to_le_bytes(), 0);
}

fn bitop_single_mut<const L: usize, F>(a: &mut [Single; L], b: Single, f: F)
where
    F: Fn(Single, Single) -> Single,
{
    a.iter_mut()
        .zip(once(b).chain(repeat(0)))
        .for_each(|(ptr, val)| *ptr = f(*ptr, val));
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

fn get_len<D: Digit, const L: usize>(digits: &[D; L]) -> usize {
    for (i, digit) in digits.iter().enumerate().rev() {
        if digit != &D::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_len_slice<D: Digit>(digits: &[D]) -> usize {
    for (i, digit) in digits.iter().enumerate().rev() {
        if digit != &D::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_sign<D: Digit, const L: usize>(digits: &[D; L], sign: Sign) -> Sign {
    if digits != &[D::ZERO; L] { sign } else { Sign::ZERO }
}

fn get_sign_slice<D: Digit>(digits: &[D], sign: Sign) -> Sign {
    if !is_zero(digits) { sign } else { Sign::ZERO }
}

fn is_zero<D: Digit>(digits: &[D]) -> bool {
    digits.iter().all(|digit| digit == &D::ZERO)
}

fn is_non_zero<D: Digit>(digits: &[D]) -> bool {
    digits.iter().any(|digit| digit != &D::ZERO)
}

mod uops {
    use super::*;

    pub(super) fn pos<const L: usize>(digits: &[Single; L]) -> [Single; L] {
        *digits
    }

    pub(super) fn pos_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        digits
    }

    pub(super) fn neg<const L: usize>(digits: &[Single; L]) -> [Single; L] {
        let mut digits = *digits;

        not_mut(&mut digits);
        inc_mut(&mut digits);

        digits
    }

    pub(super) fn neg_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(digits);
        inc_mut(digits);

        digits
    }

    pub(super) fn not<const L: usize>(digits: &[Single; L]) -> [Single; L] {
        digits.iter().map(|&digit| !digit).collect_with([0; L])
    }

    pub(super) fn not_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        digits.iter_mut().for_each(|digit| *digit = !*digit);
        digits
    }

    pub(super) fn inc<const L: usize>(digits: &[Single; L]) -> [Single; L] {
        inc_impl!(*digits)
    }

    pub(super) fn inc_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        inc_impl!(digits)
    }

    pub(super) fn dec<const L: usize>(digits: &[Single; L]) -> [Single; L] {
        dec_impl!(*digits)
    }

    pub(super) fn dec_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        dec_impl!(digits)
    }

    pub(super) fn shl<const L: usize>(digits: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shl_impl!(*digits, digits, shift, default, |digits: &[Single; L]| { [default; L] })
    }

    pub(super) fn shr<const L: usize>(digits: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shr_impl!(*digits, digits, shift, default, |digits: &[Single; L]| { [default; L] })
    }

    pub(super) fn shl_mut<'digits, const L: usize>(
        digits: &'digits mut [Single; L],
        shift: usize,
        default: Single,
    ) -> &'digits mut [Single; L] {
        shl_impl!(digits, digits, shift, default, |digits: &'digits mut [Single; L]| {
            *digits = [default; L];
            digits
        })
    }

    pub(super) fn shr_mut<'digits, const L: usize>(
        digits: &'digits mut [Single; L],
        shift: usize,
        default: Single,
    ) -> &'digits mut [Single; L] {
        shr_impl!(digits, digits, shift, default, |digits: &'digits mut [Single; L]| {
            *digits = [default; L];
            digits
        })
    }

    pub(super) fn shl_signed<const L: usize>(digits: &[Single; L], shift: usize) -> [Single; L] {
        shl(digits, shift, 0)
    }

    pub(super) fn shr_signed<const L: usize>(digits: &[Single; L], shift: usize) -> [Single; L] {
        shr(digits, shift, if sign(digits) != Sign::NEG { 0 } else { MAX })
    }

    pub(super) fn shl_signed_mut<const L: usize>(digits: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        shl_mut(digits, shift, 0)
    }

    pub(super) fn shr_signed_mut<const L: usize>(digits: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        let default = if sign(digits) != Sign::NEG { 0 } else { MAX };

        shr_mut(digits, shift, default)
    }

    pub(super) fn sign<const L: usize>(digits: &[Single; L]) -> Sign {
        if digits == &[0; L] {
            return Sign::ZERO;
        }

        if digits[L - 1] >> (BITS - 1) == 0 {
            Sign::POS
        } else {
            Sign::NEG
        }
    }
}

pub mod asm {
    use super::*;

    const L: usize = 4096 / BITS;
    const N: usize = 256 / BITS;

    type D = u8;

    #[inline(never)]
    pub fn from_arr_(arr: &[D; N], default: Single) -> [Single; L] {
        from_arr(arr, default)
    }

    #[inline(never)]
    pub fn from_slice_(slice: &[D]) -> [Single; L] {
        from_slice(slice)
    }

    #[inline(never)]
    pub fn from_iter_(slice: &[D]) -> [Single; L] {
        from_iter(slice.iter().copied())
    }

    #[inline(never)]
    pub fn from_digits_(digits: &[u8], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
        from_digits(digits, exp)
    }

    #[inline(never)]
    pub fn from_digits_iter_(digits: &[u8], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
        from_digits_iter(digits.iter().copied(), exp)
    }

    #[inline(never)]
    pub fn from_str_(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], TryFromStrError> {
        from_str(s, exp, sign)
    }

    #[inline(never)]
    pub fn from_digits_arb_(digits: &[u8], radix: u8) -> Result<[Single; L], TryFromDigitsError> {
        from_digits_arb(digits, radix)
    }

    #[inline(never)]
    pub fn from_digits_iter_arb_(digits: &[u8], radix: u8) -> Result<[Single; L], TryFromDigitsError> {
        from_digits_arb_iter(digits.iter().copied(), radix)
    }

    #[inline(never)]
    pub fn from_str_arb_(s: &str) -> Result<[Single; L], TryFromStrError> {
        from_str_arb(s)
    }

    #[inline(never)]
    pub fn to_digits_(digits: &[Single; L], exp: u8) -> Result<Vec<u8>, TryToDigitsError> {
        to_digits::<L, u8>(digits, exp)
    }

    #[inline(never)]
    pub fn to_digits_iter_(digits: &[Single; L], exp: u8) -> Result<usize, TryToDigitsError> {
        to_digits_iter::<L, u8>(digits, exp).map(|iter| iter.count())
    }

    #[inline(never)]
    pub fn into_digits_(digits: [Single; L], radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        into_digits(digits, radix)
    }

    #[inline(never)]
    pub fn into_digits_iter_(digits: [Single; L], radix: u8) -> Result<usize, TryIntoDigitsError> {
        into_digits_iter(digits, radix).map(|iter| iter.count())
    }

    #[inline(never)]
    pub fn add_long_(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
        add_long(a, b)
    }

    #[inline(never)]
    pub fn sub_long_(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
        sub_long(a, b)
    }

    #[inline(never)]
    pub fn mul_long_(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
        mul_long(a, b)
    }

    #[inline(never)]
    pub fn div_long_(a: &[Single; L], b: &[Single; L]) -> ([Single; L], [Single; L]) {
        div_long(a, b)
    }

    #[inline(never)]
    pub fn add_single_(a: &[Single; L], b: Single) -> [Single; L] {
        add_single(a, b)
    }

    #[inline(never)]
    pub fn sub_single_(a: &[Single; L], b: Single) -> [Single; L] {
        sub_single(a, b)
    }

    #[inline(never)]
    pub fn mul_single_(a: &[Single; L], b: Single) -> [Single; L] {
        mul_single(a, b)
    }

    #[inline(never)]
    pub fn div_single_(a: &[Single; L], b: Single) -> ([Single; L], [Single; L]) {
        div_single(a, b)
    }

    #[inline(never)]
    pub fn add_long_mut_(a: &mut [Single; L], b: &[Single; L]) {
        add_long_mut(a, b)
    }

    #[inline(never)]
    pub fn sub_long_mut_(a: &mut [Single; L], b: &[Single; L]) {
        sub_long_mut(a, b)
    }

    #[inline(never)]
    pub fn mul_long_mut_(a: &mut [Single; L], b: &[Single; L]) {
        mul_long_mut(a, b)
    }

    #[inline(never)]
    pub fn div_long_mut_(a: &mut [Single; L], b: &[Single; L]) {
        div_long_mut(a, b)
    }

    #[inline(never)]
    pub fn add_single_mut_(a: &mut [Single; L], b: Single) {
        add_single_mut(a, b)
    }

    #[inline(never)]
    pub fn sub_single_mut_(a: &mut [Single; L], b: Single) {
        sub_single_mut(a, b)
    }

    #[inline(never)]
    pub fn mul_single_mut_(a: &mut [Single; L], b: Single) {
        mul_single_mut(a, b)
    }

    #[inline(never)]
    pub fn div_single_mut_(a: &mut [Single; L], b: Single) {
        div_single_mut(a, b)
    }

    #[inline(never)]
    pub fn pos_(digits: &[Single; L]) -> [Single; L] {
        pos(digits)
    }

    #[inline(never)]
    pub fn pos_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        pos_mut(digits)
    }

    #[inline(never)]
    pub fn neg_(digits: &[Single; L]) -> [Single; L] {
        neg(digits)
    }

    #[inline(never)]
    pub fn neg_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        neg_mut(digits)
    }

    #[inline(never)]
    pub fn not_(digits: &[Single; L]) -> [Single; L] {
        not(digits)
    }

    #[inline(never)]
    pub fn not_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(digits)
    }

    #[inline(never)]
    pub fn inc_(digits: &[Single; L]) -> [Single; L] {
        inc(digits)
    }

    #[inline(never)]
    pub fn inc_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        inc_mut(digits)
    }

    #[inline(never)]
    pub fn dec_(digits: &[Single; L]) -> [Single; L] {
        dec(digits)
    }

    #[inline(never)]
    pub fn dec_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        dec_mut(digits)
    }

    #[inline(never)]
    pub fn shl_(digits: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shl(digits, shift, default)
    }

    #[inline(never)]
    pub fn shr_(digits: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shr(digits, shift, default)
    }

    #[inline(never)]
    pub fn shl_mut_(digits: &mut [Single; L], shift: usize, default: Single) -> &mut [Single; L] {
        shl_mut(digits, shift, default)
    }

    #[inline(never)]
    pub fn shr_mut_(digits: &mut [Single; L], shift: usize, default: Single) -> &mut [Single; L] {
        shr_mut(digits, shift, default)
    }

    #[inline(never)]
    pub fn shl_signed_(digits: &[Single; L], shift: usize) -> [Single; L] {
        shl_signed(digits, shift)
    }

    #[inline(never)]
    pub fn shr_signed_(digits: &[Single; L], shift: usize) -> [Single; L] {
        shr_signed(digits, shift)
    }

    #[inline(never)]
    pub fn shl_signed_mut_(digits: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        shl_signed_mut(digits, shift)
    }

    #[inline(never)]
    pub fn shr_signed_mut_(digits: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        shr_signed_mut(digits, shift)
    }

    #[inline(never)]
    pub fn sign_(digits: &mut [Single; L]) -> Sign {
        sign(digits)
    }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat;

    use anyhow::Result;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;

    type S64 = signed!(64);
    type U64 = unsigned!(64);

    const PRIMES_32BIT: [usize; 2] = [4_294_392_163, 4_294_289_141];
    const PRIMES_40BIT: [usize; 2] = [1_099_466_711_507, 1_099_459_659_533];
    const PRIMES_48BIT: [usize; 2] = [281_415_416_265_077, 281_397_419_487_323];
    const PRIMES_56BIT: [usize; 2] = [72_057_582_686_044_051, 72_051_998_136_909_223];

    macro_rules! assert_ops {
        ($type_std:ty, $type:ty, |$a:ident, $b:ident, $aop:ident, $bop:ident| [$({ $($fn_lval:tt)+ } { $($fn_rval:tt)+ })+]) => {
            for a in (<$type_std>::MIN + 1..<$type_std>::MAX).step_by(PRIMES_56BIT[0]) {
                for b in (<$type_std>::MIN + 1..<$type_std>::MAX).step_by(PRIMES_56BIT[1]) {
                    let aop = &<$type>::from(a);
                    let bop = &<$type>::from(b);

                    $({
                        let lval = (|$aop: &$type, $bop: &$type| { $($fn_lval)+ })(aop, bop);
                        let rval = (|$a: $type_std, $b: $type_std| { $($fn_rval)+ })(a, b);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };

        (@shift $type_std:ty, $type:ty, $range:expr, |$val:ident, $valop:ident, $shift:ident| [$({ $($fn_lval:tt)+ } { $($fn_rval:tt)+ })+]) => {
            for val in (<$type_std>::MIN + 1..<$type_std>::MAX).step_by(PRIMES_48BIT[0]) {
                for shift in $range {
                    let valop = &<$type>::from(val);

                    $({
                        let lval = (|$valop: &$type, $shift: usize| { $($fn_lval)+ })(valop, shift);
                        let rval = (|$val: $type_std, $shift: usize| { $($fn_rval)+ })(val, shift);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };
    }

    macro_rules! assert_ops_mut {
        ($type_std:ty, $type:ty, |$a:ident, $b:ident, $aop:ident, $bop:ident| [$({ $($fn_lval:tt)+ } { $($fn_rval:expr)+ })+]) => {
            for a in (<$type_std>::MIN + 1..<$type_std>::MAX).step_by(PRIMES_56BIT[0]) {
                for b in (<$type_std>::MIN + 1..<$type_std>::MAX).step_by(PRIMES_56BIT[1]) {
                    $({
                        let aop = &mut <$type>::from(a);
                        let bop = &<$type>::from(b);

                        (|mut $aop: &mut $type, $bop: &$type| { $($fn_lval)+ })(aop, bop);

                        assert_eq!(*aop, (|mut $a: $type_std, $b: $type_std| { $($fn_rval)+ })(a, b));
                    })+
                }
            }
        };

        (@shift $type_std:ty, $type:ty, $range:expr, |$val:ident, $valop:ident, $shift:ident| [$({ $($fn_lval:tt)+ } { $($fn_rval:tt)+ })+]) => {
            for val in (<$type_std>::MIN + 1..<$type_std>::MAX).step_by(PRIMES_48BIT[0]) {
                for shift in $range {
                    $({
                        let valop = &mut <$type>::from(val);

                        (|mut $valop: &mut $type, $shift: usize| { $($fn_lval)+ })(valop, shift);

                        assert_eq!(*valop, (|mut $val: $type_std, $shift: usize| { $($fn_rval)+ })(val, shift));
                    })+
                }
            }
        };
    }

    #[test]
    fn from_std() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i128;
            let nval = -pval;

            assert_eq!(S64::from(pval), S64 { 0: pos(&bytes) });
            assert_eq!(S64::from(nval), S64 { 0: neg(&bytes) });
            assert_eq!(U64::from(val), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_slice() {
        let empty = &[] as &[u8];

        assert_eq!(S64::from(empty), S64::default());
        assert_eq!(U64::from(empty), U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();
            let slice = bytes.as_slice();

            assert_eq!(S64::from(slice), S64 { 0: pos(&bytes) });
            assert_eq!(U64::from(slice), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_iter() {
        let empty = (&[] as &[u8]).iter().copied();

        assert_eq!(empty.clone().collect::<S64>(), S64::default());
        assert_eq!(empty.clone().collect::<U64>(), U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();
            let iter = bytes.iter().copied();

            assert_eq!(iter.clone().collect::<S64>(), S64 { 0: pos(&bytes) });
            assert_eq!(iter.clone().collect::<U64>(), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_digits() -> Result<()> {
        let empty = &[] as &[u8];

        assert_eq!(S64::from_digits(empty, 7)?, S64::default());
        assert_eq!(U64::from_digits(empty, 7)?, U64::default());
        assert_eq!(S64::from_digits_arb(empty, 251u8)?, S64::default());
        assert_eq!(U64::from_digits_arb(empty, 251u8)?, U64::default());

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                assert_eq!(S64::from_digits_arb(digits, radix)?, S64 { 0: pos(&bytes) });
                assert_eq!(U64::from_digits_arb(digits, radix)?, U64 { 0: pos(&bytes) });
            }
        }

        Ok(())
    }

    #[test]
    fn from_digits_iter() -> Result<()> {
        let empty = (&[] as &[u8]).iter().copied();

        assert_eq!(S64::from_digits_iter(empty.clone(), 7)?, S64::default());
        assert_eq!(U64::from_digits_iter(empty.clone(), 7)?, U64::default());
        assert_eq!(S64::from_digits_arb_iter(empty.clone(), 251u8)?, S64::default());
        assert_eq!(U64::from_digits_arb_iter(empty.clone(), 251u8)?, U64::default());

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                assert_eq!(
                    S64::from_digits_arb_iter(digits.iter().copied(), radix)?,
                    S64 { 0: pos(&bytes) }
                );

                assert_eq!(
                    U64::from_digits_arb_iter(digits.iter().copied(), radix)?,
                    U64 { 0: pos(&bytes) }
                );
            }
        }

        Ok(())
    }

    #[test]
    fn to_digits() -> Result<()> {
        assert_eq!(S64::from(0i8).to_digits::<u8>(7)?, vec![]);
        assert_eq!(U64::from(0u8).to_digits::<u8>(7)?, vec![]);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for exp in 1..u8::BITS as u8 {
            for _ in 0..=u8::MAX {
                let radix = 1u8 << exp;
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits(digits, exp)?
                        .to_digits(exp)?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits_arb(digits, radix)?
                        .into_digits(radix)?
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
    fn to_digits_iter() -> Result<()> {
        assert_eq!(S64::from(0i8).to_digits_iter::<u8>(7)?.len(), 0);
        assert_eq!(U64::from(0u8).to_digits_iter::<u8>(7)?.len(), 0);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for exp in 1..u8::BITS as u8 {
            for _ in 0..=u8::MAX {
                let radix = 1u8 << exp;
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits(digits, exp)?
                        .to_digits_iter(exp)?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits(digits, exp)?
                        .to_digits_iter(exp)?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn into_digits() -> Result<()> {
        assert_eq!(S64::from(0i8).into_digits::<u8>(251)?, vec![]);
        assert_eq!(U64::from(0u8).into_digits::<u8>(251)?, vec![]);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits_arb(digits, radix)?
                        .into_digits(radix)?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits_arb(digits, radix)?
                        .into_digits(radix)?
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
    fn into_digits_iter() -> Result<()> {
        assert_eq!(S64::from(0i8).into_digits_iter::<u8>(251)?.len(), 0);
        assert_eq!(U64::from(0u8).into_digits_iter::<u8>(251)?.len(), 0);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits_arb(digits, radix)?
                        .into_digits_iter(radix)?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits_arb(digits, radix)?
                        .into_digits_iter(radix)?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn from_str() -> Result<()> {
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

            assert_eq!(pos_dec.parse::<S64>()?, S64 { 0: pos(&bytes) });
            assert_eq!(pos_bin.parse::<S64>()?, S64 { 0: pos(&bytes) });
            assert_eq!(pos_oct.parse::<S64>()?, S64 { 0: pos(&bytes) });
            assert_eq!(pos_hex.parse::<S64>()?, S64 { 0: pos(&bytes) });

            assert_eq!(neg_dec.parse::<S64>()?, S64 { 0: neg(&bytes) });
            assert_eq!(neg_bin.parse::<S64>()?, S64 { 0: neg(&bytes) });
            assert_eq!(neg_oct.parse::<S64>()?, S64 { 0: neg(&bytes) });
            assert_eq!(neg_hex.parse::<S64>()?, S64 { 0: neg(&bytes) });

            assert_eq!(dec.parse::<U64>()?, U64 { 0: pos(&bytes) });
            assert_eq!(bin.parse::<U64>()?, U64 { 0: pos(&bytes) });
            assert_eq!(oct.parse::<U64>()?, U64 { 0: pos(&bytes) });
            assert_eq!(hex.parse::<U64>()?, U64 { 0: pos(&bytes) });
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

            assert_eq!(format!("{:#}", S64 { 0: pos(&bytes) }), pos_dec);
            assert_eq!(format!("{:#b}", S64 { 0: pos(&bytes) }), pos_bin);
            assert_eq!(format!("{:#o}", S64 { 0: pos(&bytes) }), pos_oct);
            assert_eq!(format!("{:#x}", S64 { 0: pos(&bytes) }), pos_hex);

            assert_eq!(format!("{:#}", S64 { 0: neg(&bytes) }), neg_dec);
            assert_eq!(format!("{:#b}", S64 { 0: neg(&bytes) }), neg_bin);
            assert_eq!(format!("{:#o}", S64 { 0: neg(&bytes) }), neg_oct);
            assert_eq!(format!("{:#x}", S64 { 0: neg(&bytes) }), neg_hex);

            assert_eq!(format!("{:#}", U64 { 0: pos(&bytes) }), dec);
            assert_eq!(format!("{:#b}", U64 { 0: pos(&bytes) }), bin);
            assert_eq!(format!("{:#o}", U64 { 0: pos(&bytes) }), oct);
            assert_eq!(format!("{:#x}", U64 { 0: pos(&bytes) }), hex);
        }
    }

    #[test]
    fn signed_ops() {
        assert_ops!(i64, S64, |a, b, aop, bop| [
            { aop + bop } { S64::from(a.wrapping_add(b)) }
            { aop - bop } { S64::from(a.wrapping_sub(b)) }
            { aop * bop } { S64::from(a.wrapping_mul(b)) }
            { aop / bop } { S64::from(a / b) }
            { aop % bop } { S64::from(a % b) }
            { aop | bop } { S64::from(a | b) }
            { aop & bop } { S64::from(a & b) }
            { aop ^ bop } { S64::from(a ^ b) }
        ]);
    }

    #[test]
    fn unsigned_ops() {
        assert_ops!(u64, U64, |a, b, aop, bop| [
            { aop + bop } { U64::from(a.wrapping_add(b)) }
            { aop - bop } { U64::from(a.wrapping_sub(b)) }
            { aop * bop } { U64::from(a.wrapping_mul(b)) }
            { aop / bop } { U64::from(a / b) }
            { aop % bop } { U64::from(a % b) }
            { aop | bop } { U64::from(a | b) }
            { aop & bop } { U64::from(a & b) }
            { aop ^ bop } { U64::from(a ^ b) }
        ]);
    }

    #[test]
    fn signed_shift() {
        assert_ops!(@shift i64, S64, 0..64, |val, valop, shift| [
            { valop << shift } { S64::from(val << shift) }
            { valop >> shift } { S64::from(val >> shift) }
        ]);
    }

    #[test]
    fn unsigned_shift() {
        assert_ops!(@shift u64, U64, 0..64, |val, valop, shift| [
            { valop << shift } { U64::from(val << shift) }
            { valop >> shift } { U64::from(val >> shift) }
        ]);
    }

    #[test]
    fn signed_ops_mut() {
        assert_ops_mut!(i64, S64, |a, b, aop, bop| [
            { aop += bop; } { S64::from(a.wrapping_add(b)) }
            { aop -= bop; } { S64::from(a.wrapping_sub(b)) }
            { aop *= bop; } { S64::from(a.wrapping_mul(b)) }
            { aop /= bop; } { S64::from(a / b) }
            { aop %= bop; } { S64::from(a % b) }
            { aop |= bop; } { S64::from(a | b) }
            { aop &= bop; } { S64::from(a & b) }
            { aop ^= bop; } { S64::from(a ^ b) }
        ]);
    }

    #[test]
    fn unsigned_ops_mut() {
        assert_ops_mut!(u64, U64, |a, b, aop, bop| [
            { aop += bop; } { U64::from(a.wrapping_add(b)) }
            { aop -= bop; } { U64::from(a.wrapping_sub(b)) }
            { aop *= bop; } { U64::from(a.wrapping_mul(b)) }
            { aop /= bop; } { U64::from(a / b) }
            { aop %= bop; } { U64::from(a % b) }
            { aop |= bop; } { U64::from(a | b) }
            { aop &= bop; } { U64::from(a & b) }
            { aop ^= bop; } { U64::from(a ^ b) }
        ]);
    }

    #[test]
    fn signed_shift_mut() {
        assert_ops_mut!(@shift i64, S64, 0..64, |val, valop, shift| [
            { valop <<= shift; } { S64::from(val << shift) }
            { valop >>= shift; } { S64::from(val >> shift) }
        ]);
    }

    #[test]
    fn unsigned_shift_mut() {
        assert_ops_mut!(@shift u64, U64, 0..64, |val, valop, shift| [
            { valop <<= shift; } { U64::from(val << shift) }
            { valop >>= shift; } { U64::from(val >> shift) }
        ]);
    }
}

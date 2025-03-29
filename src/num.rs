#![allow(clippy::manual_div_ceil)]

use crate::ops::{AddChecked, DivChecked, MulChecked, Ops, OpsAll, OpsAllAssign, OpsAssign, OpsChecked, SubChecked};
use digit::{Double, Single};
use proc::ops_impl;
use radix::RADIX;
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
    str::FromStr,
};
use thiserror::Error;

#[macro_export]
macro_rules! signed_fixed {
    ($bits:expr) => {
        SignedFixed<{ (($bits + Single::BITS - 1) / Single::BITS) as usize }>
    };
}

#[macro_export]
macro_rules! unsigned_fixed {
    ($bits:expr) => {
        UnsignedFixed<{ (($bits + Single::BITS - 1) / Single::BITS) as usize }>
    };
}

macro_rules! number_impl {
    ($type:ty, $zero:expr, $one:expr $(,)?) => {
        impl Constants for $type {
            const MAX: Self = <$type>::MAX;
            const MIN: Self = <$type>::MIN;
            const ONE: Self = $one;
            const ZERO: Self = $zero;
        }

        impl Number for $type {
            type Type = $type;

            fn val(&self) -> &Self::Type {
                self
            }
        }
    };
}

macro_rules! int_impl_checked {
    ($type:ty $(,)?) => {
        impl AddChecked for $type {
            type Output = $type;

            fn checked_add(self, rhs: Self) -> Option<Self::Output> {
                self.checked_add(rhs)
            }
        }

        impl SubChecked for $type {
            type Output = $type;

            fn checked_sub(self, rhs: Self) -> Option<Self::Output> {
                self.checked_sub(rhs)
            }
        }

        impl MulChecked for $type {
            type Output = $type;

            fn checked_mul(self, rhs: Self) -> Option<Self::Output> {
                self.checked_mul(rhs)
            }
        }

        impl DivChecked for $type {
            type Output = $type;

            fn checked_div(self, rhs: Self) -> Option<Self::Output> {
                self.checked_div(rhs)
            }
        }

        impl OpsChecked for $type {}
    };
}

macro_rules! int_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(int_impl!($trait, $type,);)+
    };
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type, 0, 1);

        impl Integer for $type {
            const BITS: u32 = <$type>::BITS;
        }

        impl $trait for $type {}

        int_impl_checked!($type);
    };
}

macro_rules! float_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(float_impl!($trait, $type);)+
    };
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type, 0.0, 1.0);

        impl $trait for $type {}
    };
}

macro_rules! sign_from {
    ([$($from:ty),+]) => {
        $(sign_from!($from);)+
    };
    ($from:ty) => {
        impl From<$from> for Sign {
            fn from(value: $from) -> Self {
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
    ($type:ident, [$($from:ty),+] $(,)?) => {
        $(long_from!($type, $from);)+
    };
    ($type:ident, [$pos:expr], [$($from:ty),+] $(,)?) => {
        $(long_from!($type, $from, $pos);)+
    };
    ($type:ident, $from:ty $(, $pos:expr)?) => {
        impl From<$from> for $type {
            fn from(value: $from) -> Self {
                const LEN: usize = ((<$from>::BITS + Single::BITS - 1) / Single::BITS) as usize;

                if value == 0 {
                    return Default::default();
                }

                let mut data = vec![0; LEN];
                let mut len = 0;
                let mut val = value.abs_diff(0);

                while val > 0 {
                    data[len] = val as Single;
                    len += 1;
                    val = val.checked_shr(Single::BITS).unwrap_or(0);
                }

                data.truncate(len);

                Self { $(sign: $pos * Sign::from(value),)? data }
            }
        }
    };
}

macro_rules! fixed_from {
    ($type:ident, [$($from:ty),+] $(,)?) => {
        $(fixed_from!($type, $from);)+
    };
    ($type:ident, [$pos:expr], [$($from:ty),+] $(,)?) => {
        $(fixed_from!($type, $from, $pos);)+
    };
    ($type:ident, $from:ty $(, $pos:expr)?) => {
        impl<const L: usize> From<$from> for $type<L> {
            fn from(value: $from) -> Self {
                if value == 0 {
                    return Default::default();
                }

                let mut data = [0; L];
                let mut len = 0;
                let mut val = value.abs_diff(0);

                while val > 0 {
                    data[len] = val as Single;
                    len += 1;
                    val = val.checked_shr(Single::BITS).unwrap_or(0);
                }

                Self { $(sign: $pos * Sign::from(value),)? data, len }
            }
        }
    };
}

pub type S128 = signed_fixed!(128);
pub type S192 = signed_fixed!(192);
pub type S256 = signed_fixed!(256);
pub type S384 = signed_fixed!(384);
pub type S512 = signed_fixed!(512);
pub type S1024 = signed_fixed!(1024);
pub type S2048 = signed_fixed!(2048);
pub type S3072 = signed_fixed!(3072);
pub type S4096 = signed_fixed!(4096);

pub type U128 = unsigned_fixed!(128);
pub type U192 = unsigned_fixed!(192);
pub type U256 = unsigned_fixed!(256);
pub type U384 = unsigned_fixed!(384);
pub type U512 = unsigned_fixed!(512);
pub type U1024 = unsigned_fixed!(1024);
pub type U2048 = unsigned_fixed!(2048);
pub type U3072 = unsigned_fixed!(3072);
pub type U4096 = unsigned_fixed!(4096);

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromStrError {
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error("Found invalid symbol '{ch}' during parsing from string of radix '{radix}'")]
    InvalidSymbol { ch: char, radix: u16 },
    #[error("Found negative number during parsing from string for unsigned")]
    UnsignedNegative,
    #[error(transparent)]
    FromDigits(#[from] TryFromDigitsError),
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromSliceError {
    #[error("Exceeded maximum length of {max} with {len}")]
    ExceedLength { len: usize, max: usize },
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromDigitsError {
    #[error("Exceeded maximum length of {max} with {len}")]
    ExceedLength { len: usize, max: usize },
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: Double },
    #[error("Found invalid radix pow '{pow}'")]
    InvalidPow { pow: u8 },
    #[error("Found invalid value '{digit}' for radix '{radix}'")]
    InvalidDigit { digit: Single, radix: Double },
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntoRadixError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: Double },
    #[error("Found invalid radix pow '{pow}'")]
    InvalidPow { pow: u8 },
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedLong {
    sign: Sign,
    data: Vec<Single>,
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedLong {
    data: Vec<Single>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedFixed<const L: usize> {
    sign: Sign,
    data: [Single; L],
    len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedFixed<const L: usize> {
    data: [Single; L],
    len: usize,
}

pub trait Constants {
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

pub trait Number: Sized + Default + Display + Clone + PartialEq + PartialOrd + Constants + Ops + OpsAssign {
    type Type;

    fn val(&self) -> &Self::Type;
}

pub trait Integer: Eq + Ord + Number + OpsChecked + OpsAll + OpsAllAssign {
    const BITS: u32;
}

pub trait Signed: Integer {}
pub trait Unsigned: Integer {}
pub trait Float: Number {}

int_impl!(Signed, [i8, i16, i32, i64, i128]);
int_impl!(Unsigned, [u8, u16, u32, u64, u128]);
float_impl!(Float, [f32, f64]);

#[cfg(all(target_pointer_width = "64", not(test)))]
mod digit {
    pub(super) type Single = u64;
    pub(super) type Double = u128;

    pub(super) const OCT_MAX: Double = (1 << 63) - 1;
    pub(super) const OCT_RADIX: Double = 1 << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_MAX: Double = 9_999_999_999_999_999_999;
    pub(super) const DEC_RADIX: Double = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;
}

#[cfg(all(target_pointer_width = "32", not(test)))]
mod digit {
    pub(super) type Single = u32;
    pub(super) type Double = u64;

    pub(super) const OCT_MAX: Double = (1 << 30) - 1;
    pub(super) const OCT_RADIX: Double = 1 << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_MAX: Double = 999_999_999;
    pub(super) const DEC_RADIX: Double = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;
}

#[cfg(test)]
mod digit {
    pub(super) type Single = u8;
    pub(super) type Double = u16;

    pub(super) const OCT_MAX: Double = (1 << 6) - 1;
    pub(super) const OCT_RADIX: Double = 1 << 6;
    pub(super) const OCT_WIDTH: u8 = 2;

    pub(super) const DEC_MAX: Double = 99;
    pub(super) const DEC_RADIX: Double = 100;
    pub(super) const DEC_WIDTH: u8 = 2;
}

mod radix {
    use super::{
        Double, Single,
        digit::{DEC_MAX, DEC_RADIX, DEC_WIDTH, OCT_MAX, OCT_RADIX, OCT_WIDTH},
    };

    pub(super) const RADIX: Double = Single::MAX as Double + 1;

    pub trait Radix {
        const MAX: Double = Single::MAX as Double;
        const RADIX: Double = Single::MAX as Double + 1;
        const WIDTH: u8;
        const PREFIX: &str;
        const ALPHABET: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Radix for Bin {
        const WIDTH: u8 = Single::BITS as u8;
        const PREFIX: &str = "0b";
        const ALPHABET: &str = "01";
    }

    impl Radix for Oct {
        const MAX: Double = OCT_MAX;
        const RADIX: Double = OCT_RADIX;
        const WIDTH: u8 = OCT_WIDTH;
        const PREFIX: &str = "0o";
        const ALPHABET: &str = "01234567";
    }

    impl Radix for Dec {
        const MAX: Double = DEC_MAX;
        const RADIX: Double = DEC_RADIX;
        const WIDTH: u8 = DEC_WIDTH;
        const PREFIX: &str = "";
        const ALPHABET: &str = "0123456789";
    }

    impl Radix for Hex {
        const WIDTH: u8 = Single::BITS as u8 / 4;
        const PREFIX: &str = "0x";
        const ALPHABET: &str = "0123456789ABCDEF";
    }
}

impl<const L: usize> Default for SignedFixed<L> {
    fn default() -> Self {
        Self {
            sign: Sign::ZERO,
            data: [0; L],
            len: 0,
        }
    }
}

impl<const L: usize> Default for UnsignedFixed<L> {
    fn default() -> Self {
        Self { data: [0; L], len: 0 }
    }
}

sign_from!([u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize]);

long_from!(
    SignedLong,
    [Sign::POS],
    [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize],
);

fixed_from!(
    SignedFixed,
    [Sign::POS],
    [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize],
);

long_from!(UnsignedLong, [u8, u16, u32, u64, u128, usize]);
fixed_from!(UnsignedFixed, [u8, u16, u32, u64, u128, usize]);

impl FromStr for SignedLong {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (sign, data) = try_from_str_long(s)?;

        Ok(Self { sign, data })
    }
}

impl FromStr for UnsignedLong {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (sign, data) = try_from_str_long(s)?;

        (sign != Sign::NEG)
            .then_some(Self { data })
            .ok_or(TryFromStrError::UnsignedNegative)
    }
}

impl<const L: usize> FromStr for SignedFixed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (sign, data, len) = try_from_str_fixed(s)?;

        Ok(Self { sign, data, len })
    }
}

impl<const L: usize> FromStr for UnsignedFixed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (sign, data, len) = try_from_str_fixed(s)?;

        (sign != Sign::NEG)
            .then_some(Self { data, len })
            .ok_or(TryFromStrError::UnsignedNegative)
    }
}

impl SignedLong {
    fn from_raw((data, sign): (Vec<Single>, Sign)) -> Self {
        Self { data, sign }
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let data = from_slice_long(slice);
        let sign = get_sign(data.len(), Sign::POS);

        Self { sign, data }
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        let data = try_from_digits_long(digits, radix)?;
        let sign = get_sign(data.len(), Sign::POS);

        Ok(Self { sign, data })
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        let data = try_from_digits_long_bin(digits, pow)?;
        let sign = get_sign(data.len(), Sign::POS);

        Ok(Self { sign, data })
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.data, radix)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        self.clone().into_radix(radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.data, pow)
    }
}

impl UnsignedLong {
    fn from_raw((data, sign): (Vec<Single>, Sign)) -> Self {
        if sign != Sign::NEG {
            Self { data }
        } else {
            Default::default()
        }
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let data = from_slice_long(slice);

        Self { data }
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        let data = try_from_digits_long(digits, radix)?;

        Ok(Self { data })
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        let data = try_from_digits_long_bin(digits, pow)?;

        Ok(Self { data })
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.data, radix)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        self.clone().into_radix(radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.data, pow)
    }
}

impl<const L: usize> SignedFixed<L> {
    fn from_raw((data, len, sign): ([Single; L], usize, Sign)) -> Self {
        Self { data, sign, len }
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let (data, len) = from_slice_fixed(slice);
        let sign = get_sign(len, Sign::POS);

        Self { sign, data, len }
    }

    pub fn try_from_slice(slice: &[u8]) -> Result<Self, TryFromSliceError> {
        let (data, len) = try_from_slice_fixed(slice)?;
        let sign = get_sign(len, Sign::POS);

        Ok(Self { sign, data, len })
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        let (data, len) = try_from_digits_fixed(digits, radix)?;
        let sign = get_sign(len, Sign::POS);

        Ok(Self { sign, data, len })
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        let (data, len) = try_from_digits_fixed_bin(digits, pow)?;
        let sign = get_sign(data.len(), Sign::POS);

        Ok(Self { sign, data, len })
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.data[..self.len], radix)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        (*self).into_radix(radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.data[..self.len], pow)
    }
}

impl<const L: usize> UnsignedFixed<L> {
    fn from_raw((data, len, sign): ([Single; L], usize, Sign)) -> Self {
        if sign != Sign::NEG {
            Self { data, len }
        } else {
            Default::default()
        }
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let (data, len) = from_slice_fixed(slice);

        Self { data, len }
    }

    pub fn try_from_slice(slice: &[u8]) -> Result<Self, TryFromSliceError> {
        let (data, len) = try_from_slice_fixed(slice)?;

        Ok(Self { data, len })
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        let (data, len) = try_from_digits_fixed(digits, radix)?;

        Ok(Self { data, len })
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        let (data, len) = try_from_digits_fixed_bin(digits, pow)?;

        Ok(Self { data, len })
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.data[..self.len], radix)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        (*self).into_radix(radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.data[..self.len], pow)
    }
}

impl Display for SignedLong {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Display for UnsignedLong {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl<const L: usize> Display for SignedFixed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl<const L: usize> Display for UnsignedFixed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

fn from_slice_long(slice: &[u8]) -> Vec<Single> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let mut shift = 0;
    let mut res = vec![0; (slice.len() + RATIO - 1) / RATIO];

    for (i, &byte) in slice.iter().enumerate() {
        let idx = i / RATIO;

        res[idx] |= ((byte as Single) << shift) as Single;
        shift = (shift + u8::BITS) & (Single::BITS - 1);
    }

    res.truncate(get_len(&res));
    res
}

fn from_slice_fixed<const L: usize>(slice: &[u8]) -> ([Single; L], usize) {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let mut shift = 0;
    let mut res = [0; L];

    for (i, &byte) in slice.iter().enumerate().take(RATIO * L) {
        let idx = i / RATIO;

        res[idx] |= ((byte as Single) << shift) as Single;
        shift = (shift + u8::BITS) & (Single::BITS - 1);
    }

    (res, get_len(&res))
}

fn try_from_slice_fixed<const L: usize>(slice: &[u8]) -> Result<([Single; L], usize), TryFromSliceError> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (slice.len() + RATIO - 1) / RATIO;

    if len > L {
        return Err(TryFromSliceError::ExceedLength { len, max: L });
    }

    let mut shift = 0;
    let mut res = [0; L];

    for (i, &byte) in slice.iter().enumerate() {
        let idx = i / RATIO;

        res[idx] |= ((byte as Single) << shift) as Single;
        shift = (shift + u8::BITS) & (Single::BITS - 1);
    }

    Ok((res, get_len(&res)))
}

fn try_from_str_long(s: &str) -> Result<(Sign, Vec<Single>), TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    let res = try_from_digits_long(&digits, radix)?;

    let sign = get_sign(res.len(), sign);

    Ok((sign, res))
}

fn try_from_str_fixed<const L: usize>(s: &str) -> Result<(Sign, [Single; L], usize), TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    let (res, len) = try_from_digits_fixed(&digits, radix)?;

    let sign = get_sign(len, sign);

    Ok((sign, res, len))
}

fn try_from_digits_validate(digits: &[u8], radix: u16) -> Result<(), TryFromDigitsError> {
    if let Some(&digit) = digits.iter().find(|&&digit| digit as u16 >= radix) {
        return Err(TryFromDigitsError::InvalidDigit {
            digit: digit as Single,
            radix: radix as Double,
        });
    }

    Ok(())
}

fn try_from_digits_long_bin(digits: &[u8], pow: u8) -> Result<Vec<Single>, TryFromDigitsError> {
    if !(1..=u8::BITS).contains(&(pow as u32)) {
        return Err(TryFromDigitsError::InvalidPow { pow });
    }

    let radix = (1 << pow) as u16;

    try_from_digits_validate(digits, radix)?;

    let sbits = Single::BITS as usize;
    let rbits = pow as usize;
    let len = (digits.len() * rbits + sbits - 1) / sbits;

    let mut acc = 0;
    let mut pow = 1;
    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits.iter() {
        acc += pow * digit as Double;
        pow *= radix as Double;

        if pow >= RADIX {
            res[idx] = acc as Single;
            idx += 1;

            acc >>= Single::BITS;
            pow >>= Single::BITS;
        }
    }

    if acc > 0 {
        res[idx] = acc as Single;
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn try_from_digits_long(digits: &[u8], radix: u16) -> Result<Vec<Single>, TryFromDigitsError> {
    if !(2..=u8::MAX as u16 + 1).contains(&radix) {
        return Err(TryFromDigitsError::InvalidRadix { radix: radix as Double });
    }

    if radix & (radix - 1) == 0 {
        return try_from_digits_long_bin(digits, radix.ilog2() as u8);
    }

    try_from_digits_validate(digits, radix)?;

    let sbits = Single::BITS as usize;
    let rbits = 1 + radix.ilog2() as usize;
    let len = (digits.len() * rbits + sbits - 1) / sbits;

    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for res in res.iter_mut().take(idx + 1) {
            acc += *res as Double * radix as Double;

            *res = acc as Single;

            acc >>= Single::BITS;
        }

        if idx < len && acc > 0 {
            res[idx] += acc as Single;
        }

        if idx < len && res[idx] > 0 {
            idx += 1;
        }
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn try_from_digits_fixed_bin<const L: usize>(
    digits: &[u8],
    pow: u8,
) -> Result<([Single; L], usize), TryFromDigitsError> {
    if !(1..=u8::BITS).contains(&(pow as u32)) {
        return Err(TryFromDigitsError::InvalidPow { pow });
    }

    let radix = (1 << pow) as u16;

    try_from_digits_validate(digits, radix)?;

    let mut acc = 0;
    let mut pow = 1;
    let mut idx = 0;
    let mut res = [0; L];

    for &digit in digits.iter() {
        acc += pow * digit as Double;
        pow *= radix as Double;

        if pow >= RADIX {
            if idx == L && acc > 0 {
                return Err(TryFromDigitsError::ExceedLength { len: idx + 1, max: L });
            }

            if idx < L {
                res[idx] = acc as Single;
                idx += 1;
            }

            acc >>= Single::BITS;
            pow >>= Single::BITS;
        }
    }

    if idx == L && acc > 0 {
        return Err(TryFromDigitsError::ExceedLength { len: idx + 1, max: L });
    }

    if idx < L && acc > 0 {
        res[idx] = acc as Single;
    }

    Ok((res, get_len(&res)))
}

fn try_from_digits_fixed<const L: usize>(
    digits: &[u8],
    radix: u16,
) -> Result<([Single; L], usize), TryFromDigitsError> {
    if !(2..=u8::MAX as u16 + 1).contains(&radix) {
        return Err(TryFromDigitsError::InvalidRadix { radix: radix as Double });
    }

    if radix & (radix - 1) == 0 {
        return try_from_digits_fixed_bin(digits, radix.ilog2() as u8);
    }

    try_from_digits_validate(digits, radix)?;

    let mut idx = 0;
    let mut res = [0; L];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for (i, res) in res.iter_mut().enumerate().take(idx + 1) {
            acc += *res as Double * radix as Double;

            *res = acc as Single;

            acc >>= Single::BITS;

            if i + 1 == L && acc > 0 {
                return Err(TryFromDigitsError::ExceedLength { len: idx + 1, max: L });
            }
        }

        if idx < L && acc > 0 {
            res[idx] += acc as Single;
        }

        if idx < L && res[idx] > 0 {
            idx += 1;
        }
    }

    Ok((res, get_len(&res)))
}

fn into_radix_bin(digits: &[Single], pow: u8) -> Result<Vec<Single>, IntoRadixError> {
    if !(1..=Single::BITS).contains(&(pow as u32)) {
        return Err(IntoRadixError::InvalidPow { pow });
    }

    let radix = (1 << pow) as Double;
    let mask = radix - 1;
    let pow = pow as Double;

    let sbits = Single::BITS as usize;
    let rbits = pow as usize;
    let len = (digits.len() * sbits + rbits - 1) / rbits;

    let mut acc = 0;
    let mut rem = 0;
    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits {
        acc |= (digit as Double) << rem;
        rem += sbits as Double;

        while acc >= radix {
            res[idx] = (acc & mask) as Single;
            idx += 1;

            acc >>= pow;
            rem -= pow;
        }
    }

    if acc > 0 {
        res[idx] = acc as Single;
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn into_radix(digits: &mut [Single], radix: Double) -> Result<Vec<Single>, IntoRadixError> {
    if !(2..=RADIX).contains(&radix) {
        return Err(IntoRadixError::InvalidRadix { radix });
    }

    if radix & (radix - 1) == 0 {
        return into_radix_bin(digits, radix.ilog2() as u8);
    }

    let sbits = Single::BITS as usize;
    let rbits = 1 + radix.ilog2() as usize;
    let len = (digits.len() * sbits + rbits - 1) / rbits;

    let mut idx = 0;
    let mut res = vec![0; len];
    let mut len = digits.len();

    loop {
        let mut any = 0;
        let mut acc = 0;

        for digit in digits.iter_mut().take(len).rev() {
            any |= *digit;
            acc = (acc << Single::BITS) | *digit as Double;

            *digit = (acc / radix) as Single;

            acc %= radix;
        }

        if any == 0 {
            break;
        }

        res[idx] = acc as Single;
        idx += 1;
        len -= digits.iter().take(len).rev().position(|&digit| digit > 0).unwrap_or(len);
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn cmp_nums(a: &[Single], b: &[Single]) -> Ordering {
    match a.len().cmp(&b.len()) {
        | Ordering::Less => Ordering::Less,
        | Ordering::Equal => a
            .iter()
            .rev()
            .zip(b.iter().rev())
            .map(|(&a, &b)| a.cmp(&b))
            .find(|&x| x != Ordering::Equal)
            .unwrap_or(Ordering::Equal),
        | Ordering::Greater => Ordering::Greater,
    }
}

fn add_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, Sign::ZERO) => return Default::default(),
        | (Sign::ZERO, _) => return (b.to_vec(), bsign),
        | (_, Sign::ZERO) => return (a.to_vec(), asign),
        | _ => (),
    }

    if asign != bsign {
        return sub_long((a, asign), (b, -bsign));
    }

    let len = a.len().max(b.len()) + 1;

    let mut acc = 0;
    let mut res = vec![0; len];

    for i in 0..len {
        let aop = if i < a.len() { a[i] } else { 0 } as Double;
        let bop = if i < b.len() { b[i] } else { 0 } as Double;

        acc += aop + bop;

        res[i] = acc as Single;
        acc >>= Single::BITS;
    }

    res.truncate(get_len(&res));

    let sign = get_sign(res.len(), asign);

    (res, sign)
}

fn sub_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, Sign::ZERO) => return Default::default(),
        | (Sign::ZERO, _) => return (b.to_vec(), Sign::NEG * bsign),
        | (_, Sign::ZERO) => return (a.to_vec(), Sign::POS * asign),
        | _ => (),
    }

    if asign != bsign {
        return add_long((a, asign), (b, -bsign));
    }

    let (a, b, sign) = match cmp_nums(a, b) {
        | Ordering::Less => (b, a, asign * Sign::NEG),
        | Ordering::Equal => return Default::default(),
        | Ordering::Greater => (a, b, asign * Sign::POS),
    };

    let mut acc = 0;
    let mut res = vec![0; a.len()];

    for i in 0..a.len() {
        let aop = if i < a.len() { a[i] } else { 0 } as Double;
        let bop = if i < b.len() { b[i] } else { 0 } as Double;

        res[i] = (RADIX + aop - bop - acc) as Single;

        if aop < bop + acc {
            acc = 1;
        } else {
            acc = 0;
        }
    }

    res.truncate(get_len(&res));

    let sign = get_sign(res.len(), sign);

    (res, sign)
}

fn mul_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, _) => return Default::default(),
        | (_, Sign::ZERO) => return Default::default(),
        | _ => (),
    }

    let len = a.len() + b.len();

    let mut res = vec![0; len];

    for i in 0..a.len() {
        let mut acc = 0;

        for j in 0..b.len() {
            let aop = a[i] as Double;
            let bop = b[j] as Double;
            let rop = res[i + j] as Double;

            acc += rop + aop * bop;

            res[i + j] = acc as Single;
            acc >>= Single::BITS;
        }

        let idx = i + b.len();
        let val = acc + res[idx] as Double;

        res[idx] = val as Single;
    }

    res.truncate(get_len(&res));

    let sign = get_sign(res.len(), asign * bsign);

    (res, sign)
}

fn div_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    let (div, _, sign, _) = divrem_long((a, asign), (b, bsign));

    (div, sign)
}

fn rem_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    let (_, rem, _, sign) = divrem_long((a, asign), (b, bsign));

    (rem, sign)
}

fn divrem_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Vec<Single>, Sign, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, _) => return Default::default(),
        | (_, Sign::ZERO) => panic!("Division by zero"),
        | _ => (),
    }

    match cmp_nums(a, b) {
        | Ordering::Less => return (vec![], a.to_vec(), Sign::ZERO, asign),
        | Ordering::Equal => return (vec![1], vec![], asign * bsign, Sign::ZERO),
        | Ordering::Greater => (),
    }

    let mut div = vec![0; a.len()];
    let mut rem = vec![0; b.len() + 1];
    let mut len = 0;

    for i in (0..a.len()).rev() {
        for j in (1..len + 1).rev() {
            rem[j] = rem[j - 1];
        }

        rem[0] = a[i];
        len += 1;

        if len < b.len() {
            continue;
        }

        let mut l = 0 as Double;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;
            let s = Sign::from(m);

            let (val, _) = mul_long((b, Sign::POS), (&[m as Single], s));

            match cmp_nums(&val, &rem[..len]) {
                | Ordering::Less => l = m + 1,
                | Ordering::Equal => l = m + 1,
                | Ordering::Greater => r = m,
            }
        }

        let digit = l.saturating_sub(1) as Single;
        if digit > 0 {
            let (val, _) = mul_long((b, Sign::POS), (&[digit], Sign::POS));
            let (sub, _) = sub_long((&rem[..len], Sign::POS), (&val, Sign::POS));

            div[i] = digit;
            len = sub.len();

            rem.fill(0);

            for (j, d) in sub.iter().copied().enumerate() {
                rem[j] = d;
            }
        };
    }

    div.truncate(get_len(&div));
    rem.truncate(get_len(&rem));

    let div_sign = if div.is_empty() { Sign::ZERO } else { asign * bsign };
    let rem_sign = if rem.is_empty() { Sign::ZERO } else { asign };

    (div, rem, div_sign, rem_sign)
}

fn add_fixed<const L: usize>(
    (a, alen, asign): (&[Single; L], usize, Sign),
    (b, blen, bsign): (&[Single; L], usize, Sign),
) -> ([Single; L], usize, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, Sign::ZERO) => return ([0; L], 0, Sign::ZERO),
        | (Sign::ZERO, _) => return (*b, blen, bsign),
        | (_, Sign::ZERO) => return (*a, alen, asign),
        | _ => (),
    }

    if asign != bsign {
        return sub_fixed((a, alen, asign), (b, blen, -bsign));
    }

    let len = alen.max(blen);

    let mut acc = 0;
    let mut res = [0; L];

    for i in 0..len {
        let aop = a[i] as Double;
        let bop = b[i] as Double;

        acc += aop + bop;

        res[i] = acc as Single;
        acc >>= Single::BITS;
    }

    if len < L {
        res[len] = acc as Single;
    }

    let len = get_len(&res);
    let sign = get_sign(len, asign);

    (res, len, sign)
}

fn sub_fixed<const L: usize>(
    (a, alen, asign): (&[Single; L], usize, Sign),
    (b, blen, bsign): (&[Single; L], usize, Sign),
) -> ([Single; L], usize, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, Sign::ZERO) => return ([0; L], 0, Sign::ZERO),
        | (Sign::ZERO, _) => return (*b, blen, Sign::NEG * bsign),
        | (_, Sign::ZERO) => return (*a, alen, Sign::POS * asign),
        | _ => (),
    }

    if asign != bsign {
        return add_fixed((a, alen, asign), (b, blen, -bsign));
    }

    let (a, alen, b, _, sign) = match cmp_nums(a, b) {
        | Ordering::Less => (b, blen, a, alen, asign * Sign::NEG),
        | Ordering::Equal => return ([0; L], 0, Sign::ZERO),
        | Ordering::Greater => (a, alen, b, blen, asign * Sign::POS),
    };

    let mut acc = 0;
    let mut res = [0; L];

    for i in 0..alen {
        let aop = a[i] as Double;
        let bop = b[i] as Double;

        res[i] = (RADIX + aop - bop - acc) as Single;

        if aop < bop + acc {
            acc = 1;
        } else {
            acc = 0;
        }
    }

    let len = get_len(&res);
    let sign = get_sign(res.len(), sign);

    (res, len, sign)
}

fn mul_fixed<const L: usize>(
    (a, alen, asign): (&[Single; L], usize, Sign),
    (b, blen, bsign): (&[Single; L], usize, Sign),
) -> ([Single; L], usize, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, _) => return ([0; L], 0, Sign::ZERO),
        | (_, Sign::ZERO) => return ([0; L], 0, Sign::ZERO),
        | _ => (),
    }

    let mut res = [0; L];

    for i in 0..alen {
        let mut acc = 0;

        for j in 0..blen.min(L - i) {
            let aop = a[i] as Double;
            let bop = b[j] as Double;
            let rop = res[i + j] as Double;

            acc += rop + aop * bop;

            res[i + j] = acc as Single;
            acc >>= Single::BITS;
        }

        if i + blen < L {
            let idx = i + blen;
            let val = acc + res[idx] as Double;

            res[idx] = val as Single;
        }
    }

    let len = get_len(&res);
    let sign = get_sign(len, asign * bsign);

    (res, len, sign)
}

fn div_fixed<const L: usize>(
    (a, alen, asign): (&[Single; L], usize, Sign),
    (b, blen, bsign): (&[Single; L], usize, Sign),
) -> ([Single; L], usize, Sign) {
    let (div, _, len, _, sign, _) = divrem_fixed((a, alen, asign), (b, blen, bsign));

    (div, len, sign)
}

fn rem_fixed<const L: usize>(
    (a, alen, asign): (&[Single; L], usize, Sign),
    (b, blen, bsign): (&[Single; L], usize, Sign),
) -> ([Single; L], usize, Sign) {
    let (_, rem, _, len, _, sign) = divrem_fixed((a, alen, asign), (b, blen, bsign));

    (rem, len, sign)
}

fn divrem_fixed<const L: usize>(
    (a, alen, asign): (&[Single; L], usize, Sign),
    (b, blen, bsign): (&[Single; L], usize, Sign),
) -> ([Single; L], [Single; L], usize, usize, Sign, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, _) => {
            return ([0; L], [0; L], 0, 0, Sign::ZERO, Sign::ZERO);
        },
        | (_, Sign::ZERO) => panic!("Division by zero"),
        | _ => (),
    }

    match cmp_nums(a, b) {
        | Ordering::Less => return ([0; L], *a, 0, alen, Sign::ZERO, asign),
        | Ordering::Equal => return (get_arr::<L>(1), [0; L], 1, 0, asign * bsign, Sign::ZERO),
        | Ordering::Greater => (),
    }

    // TODO: Find a way to make this static array
    let mut div = vec![0; L];
    let mut rem = vec![0; L + 1];
    let mut len = 0;

    for i in (0..alen).rev() {
        for j in (1..len + 1).rev() {
            rem[j] = rem[j - 1];
        }

        rem[0] = a[i];
        len += 1;

        if len < blen {
            continue;
        }

        let mut l = 0 as Double;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;
            let s = Sign::from(m);

            let (val, _, _) = mul_fixed((b, blen, Sign::POS), (&get_arr::<L>(m as Single), 1, s));
            let remop = rem.first_chunk().unwrap_or(&[0; L]);

            match cmp_nums(&val, remop) {
                | Ordering::Less => l = m + 1,
                | Ordering::Equal => l = m + 1,
                | Ordering::Greater => r = m,
            }
        }

        let digit = l.saturating_sub(1) as Single;
        if digit > 0 {
            let remop = rem.first_chunk().unwrap_or(&[0; L]);

            let (val, val_len, _) = mul_fixed((b, blen, Sign::POS), (&get_arr::<L>(digit), 1, Sign::POS));
            let (sub, sub_len, _) = sub_fixed((remop, len, Sign::POS), (&val, val_len, Sign::POS));

            div[i] = digit;
            len = sub_len;

            rem.fill(0);

            for (j, d) in sub.iter().copied().enumerate() {
                rem[j] = d;
            }
        };
    }

    let div = *div.first_chunk().unwrap_or(&[0; L]);
    let rem = *rem.first_chunk().unwrap_or(&[0; L]);

    let div_len = get_len(&div);
    let rem_len = get_len(&rem);

    let div_sign = if div_len == 0 { Sign::ZERO } else { asign * bsign };
    let rem_sign = if rem_len == 0 { Sign::ZERO } else { asign };

    (div, rem, div_len, rem_len, div_sign, rem_sign)
}

ops_impl!(@bin |a: Sign, b: Sign| -> Sign,
* {
    match (a, b) {
        (Sign::ZERO, _) => Sign::ZERO,
        (_, Sign::ZERO) => Sign::ZERO,
        (Sign::NEG, Sign::NEG) => Sign::POS,
        (Sign::NEG, Sign::POS) => Sign::NEG,
        (Sign::POS, Sign::NEG) => Sign::NEG,
        (Sign::POS, Sign::POS) => Sign::POS,
    }
});

ops_impl!(@un |a: Sign| -> Sign,
- {
    match a {
        Sign::ZERO => Sign::ZERO,
        Sign::NEG => Sign::POS,
        Sign::POS => Sign::NEG,
    }
});

ops_impl!(@un |a: &SignedLong| -> SignedLong, - SignedLong { sign: -a.sign, data: a.data.clone() });

ops_impl!(@bin |a: &SignedLong, b: &SignedLong| -> SignedLong,
    + SignedLong::from_raw(add_long((&a.data, a.sign), (&b.data, b.sign))),
    - SignedLong::from_raw(sub_long((&a.data, a.sign), (&b.data, b.sign))),
    * SignedLong::from_raw(mul_long((&a.data, a.sign), (&b.data, b.sign))),
    / SignedLong::from_raw(div_long((&a.data, a.sign), (&b.data, b.sign))),
    % SignedLong::from_raw(rem_long((&a.data, a.sign), (&b.data, b.sign))));

ops_impl!(@bin |a: &UnsignedLong, b: &UnsignedLong| -> UnsignedLong,
    + UnsignedLong::from_raw(add_long((&a.data, get_sign(a.data.len(), Sign::POS)), (&b.data, get_sign(b.data.len(), Sign::POS)))),
    - UnsignedLong::from_raw(sub_long((&a.data, get_sign(a.data.len(), Sign::POS)), (&b.data, get_sign(b.data.len(), Sign::POS)))),
    * UnsignedLong::from_raw(mul_long((&a.data, get_sign(a.data.len(), Sign::POS)), (&b.data, get_sign(b.data.len(), Sign::POS)))),
    / UnsignedLong::from_raw(div_long((&a.data, get_sign(a.data.len(), Sign::POS)), (&b.data, get_sign(b.data.len(), Sign::POS)))),
    % UnsignedLong::from_raw(rem_long((&a.data, get_sign(a.data.len(), Sign::POS)), (&b.data, get_sign(b.data.len(), Sign::POS)))));

ops_impl!(@un <const L: usize> |a: &SignedFixed<L>| -> SignedFixed<L>, - SignedFixed::<L> { sign: -a.sign, data: a.data, len: a.len });

ops_impl!(@bin <const L: usize> |a: &SignedFixed<L>, b: &SignedFixed<L>| -> SignedFixed<L>,
    + SignedFixed::<L>::from_raw(add_fixed((&a.data, a.len, a.sign), (&b.data, b.len, b.sign))),
    - SignedFixed::<L>::from_raw(sub_fixed((&a.data, a.len, a.sign), (&b.data, b.len, b.sign))),
    * SignedFixed::<L>::from_raw(mul_fixed((&a.data, a.len, a.sign), (&b.data, b.len, b.sign))),
    / SignedFixed::<L>::from_raw(div_fixed((&a.data, a.len, a.sign), (&b.data, b.len, b.sign))),
    % SignedFixed::<L>::from_raw(rem_fixed((&a.data, a.len, a.sign), (&b.data, b.len, b.sign))));

ops_impl!(@bin <const L: usize> |a: &UnsignedFixed<L>, b: &UnsignedFixed<L>| -> UnsignedFixed<L>,
    + UnsignedFixed::<L>::from_raw(add_fixed((&a.data, a.len, get_sign(a.len, Sign::POS)), (&b.data, b.len, get_sign(b.len, Sign::POS)))),
    - UnsignedFixed::<L>::from_raw(sub_fixed((&a.data, a.len, get_sign(a.len, Sign::POS)), (&b.data, b.len, get_sign(b.len, Sign::POS)))),
    * UnsignedFixed::<L>::from_raw(mul_fixed((&a.data, a.len, get_sign(a.len, Sign::POS)), (&b.data, b.len, get_sign(b.len, Sign::POS)))),
    / UnsignedFixed::<L>::from_raw(div_fixed((&a.data, a.len, get_sign(a.len, Sign::POS)), (&b.data, b.len, get_sign(b.len, Sign::POS)))),
    % UnsignedFixed::<L>::from_raw(rem_fixed((&a.data, a.len, get_sign(a.len, Sign::POS)), (&b.data, b.len, get_sign(b.len, Sign::POS)))));

fn get_sign_from_str(s: &str) -> Result<(&str, Sign), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    let bytes = s.as_bytes();

    let val = match bytes[0] {
        | b'+' => (&s[1..], Sign::POS),
        | b'-' => (&s[1..], Sign::NEG),
        | _ => (s, Sign::POS),
    };

    Ok(val)
}

fn get_radix_from_str(s: &str) -> Result<(&str, u16), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    if s.len() < 2 {
        return Ok((s, 10));
    }

    let bytes = s.as_bytes();

    let val = match &bytes[..2] {
        | b"0x" | b"0X" => (&s[2..], 16),
        | b"0o" | b"0O" => (&s[2..], 8),
        | b"0b" | b"0B" => (&s[2..], 2),
        | _ => (s, 10),
    };

    Ok(val)
}

fn get_digits_from_str(s: &str, radix: u16) -> Result<Vec<u8>, TryFromStrError> {
    let r = radix as u8;

    let mut res = s
        .as_bytes()
        .iter()
        .rev()
        .filter_map(|&ch| match ch {
            | b'0'..=b'9' if ch - b'0' < r => Some(Ok(ch - b'0')),
            | b'a'..=b'f' if ch - b'a' + 10 < r => Some(Ok(ch - b'a' + 10)),
            | b'A'..=b'F' if ch - b'A' + 10 < r => Some(Ok(ch - b'A' + 10)),
            | b'_' => None,
            | _ => Some(Err(TryFromStrError::InvalidSymbol { ch: ch as char, radix })),
        })
        .collect::<Result<Vec<u8>, TryFromStrError>>()?;

    let mut len = res.len();

    for &digit in res.iter().rev() {
        if digit > 0 {
            break;
        }

        len -= 1;
    }

    res.truncate(len);

    Ok(res)
}

fn get_len<T: Constants + PartialEq + Eq>(data: &[T]) -> usize {
    let mut len = data.len();

    for digit in data.iter().rev() {
        if digit != &T::ZERO {
            return len;
        }

        len -= 1;
    }

    0
}

fn get_sign(len: usize, default: Sign) -> Sign {
    if len > 0 { default } else { Sign::ZERO }
}

fn get_arr<const L: usize>(val: Single) -> [Single; L] {
    let mut res = [0; L];

    res[0] = val;
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    type S32 = signed_fixed!(32);
    type U32 = unsigned_fixed!(32);

    macro_rules! assert_long_from {
        (@signed $expr:expr, $data:expr, $sign:expr) => {
            assert_eq!(SignedLong::from($expr), SignedLong { sign: $sign, data: $data });
        };
        (@unsigned $expr:expr, $data:expr) => {
            assert_eq!(UnsignedLong::from($expr), UnsignedLong { data: $data });
        };
    }

    macro_rules! assert_fixed_from {
        (@signed $expr:expr, $data:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::from($expr),
                S32 {
                    sign: $sign,
                    data: $data,
                    len: $len
                }
            );
        };
        (@unsigned $expr:expr, $data:expr, $len:expr) => {
            assert_eq!(U32::from($expr), U32 { data: $data, len: $len });
        };
    }

    macro_rules! assert_long_from_slice {
        (@signed $expr:expr, $data:expr, $sign:expr) => {
            assert_eq!(SignedLong::from_slice($expr), SignedLong { sign: $sign, data: $data });
        };
        (@unsigned $expr:expr, $data:expr) => {
            assert_eq!(UnsignedLong::from_slice($expr), UnsignedLong { data: $data });
        };
    }

    macro_rules! assert_fixed_from_slice {
        (@signed $expr:expr, $data:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::from_slice($expr),
                S32 {
                    sign: $sign,
                    data: $data,
                    len: $len
                }
            );
        };
        (@unsigned $expr:expr, $data:expr, $len:expr) => {
            assert_eq!(U32::from_slice($expr), U32 { data: $data, len: $len });
        };
    }

    macro_rules! assert_long_from_digits {
        (@signed $expr:expr, $radix:expr, $data:expr, $sign:expr) => {
            assert_eq!(
                SignedLong::try_from_digits($expr, $radix),
                Ok(SignedLong { sign: $sign, data: $data })
            );
        };
        (@unsigned $expr:expr, $radix:expr, $data:expr) => {
            assert_eq!(UnsignedLong::try_from_digits($expr, $radix), Ok(UnsignedLong { data: $data }));
        };
    }

    macro_rules! assert_fixed_from_digits {
        (@signed $expr:expr, $radix:expr, $data:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::try_from_digits($expr, $radix),
                Ok(S32 {
                    sign: $sign,
                    data: $data,
                    len: $len
                })
            );
        };
        (@unsigned $expr:expr, $radix:expr, $data:expr, $len:expr) => {
            assert_eq!(U32::try_from_digits($expr, $radix), Ok(U32 { data: $data, len: $len }));
        };
    }

    macro_rules! assert_long_from_str {
        (@signed $expr:expr, $data:expr, $sign:expr) => {
            assert_eq!(SignedLong::from_str($expr), Ok(SignedLong { sign: $sign, data: $data }));
        };
        (@unsigned $expr:expr, $data:expr) => {
            assert_eq!(UnsignedLong::from_str($expr), Ok(UnsignedLong { data: $data }));
        };
    }

    macro_rules! assert_fixed_from_str {
        (@signed $expr:expr, $data:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::from_str($expr),
                Ok(S32 {
                    sign: $sign,
                    data: $data,
                    len: $len
                })
            );
        };
        (@unsigned $expr:expr, $data:expr, $len:expr) => {
            assert_eq!(U32::from_str($expr), Ok(U32 { data: $data, len: $len }));
        };
    }

    macro_rules! assert_long_into_radix {
        (@signed $expr:expr, $radix:expr) => {
            assert_eq!(
                SignedLong::try_from_digits($expr, $radix)?.into_radix($radix)?,
                normalized($expr)
            );
        };
        (@unsigned $expr:expr, $radix:expr) => {
            assert_eq!(
                UnsignedLong::try_from_digits($expr, $radix)?.into_radix($radix)?,
                normalized($expr)
            );
        };
    }

    macro_rules! assert_fixed_into_radix {
        (@signed $expr:expr, $len:expr, $radix:expr) => {
            assert_eq!(
                S32::try_from_digits($expr, $radix)?.into_radix($radix)?,
                $expr.iter().take($len).copied().collect::<Vec<_>>()
            );
        };
        (@unsigned $expr:expr, $len:expr, $radix:expr) => {
            assert_eq!(
                U32::try_from_digits($expr, $radix)?.into_radix($radix)?,
                $expr.iter().take($len).copied().collect::<Vec<_>>()
            );
        };
    }

    fn normalized(val: &[u8]) -> Vec<u8> {
        let len = get_len(val);

        val[..len].to_vec()
    }

    #[test]
    fn from_std_long() {
        for val in u16::MIN..=u16::MAX {
            let bytes = (val as u32).to_le_bytes();

            let pval = val as i32;
            let nval = -pval;

            let sign_pos = Sign::from(pval);
            let sign_neg = Sign::from(nval);

            assert_long_from!(@signed pval, normalized(&bytes), sign_pos);
            assert_long_from!(@signed nval, normalized(&bytes), sign_neg);
            assert_long_from!(@unsigned val, normalized(&bytes));
        }
    }

    #[test]
    fn from_std_fixed() {
        for val in u16::MIN..=u16::MAX {
            let bytes = (val as u32).to_le_bytes();

            let pval = val as i32;
            let nval = -pval;

            let sign_pos = Sign::from(pval);
            let sign_neg = Sign::from(nval);

            assert_fixed_from!(@signed pval, bytes, get_len(&bytes), sign_pos);
            assert_fixed_from!(@signed nval, bytes, get_len(&bytes), sign_neg);
            assert_fixed_from!(@unsigned val, bytes, get_len(&bytes));
        }
    }

    #[test]
    fn from_slice_long() {
        assert_eq!(SignedLong::from_slice(&[]), SignedLong::default());
        assert_eq!(UnsignedLong::from_slice(&[]), UnsignedLong::default());

        for val in u16::MIN..=u16::MAX {
            let bytes = (val as u32).to_le_bytes();

            assert_long_from_slice!(@signed &bytes, normalized(&bytes), Sign::from(val));
            assert_long_from_slice!(@unsigned &bytes, normalized(&bytes));
        }
    }

    #[test]
    fn from_slice_fixed() {
        assert_eq!(S32::from_slice(&[]), S32::default());
        assert_eq!(U32::from_slice(&[]), U32::default());

        for val in u16::MIN..=u16::MAX {
            let bytes = (val as u32).to_le_bytes();

            assert_fixed_from_slice!(@signed &bytes, bytes, get_len(&bytes), Sign::from(val));
            assert_fixed_from_slice!(@unsigned &bytes, bytes, get_len(&bytes));
        }
    }

    #[test]
    fn from_digits_long() {
        assert_eq!(SignedLong::try_from_digits(&[], 31), Ok(SignedLong::default()));
        assert_eq!(UnsignedLong::try_from_digits(&[], 31), Ok(UnsignedLong::default()));

        assert_long_from_digits!(@signed &[30, 30, 0, 0], 31, vec![192, 3], Sign::POS);
        assert_long_from_digits!(@unsigned &[30, 30, 0, 0], 31, vec![192, 3]);

        assert_long_from_digits!(@signed &[30, 30, 30, 30], 31, vec![128, 23, 14], Sign::POS);
        assert_long_from_digits!(@unsigned &[30, 30, 30, 30], 31, vec![128, 23, 14]);

        assert_long_from_digits!(@signed &[30, 30, 0, 0], 32, vec![222, 3], Sign::POS);
        assert_long_from_digits!(@unsigned &[30, 30, 0, 0], 32, vec![222, 3]);

        assert_long_from_digits!(@signed &[30, 30, 30, 30], 32, vec![222, 123, 15], Sign::POS);
        assert_long_from_digits!(@unsigned &[30, 30, 30, 30], 32, vec![222, 123, 15]);
    }

    #[test]
    fn from_digits_fixed() {
        assert_eq!(S32::try_from_digits(&[], 31), Ok(S32::default()));
        assert_eq!(U32::try_from_digits(&[], 31), Ok(U32::default()));

        assert_fixed_from_digits!(@signed &[30, 30, 0, 0], 31, [192, 3, 0, 0], 2, Sign::POS);
        assert_fixed_from_digits!(@unsigned &[30, 30, 0, 0], 31, [192, 3, 0, 0], 2);

        assert_fixed_from_digits!(@signed &[30, 30, 30, 30], 31, [128, 23, 14, 0], 3, Sign::POS);
        assert_fixed_from_digits!(@unsigned &[30, 30, 30, 30], 31, [128, 23, 14, 0], 3);

        assert_fixed_from_digits!(@signed &[30, 30, 0, 0], 32, [222, 3, 0, 0], 2, Sign::POS);
        assert_fixed_from_digits!(@unsigned &[30, 30, 0, 0], 32, [222, 3, 0, 0], 2);

        assert_fixed_from_digits!(@signed &[30, 30, 30, 30], 32, [222, 123, 15, 0], 3, Sign::POS);
        assert_fixed_from_digits!(@unsigned &[30, 30, 30, 30], 32, [222, 123, 15, 0], 3);
    }

    #[test]
    fn from_str_long() {
        for val in (u16::MIN..=u16::MAX).step_by(7) {
            let dec_pos = format!("{:#020}", val);
            let bin_pos = format!("{:#020b}", val);
            let oct_pos = format!("{:#020o}", val);
            let hex_pos = format!("{:#020x}", val);

            let dec_neg = format!("-{:#020}", val);
            let bin_neg = format!("-{:#020b}", val);
            let oct_neg = format!("-{:#020o}", val);
            let hex_neg = format!("-{:#020x}", val);

            let bytes = val.to_le_bytes();

            let (sign_pos, sign_neg) = if val > 0 {
                (Sign::POS, Sign::NEG)
            } else {
                (Sign::ZERO, Sign::ZERO)
            };

            assert_long_from_str!(@signed &dec_pos, normalized(&bytes), sign_pos);
            assert_long_from_str!(@signed &bin_pos, normalized(&bytes), sign_pos);
            assert_long_from_str!(@signed &oct_pos, normalized(&bytes), sign_pos);
            assert_long_from_str!(@signed &hex_pos, normalized(&bytes), sign_pos);

            assert_long_from_str!(@signed &dec_neg, normalized(&bytes), sign_neg);
            assert_long_from_str!(@signed &bin_neg, normalized(&bytes), sign_neg);
            assert_long_from_str!(@signed &oct_neg, normalized(&bytes), sign_neg);
            assert_long_from_str!(@signed &hex_neg, normalized(&bytes), sign_neg);

            assert_long_from_str!(@unsigned &dec_pos, normalized(&bytes));
            assert_long_from_str!(@unsigned &bin_pos, normalized(&bytes));
            assert_long_from_str!(@unsigned &oct_pos, normalized(&bytes));
            assert_long_from_str!(@unsigned &hex_pos, normalized(&bytes));
        }
    }

    #[test]
    fn from_str_fixed() {
        for val in (u16::MIN..=u16::MAX).step_by(7) {
            let dec_pos = format!("{:#020}", val);
            let bin_pos = format!("{:#020b}", val);
            let oct_pos = format!("{:#020o}", val);
            let hex_pos = format!("{:#020x}", val);

            let dec_neg = format!("-{:#020}", val);
            let bin_neg = format!("-{:#020b}", val);
            let oct_neg = format!("-{:#020o}", val);
            let hex_neg = format!("-{:#020x}", val);

            let bytes = (val as u32).to_le_bytes();

            let (sign_pos, sign_neg) = if val > 0 {
                (Sign::POS, Sign::NEG)
            } else {
                (Sign::ZERO, Sign::ZERO)
            };

            assert_fixed_from_str!(@signed &dec_pos, bytes, get_len(&bytes), sign_pos);
            assert_fixed_from_str!(@signed &bin_pos, bytes, get_len(&bytes), sign_pos);
            assert_fixed_from_str!(@signed &oct_pos, bytes, get_len(&bytes), sign_pos);
            assert_fixed_from_str!(@signed &hex_pos, bytes, get_len(&bytes), sign_pos);

            assert_fixed_from_str!(@signed &dec_neg, bytes, get_len(&bytes), sign_neg);
            assert_fixed_from_str!(@signed &bin_neg, bytes, get_len(&bytes), sign_neg);
            assert_fixed_from_str!(@signed &oct_neg, bytes, get_len(&bytes), sign_neg);
            assert_fixed_from_str!(@signed &hex_neg, bytes, get_len(&bytes), sign_neg);

            assert_fixed_from_str!(@unsigned &dec_pos, bytes, get_len(&bytes));
            assert_fixed_from_str!(@unsigned &bin_pos, bytes, get_len(&bytes));
            assert_fixed_from_str!(@unsigned &oct_pos, bytes, get_len(&bytes));
            assert_fixed_from_str!(@unsigned &hex_pos, bytes, get_len(&bytes));
        }
    }

    #[test]
    fn into_radix_long() -> anyhow::Result<()> {
        assert_eq!(SignedLong::try_from_digits(&[], 31)?.into_radix(31)?, vec![]);
        assert_eq!(UnsignedLong::try_from_digits(&[], 31)?.into_radix(31)?, vec![]);

        let radixes = [31, 32, 33, 127, 128, 129, 101, 103];
        let entries = [[0, 0, 0, 0], [7, 11, 0, 0], [7, 11, 13, 19], [0, 0, 13, 19]];

        for &radix in &radixes {
            for entry in &entries {
                assert_long_into_radix!(@signed entry, radix as u16);
                assert_long_into_radix!(@unsigned entry, radix as u16);
            }
        }

        Ok(())
    }

    #[test]
    fn into_radix_fixed() -> anyhow::Result<()> {
        assert_eq!(S32::try_from_digits(&[], 31)?.into_radix(31)?, vec![]);
        assert_eq!(U32::try_from_digits(&[], 31)?.into_radix(31)?, vec![]);

        let radixes = [31, 32, 33, 127, 128, 129, 101, 103];
        let entries = [[0, 0, 0, 0], [7, 11, 0, 0], [7, 11, 13, 19], [0, 0, 13, 19]];

        for &radix in &radixes {
            for entry in &entries {
                assert_fixed_into_radix!(@signed entry, get_len(entry), radix as u16);
                assert_fixed_into_radix!(@unsigned entry, get_len(entry), radix as u16);
            }
        }

        Ok(())
    }

    #[test]
    fn addsub_long() {
        for aop in (i16::MIN..=i16::MAX).step_by(211) {
            for bop in (i16::MIN..=i16::MAX).step_by(307) {
                let aop = aop as i32;
                let bop = bop as i32;

                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                assert_eq!(a + b, SignedLong::from(aop + bop));
                assert_eq!(a - b, SignedLong::from(aop - bop));
            }
        }
    }

    #[test]
    fn muldiv_long() {
        for aop in (i16::MIN..=i16::MAX).step_by(211) {
            for bop in (i16::MIN..=i16::MAX).step_by(307) {
                let aop = aop as i32;
                let bop = bop as i32;

                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                assert_eq!(a * b, SignedLong::from(aop * bop));
                assert_eq!(a / b, SignedLong::from(aop / bop));
                assert_eq!(a % b, SignedLong::from(aop % bop));
            }
        }
    }

    #[test]
    fn addsub_fixed() {
        for aop in (i16::MIN..=i16::MAX).step_by(211) {
            for bop in (i16::MIN..=i16::MAX).step_by(307) {
                let aop = aop as i32;
                let bop = bop as i32;

                let a = &S32::from(aop);
                let b = &S32::from(bop);

                assert_eq!(a + b, S32::from(aop + bop));
                assert_eq!(a - b, S32::from(aop - bop));
            }
        }
    }

    #[test]
    fn muldiv_fixed() {
        for aop in (i16::MIN..=i16::MAX).step_by(211) {
            for bop in (i16::MIN..=i16::MAX).step_by(307) {
                let aop = aop as i32;
                let bop = bop as i32;

                let a = &S32::from(aop);
                let b = &S32::from(bop);

                assert_eq!(a * b, S32::from(aop * bop));
                assert_eq!(a / b, S32::from(aop / bop));
                assert_eq!(a % b, S32::from(aop % bop));
            }
        }
    }
}

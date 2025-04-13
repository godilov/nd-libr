#![allow(clippy::manual_div_ceil)]

use crate::ops::{AddChecked, DivChecked, MulChecked, Ops, OpsAll, OpsAllAssign, OpsAssign, OpsChecked, SubChecked};
use digit::{Double, Single};
use proc::ops_impl;
use radix::{Bin, Dec, Hex, Oct, RADIX, Radix};
use std::{
    cmp::Ordering,
    fmt::{Binary, Display, Formatter, LowerHex, Octal, UpperHex, Write},
    iter::{once, repeat_n},
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

macro_rules! radix_impl {
    ([$($type:ty),+]) => {
        $(radix_impl!($type);)+
    };
    ($type:ty) => {
        impl Radix for $type {
            const VAL: Double = Self::RADIX;
            const WIDTH: u8 = Self::WIDTH;
            const PREFIX: &str = Self::PREFIX;
        }
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

                let mut res = vec![0; LEN];
                let mut idx = 0;
                let mut val = value.abs_diff(0);

                while val > 0 {
                    res[idx] = val as Single;
                    idx += 1;
                    val = val.checked_shr(Single::BITS).unwrap_or(0);
                }

                let len = get_len(&res);

                res.truncate(len);

                Self(res $(, $pos * Sign::from(value))?)
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

                let mut res = [0; L];
                let mut idx = 0;
                let mut val = value.abs_diff(0);

                while idx < L && val > 0 {
                    res[idx] = val as Single;
                    idx += 1;
                    val = val.checked_shr(Single::BITS).unwrap_or(0);
                }

                let len = get_len(&res);

                Self(res, len $(, if len > 0 { $pos * Sign::from(value) } else { Sign::ZERO })?)
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
pub type S6144 = signed_fixed!(6144);
pub type S8192 = signed_fixed!(8192);

pub type U128 = unsigned_fixed!(128);
pub type U192 = unsigned_fixed!(192);
pub type U256 = unsigned_fixed!(256);
pub type U384 = unsigned_fixed!(384);
pub type U512 = unsigned_fixed!(512);
pub type U1024 = unsigned_fixed!(1024);
pub type U2048 = unsigned_fixed!(2048);
pub type U3072 = unsigned_fixed!(3072);
pub type U4096 = unsigned_fixed!(4096);
pub type U6144 = unsigned_fixed!(6144);
pub type U8192 = unsigned_fixed!(8192);

#[cfg(all(target_pointer_width = "64", not(test)))]
pub mod digit {
    pub type Single = u64;
    pub type Double = u128;

    pub(super) const OCT_VAL: Double = (1 as Double) << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_VAL: Double = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;
}

#[cfg(all(target_pointer_width = "32", not(test)))]
pub mod digit {
    pub type Single = u32;
    pub type Double = u64;

    pub(super) const OCT_VAL: Double = (1 as Double) << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_VAL: Double = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;
}

#[cfg(test)]
pub mod digit {
    pub type Single = u8;
    pub type Double = u16;

    pub(super) const OCT_VAL: Double = (1 as Double) << 6;
    pub(super) const OCT_WIDTH: u8 = 2;

    pub(super) const DEC_VAL: Double = 100;
    pub(super) const DEC_WIDTH: u8 = 2;
}

mod radix {
    use super::{
        Double, Single,
        digit::{DEC_VAL, DEC_WIDTH, OCT_VAL, OCT_WIDTH},
    };

    pub(super) const RADIX: Double = Single::MAX as Double + 1;

    pub trait Radix {
        const VAL: Double = Single::MAX as Double + 1;
        const WIDTH: u8;
        const PREFIX: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Bin {
        pub const RADIX: Double = Single::MAX as Double + 1;
        pub const WIDTH: u8 = Single::BITS as u8;
        pub const PREFIX: &str = "0b";
    }

    impl Oct {
        pub const RADIX: Double = OCT_VAL;
        pub const WIDTH: u8 = OCT_WIDTH;
        pub const PREFIX: &str = "0o";
    }

    impl Dec {
        pub const RADIX: Double = DEC_VAL;
        pub const WIDTH: u8 = DEC_WIDTH;
        pub const PREFIX: &str = "";
    }

    impl Hex {
        pub const RADIX: Double = Single::MAX as Double + 1;
        pub const WIDTH: u8 = Single::BITS as u8 / 4;
        pub const PREFIX: &str = "0x";
    }

    radix_impl!([Bin, Oct, Dec, Hex]);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: Double },
    #[error("Found invalid radix pow '{pow}'")]
    InvalidPow { pow: u8 },
    #[error("Found invalid value '{digit}' for radix '{radix}'")]
    InvalidDigit { digit: Single, radix: Double },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum IntoRadixError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: Double },
    #[error("Found invalid radix pow '{pow}'")]
    InvalidPow { pow: u8 },
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedLong(Vec<Single>, Sign);

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedLong(Vec<Single>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedFixed<const L: usize>([Single; L], usize, Sign);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedFixed<const L: usize>([Single; L], usize);

#[derive(Debug, Default)]
struct LongRepr(Vec<Single>, Sign);

#[derive(Debug)]
struct FixedRepr<const L: usize>([Single; L], usize, Sign, Single, bool);

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Operand<'digits>(&'digits [Single], Sign);

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

int_impl!(Signed, [i8, i16, i32, i64, i128, isize]);
int_impl!(Unsigned, [u8, u16, u32, u64, u128, usize]);
float_impl!(Float, [f32, f64]);

impl<'digits> From<&'digits SignedLong> for Operand<'digits> {
    fn from(value: &'digits SignedLong) -> Self {
        Self(value.digits(), value.sign())
    }
}

impl<'digits> From<&'digits UnsignedLong> for Operand<'digits> {
    fn from(value: &'digits UnsignedLong) -> Self {
        let sign = get_sign(value.len(), Sign::POS);

        Self(value.digits(), sign)
    }
}

impl<'digits> From<&&'digits SignedLong> for Operand<'digits> {
    fn from(value: &&'digits SignedLong) -> Self {
        Self::from(*value)
    }
}

impl<'digits> From<&&'digits UnsignedLong> for Operand<'digits> {
    fn from(value: &&'digits UnsignedLong) -> Self {
        Self::from(*value)
    }
}

impl From<Operand<'_>> for LongRepr {
    fn from(value: Operand<'_>) -> Self {
        Self(value.digits().to_vec(), value.sign())
    }
}

impl<'digits> From<&'digits LongRepr> for Operand<'digits> {
    fn from(value: &'digits LongRepr) -> Self {
        Self(value.digits(), value.sign())
    }
}

impl From<LongRepr> for SignedLong {
    fn from(value: LongRepr) -> Self {
        Self(value.0, value.1)
    }
}

impl From<LongRepr> for UnsignedLong {
    fn from(value: LongRepr) -> Self {
        match value.1 {
            Sign::ZERO => Default::default(),
            Sign::NEG => Default::default(),
            Sign::POS => Self(value.0),
        }
    }
}

impl<const L: usize> Default for SignedFixed<L> {
    fn default() -> Self {
        Self([0; L], 0, Sign::ZERO)
    }
}

impl<const L: usize> Default for UnsignedFixed<L> {
    fn default() -> Self {
        Self([0; L], 0)
    }
}

impl<'digits, const L: usize> From<&'digits SignedFixed<L>> for Operand<'digits> {
    fn from(value: &'digits SignedFixed<L>) -> Self {
        Self(value.digits(), value.sign())
    }
}

impl<'digits, const L: usize> From<&'digits UnsignedFixed<L>> for Operand<'digits> {
    fn from(value: &'digits UnsignedFixed<L>) -> Self {
        let sign = get_sign(value.len(), Sign::POS);

        Self(value.digits(), sign)
    }
}

impl<'digits, const L: usize> From<&&'digits SignedFixed<L>> for Operand<'digits> {
    fn from(value: &&'digits SignedFixed<L>) -> Self {
        Self::from(*value)
    }
}

impl<'digits, const L: usize> From<&&'digits UnsignedFixed<L>> for Operand<'digits> {
    fn from(value: &&'digits UnsignedFixed<L>) -> Self {
        Self::from(*value)
    }
}

impl<const L: usize> From<Operand<'_>> for FixedRepr<L> {
    fn from(value: Operand<'_>) -> Self {
        let mut res = [0; L];

        let len = value.len().min(L);

        res[..len].copy_from_slice(&value.digits()[..len]);

        Self(res, value.len(), value.sign(), 0, false)
    }
}

impl<'digits, const L: usize> From<&'digits FixedRepr<L>> for Operand<'digits> {
    fn from(value: &'digits FixedRepr<L>) -> Self {
        Self(value.digits(), value.sign())
    }
}

impl<const L: usize> From<FixedRepr<L>> for SignedFixed<L> {
    fn from(value: FixedRepr<L>) -> Self {
        Self(value.0, value.1, value.2)
    }
}

impl<const L: usize> From<FixedRepr<L>> for UnsignedFixed<L> {
    fn from(value: FixedRepr<L>) -> Self {
        match value.2 {
            Sign::ZERO => Default::default(),
            Sign::NEG => Default::default(),
            Sign::POS => Self(value.0, value.1),
        }
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
        Ok(try_from_str_long(s)?.into())
    }
}

impl FromStr for UnsignedLong {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let val = try_from_str_long(s)?;

        (val.1 != Sign::NEG)
            .then_some(val.into())
            .ok_or(TryFromStrError::UnsignedNegative)
    }
}

impl<const L: usize> FromStr for SignedFixed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(try_from_str_fixed(s)?.into())
    }
}

impl<const L: usize> FromStr for UnsignedFixed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let repr = try_from_str_fixed(s)?;

        (repr.2 != Sign::NEG)
            .then_some(repr.into())
            .ok_or(TryFromStrError::UnsignedNegative)
    }
}

impl SignedLong {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_long(bytes).into()
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.0, radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.0, pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        self.clone().into_radix(radix)
    }

    pub fn into_unsigned(self) -> UnsignedLong {
        UnsignedLong(self.0)
    }

    pub fn to_fixed<const L: usize>(&self) -> SignedFixed<L> {
        fixed_from_long(&self.0).with_sign(self.1).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn sign(&self) -> Sign {
        self.1
    }

    pub fn with_sign(mut self, sign: Sign) -> Self {
        self.1 = if self.1 != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl UnsignedLong {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_long(bytes).into()
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.0, radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.0, pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        self.clone().into_radix(radix)
    }

    pub fn into_signed(self, sign: Sign) -> SignedLong {
        let len = self.0.len();

        SignedLong(self.0, get_sign(len, sign))
    }

    pub fn to_fixed<const L: usize>(&self) -> UnsignedFixed<L> {
        fixed_from_long(&self.0).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const L: usize> SignedFixed<L> {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_fixed(bytes).into()
    }

    pub fn try_from_bytes(bytes: &[u8]) -> (Self, bool) {
        let repr = from_bytes_fixed(bytes);
        let over = repr.4;

        (repr.into(), over)
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.0[..self.1], radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.0[..self.1], pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        (*self).into_radix(radix)
    }

    pub fn into_unsigned(self) -> UnsignedFixed<L> {
        UnsignedFixed::<L>(self.0, self.1)
    }

    pub fn to_long(&self) -> SignedLong {
        long_from_fixed(&self.0, self.1).with_sign(self.2).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.0[..self.len()]
    }

    pub fn len(&self) -> usize {
        self.1
    }

    pub fn sign(&self) -> Sign {
        self.2
    }

    pub fn with_sign(mut self, sign: Sign) -> Self {
        self.2 = if self.2 != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const L: usize> UnsignedFixed<L> {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_fixed(bytes).into()
    }

    pub fn try_from_bytes(bytes: &[u8]) -> (Self, bool) {
        let repr = from_bytes_fixed(bytes);
        let over = repr.4;

        (repr.into(), over)
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(&mut self.0[..self.1], radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(&self.0[..self.1], pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        (*self).into_radix(radix)
    }

    pub fn into_signed(self, sign: Sign) -> SignedFixed<L> {
        let len = self.1;

        SignedFixed::<L>(self.0, self.1, get_sign(len, sign))
    }

    pub fn to_long(&self) -> SignedLong {
        long_from_fixed(&self.0, self.1).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.0[..self.len()]
    }

    pub fn len(&self) -> usize {
        self.1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl LongRepr {
    const ZERO: Self = LongRepr(vec![], Sign::ZERO);

    fn from_raw(mut digits: Vec<Single>, sign: Sign) -> Self {
        let len = get_len(&digits);
        let sign = get_sign(len, sign);

        digits.truncate(len);

        Self(digits, sign)
    }

    fn digits(&self) -> &[Single] {
        &self.0
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn sign(&self) -> Sign {
        self.1
    }

    fn single(digit: Single) -> Self {
        match digit {
            0 => LongRepr::ZERO,
            x => Self(vec![x], Sign::POS),
        }
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.1 = if self.1 != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }
}

impl<const L: usize> FixedRepr<L> {
    const ZERO: Self = FixedRepr::<L>(get_arr(0), 0, Sign::ZERO, 0, false);
    const ONE: Self = FixedRepr::<L>(get_arr(1), 1, Sign::POS, 0, false);
    const TWO: Self = FixedRepr::<L>(get_arr(2), 1, Sign::POS, 0, false);

    fn from_raw(digits: [Single; L], sign: Sign) -> Self {
        let len = get_len(&digits);
        let sign = get_sign(len, sign);

        Self(digits, len, sign, 0, false)
    }

    fn digits(&self) -> &[Single] {
        &self.0[..self.1]
    }

    fn len(&self) -> usize {
        self.1
    }

    fn sign(&self) -> Sign {
        self.2
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.2 = if self.2 != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    fn with_next(mut self, digit: Single) -> Self {
        self.3 = digit;
        self
    }

    fn with_overflow(mut self, over: bool) -> Self {
        self.4 = over;
        self
    }
}

impl<'digits> Operand<'digits> {
    fn from_raw(slice: &'digits [Single]) -> Self {
        let len = slice.len();
        let sign = get_sign(len, Sign::POS);

        Self(slice, sign)
    }

    fn iter<T: From<Single>>(&self) -> impl Iterator<Item = T> {
        self.digits().iter().map(|&x| T::from(x))
    }

    fn digits(&self) -> &[Single] {
        self.0
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn sign(&self) -> Sign {
        self.1
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.1 = if self.1 != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }
}

fn from_bytes_long(bytes: &[u8]) -> LongRepr {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (bytes.len() + RATIO - 1) / RATIO;

    let mut shl = 0;
    let mut res = vec![0; len];

    for (i, &byte) in bytes.iter().enumerate() {
        let idx = i / RATIO;

        res[idx] |= (byte as Single) << shl;
        shl = (shl + u8::BITS) % Single::BITS;
    }

    LongRepr::from_raw(res, Sign::POS)
}

fn from_bytes_fixed<const L: usize>(bytes: &[u8]) -> FixedRepr<L> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (bytes.len() + RATIO - 1) / RATIO;

    let mut shl = 0;
    let mut res = [0; L];

    for (i, &byte) in bytes.iter().enumerate().take(RATIO * L) {
        let idx = i / RATIO;

        res[idx] |= (byte as Single) << shl;
        shl = (shl + u8::BITS) % Single::BITS;
    }

    FixedRepr::from_raw(res, Sign::POS).with_overflow(len > L)
}

fn try_from_str_long(s: &str) -> Result<LongRepr, TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    Ok(try_from_digits_long(&digits, radix, sign)?)
}

fn try_from_str_fixed<const L: usize>(s: &str) -> Result<FixedRepr<L>, TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    Ok(try_from_digits_fixed(&digits, radix, sign)?)
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

fn try_from_digits_long_bin(digits: &[u8], pow: u8, sign: Sign) -> Result<LongRepr, TryFromDigitsError> {
    const BITS: usize = Single::BITS as usize;

    if digits.is_empty() {
        return Ok(LongRepr::ZERO);
    }

    if !(1..=u8::BITS as u8).contains(&pow) {
        return Err(TryFromDigitsError::InvalidPow { pow });
    }

    try_from_digits_validate(digits, 1 << pow)?;

    let bits = pow as usize;
    let len = (digits.len() * bits + BITS - 1) / BITS;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![0; len];
    let mut ptr = &mut res[idx];

    for &digit in digits.iter() {
        acc |= (digit as Double) << shl;
        shl += pow as u32;
        *ptr = acc as Single;

        if shl >= Single::BITS {
            if idx + 1 == len {
                break;
            }

            acc >>= Single::BITS;
            shl -= Single::BITS;
            idx += 1;
            ptr = &mut res[idx];
            *ptr = acc as Single;
        }
    }

    Ok(LongRepr::from_raw(res, sign))
}

fn try_from_digits_fixed_bin<const L: usize>(
    digits: &[u8],
    pow: u8,
    sign: Sign,
) -> Result<FixedRepr<L>, TryFromDigitsError> {
    const BITS: usize = Single::BITS as usize;

    if digits.is_empty() {
        return Ok(FixedRepr::ZERO);
    }

    if !(1..=u8::BITS as u8).contains(&pow) {
        return Err(TryFromDigitsError::InvalidPow { pow });
    }

    try_from_digits_validate(digits, 1 << pow)?;

    let bits = pow as usize;
    let len = (digits.len() * bits + BITS - 1) / BITS;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = [0; L];
    let mut ptr = &mut res[idx];

    for &digit in digits.iter() {
        acc |= (digit as Double) << shl;
        shl += pow as u32;
        *ptr = acc as Single;

        if shl >= Single::BITS {
            if idx + 1 == L {
                break;
            }

            acc >>= Single::BITS;
            shl -= Single::BITS;
            idx += 1;
            ptr = &mut res[idx];
            *ptr = acc as Single;
        }
    }

    Ok(FixedRepr::from_raw(res, sign).with_overflow(len > L))
}

fn into_radix_bin(digits: &[Single], pow: u8) -> Result<Vec<Single>, IntoRadixError> {
    const BITS: usize = Single::BITS as usize;

    if pow == Single::BITS as u8 {
        return Ok(digits.to_vec());
    }

    if !(1..Single::BITS as u8).contains(&pow) {
        return Err(IntoRadixError::InvalidPow { pow });
    }

    let radix = (1 as Double) << pow;
    let rem = radix - 1;
    let pow = pow as Double;

    let bits = pow as usize;
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits {
        acc |= (digit as Double) << shl;
        shl += BITS as Double;

        while shl >= pow {
            res[idx] = (acc & rem) as Single;
            idx += 1;

            acc >>= pow;
            shl -= pow;
        }
    }

    if acc > 0 {
        res[idx] = acc as Single;
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn try_from_digits_long(digits: &[u8], radix: u16, sign: Sign) -> Result<LongRepr, TryFromDigitsError> {
    const BITS: usize = Single::BITS as usize;

    if !(2..=u8::MAX as u16 + 1).contains(&radix) {
        return Err(TryFromDigitsError::InvalidRadix { radix: radix as Double });
    }

    if radix & (radix - 1) == 0 {
        return try_from_digits_long_bin(digits, radix.ilog2() as u8, sign);
    }

    try_from_digits_validate(digits, radix)?;

    let bits = 1 + radix.ilog2() as usize;
    let len = (digits.len() * bits + BITS - 1) / BITS;

    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for ptr in res.iter_mut().take(idx + 1) {
            acc += *ptr as Double * radix as Double;

            *ptr = acc as Single;

            acc >>= Single::BITS;
        }

        if idx < len && res[idx] > 0 {
            idx += 1;
        }
    }

    Ok(LongRepr::from_raw(res, sign))
}

fn try_from_digits_fixed<const L: usize>(
    digits: &[u8],
    radix: u16,
    sign: Sign,
) -> Result<FixedRepr<L>, TryFromDigitsError> {
    if !(2..=u8::MAX as u16 + 1).contains(&radix) {
        return Err(TryFromDigitsError::InvalidRadix { radix: radix as Double });
    }

    if radix & (radix - 1) == 0 {
        return try_from_digits_fixed_bin(digits, radix.ilog2() as u8, sign);
    }

    try_from_digits_validate(digits, radix)?;

    let mut idx = 0;
    let mut res = [0; L];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for ptr in res.iter_mut().take(idx + 1) {
            acc += *ptr as Double * radix as Double;

            *ptr = acc as Single;

            acc >>= Single::BITS;
        }

        if idx < L && res[idx] > 0 {
            idx += 1;
        }
    }

    Ok(FixedRepr::from_raw(res, sign).with_overflow(idx == L))
}

fn into_radix(digits: &mut [Single], radix: Double) -> Result<Vec<Single>, IntoRadixError> {
    const BITS: usize = Single::BITS as usize;

    if !(2..=RADIX).contains(&radix) {
        return Err(IntoRadixError::InvalidRadix { radix });
    }

    if radix & (radix - 1) == 0 {
        return into_radix_bin(digits, radix.ilog2() as u8);
    }

    let bits = 1 + radix.ilog2() as usize;
    let len = (digits.len() * BITS + bits - 1) / bits;

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

fn fixed_from_long<const L: usize>(digits: &[Single]) -> FixedRepr<L> {
    let mut res = [0; L];

    let len = digits.len().min(L);

    res[..len].copy_from_slice(&digits[..len]);

    FixedRepr::from_raw(res, Sign::POS).with_overflow(digits.len() > L)
}

fn long_from_fixed<const L: usize>(digits: &[Single; L], len: usize) -> LongRepr {
    let mut res = vec![0; len];

    res.copy_from_slice(&digits[..len]);

    LongRepr::from_raw(res, Sign::POS)
}

fn write_num_bin(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{:01$b}", digit, width)
}

fn write_num_oct(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{:01$o}", digit, width)
}

fn write_num_dec(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{:01$}", digit, width)
}

fn write_num_lhex(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{:01$x}", digit, width)
}

fn write_num_uhex(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{:01$X}", digit, width)
}

fn write_num<R: Radix, F>(_: R, fmt: &mut Formatter<'_>, digits: &[Single], sign: Sign, func: F) -> std::fmt::Result
where
    F: Fn(&mut String, Single, usize) -> std::fmt::Result,
{
    let sign = get_sign(digits.len(), sign);

    let prefix = if fmt.alternate() { R::PREFIX } else { "" };

    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let len = digits.len();
    let width = R::WIDTH as usize;

    let mut buf = String::with_capacity(len * width);

    for &digit in digits.iter().rev() {
        func(&mut buf, digit, width)?;
    }

    let len = get_len_rev(buf.as_bytes(), b'0');

    write!(fmt, "{}{}{}", sign, prefix, &buf[len..])
}

impl Display for SignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix(Dec::RADIX).unwrap_or_default();

        write_num(Dec, fmt, &digits, self.1, write_num_dec)
    }
}

impl Display for UnsignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix(Dec::RADIX).unwrap_or_default();

        write_num(Dec, fmt, &digits, Sign::POS, write_num_dec)
    }
}

impl<const L: usize> Display for SignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix(Dec::RADIX).unwrap_or_default();

        write_num(Dec, fmt, &digits, self.2, write_num_dec)
    }
}

impl<const L: usize> Display for UnsignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix(Dec::RADIX).unwrap_or_default();

        write_num(Dec, fmt, &digits, Sign::POS, write_num_dec)
    }
}

impl Binary for SignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Bin::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Bin, fmt, &digits, self.1, write_num_bin)
    }
}

impl Binary for UnsignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Bin::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Bin, fmt, &digits, Sign::POS, write_num_bin)
    }
}

impl<const L: usize> Binary for SignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Bin::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Bin, fmt, &digits, self.2, write_num_bin)
    }
}

impl<const L: usize> Binary for UnsignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Bin::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Bin, fmt, &digits, Sign::POS, write_num_bin)
    }
}

impl Octal for SignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Oct::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Oct, fmt, &digits, self.1, write_num_oct)
    }
}

impl Octal for UnsignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Oct::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Oct, fmt, &digits, Sign::POS, write_num_oct)
    }
}

impl<const L: usize> Octal for SignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Oct::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Oct, fmt, &digits, self.2, write_num_oct)
    }
}

impl<const L: usize> Octal for UnsignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Oct::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Oct, fmt, &digits, Sign::POS, write_num_oct)
    }
}

impl LowerHex for SignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, self.1, write_num_lhex)
    }
}

impl LowerHex for UnsignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, Sign::POS, write_num_lhex)
    }
}

impl<const L: usize> LowerHex for SignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, self.2, write_num_lhex)
    }
}

impl<const L: usize> LowerHex for UnsignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, Sign::POS, write_num_lhex)
    }
}

impl UpperHex for SignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, self.1, write_num_uhex)
    }
}

impl UpperHex for UnsignedLong {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, Sign::POS, write_num_uhex)
    }
}

impl<const L: usize> UpperHex for SignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, self.2, write_num_uhex)
    }
}

impl<const L: usize> UpperHex for UnsignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, Sign::POS, write_num_uhex)
    }
}

fn zip_nums<T: From<Single>>(a: &[Single], b: &[Single], zeros: usize) -> impl Iterator<Item = (T, T)> {
    let len_a = a.len();
    let len_b = b.len();
    let len = len_a.max(len_b);

    let iter_a = a.iter().chain(repeat_n(&0, len - len_a + zeros)).map(|&x| T::from(x));
    let iter_b = b.iter().chain(repeat_n(&0, len - len_b + zeros)).map(|&x| T::from(x));

    iter_a.zip(iter_b)
}

fn cmp_nums(a: &[Single], b: &[Single]) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Less => Ordering::Less,
        Ordering::Equal => a
            .iter()
            .rev()
            .zip(b.iter().rev())
            .map(|(&a, &b)| a.cmp(&b))
            .find(|&x| x != Ordering::Equal)
            .unwrap_or(Ordering::Equal),
        Ordering::Greater => Ordering::Greater,
    }
}

fn cmp_nums_ext(a: &[Single], b: &[Single], ax: Single, bx: Single) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Less => Ordering::Less,
        Ordering::Equal => match ax.cmp(&bx) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => a
                .iter()
                .rev()
                .zip(b.iter().rev())
                .map(|(&a, &b)| a.cmp(&b))
                .find(|&x| x != Ordering::Equal)
                .unwrap_or(Ordering::Equal),
            Ordering::Greater => Ordering::Greater,
        },
        Ordering::Greater => Ordering::Greater,
    }
}

fn add_long(a: Operand<'_>, b: Operand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return b.into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_long(a, -b);
    }

    let len_a = a.len();
    let len_b = b.len();
    let len = len_a.max(len_b) + 1;

    let mut acc = 0;
    let mut res = vec![0; len];

    let iter = zip_nums::<Double>(a.digits(), b.digits(), 1);

    for (r, (aop, bop)) in res.iter_mut().zip(iter) {
        acc += aop + bop;

        *r = acc as Single;
        acc >>= Single::BITS;
    }

    LongRepr::from_raw(res, a.sign())
}

fn add_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return b.into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_fixed(a, -b);
    }

    let mut acc = 0;
    let mut res = [0; L];

    let iter = zip_nums::<Double>(a.digits(), b.digits(), 1);

    for (r, (aop, bop)) in res.iter_mut().zip(iter) {
        acc += aop + bop;

        *r = acc as Single;
        acc >>= Single::BITS;
    }

    FixedRepr::from_raw(res, a.sign())
        .with_next(acc as Single)
        .with_overflow(acc > 0)
}

fn sub_long(a: Operand<'_>, b: Operand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return (-b).into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return add_long(a, -b);
    }

    let (a, b, sign) = match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => (b, a, -a.sign()),
        Ordering::Equal => return LongRepr::ZERO,
        Ordering::Greater => (a, b, a.sign()),
    };

    let len = a.len();

    let mut acc = 0;
    let mut res = vec![0; len];

    let iter = zip_nums::<Double>(a.digits(), b.digits(), 0);

    for (r, (aop, bop)) in res.iter_mut().zip(iter) {
        *r = (RADIX + aop - bop - acc) as Single;

        acc = (aop < bop + acc) as Double;
    }

    LongRepr::from_raw(res, sign)
}

fn sub_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return (-b).into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return add_fixed(a, -b);
    }

    let (a, b, sign) = match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => (b, a, -a.sign()),
        Ordering::Equal => return FixedRepr::ZERO,
        Ordering::Greater => (a, b, a.sign()),
    };

    let mut acc = 0;
    let mut res = [0; L];

    let iter = zip_nums::<Double>(a.digits(), b.digits(), 0);

    for (r, (aop, bop)) in res.iter_mut().zip(iter) {
        *r = (RADIX + aop - bop - acc) as Single;

        acc = (aop < bop + acc) as Double;
    }

    FixedRepr::from_raw(res, sign)
}

fn addshr_long(a: Operand<'_>, b: Operand<'_>, shr: usize) -> LongRepr {
    if shr == 0 {
        return add_long(a, b);
    }

    if shr >= Single::BITS as usize {
        return LongRepr::ZERO;
    }

    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return shr_long(b, shr),
        (_, Sign::ZERO) => return shr_long(a, shr),
        _ => (),
    }

    if a.sign() != b.sign() {
        return subshr_long(a, -b, shr);
    }

    let len_a = a.len();
    let len_b = b.len();
    let len = len_a.max(len_b) + 1;
    let shl = Single::BITS as usize - shr;

    let mut acc = 0;
    let mut res = vec![0; len];

    for (i, (aop, bop)) in zip_nums::<Double>(a.digits(), b.digits(), 1).enumerate() {
        let vop = aop + bop;

        acc += vop >> shr;

        if i > 0 {
            let vop = vop as Single;
            let val = res[i - 1] as Double + (vop << shl) as Double;

            res[i - 1] = val as Single;
            acc += val >> Single::BITS;
        }

        res[i] = acc as Single;
        acc >>= Single::BITS;
    }

    LongRepr::from_raw(res, a.sign())
}

fn addshr_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>, shr: usize) -> FixedRepr<L> {
    if shr == 0 {
        return add_fixed(a, b);
    }

    if shr >= Single::BITS as usize {
        return FixedRepr::ZERO;
    }

    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return shr_fixed(b, shr),
        (_, Sign::ZERO) => return shr_fixed(a, shr),
        _ => (),
    }

    if a.sign() != b.sign() {
        return subshr_fixed(a, -b, shr);
    }

    let shl = Single::BITS as usize - shr;

    let mut acc = 0;
    let mut res = [0; L];

    for (i, (aop, bop)) in zip_nums::<Double>(a.digits(), b.digits(), 1).enumerate().take(L) {
        let vop = aop + bop;

        acc += vop >> shr;

        if i > 0 {
            let vop = vop as Single;
            let val = res[i - 1] as Double + (vop << shl) as Double;

            res[i - 1] = val as Single;
            acc += val >> Single::BITS;
        }

        res[i] = acc as Single;
        acc >>= Single::BITS;
    }

    FixedRepr::from_raw(res, a.sign())
        .with_next(acc as Single)
        .with_overflow(acc > 0)
}

fn subshr_long(a: Operand<'_>, b: Operand<'_>, shr: usize) -> LongRepr {
    if shr == 0 {
        return sub_long(a, b);
    }

    if shr >= Single::BITS as usize {
        return LongRepr::ZERO;
    }

    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return shr_long(-b, shr),
        (_, Sign::ZERO) => return shr_long(a, shr),
        _ => (),
    }

    if a.sign() != b.sign() {
        return addshr_long(a, -b, shr);
    }

    let (a, b, sign) = match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => (b, a, -a.sign()),
        Ordering::Equal => return LongRepr::ZERO,
        Ordering::Greater => (a, b, a.sign()),
    };

    let len = a.len();
    let shl = Single::BITS as usize - shr;

    let mut acc = 0;
    let mut res = vec![0; len];

    for (i, (aop, bop)) in zip_nums::<Double>(a.digits(), b.digits(), 0).enumerate() {
        let vop = RADIX + aop - bop - acc;

        if i > 0 {
            let vop = vop as Single;
            let val = res[i - 1] as Double + (vop << shl) as Double;

            res[i - 1] = val as Single;
        }

        res[i] = (vop as Single) >> shr;
        acc = (aop < bop + acc) as Double;
    }

    LongRepr::from_raw(res, sign)
}

fn subshr_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>, shr: usize) -> FixedRepr<L> {
    if shr == 0 {
        return sub_fixed(a, b);
    }

    if shr >= Single::BITS as usize {
        return FixedRepr::ZERO;
    }

    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return shr_fixed(-b, shr),
        (_, Sign::ZERO) => return shr_fixed(a, shr),
        _ => (),
    }

    if a.sign() != b.sign() {
        return addshr_fixed(a, -b, shr);
    }

    let (a, b, sign) = match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => (b, a, -a.sign()),
        Ordering::Equal => return FixedRepr::ZERO,
        Ordering::Greater => (a, b, a.sign()),
    };

    let shl = Single::BITS as usize - shr;

    let mut acc = 0;
    let mut res = [0; L];

    for (i, (aop, bop)) in zip_nums::<Double>(a.digits(), b.digits(), 0).enumerate().take(L) {
        let vop = RADIX + aop - bop - acc;

        if i > 0 {
            let vop = vop as Single;
            let val = res[i - 1] as Double + (vop << shl) as Double;

            res[i - 1] = val as Single;
        }

        res[i] = (vop as Single) >> shr;
        acc = (aop < bop + acc) as Double;
    }

    FixedRepr::from_raw(res, sign)
}

fn mul_long(a: Operand<'_>, b: Operand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return LongRepr::ZERO,
        (_, Sign::ZERO) => return LongRepr::ZERO,
        _ => (),
    }

    let len_a = a.len();
    let len_b = b.len();
    let len = len_a + len_b;

    let mut res = vec![0; len];

    for (i, aop) in a.iter::<Double>().enumerate() {
        let mut acc = 0;

        for (j, bop) in b.iter::<Double>().chain(once(0)).enumerate() {
            let rop = res[i + j] as Double;

            acc += rop + aop * bop;

            res[i + j] = acc as Single;
            acc >>= Single::BITS;
        }
    }

    LongRepr::from_raw(res, a.sign() * b.sign())
}

fn mul_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return FixedRepr::ZERO,
        (_, Sign::ZERO) => return FixedRepr::ZERO,
        _ => (),
    }

    let mut res = [0; L];
    let mut over = false;
    let mut next = 0;

    for (i, aop) in a.iter::<Double>().enumerate() {
        let mut acc = 0;

        for (j, bop) in b.iter::<Double>().chain(once(0)).enumerate().take(L - i) {
            let rop = res[i + j] as Double;

            acc += rop + aop * bop;

            res[i + j] = acc as Single;
            acc >>= Single::BITS;
        }

        over |= acc > 0 || i + b.len() > L;
        next = (next + acc) % RADIX;
    }

    FixedRepr::from_raw(res, a.sign() * b.sign())
        .with_next(next as Single)
        .with_overflow(over)
}

fn div_long(a: Operand<'_>, b: Operand<'_>) -> (LongRepr, LongRepr) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return (LongRepr::ZERO, LongRepr::ZERO),
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b == (&LongRepr::single(1)).into() {
        return (a.into(), LongRepr::ZERO);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => return (LongRepr::ZERO, a.into()),
        Ordering::Equal => return (LongRepr::single(1).with_sign(a.sign() * b.sign()), LongRepr::ZERO),
        Ordering::Greater => (),
    }

    let sign_a = a.sign();
    let sign_b = b.sign();
    let apos = a.with_sign(Sign::POS);
    let bpos = b.with_sign(Sign::POS);

    let one = [1];
    let one = Operand::from_raw(&one);

    let mut l = LongRepr::single(2);
    let mut r = LongRepr::from(apos);

    while cmp_nums(l.digits(), r.digits()) == Ordering::Less {
        let m = addshr_long((&l).into(), (&r).into(), 1);

        let val = mul_long(bpos, (&m).into());

        match cmp_nums(val.digits(), apos.digits()) {
            Ordering::Less | Ordering::Equal => {
                l = add_long((&m).into(), one);
            },
            Ordering::Greater => {
                r = m;
            },
        }
    }

    let div = sub_long((&l).into(), one);
    let mul = mul_long((&div).into(), bpos);
    let rem = sub_long((&mul).into(), apos);

    (div.with_sign(sign_a * sign_b), rem.with_sign(sign_a))
}

fn div_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>) -> (FixedRepr<L>, FixedRepr<L>) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => {
            return (FixedRepr::ZERO, FixedRepr::ZERO);
        },
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b == (&FixedRepr::<L>::ONE).into() {
        return (a.into(), FixedRepr::ZERO);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => return (FixedRepr::ZERO, a.into()),
        Ordering::Equal => return (FixedRepr::ONE.with_sign(a.sign() * b.sign()), FixedRepr::ZERO),
        Ordering::Greater => (),
    }

    let sign_a = a.sign();
    let sign_b = b.sign();
    let apos = a.with_sign(Sign::POS);
    let bpos = b.with_sign(Sign::POS);

    let one = [1];
    let one = Operand::from_raw(&one);

    let mut l = FixedRepr::<L>::TWO;
    let mut r = FixedRepr::<L>::from(apos);

    while cmp_nums(l.digits(), r.digits()) == Ordering::Less {
        let m = addshr_fixed((&l).into(), (&r).into(), 1);

        let val = mul_fixed::<L>(bpos, (&m).into());

        if val.4 {
            r = m;

            continue;
        }

        match cmp_nums(val.digits(), apos.digits()) {
            Ordering::Less | Ordering::Equal => {
                l = add_fixed((&m).into(), one);
            },
            Ordering::Greater => {
                r = m;
            },
        }
    }

    let div = sub_fixed::<L>((&l).into(), one);
    let mul = mul_fixed::<L>((&div).into(), bpos);
    let rem = sub_fixed::<L>((&mul).into(), apos);

    (div.with_sign(sign_a * sign_b), rem.with_sign(sign_a))
}

fn bit_long<F>(a: Operand<'_>, b: Operand<'_>, func: F) -> LongRepr
where
    F: Fn(Single, Single) -> Single,
{
    let res = zip_nums::<Single>(a.digits(), b.digits(), 0)
        .map(|(aop, bop)| func(aop, bop))
        .collect();

    LongRepr::from_raw(res, Sign::POS)
}

fn bit_fixed<const L: usize, F>(a: Operand<'_>, b: Operand<'_>, func: F) -> FixedRepr<L>
where
    F: Fn(Single, Single) -> Single,
{
    let iter = zip_nums::<Single>(a.digits(), b.digits(), 0).map(|(aop, bop)| func(aop, bop));

    let mut res = [0; L];

    for (r, v) in res.iter_mut().zip(iter) {
        *r = v;
    }

    FixedRepr::from_raw(res, Sign::POS)
}

fn shl_long(a: Operand<'_>, val: usize) -> LongRepr {
    const BITS: usize = Single::BITS as usize;

    let sign = a.sign();

    if val == 0 {
        return a.into();
    }

    if sign == Sign::ZERO {
        return LongRepr::ZERO;
    }

    let offset = val / BITS;
    let shl = val % BITS;
    let shr = BITS - shl;
    let len = a.len() + (val + BITS - 1) / BITS;

    let mut res = vec![0; len];

    for (i, r) in res.iter_mut().skip(offset).enumerate() {
        let val_h = a.digits().get(i).unwrap_or(&0);
        let val_l = a.digits().get(i.wrapping_sub(1)).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *r = val_h | val_l;
    }

    LongRepr::from_raw(res, sign)
}

fn shl_fixed<const L: usize>(a: Operand<'_>, val: usize) -> FixedRepr<L> {
    const BITS: usize = Single::BITS as usize;

    let sign = a.sign();

    if val == 0 {
        return a.into();
    }

    if sign == Sign::ZERO {
        return FixedRepr::ZERO;
    }

    let offset = val / BITS;
    let shl = val % BITS;
    let shr = BITS - shl;

    let mut res = [0; L];

    for (i, r) in res.iter_mut().skip(offset).enumerate() {
        let val_h = a.digits().get(i).unwrap_or(&0);
        let val_l = a.digits().get(i.wrapping_sub(1)).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *r = val_h | val_l;
    }

    FixedRepr::from_raw(res, sign)
}

fn shr_long(a: Operand<'_>, val: usize) -> LongRepr {
    const BITS: usize = Single::BITS as usize;

    let sign = a.sign();

    if val == 0 {
        return a.into();
    }

    if val >= a.len() * BITS {
        return LongRepr::ZERO;
    }

    let offset = val / BITS;
    let shr = val % BITS;
    let shl = BITS - shr;
    let len = a.len() - offset;

    let mut res = vec![0; len];

    for (i, r) in res.iter_mut().enumerate() {
        let val_h = a.digits().get(i + offset + 1).unwrap_or(&0);
        let val_l = a.digits().get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *r = val_h | val_l;
    }

    LongRepr::from_raw(res, sign)
}

fn shr_fixed<const L: usize>(a: Operand<'_>, val: usize) -> FixedRepr<L> {
    const BITS: usize = Single::BITS as usize;

    let sign = a.sign();

    if val == 0 {
        return a.into();
    }

    if val >= a.len() * BITS {
        return FixedRepr::ZERO;
    }

    let offset = val / BITS;
    let shr = val % BITS;
    let shl = BITS - shr;
    let len = a.len() - offset;

    let mut res = [0; L];

    for (i, r) in res.iter_mut().take(len).enumerate() {
        let val_h = a.digits().get(i + offset + 1).unwrap_or(&0);
        let val_l = a.digits().get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *r = val_h | val_l;
    }

    FixedRepr::from_raw(res, sign)
}

fn shr_long_mut(a: LongRepr, val: usize) -> LongRepr {
    const BITS: usize = Single::BITS as usize;

    let len = a.len();
    let sign = a.sign();

    if val >= a.len() * BITS {
        return LongRepr::ZERO;
    }

    let offset = val / BITS;
    let shr = val % BITS;
    let shl = BITS - shr;

    let mut res = a.0;

    for i in 0..len - offset {
        let val_h = res.get(i + offset + 1).unwrap_or(&0);
        let val_l = res.get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        res[i] = val_h | val_l;
    }

    LongRepr::from_raw(res, sign)
}

fn shr_fixed_mut<const L: usize>(a: FixedRepr<L>, val: usize) -> FixedRepr<L> {
    const BITS: usize = Single::BITS as usize;

    let len = a.len();
    let sign = a.sign();

    if val >= a.len() * BITS {
        return FixedRepr::ZERO;
    }

    let offset = val / BITS;
    let shr = val % BITS;
    let shl = BITS - shr;

    let mut res = a.0;

    for i in 0..len - offset {
        let val_h = res.get(i + offset + 1).unwrap_or(&0);
        let val_l = res.get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        res[i] = val_h | val_l;
    }

    FixedRepr::from_raw(res, sign)
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

ops_impl!(@un |a: &SignedLong| -> SignedLong, - SignedLong(a.0.clone(), -a.1));

ops_impl!(@bin |a: &SignedLong, b: &SignedLong| -> SignedLong,
    + add_long((&a).into(), (&b).into()),
    - sub_long((&a).into(), (&b).into()),
    * mul_long((&a).into(), (&b).into()),
    / div_long((&a).into(), (&b).into()).0,
    % div_long((&a).into(), (&b).into()).1,
    | bit_long((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_long((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_long((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |a: &UnsignedLong, b: &UnsignedLong| -> UnsignedLong,
    + add_long((&a).into(), (&b).into()),
    - sub_long((&a).into(), (&b).into()),
    * mul_long((&a).into(), (&b).into()),
    / div_long((&a).into(), (&b).into()).0,
    % div_long((&a).into(), (&b).into()).1,
    | bit_long((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_long((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_long((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |a: &SignedLong, b: usize| -> SignedLong,
    << shl_long((&a).into(), b),
    >> shr_long((&a).into(), b));

ops_impl!(@bin |a: &UnsignedLong, b: usize| -> UnsignedLong,
    << shl_long((&a).into(), b),
    >> shr_long((&a).into(), b));

ops_impl!(@un <const L: usize> |a: &SignedFixed<L>| -> SignedFixed<L>, - SignedFixed(a.0, a.1, -a.2));

ops_impl!(@bin <const L: usize> |a: &SignedFixed<L>, b: &SignedFixed<L>| -> SignedFixed::<L>,
    + add_fixed((&a).into(), (&b).into()),
    - sub_fixed((&a).into(), (&b).into()),
    * mul_fixed((&a).into(), (&b).into()),
    / div_fixed((&a).into(), (&b).into()).0,
    % div_fixed((&a).into(), (&b).into()).1,
    | bit_fixed((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_fixed((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_fixed((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |a: &UnsignedFixed<L>, b: &UnsignedFixed<L>| -> UnsignedFixed::<L>,
    + add_fixed((&a).into(), (&b).into()),
    - sub_fixed((&a).into(), (&b).into()),
    * mul_fixed((&a).into(), (&b).into()),
    / div_fixed((&a).into(), (&b).into()).0,
    % div_fixed((&a).into(), (&b).into()).1,
    | bit_fixed((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_fixed((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_fixed((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |a: &SignedFixed<L>, b: usize| -> SignedFixed::<L>,
    << shl_fixed((&a).into(), b),
    >> shr_fixed((&a).into(), b));

ops_impl!(@bin <const L: usize> |a: &UnsignedFixed<L>, b: usize| -> UnsignedFixed::<L>,
    << shl_fixed((&a).into(), b),
    >> shr_fixed((&a).into(), b));

ops_impl!(@un <'digits> |a: &Operand<'digits>| -> Operand<'digits>, - Operand(a.0, -a.1));

fn get_sign_from_str(s: &str) -> Result<(&str, Sign), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    let bytes = s.as_bytes();

    let val = match bytes[0] {
        b'+' => (&s[1..], Sign::POS),
        b'-' => (&s[1..], Sign::NEG),
        _ => (s, Sign::POS),
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
        b"0x" | b"0X" => (&s[2..], 16),
        b"0o" | b"0O" => (&s[2..], 8),
        b"0b" | b"0B" => (&s[2..], 2),
        _ => (s, 10),
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
            b'0'..=b'9' if ch - b'0' < r => Some(Ok(ch - b'0')),
            b'a'..=b'f' if ch - b'a' + 10 < r => Some(Ok(ch - b'a' + 10)),
            b'A'..=b'F' if ch - b'A' + 10 < r => Some(Ok(ch - b'A' + 10)),
            b'_' => None,
            _ => Some(Err(TryFromStrError::InvalidSymbol { ch: ch as char, radix })),
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

fn get_len<T: Constants + PartialEq + Eq>(digits: &[T]) -> usize {
    let mut len = digits.len();

    for digit in digits.iter().rev() {
        if digit != &T::ZERO {
            return len;
        }

        len -= 1;
    }

    0
}

fn get_len_rev<T: Constants + PartialEq + Eq>(digits: &[T], val: T) -> usize {
    for (idx, digit) in digits.iter().enumerate() {
        if digit != &val {
            return idx;
        }
    }

    0
}

fn get_sign<T: Constants + PartialEq + Eq>(val: T, default: Sign) -> Sign {
    if val != T::ZERO { default } else { Sign::ZERO }
}

const fn get_arr<const L: usize>(val: Single) -> [Single; L] {
    let mut res = [0; L];

    res[0] = val;
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRIMES: [usize; 2] = [10_570_841, 10_570_849];

    type S32 = signed_fixed!(32);
    type U32 = unsigned_fixed!(32);

    macro_rules! assert_long_from {
        (@signed $expr:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::from($expr), SignedLong($digits, $sign));
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from($expr), UnsignedLong($digits));
        };
    }

    macro_rules! assert_fixed_from {
        (@signed $expr:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(S32::from($expr), SignedFixed($digits, $len, $sign));
        };
        (@unsigned $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::from($expr), UnsignedFixed($digits, $len));
        };
    }

    macro_rules! assert_long_from_bytes {
        (@signed $expr:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::from_bytes($expr), SignedLong($digits, $sign));
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from_bytes($expr), UnsignedLong($digits));
        };
    }

    macro_rules! assert_fixed_from_bytes {
        (@signed $expr:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(S32::from_bytes($expr), SignedFixed($digits, $len, $sign));
        };
        (@unsigned $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::from_bytes($expr), UnsignedFixed($digits, $len));
        };
    }

    macro_rules! assert_long_from_digits {
        (@signed $expr:expr, $radix:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::try_from_digits($expr, $radix), Ok(SignedLong($digits, $sign)));
        };
        (@unsigned $expr:expr, $radix:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::try_from_digits($expr, $radix), Ok(UnsignedLong($digits)));
        };
    }

    macro_rules! assert_fixed_from_digits {
        (@signed $expr:expr, $radix:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(S32::try_from_digits($expr, $radix), Ok(SignedFixed($digits, $len, $sign)));
        };
        (@unsigned $expr:expr, $radix:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::try_from_digits($expr, $radix), Ok(UnsignedFixed($digits, $len)));
        };
    }

    macro_rules! assert_long_from_str {
        (@signed $expr:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::from_str($expr), Ok(SignedLong($digits, $sign)));
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from_str($expr), Ok(UnsignedLong($digits)));
        };
    }

    macro_rules! assert_fixed_from_str {
        (@signed $expr:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(S32::from_str($expr), Ok(SignedFixed($digits, $len, $sign,)));
        };
        (@unsigned $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::from_str($expr), Ok(UnsignedFixed($digits, $len)));
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

    fn trimmed(val: SignedLong, len: usize) -> SignedLong {
        let len = len.min(val.0.len());

        let digits = normalized(&val.0[..len]);
        let sign = get_sign(digits.len(), val.1);

        SignedLong(digits, sign)
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
    fn from_bytes_long() {
        assert_eq!(SignedLong::from_bytes(&[]), SignedLong::default());
        assert_eq!(UnsignedLong::from_bytes(&[]), UnsignedLong::default());

        for val in u16::MIN..=u16::MAX {
            let bytes = (val as u32).to_le_bytes();

            assert_long_from_bytes!(@signed &bytes, normalized(&bytes), Sign::from(val));
            assert_long_from_bytes!(@unsigned &bytes, normalized(&bytes));
        }
    }

    #[test]
    fn from_bytes_fixed() {
        assert_eq!(S32::from_bytes(&[]), S32::default());
        assert_eq!(U32::from_bytes(&[]), U32::default());

        for val in u16::MIN..=u16::MAX {
            let bytes = (val as u32).to_le_bytes();

            assert_fixed_from_bytes!(@signed &bytes, bytes, get_len(&bytes), Sign::from(val));
            assert_fixed_from_bytes!(@unsigned &bytes, bytes, get_len(&bytes));
        }
    }

    #[test]
    fn from_digits_long() {
        // TODO: Make better test
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
        // TODO: Make better test
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
        // TODO: Make better test
        assert_eq!(SignedLong::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());
        assert_eq!(UnsignedLong::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());

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
        // TODO: Make better test
        assert_eq!(S32::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());
        assert_eq!(U32::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());

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
    fn to_str_long() {
        for val in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            let x = SignedLong::from(val);

            let (sign, abs) = if val >= 0 { ("", val) } else { ("-", -val) };

            assert_eq!(format!("{:#}", &x), format!("{}{:#}", sign, abs));
            assert_eq!(format!("{:#b}", &x), format!("{}{:#b}", sign, abs));
            assert_eq!(format!("{:#o}", &x), format!("{}{:#o}", sign, abs));
            assert_eq!(format!("{:#x}", &x), format!("{}{:#x}", sign, abs));

            assert_eq!(format!("{:}", &x), format!("{}{:}", sign, abs));
            assert_eq!(format!("{:b}", &x), format!("{}{:b}", sign, abs));
            assert_eq!(format!("{:o}", &x), format!("{}{:o}", sign, abs));
            assert_eq!(format!("{:x}", &x), format!("{}{:x}", sign, abs));
        }
    }

    #[test]
    fn to_str_fixed() {
        for val in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            let x = S32::from(val);

            let (sign, abs) = if val >= 0 { ("", val) } else { ("-", -val) };

            assert_eq!(format!("{:#}", &x), format!("{}{:#}", sign, abs));
            assert_eq!(format!("{:#b}", &x), format!("{}{:#b}", sign, abs));
            assert_eq!(format!("{:#o}", &x), format!("{}{:#o}", sign, abs));
            assert_eq!(format!("{:#x}", &x), format!("{}{:#x}", sign, abs));

            assert_eq!(format!("{:}", &x), format!("{}{:}", sign, abs));
            assert_eq!(format!("{:b}", &x), format!("{}{:b}", sign, abs));
            assert_eq!(format!("{:o}", &x), format!("{}{:o}", sign, abs));
            assert_eq!(format!("{:x}", &x), format!("{}{:x}", sign, abs));
        }
    }

    #[test]
    fn addsub_long() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                let aop = aop as i64;
                let bop = bop as i64;

                assert_eq!(a + b, SignedLong::from(aop + bop));
                assert_eq!(a - b, SignedLong::from(aop - bop));
            }
        }
    }

    #[test]
    fn addsub_fixed() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &S32::from(aop);
                let b = &S32::from(bop);

                let aop = aop as i64;
                let bop = bop as i64;

                assert_eq!(a + b, S32::from(aop + bop));
                assert_eq!(a - b, S32::from(aop - bop));
            }
        }
    }

    #[test]
    fn addsubshr_long() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                let aop = aop as i64;
                let bop = bop as i64;

                let add = SignedLong::from(addshr_long((&a).into(), (&b).into(), 1));
                let sub = SignedLong::from(subshr_long((&a).into(), (&b).into(), 1));

                assert_eq!(add, SignedLong::from((aop + bop) / 2));
                assert_eq!(sub, SignedLong::from((aop - bop) / 2));
            }
        }
    }

    #[test]
    fn addsubshr_fixed() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &S32::from(aop);
                let b = &S32::from(bop);

                let aop = aop as i64;
                let bop = bop as i64;

                let add = S32::from(addshr_fixed((&a).into(), (&b).into(), 1));
                let sub = S32::from(subshr_fixed((&a).into(), (&b).into(), 1));

                assert_eq!(add, S32::from((aop + bop) / 2));
                assert_eq!(sub, S32::from((aop - bop) / 2));
            }
        }
    }

    #[test]
    fn muldiv_long() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                let aop = aop as i64;
                let bop = bop as i64;

                assert_eq!(a * b, SignedLong::from(aop * bop));
                assert_eq!(a / b, SignedLong::from(aop / bop));
                assert_eq!(a % b, SignedLong::from(aop % bop));
            }
        }
    }

    #[test]
    fn muldiv_fixed() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &S32::from(aop);
                let b = &S32::from(bop);

                let aop = aop as i64;
                let bop = bop as i64;

                assert_eq!(a * b, S32::from(aop * bop));
                assert_eq!(a / b, S32::from(aop / bop));
                assert_eq!(a % b, S32::from(aop % bop));
            }
        }
    }

    #[test]
    fn bit_long() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                let aop = aop.unsigned_abs();
                let bop = bop.unsigned_abs();

                assert_eq!(a | b, SignedLong::from(aop | bop));
                assert_eq!(a & b, SignedLong::from(aop & bop));
                assert_eq!(a ^ b, SignedLong::from(aop ^ bop));
            }
        }
    }

    #[test]
    fn bit_fixed() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[1]) {
                let a = &S32::from(aop);
                let b = &S32::from(bop);

                let aop = aop.unsigned_abs();
                let bop = bop.unsigned_abs();

                assert_eq!(a | b, S32::from(aop | bop));
                assert_eq!(a & b, S32::from(aop & bop));
                assert_eq!(a ^ b, S32::from(aop ^ bop));
            }
        }
    }

    #[test]
    fn shift_long() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in 0..64 {
                let a = &SignedLong::from(aop);
                let sign = Sign::from(aop);

                let shl = aop.unsigned_abs().checked_shl(bop as u32).unwrap_or(0);
                let shr = aop.unsigned_abs().checked_shr(bop as u32).unwrap_or(0);

                assert_eq!(trimmed(a << bop, 4), SignedLong::from(shl).with_sign(get_sign(shl, sign)));
                assert_eq!(trimmed(a >> bop, 4), SignedLong::from(shr).with_sign(get_sign(shr, sign)));
            }
        }
    }

    #[test]
    fn shift_fixed() {
        for aop in (i32::MIN + 1..=i32::MAX).step_by(PRIMES[0]) {
            for bop in 0..64 {
                let a = &S32::from(aop);
                let sign = Sign::from(aop);

                let shl = aop.unsigned_abs().checked_shl(bop as u32).unwrap_or(0);
                let shr = aop.unsigned_abs().checked_shr(bop as u32).unwrap_or(0);

                assert_eq!(a << bop, S32::from(shl).with_sign(get_sign(shl, sign)));
                assert_eq!(a >> bop, S32::from(shr).with_sign(get_sign(shr, sign)));
            }
        }
    }
}

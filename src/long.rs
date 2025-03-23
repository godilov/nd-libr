#![allow(clippy::manual_div_ceil)]

use self::{
    digit::{Double, Single},
    radix::RADIX_VAL,
};
use crate::num::{Constants, Sign};
use radix::RADIX_MASK;
use std::{cmp::Ordering, panic, str::FromStr};
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
    #[error("Found invalid symbol '{0}' during parsing from string of radix `{1}`")]
    InvalidSymbol(char, u8),
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
    #[error(transparent)]
    InvalidRadix(#[from] RadixError),
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum RadixError {
    #[error("Found invalid radix '{radix}'")]
    Invalid { radix: u8 },
    #[error("Found invalid radix '{radix}' for binary impl")]
    InvalidBin { radix: u8 },
    #[error("Found invalid value '{digit}' for radix '{radix}'")]
    InvalidDigit { digit: u8, radix: u8 },
}

#[cfg(all(target_pointer_width = "64", not(test)))]
mod digit {
    pub(super) type Single = u64;
    pub(super) type Double = u128;

    pub(super) const OCT_MAX: Single = (1 << 63) - 1;
    pub(super) const OCT_RADIX: Double = 1 << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_MAX: Single = 9_999_999_999_999_999_999;
    pub(super) const DEC_RADIX: Double = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;
}

#[cfg(all(target_pointer_width = "32", not(test)))]
mod digit {
    pub(super) type Single = u32;
    pub(super) type Double = u64;

    pub(super) const OCT_MAX: Single = (1 << 30) - 1;
    pub(super) const OCT_RADIX: Double = 1 << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_MAX: Single = 999_999_999;
    pub(super) const DEC_RADIX: Double = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;
}

#[cfg(test)]
mod digit {
    pub(super) type Single = u8;
    pub(super) type Double = u16;

    pub(super) const OCT_MAX: Single = (1 << 6) - 1;
    pub(super) const OCT_RADIX: Double = 1 << 6;
    pub(super) const OCT_WIDTH: u8 = 2;

    pub(super) const DEC_MAX: Single = 99;
    pub(super) const DEC_RADIX: Double = 100;
    pub(super) const DEC_WIDTH: u8 = 2;
}

#[allow(unused)]
mod radix {
    use super::{
        Double, Single,
        digit::{DEC_MAX, DEC_RADIX, DEC_WIDTH, OCT_MAX, OCT_RADIX, OCT_WIDTH},
    };

    pub(super) const RADIX_VAL: Double = Single::MAX as Double + 1;
    pub(super) const RADIX_MASK: Double = Single::MAX as Double;

    pub trait Constants {
        const MAX: Single = Single::MAX;
        const RADIX: Double = (1 as Double) << Single::BITS;
        const WIDTH: u8;
        const PREFIX: &str;
        const ALPHABET: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Constants for Bin {
        const WIDTH: u8 = Single::BITS as u8;
        const PREFIX: &str = "0b";
        const ALPHABET: &str = "01";
    }

    impl Constants for Oct {
        const MAX: Single = OCT_MAX;
        const RADIX: Double = OCT_RADIX;
        const WIDTH: u8 = OCT_WIDTH;
        const PREFIX: &str = "0o";
        const ALPHABET: &str = "01234567";
    }

    impl Constants for Dec {
        const MAX: Single = DEC_MAX;
        const RADIX: Double = DEC_RADIX;
        const WIDTH: u8 = DEC_WIDTH;
        const PREFIX: &str = "";
        const ALPHABET: &str = "0123456789";
    }

    impl Constants for Hex {
        const WIDTH: u8 = Single::BITS as u8 / 4;
        const PREFIX: &str = "0x";
        const ALPHABET: &str = "0123456789ABCDEF";
    }
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

macro_rules! from_impl_long {
    ($type:ident, [$($from:ty),+] $(,)?) => {
        $(from_impl_long!($type, $from);)+
    };
    ($type:ident, [$pos:expr], [$($from:ty),+] $(,)?) => {
        $(from_impl_long!($type, $from, $pos);)+
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

macro_rules! from_impl_fixed {
    ($type:ident, [$($from:ty),+] $(,)?) => {
        $(from_impl_fixed!($type, $from);)+
    };
    ($type:ident, [$pos:expr], [$($from:ty),+] $(,)?) => {
        $(from_impl_fixed!($type, $from, $pos);)+
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

from_impl_long!(
    SignedLong,
    [Sign::POS],
    [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize],
);

from_impl_fixed!(
    SignedFixed,
    [Sign::POS],
    [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize],
);

from_impl_long!(UnsignedLong, [u8, u16, u32, u64, u128, usize]);
from_impl_fixed!(UnsignedFixed, [u8, u16, u32, u64, u128, usize]);

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
    #[allow(dead_code)]
    fn from_raw((data, sign): (Vec<Single>, Sign)) -> Self {
        Self { data, sign }
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let data = from_slice_long(slice);
        let sign = if data.is_empty() { Sign::ZERO } else { Sign::POS };

        Self { sign, data }
    }

    pub fn try_from_digits(digits: &[u8], radix: u8) -> Result<Self, TryFromDigitsError> {
        let data = try_from_digits_long(digits, radix)?;
        let sign = if data.is_empty() { Sign::ZERO } else { Sign::POS };

        Ok(Self { sign, data })
    }

    pub fn into_radix(mut self, radix: u8) -> Result<Vec<u8>, RadixError> {
        into_radix(&mut self.data, radix)
    }

    pub fn to_radix(&self, radix: u8) -> Result<Vec<u8>, RadixError> {
        self.clone().into_radix(radix)
    }
}

impl UnsignedLong {
    #[allow(dead_code)]
    fn from_raw((data, _): (Vec<Single>, Sign)) -> Self {
        Self { data }
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let data = from_slice_long(slice);

        Self { data }
    }

    pub fn try_from_digits(digits: &[u8], radix: u8) -> Result<Self, TryFromDigitsError> {
        let data = try_from_digits_long(digits, radix)?;

        Ok(Self { data })
    }

    pub fn into_radix(mut self, radix: u8) -> Result<Vec<u8>, RadixError> {
        into_radix(&mut self.data, radix)
    }

    pub fn to_radix(&self, radix: u8) -> Result<Vec<u8>, RadixError> {
        self.clone().into_radix(radix)
    }
}

impl<const L: usize> SignedFixed<L> {
    #[allow(dead_code)]
    fn from_raw((data, sign, len): ([Single; L], Sign, usize)) -> Self {
        Self { data, sign, len }
    }

    pub fn try_from_slice(slice: &[u8]) -> Result<Self, TryFromSliceError> {
        let (data, len) = from_slice_fixed(slice)?;
        let sign = if len == 0 { Sign::ZERO } else { Sign::POS };

        Ok(Self { sign, data, len })
    }

    pub fn try_from_digits(digits: &[u8], radix: u8) -> Result<Self, TryFromDigitsError> {
        let (data, len) = try_from_digits_fixed(digits, radix)?;
        let sign = if len == 0 { Sign::ZERO } else { Sign::POS };

        Ok(Self { sign, data, len })
    }

    pub fn into_radix(mut self, radix: u8) -> Result<Vec<u8>, RadixError> {
        into_radix(&mut self.data[..self.len], radix)
    }

    pub fn to_radix(&self, radix: u8) -> Result<Vec<u8>, RadixError> {
        (*self).into_radix(radix)
    }
}

impl<const L: usize> UnsignedFixed<L> {
    #[allow(dead_code)]
    fn from_raw((data, _, len): ([Single; L], Sign, usize)) -> Self {
        Self { data, len }
    }

    pub fn try_from_slice(slice: &[u8]) -> Result<Self, TryFromSliceError> {
        let (data, len) = from_slice_fixed(slice)?;

        Ok(Self { data, len })
    }

    pub fn try_from_digits(digits: &[u8], radix: u8) -> Result<Self, TryFromDigitsError> {
        let (data, len) = try_from_digits_fixed(digits, radix)?;

        Ok(Self { data, len })
    }

    pub fn into_radix(mut self, radix: u8) -> Result<Vec<u8>, RadixError> {
        into_radix(&mut self.data[..self.len], radix)
    }

    pub fn to_radix(&self, radix: u8) -> Result<Vec<u8>, RadixError> {
        (*self).into_radix(radix)
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

fn from_slice_fixed<const L: usize>(slice: &[u8]) -> Result<([Single; L], usize), TryFromSliceError> {
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

    let sign = if res.is_empty() { Sign::ZERO } else { sign };

    Ok((sign, res))
}

fn try_from_str_fixed<const L: usize>(s: &str) -> Result<(Sign, [Single; L], usize), TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    let (res, len) = try_from_digits_fixed(&digits, radix)?;

    let sign = if len == 0 { Sign::ZERO } else { sign };

    Ok((sign, res, len))
}

fn try_from_digits_long(digits: &[u8], radix: u8) -> Result<Vec<Single>, TryFromDigitsError> {
    fn binary_impl(digits: &[u8], radix: u8) -> Result<Vec<Single>, TryFromDigitsError> {
        if radix < 2 {
            return Err(RadixError::Invalid { radix }.into());
        }

        if let Some(&digit) = digits.iter().find(|&&digit| digit >= radix) {
            return Err(RadixError::InvalidDigit { digit, radix }.into());
        }

        if radix & (radix - 1) > 0 {
            return Err(RadixError::InvalidBin { radix }.into());
        }

        let sbits = Single::BITS as usize;
        let rbits = radix.ilog2() as usize;
        let len = (digits.len() * rbits + sbits - 1) / sbits;

        let mut acc = 0;
        let mut pow = 1;
        let mut idx = 0;
        let mut res = vec![0; len];

        for &digit in digits.iter() {
            acc += pow * digit as Double;
            pow *= radix as Double;

            if pow >= RADIX_VAL {
                res[idx] = (acc & RADIX_MASK) as Single;
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

    match binary_impl(digits, radix) {
        | Ok(val) => return Ok(val),
        | Err(err) => match err {
            | TryFromDigitsError::ExceedLength { len: _, max: _ } => return Err(err),
            | TryFromDigitsError::InvalidRadix(RadixError::Invalid { radix: _ }) => return Err(err),
            | TryFromDigitsError::InvalidRadix(RadixError::InvalidBin { radix: _ }) => (),
            | TryFromDigitsError::InvalidRadix(RadixError::InvalidDigit { digit: _, radix: _ }) => return Err(err),
        },
    }

    let sbits = Single::BITS as usize;
    let rbits = 1 + radix.ilog2() as usize;
    let len = (digits.len() * rbits + sbits - 1) / sbits;

    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for res in res.iter_mut().take(idx + 1) {
            acc += *res as Double * radix as Double;

            *res = (acc & RADIX_MASK) as Single;

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

fn try_from_digits_fixed<const L: usize>(digits: &[u8], radix: u8) -> Result<([Single; L], usize), TryFromDigitsError> {
    fn binary_impl<const L: usize>(digits: &[u8], radix: u8) -> Result<([Single; L], usize), TryFromDigitsError> {
        if radix < 2 {
            return Err(RadixError::Invalid { radix }.into());
        }

        if let Some(&digit) = digits.iter().find(|&&digit| digit >= radix) {
            return Err(RadixError::InvalidDigit { digit, radix }.into());
        }

        if radix & (radix - 1) > 0 {
            return Err(RadixError::InvalidBin { radix }.into());
        }

        let mut acc = 0;
        let mut pow = 1;
        let mut idx = 0;
        let mut res = [0; L];

        for &digit in digits.iter() {
            acc += pow * digit as Double;
            pow *= radix as Double;

            if pow >= RADIX_VAL {
                if idx == L && acc > 0 {
                    return Err(TryFromDigitsError::ExceedLength { len: idx + 1, max: L });
                }

                if idx < L {
                    res[idx] = (acc & RADIX_MASK) as Single;
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

    match binary_impl(digits, radix) {
        | Ok(val) => return Ok(val),
        | Err(err) => match err {
            | TryFromDigitsError::ExceedLength { len: _, max: _ } => return Err(err),
            | TryFromDigitsError::InvalidRadix(RadixError::Invalid { radix: _ }) => return Err(err),
            | TryFromDigitsError::InvalidRadix(RadixError::InvalidBin { radix: _ }) => (),
            | TryFromDigitsError::InvalidRadix(RadixError::InvalidDigit { digit: _, radix: _ }) => return Err(err),
        },
    }

    let mut idx = 0;
    let mut res = [0; L];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for (i, res) in res.iter_mut().enumerate().take(idx + 1) {
            acc += *res as Double * radix as Double;

            *res = (acc & RADIX_MASK) as Single;

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

fn into_radix(digits: &mut [Single], radix: u8) -> Result<Vec<u8>, RadixError> {
    fn binary_impl(digits: &[Single], radix: u8) -> Result<Vec<u8>, RadixError> {
        if radix < 2 {
            return Err(RadixError::Invalid { radix });
        }

        if radix & (radix - 1) > 0 {
            return Err(RadixError::InvalidBin { radix });
        }

        let mask = (radix - 1) as Double;
        let shift = radix.ilog2() as Double;

        let sbits = Single::BITS as usize;
        let rbits = shift as usize;
        let len = (digits.len() * sbits + rbits - 1) / rbits;

        let mut acc = 0;
        let mut rem = 0;
        let mut idx = 0;
        let mut res = vec![0; len];

        for &digit in digits {
            acc |= (digit as Double) << rem;
            rem += sbits as Double;

            while acc >= radix as Double {
                res[idx] = (acc & mask) as u8;
                idx += 1;

                acc >>= shift;
                rem -= shift;
            }
        }

        if acc > 0 {
            res[idx] = acc as u8;
        }

        res.truncate(get_len(&res));

        Ok(res)
    }

    match binary_impl(digits, radix) {
        | Ok(val) => return Ok(val),
        | Err(err) => match err {
            | RadixError::Invalid { radix: _ } => return Err(err),
            | RadixError::InvalidBin { radix: _ } => (),
            | RadixError::InvalidDigit { digit: _, radix: _ } => return Err(err),
        },
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

            *digit = (acc / radix as Double) as Single;

            acc %= radix as Double;
        }

        if any == 0 {
            break;
        }

        res[idx] = acc as u8;
        idx += 1;
        len -= digits.iter().take(len).rev().position(|&digit| digit > 0).unwrap_or(len);
    }

    res.truncate(get_len(&res));

    Ok(res)
}

fn cmp_long(a: &[Single], b: &[Single]) -> Ordering {
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

        res[i] = (acc & RADIX_MASK) as Single;
        acc >>= Single::BITS;
    }

    res.truncate(get_len(&res));

    let sign = if res.is_empty() { Sign::ZERO } else { asign };

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

    let (a, b, sign) = match cmp_long(a, b) {
        | Ordering::Less => (b, a, asign * Sign::NEG),
        | Ordering::Equal => return Default::default(),
        | Ordering::Greater => (a, b, asign * Sign::POS),
    };

    let mut acc = 0;
    let mut res = vec![0; a.len()];

    for i in 0..a.len() {
        let aop = if i < a.len() { a[i] } else { 0 } as Double;
        let bop = if i < b.len() { b[i] } else { 0 } as Double;

        let diff = (RADIX_VAL + aop - bop - acc) & RADIX_MASK;

        res[i] = diff as Single;

        if aop < bop + acc {
            acc = 1;
        } else {
            acc = 0;
        }
    }

    res.truncate(get_len(&res));

    let sign = if res.is_empty() { Sign::ZERO } else { sign };

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

            res[i + j] = (acc & RADIX_MASK) as Single;
            acc >>= Single::BITS;
        }

        let idx = i + b.len();
        let val = acc + res[idx] as Double;

        res[idx] = (val & RADIX_MASK) as Single;
    }

    res.truncate(get_len(&res));

    let sign = if res.is_empty() { Sign::ZERO } else { asign * bsign };

    (res, sign)
}

fn div_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    let (div, _, sign) = divrem_long((a, asign), (b, bsign));

    (div, sign)
}

fn rem_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Sign) {
    let (_, rem, sign) = divrem_long((a, asign), (b, bsign));

    (rem, sign)
}

fn divrem_long((a, asign): (&[Single], Sign), (b, bsign): (&[Single], Sign)) -> (Vec<Single>, Vec<Single>, Sign) {
    match (asign, bsign) {
        | (Sign::ZERO, _) => return Default::default(),
        | (_, Sign::ZERO) => panic!("Division by zero"),
        | _ => (),
    }

    match cmp_long(a, b) {
        | Ordering::Less => return (vec![0], a.to_vec(), asign * bsign),
        | Ordering::Equal => return (vec![1], vec![0], asign * bsign),
        | Ordering::Greater => (),
    }

    let mut div = vec![0; a.len()];
    let mut rem = vec![];

    for i in (0..a.len()).rev() {
        rem.push(a[i]);

        if rem.len() < b.len() {
            continue;
        }

        let mut l = 0 as Double;
        let mut r = RADIX_VAL;
        let mut val = vec![];

        while l < r {
            let m = l + (r - l) / 2;

            val = mul_long((b, Sign::POS), (&[m as Single], Sign::POS)).0;

            match cmp_long(&val, &rem) {
                | Ordering::Less => l = m + 1,
                | Ordering::Equal => {
                    l = m;

                    break;
                },
                | Ordering::Greater => r = m,
            }
        }

        div[i] = l as Single;
        rem = if l > 0 {
            sub_long((&rem, Sign::POS), (&val, Sign::POS)).0
        } else {
            rem
        };
    }

    div.truncate(get_len(&div));
    rem.truncate(get_len(&rem));

    let sign = if div.is_empty() { Sign::ZERO } else { asign * bsign };

    (div, rem, sign)
}

// ops_impl!(@un |a: &SignedLong| -> SignedLong, - SignedLong { sign: -a.sign, data: a.data.clone() });
// ops_impl!(@bin |a: &SignedLong, b: &SignedLong| -> SignedLong,
//     + SignedLong::from_raw(add_long((&a.data, a.sign), (&b.data, b.sign))),
//     - SignedLong::from_raw(sub_long((&a.data, a.sign), (&b.data, b.sign))),
//     * SignedLong::from_raw(mul_long((&a.data, a.sign), (&b.data, b.sign))),
//     / SignedLong::from_raw(div_long((&a.data, a.sign), (&b.data, b.sign))),
//     % SignedLong::from_raw(rem_long((&a.data, a.sign), (&b.data, b.sign))));
//
// ops_impl!(@un <const L: usize> |a: &SignedFixed<L>| -> SignedFixed<L>, - SignedFixed::<L> { sign: -a.sign, data: a.data, len: a.len });
// ops_impl!(@bin <const L: usize> |a: &SignedFixed<L>, b: &SignedFixed<L>| -> SignedFixed<L>,
//     + SignedFixed::<L>::from_raw(add_fixed((&a.data, a.sign, a.len), (&b.data, b.sign, a.len))),
//     - SignedFixed::<L>::from_raw(sub_fixed((&a.data, a.sign, a.len), (&b.data, b.sign, a.len))),
//     * SignedFixed::<L>::from_raw(mul_fixed((&a.data, a.sign, a.len), (&b.data, b.sign, a.len))),
//     / SignedFixed::<L>::from_raw(div_fixed((&a.data, a.sign, a.len), (&b.data, b.sign, a.len))),
//     % SignedFixed::<L>::from_raw(rem_fixed((&a.data, a.sign, a.len), (&b.data, b.sign, a.len))));

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

fn get_radix_from_str(s: &str) -> Result<(&str, u8), TryFromStrError> {
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

fn get_digits_from_str(s: &str, radix: u8) -> Result<Vec<u8>, TryFromStrError> {
    let mut res = s
        .as_bytes()
        .iter()
        .rev()
        .filter_map(|&ch| match ch {
            | b'0'..=b'9' if ch - b'0' < radix => Some(Ok(ch - b'0')),
            | b'a'..=b'f' if ch - b'a' + 10 < radix => Some(Ok(ch - b'a' + 10)),
            | b'A'..=b'F' if ch - b'A' + 10 < radix => Some(Ok(ch - b'A' + 10)),
            | b'_' => None,
            | _ => Some(Err(TryFromStrError::InvalidSymbol(ch as char, radix))),
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
                S32::try_from_slice($expr),
                Ok(S32 {
                    sign: $sign,
                    data: $data,
                    len: $len
                })
            );
        };
        (@unsigned $expr:expr, $data:expr, $len:expr) => {
            assert_eq!(U32::try_from_slice($expr), Ok(U32 { data: $data, len: $len }));
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
        assert_eq!(S32::try_from_slice(&[]), Ok(S32::default()));
        assert_eq!(U32::try_from_slice(&[]), Ok(U32::default()));

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
                assert_long_into_radix!(@signed entry, radix as u8);
                assert_long_into_radix!(@unsigned entry, radix as u8);
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
                assert_fixed_into_radix!(@signed entry, get_len(entry), radix as u8);
                assert_fixed_into_radix!(@unsigned entry, get_len(entry), radix as u8);
            }
        }

        Ok(())
    }

    #[test]
    fn add_long_test() {
        for aop in (i16::MIN..=i16::MAX).step_by(101) {
            for bop in (i16::MIN..=i16::MAX).step_by(103) {
                let aop = aop as i32;
                let bop = bop as i32;

                let along = SignedLong::from(aop);
                let blong = SignedLong::from(bop);

                let (sum, sign_sum) = add_long((&along.data, along.sign), (&blong.data, blong.sign));
                let (sub, sign_sub) = sub_long((&along.data, along.sign), (&blong.data, blong.sign));

                assert_eq!(SignedLong { data: sum, sign: sign_sum }, SignedLong::from(aop + bop));
                assert_eq!(SignedLong { data: sub, sign: sign_sub }, SignedLong::from(aop - bop));
            }
        }
    }

    #[test]
    fn mul_long_test() {
        for aop in (i16::MIN..=i16::MAX).step_by(101) {
            for bop in (i16::MIN..=i16::MAX).step_by(103) {
                let aop = aop as i64;
                let bop = bop as i64;

                let along = SignedLong::from(aop);
                let blong = SignedLong::from(bop);

                let (mul, sign_mul) = mul_long((&along.data, along.sign), (&blong.data, blong.sign));
                // let (div, sign_div) = div_long((&along.data, along.sign), (&blong.data, blong.sign));
                // let (rem, sign_rem) = rem_long((&along.data, along.sign), (&blong.data, blong.sign));

                assert_eq!(SignedLong { data: mul, sign: sign_mul }, SignedLong::from(aop * bop));
                // assert_eq!(SignedLong { data: div, sign: sign_div }, SignedLong::from(aop / bop));
                // assert_eq!(SignedLong { data: rem, sign: sign_rem }, SignedLong::from(aop % bop));
            }
        }
    }
}

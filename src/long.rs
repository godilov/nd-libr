#![allow(clippy::manual_div_ceil)]

use self::{
    digit::{Double, Single},
    radix::RADIX_VAL,
};
use crate::num::Sign;
use radix::RADIX_MASK;
use std::str::FromStr;
use thiserror::Error;

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromStrError {
    #[error("Exceeded maximum length of {max} with {len}")]
    ExceedLength { len: usize, max: usize },
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error("Found invalid symbol `{ch}` during parsing from string of radix `{radix}`")]
    InvalidSymbol { ch: char, radix: u8 },
    #[error("Found negative number during parsing from string for unsigned")]
    UnsignedNegative,
    #[error(transparent)]
    FromDigits(#[from] TryFromDigitsError),
    #[error(transparent)]
    FromRadix(#[from] TryFromRadixError),
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromDigitsError {
    #[error("Exceeded maximum length of {max} with {len}")]
    ExceedLength { len: usize, max: usize },
    #[error(transparent)]
    InvalidRadix(#[from] TryFromRadixError),
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromRadixError {
    #[error("Found invalid radix `{0}`")]
    InvalidRadix(u8),
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

#[macro_export]
macro_rules! signed_fixed {
    ($dataits:expr) => {
        SignedFixed<{ (($dataits + Single::BITS - 1) / Single::BITS) as usize }>
    };
}

#[macro_export]
macro_rules! unsigned_fixed {
    ($dataits:expr) => {
        UnsignedFixed<{ (($dataits + Single::BITS - 1) / Single::BITS) as usize }>
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
    ($type:ident, [$pos:expr, $neg:expr], [$($from:ty),+] $(,)?) => {
        $(from_impl_long!($type, $from, $pos, $neg);)+
    };
    ($type:ident, $from:ty $(, $pos:expr, $neg:expr)?) => {
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

                Self { $(sign: if value > 0 { $pos } else { $neg },)? data }
            }
        }
    };
}

macro_rules! from_impl_fixed {
    ($type:ident, [$($from:ty),+] $(,)?) => {
        $(from_impl_fixed!($type, $from);)+
    };
    ($type:ident, [$pos:expr, $neg:expr], [$($from:ty),+] $(,)?) => {
        $(from_impl_fixed!($type, $from, $pos, $neg);)+
    };
    ($type:ident, $from:ty $(, $pos:expr, $neg:expr)?) => {
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

                Self { $(sign: if value > 0 { $pos } else { $neg },)? data, len }
            }
        }
    };
}

from_impl_long!(
    SignedLong,
    [Sign::POS, Sign::NEG],
    [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize],
);

from_impl_fixed!(
    SignedFixed,
    [Sign::POS, Sign::NEG],
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
    pub fn from_slice(slice: &[u8]) -> Self {
        let data = from_slice_long(slice);
        let sign = if data.is_empty() { Sign::ZERO } else { Sign::POS };

        Self { sign, data }
    }

    pub fn into_radix(self, radix: usize) -> impl Iterator<Item = usize> {
        IntoRadixLongIter { radix, data: self.data }
    }

    pub fn to_radix(&self, radix: usize) -> impl Iterator<Item = usize> {
        self.clone().into_radix(radix)
    }
}

impl UnsignedLong {
    pub fn from_slice(slice: &[u8]) -> Self {
        let data = from_slice_long(slice);

        Self { data }
    }

    pub fn into_radix(self, radix: usize) -> impl Iterator<Item = usize> {
        IntoRadixLongIter { radix, data: self.data }
    }

    pub fn to_radix(&self, radix: usize) -> impl Iterator<Item = usize> {
        self.clone().into_radix(radix)
    }
}

impl<const L: usize> SignedFixed<L> {
    pub fn try_from_slice(slice: &[u8]) -> Result<Self, TryFromStrError> {
        let (data, len) = from_slice_fixed(slice)?;
        let sign = if len == 0 { Sign::ZERO } else { Sign::POS };

        Ok(Self { sign, data, len })
    }

    pub fn into_radix(self, radix: usize) -> impl Iterator<Item = usize> {
        IntoRadixFixedIter {
            radix,
            data: self.data,
            len: self.len,
        }
    }

    pub fn to_radix(&self, radix: usize) -> impl Iterator<Item = usize> {
        (*self).into_radix(radix)
    }
}

impl<const L: usize> UnsignedFixed<L> {
    pub fn try_from_slice(slice: &[u8]) -> Result<Self, TryFromStrError> {
        let (data, len) = from_slice_fixed(slice)?;

        Ok(Self { data, len })
    }

    pub fn into_radix(self, radix: usize) -> impl Iterator<Item = usize> {
        IntoRadixFixedIter {
            radix,
            data: self.data,
            len: self.len,
        }
    }

    pub fn to_radix(&self, radix: usize) -> impl Iterator<Item = usize> {
        (*self).into_radix(radix)
    }
}

fn from_slice_long(slice: &[u8]) -> Vec<Single> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let chunks = slice.chunks(RATIO).enumerate();

    let mut res = vec![0; (slice.len() + RATIO - 1) / RATIO];

    for (i, chunk) in chunks {
        let ptr = &mut res[i];

        for (s, &val) in chunk.iter().enumerate() {
            *ptr |= (val as Single) << (8 * s);
        }
    }

    let len = get_len(&res);

    res.truncate(len);
    res
}

fn from_slice_fixed<const L: usize>(slice: &[u8]) -> Result<([Single; L], usize), TryFromStrError> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (slice.len() + RATIO - 1) / RATIO;

    if len > L {
        return Err(TryFromStrError::ExceedLength { len, max: L });
    }

    let chunks = slice.chunks(RATIO).enumerate();

    let mut res = [0; L];

    for (i, chunk) in chunks {
        let ptr = &mut res[i];

        for (s, &val) in chunk.iter().enumerate() {
            *ptr |= (val as Single) << (8 * s);
        }
    }

    Ok((res, get_len(&res)))
}

fn try_from_str_long(s: &str) -> Result<(Sign, Vec<Single>), TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    let res = try_from_digits_long_bin(&digits, radix).or_else(|_| try_from_digits_long(&digits, radix))?;

    let sign = if res.is_empty() { Sign::ZERO } else { sign };

    Ok((sign, res))
}

fn try_from_str_fixed<const L: usize>(s: &str) -> Result<(Sign, [Single; L], usize), TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;
    let digits = get_digits_from_str(s, radix)?;

    let (res, len) = try_from_digits_fixed_bin(&digits, radix).or_else(|err| match err {
        | TryFromDigitsError::ExceedLength { len: _, max: _ } => Err(err),
        | TryFromDigitsError::InvalidRadix(_) => try_from_digits_fixed(&digits, radix),
    })?;

    let sign = if len == 0 { Sign::ZERO } else { sign };

    Ok((sign, res, len))
}

fn try_from_digits_long_bin(digits: &[u8], radix: u8) -> Result<Vec<Single>, TryFromDigitsError> {
    if radix < 2 || radix & (radix - 1) > 0 {
        return Err(TryFromRadixError::InvalidRadix(radix).into());
    }

    let sbits = Single::BITS as usize;
    let rbits = (2 * radix - 1).ilog2() as usize;
    let len = (digits.len() * rbits + sbits - 1) / sbits;

    let mut acc = 0 as Double;
    let mut pow = 1 as Double;
    let mut res = vec![0; len];
    let mut idx = 0;

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
        idx += 1;
    }

    res.truncate(idx);

    Ok(res)
}

fn try_from_digits_fixed_bin<const L: usize>(
    digits: &[u8],
    radix: u8,
) -> Result<([Single; L], usize), TryFromDigitsError> {
    if radix < 2 || radix & (radix - 1) > 0 {
        return Err(TryFromRadixError::InvalidRadix(radix).into());
    }

    let mut acc = 0 as Double;
    let mut pow = 1 as Double;
    let mut res = [0; L];
    let mut idx = 0;

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
        idx += 1;
    }

    Ok((res, idx))
}

fn try_from_digits_long(digits: &[u8], radix: u8) -> Result<Vec<Single>, TryFromDigitsError> {
    if radix < 2 {
        return Err(TryFromRadixError::InvalidRadix(radix).into());
    }

    let sbits = Single::BITS as usize;
    let rbits = (2 * radix - 1).ilog2() as usize;
    let len = (digits.len() * rbits + sbits - 1) / sbits;

    let mut res = vec![0; len];
    let mut idx = 0;

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

    res.truncate(idx);

    Ok(res)
}

fn try_from_digits_fixed<const L: usize>(digits: &[u8], radix: u8) -> Result<([Single; L], usize), TryFromDigitsError> {
    if radix < 2 {
        return Err(TryFromRadixError::InvalidRadix(radix).into());
    }

    let mut res = [0; L];
    let mut idx = 0;

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

    Ok((res, idx))
}

struct IntoRadixLongIter {
    radix: usize,
    data: Vec<Single>,
}

struct IntoRadixFixedIter<const L: usize> {
    radix: usize,
    data: [Single; L],
    len: usize,
}

impl Iterator for IntoRadixLongIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let mut any = Single::default();
        let mut acc = Double::default();

        for digit in self.data.iter_mut().rev() {
            any |= *digit;
            acc = (acc << Single::BITS) | *digit as Double;

            *digit = (acc / self.radix as Double) as Single;

            acc %= self.radix as Double;
        }

        let len = self.data.len();
        let len = len - self.data.iter().rev().position(|&digit| digit > 0).unwrap_or(len);

        self.data.truncate(len);

        (any != 0).then_some(acc as usize)
    }
}

impl<const L: usize> Iterator for IntoRadixFixedIter<L> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let mut any = Single::default();
        let mut acc = Double::default();

        for digit in self.data.iter_mut().take(self.len).rev() {
            any |= *digit;
            acc = (acc << Single::BITS) | *digit as Double;

            *digit = (acc / self.radix as Double) as Single;

            acc %= self.radix as Double;
        }

        self.len -= self
            .data
            .iter()
            .take(self.len)
            .rev()
            .position(|&digit| digit > 0)
            .unwrap_or(self.len);

        (any != 0).then_some(acc as usize)
    }
}

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

fn get_len(data: &[Single]) -> usize {
    let mut len = data.len();

    for &digit in data.iter().rev() {
        if digit > 0 {
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

    #[test]
    fn from_std_long() {
        assert_eq!(SignedLong::from(0_i8), SignedLong::default());
        assert_eq!(SignedLong::from(0_i16), SignedLong::default());
        assert_eq!(SignedLong::from(0_i32), SignedLong::default());
        assert_eq!(SignedLong::from(0_i64), SignedLong::default());
        assert_eq!(SignedLong::from(0_i128), SignedLong::default());

        assert_eq!(UnsignedLong::from(0_u8), UnsignedLong::default());
        assert_eq!(UnsignedLong::from(0_u16), UnsignedLong::default());
        assert_eq!(UnsignedLong::from(0_u32), UnsignedLong::default());
        assert_eq!(UnsignedLong::from(0_u64), UnsignedLong::default());
        assert_eq!(UnsignedLong::from(0_u128), UnsignedLong::default());

        assert_long_from!(@signed 0xFF_i32, vec![255], Sign::POS);
        assert_long_from!(@signed -0xFF_i32, vec![255], Sign::NEG);
        assert_long_from!(@unsigned 0xFF_u32, vec![255]);

        assert_long_from!(@signed 0x10000000_i32, vec![0, 0, 0, 16], Sign::POS);
        assert_long_from!(@signed -0x10000000_i32, vec![0, 0, 0, 16], Sign::NEG);
        assert_long_from!(@unsigned 0x10000000_u32, vec![0, 0, 0, 16]);

        assert_long_from!(@signed 0xFEDCBA9_i32, vec![169, 203, 237, 15], Sign::POS);
        assert_long_from!(@signed -0xFEDCBA9_i32, vec![169, 203, 237, 15], Sign::NEG);
        assert_long_from!(@unsigned 0xFEDCBA9_u32, vec![169, 203, 237, 15]);
    }

    #[test]
    fn from_std_fixed() {
        assert_eq!(S32::from(0_i8), S32::default());
        assert_eq!(S32::from(0_i16), S32::default());
        assert_eq!(S32::from(0_i32), S32::default());
        assert_eq!(S32::from(0_i64), S32::default());
        assert_eq!(S32::from(0_i128), S32::default());

        assert_eq!(U32::from(0_u8), U32::default());
        assert_eq!(U32::from(0_u16), U32::default());
        assert_eq!(U32::from(0_u32), U32::default());
        assert_eq!(U32::from(0_u64), U32::default());
        assert_eq!(U32::from(0_u128), U32::default());

        assert_fixed_from!(@signed 0xFF_i32, [255, 0, 0, 0], 1, Sign::POS);
        assert_fixed_from!(@signed -0xFF_i32, [255, 0, 0, 0], 1, Sign::NEG);
        assert_fixed_from!(@unsigned 0xFF_u32, [255, 0, 0, 0], 1);

        assert_fixed_from!(@signed 0x10000000_i32, [0, 0, 0, 16], 4, Sign::POS);
        assert_fixed_from!(@signed -0x10000000_i32, [0, 0, 0, 16], 4, Sign::NEG);
        assert_fixed_from!(@unsigned 0x10000000_u32, [0, 0, 0, 16], 4);

        assert_fixed_from!(@signed 0xFEDCBA9_i32, [169, 203, 237, 15], 4, Sign::POS);
        assert_fixed_from!(@signed -0xFEDCBA9_i32, [169, 203, 237, 15], 4, Sign::NEG);
        assert_fixed_from!(@unsigned 0xFEDCBA9_u32, [169, 203, 237, 15], 4);
    }

    #[test]
    fn from_slice_long() {
        assert_eq!(SignedLong::from_slice(&[]), SignedLong::default());
        assert_eq!(UnsignedLong::from_slice(&[]), UnsignedLong::default());

        assert_long_from_slice!(@signed &[255, 0, 0, 0], vec![255], Sign::POS);
        assert_long_from_slice!(@unsigned &[255, 0, 0, 0], vec![255]);

        assert_long_from_slice!(@signed &[0, 0, 0, 16], vec![0, 0, 0, 16], Sign::POS);
        assert_long_from_slice!(@unsigned &[0, 0, 0, 16], vec![0, 0, 0, 16]);

        assert_long_from_slice!(@signed &[169, 203, 237, 15], vec![169, 203, 237, 15], Sign::POS);
        assert_long_from_slice!(@unsigned &[169, 203, 237, 15], vec![169, 203, 237, 15]);
    }

    #[test]
    fn from_slice_fixed() {
        assert_eq!(S32::try_from_slice(&[]), Ok(S32::default()));
        assert_eq!(U32::try_from_slice(&[]), Ok(U32::default()));

        assert_fixed_from_slice!(@signed &[255, 0, 0, 0], [255, 0, 0, 0], 1, Sign::POS);
        assert_fixed_from_slice!(@unsigned &[255, 0, 0, 0], [255, 0, 0, 0], 1);

        assert_fixed_from_slice!(@signed &[0, 0, 0, 16], [0, 0, 0, 16], 4, Sign::POS);
        assert_fixed_from_slice!(@unsigned &[0, 0, 0, 16], [0, 0, 0, 16], 4);

        assert_fixed_from_slice!(@signed &[169, 203, 237, 15], [169, 203, 237, 15], 4, Sign::POS);
        assert_fixed_from_slice!(@unsigned &[169, 203, 237, 15], [169, 203, 237, 15], 4);
    }

    #[test]
    fn from_str_long() {
        assert_eq!(SignedLong::from_str("0"), Ok(SignedLong::default()));
        assert_eq!(SignedLong::from_str("0b0"), Ok(SignedLong::default()));
        assert_eq!(SignedLong::from_str("0o0"), Ok(SignedLong::default()));
        assert_eq!(SignedLong::from_str("0x0"), Ok(SignedLong::default()));

        assert_eq!(UnsignedLong::from_str("0"), Ok(UnsignedLong::default()));
        assert_eq!(UnsignedLong::from_str("0b0"), Ok(UnsignedLong::default()));
        assert_eq!(UnsignedLong::from_str("0o0"), Ok(UnsignedLong::default()));
        assert_eq!(UnsignedLong::from_str("0x0"), Ok(UnsignedLong::default()));

        assert_long_from_str!(@signed "0099", vec![99], Sign::POS);
        assert_long_from_str!(@signed "-0099", vec![99], Sign::NEG);
        assert_long_from_str!(@unsigned "0099", vec![99]);

        assert_long_from_str!(@signed "0b00000011", vec![0b11], Sign::POS);
        assert_long_from_str!(@signed "-0b00000011", vec![0b11], Sign::NEG);
        assert_long_from_str!(@unsigned "0b00000011", vec![0b11]);

        assert_long_from_str!(@signed "0o00000077", vec![0o77], Sign::POS);
        assert_long_from_str!(@signed "-0o00000077", vec![0o77], Sign::NEG);
        assert_long_from_str!(@unsigned "0o00000077", vec![0o77]);

        assert_long_from_str!(@signed "0x000000FF", vec![0xFF], Sign::POS);
        assert_long_from_str!(@signed "-0x000000FF", vec![0xFF], Sign::NEG);
        assert_long_from_str!(@unsigned "0x000000FF", vec![0xFF]);

        assert_long_from_str!(@signed "0000000987654321", vec![177, 104, 222, 58], Sign::POS);
        assert_long_from_str!(@signed "-0000000987654321", vec![177, 104, 222, 58], Sign::NEG);
        assert_long_from_str!(@unsigned "0000000987654321", vec![177, 104, 222, 58]);

        assert_long_from_str!(@signed "0b00000000111110101100011010001000", vec![136, 198, 250], Sign::POS);
        assert_long_from_str!(@signed "-0b00000000111110101100011010001000", vec![136, 198, 250], Sign::NEG);
        assert_long_from_str!(@unsigned "0b00000000111110101100011010001000", vec![136, 198, 250]);

        assert_long_from_str!(@signed "0o00000076543210", vec![136, 198, 250], Sign::POS);
        assert_long_from_str!(@signed "-0o00000076543210", vec![136, 198, 250], Sign::NEG);
        assert_long_from_str!(@unsigned "0o00000076543210", vec![136, 198, 250]);

        assert_long_from_str!(@signed "0x0000000FEDCBA9", vec![169, 203, 237, 15], Sign::POS);
        assert_long_from_str!(@signed "-0x0000000FEDCBA9", vec![169, 203, 237, 15], Sign::NEG);
        assert_long_from_str!(@unsigned "0x0000000FEDCBA9", vec![169, 203, 237, 15]);
    }

    #[test]
    fn from_str_fixed() {
        assert_eq!(S32::from_str("0"), Ok(S32::default()));
        assert_eq!(S32::from_str("0b0"), Ok(S32::default()));
        assert_eq!(S32::from_str("0o0"), Ok(S32::default()));
        assert_eq!(S32::from_str("0x0"), Ok(S32::default()));

        assert_eq!(U32::from_str("0"), Ok(U32::default()));
        assert_eq!(U32::from_str("0b0"), Ok(U32::default()));
        assert_eq!(U32::from_str("0o0"), Ok(U32::default()));
        assert_eq!(U32::from_str("0x0"), Ok(U32::default()));

        assert_fixed_from_str!(@signed "0099", [99, 0, 0, 0], 1, Sign::POS);
        assert_fixed_from_str!(@signed "-0099", [99, 0, 0, 0], 1, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0099", [99, 0, 0, 0], 1);

        assert_fixed_from_str!(@signed "0b00000011", [0b11, 0, 0, 0], 1, Sign::POS);
        assert_fixed_from_str!(@signed "-0b00000011", [0b11, 0, 0, 0], 1, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0b00000011", [0b11, 0, 0, 0], 1);

        assert_fixed_from_str!(@signed "0o00000077", [0o77, 0, 0, 0], 1, Sign::POS);
        assert_fixed_from_str!(@signed "-0o00000077", [0o77, 0, 0, 0], 1, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0o00000077", [0o77, 0, 0, 0], 1);

        assert_fixed_from_str!(@signed "0x000000FF", [0xFF, 0, 0, 0], 1, Sign::POS);
        assert_fixed_from_str!(@signed "-0x000000FF", [0xFF, 0, 0, 0], 1, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0x000000FF", [0xFF, 0, 0, 0], 1);

        assert_fixed_from_str!(@signed "0000000987654321", [177, 104, 222, 58], 4, Sign::POS);
        assert_fixed_from_str!(@signed "-0000000987654321", [177, 104, 222, 58], 4, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0000000987654321", [177, 104, 222, 58], 4);

        assert_fixed_from_str!(@signed "0b00000000111110101100011010001000", [136, 198, 250, 0], 3, Sign::POS);
        assert_fixed_from_str!(@signed "-0b00000000111110101100011010001000", [136, 198, 250, 0], 3, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0b00000000111110101100011010001000", [136, 198, 250, 0], 3);

        assert_fixed_from_str!(@signed "0o00000076543210", [136, 198, 250, 0], 3, Sign::POS);
        assert_fixed_from_str!(@signed "-0o00000076543210", [136, 198, 250, 0], 3, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0o00000076543210", [136, 198, 250, 0], 3);

        assert_fixed_from_str!(@signed "0x0000000FEDCBA9", [169, 203, 237, 15], 4, Sign::POS);
        assert_fixed_from_str!(@signed "-0x0000000FEDCBA9", [169, 203, 237, 15], 4, Sign::NEG);
        assert_fixed_from_str!(@unsigned "0x0000000FEDCBA9", [169, 203, 237, 15], 4);
    }
}

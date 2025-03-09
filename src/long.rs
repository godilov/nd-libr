#![allow(arithmetic_overflow, clippy::manual_div_ceil)]

use self::digit::{Double, Single};
use crate::num::Sign;
use std::str::FromStr;
use thiserror::Error;

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromRadixError {
    #[error("Found invalid radix `{0}`")]
    InvalidRadix(u8),
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromStrError {
    #[error("Exceeded maximum length of {max} with {len}")]
    ExceedLength { len: usize, max: usize },
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error(transparent)]
    InvalidRadix(#[from] TryFromRadixError),
    #[error("Found invalid symbol `{ch}` during parsing from string of radix `{radix}`")]
    InvalidSymbol { ch: char, radix: u8 },
    #[error("Found negative number during parsing from string for unsigned")]
    UnsignedNegative,
}

#[cfg(all(target_pointer_width = "64", not(test)))]
mod digit {
    pub(super) type Single = u64;
    pub(super) type Double = u128;

    pub(super) const OCT_MAX: Single = 1 << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_MAX: Single = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;
}

#[cfg(all(target_pointer_width = "32", not(test)))]
mod digit {
    pub(super) type Single = u32;
    pub(super) type Double = u64;

    pub(super) const OCT_MAX: Single = 1 << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_MAX: Single = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;
}

#[cfg(test)]
mod digit {
    pub(super) type Single = u8;
    pub(super) type Double = u16;

    pub(super) const OCT_MAX: Single = 1 << 6;
    pub(super) const OCT_WIDTH: u8 = 2;

    pub(super) const DEC_MAX: Single = 100;
    pub(super) const DEC_WIDTH: u8 = 2;
}

macro_rules! signed_fixed {
    (@bits $bits:expr) => {
        SignedFixed<{ (($bits + Single::BITS - 1) / Single::BITS) as usize }>
    };
    (@bytes $bytes:expr) => {
        signed_fixed(@bits 8 * $bytes)
    };
}

macro_rules! unsigned_fixed {
    (@bits $bits:expr) => {
        UnsignedFixed<{ (($bits + Single::BITS - 1) / Single::BITS) as usize }>
    };
    (@bytes $bytes:expr) => {
        signed_fixed(@bits 8 * $bytes)
    };
}

pub type S128 = signed_fixed!(@bits 128);
pub type S192 = signed_fixed!(@bits 192);
pub type S256 = signed_fixed!(@bits 256);
pub type S384 = signed_fixed!(@bits 384);
pub type S512 = signed_fixed!(@bits 512);
pub type S1024 = signed_fixed!(@bits 1024);
pub type S2048 = signed_fixed!(@bits 2048);
pub type S3072 = signed_fixed!(@bits 3072);
pub type S4096 = signed_fixed!(@bits 4096);

pub type U128 = unsigned_fixed!(@bits 128);
pub type U192 = unsigned_fixed!(@bits 192);
pub type U256 = unsigned_fixed!(@bits 256);
pub type U384 = unsigned_fixed!(@bits 384);
pub type U512 = unsigned_fixed!(@bits 512);
pub type U1024 = unsigned_fixed!(@bits 1024);
pub type U2048 = unsigned_fixed!(@bits 2048);
pub type U3072 = unsigned_fixed!(@bits 3072);
pub type U4096 = unsigned_fixed!(@bits 4096);

#[allow(unused)]
mod radix {
    use super::{
        Single, TryFromRadixError,
        digit::{DEC_MAX, DEC_WIDTH, OCT_MAX, OCT_WIDTH},
    };

    pub trait Constants {
        const MAX: Single = Single::MAX;
        const WIDTH: u8;
        const PREFIX: &str;
        const ALPHABET: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;
    pub struct Radix {
        pub max: Single,
        pub width: u8,
        pub prefix: &'static str,
        pub alphabet: &'static str,
    }

    impl Constants for Bin {
        const MAX: Single = Single::MAX;
        const WIDTH: u8 = Single::BITS as u8;
        const PREFIX: &str = "0b";
        const ALPHABET: &str = "01";
    }

    impl Constants for Oct {
        const MAX: Single = OCT_MAX;
        const WIDTH: u8 = OCT_WIDTH;
        const PREFIX: &str = "0o";
        const ALPHABET: &str = "01234567";
    }

    impl Constants for Dec {
        const MAX: Single = DEC_MAX;
        const WIDTH: u8 = DEC_WIDTH;
        const PREFIX: &str = "";
        const ALPHABET: &str = "0123456789";
    }

    impl Constants for Hex {
        const MAX: Single = Single::MAX;
        const WIDTH: u8 = Single::BITS as u8 / 4;
        const PREFIX: &str = "0x";
        const ALPHABET: &str = "0123456789ABCDEF";
    }

    impl TryFrom<u8> for Radix {
        type Error = TryFromRadixError;

        fn try_from(value: u8) -> Result<Self, Self::Error> {
            match value {
                | 2 => Ok(Self {
                    max: Bin::MAX,
                    width: Bin::WIDTH,
                    prefix: Bin::PREFIX,
                    alphabet: Bin::ALPHABET,
                }),
                | 8 => Ok(Self {
                    max: Oct::MAX,
                    width: Oct::WIDTH,
                    prefix: Oct::PREFIX,
                    alphabet: Oct::ALPHABET,
                }),
                | 10 => Ok(Self {
                    max: Dec::MAX,
                    width: Dec::WIDTH,
                    prefix: Dec::PREFIX,
                    alphabet: Dec::ALPHABET,
                }),
                | 16 => Ok(Self {
                    max: Hex::MAX,
                    width: Hex::WIDTH,
                    prefix: Hex::PREFIX,
                    alphabet: Hex::ALPHABET,
                }),
                | _ => Err(TryFromRadixError::InvalidRadix(value)),
            }
        }
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
                    val >>= Single::BITS;
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
                    val >>= Single::BITS;
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

from_impl_long!(UnsignedLong, [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize]);
from_impl_fixed!(UnsignedFixed, [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize]);

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
    pub fn from_slice(slice: &[u8]) -> Result<Self, TryFromStrError> {
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
    pub fn from_slice(slice: &[u8]) -> Result<Self, TryFromStrError> {
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
    let s = s.as_bytes();
    let (s, sign) = get_sign(s)?;
    let (s, radix) = get_radix(s)?;
    let vals = get_values(s, radix)?;

    let sbits = Single::BITS as usize;
    let rbits = (2 * radix - 1).ilog2() as usize;
    let len = (s.len() * rbits + sbits - 1) / sbits;

    let mut acc = 0 as Double;
    let mut mul = 1 as Double;
    let mut idx = 0;
    let mut res = vec![0; len];

    for &val in vals.iter().rev() {
        acc += mul * val as Double;
        mul *= radix as Double;

        if acc > Single::MAX as Double {
            let div = acc / Single::MAX as Double;
            let rem = acc % Single::MAX as Double;

            acc = div;
            mul = 1;

            res[idx] = rem as Single;
            idx += 1;
        }
    }

    if acc > 0 {
        res[idx] = acc as Single;
    }

    let len = get_len(&res);

    res.truncate(len);

    let sign = if res.is_empty() { Sign::ZERO } else { sign };

    Ok((sign, res))
}

fn try_from_str_fixed<const L: usize>(s: &str) -> Result<(Sign, [Single; L], usize), TryFromStrError> {
    let s = s.as_bytes();
    let (s, sign) = get_sign(s)?;
    let (s, radix) = get_radix(s)?;
    let vals = get_values(s, radix)?;

    let mut acc = 0 as Double;
    let mut mul = 1 as Double;
    let mut idx = 0;
    let mut res = [0; L];

    for &val in vals.iter().rev() {
        acc += mul * val as Double;
        mul *= radix as Double;

        if acc > Single::MAX as Double {
            if idx == L {
                return Err(TryFromStrError::ExceedLength { len: idx + 1, max: L });
            }

            let div = acc / Single::MAX as Double;
            let rem = acc % Single::MAX as Double;

            acc = div;
            mul = 1;

            res[idx] = rem as Single;
            idx += 1;
        }
    }

    if acc > 0 && idx < L {
        res[idx] = acc as Single;
    } else if idx == L {
        return Err(TryFromStrError::ExceedLength { len: idx + 1, max: L });
    }

    let len = get_len(&res);

    let sign = if len == 0 { Sign::ZERO } else { sign };

    Ok((sign, res, len))
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

fn get_sign(s: &[u8]) -> Result<(&[u8], Sign), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    let val = match s[0] {
        | b'+' => (&s[1..], Sign::POS),
        | b'-' => (&s[1..], Sign::NEG),
        | _ => (s, Sign::POS),
    };

    Ok(val)
}

fn get_radix(s: &[u8]) -> Result<(&[u8], u8), TryFromStrError> {
    if s.is_empty() {
        return Err(TryFromStrError::InvalidLength);
    }

    if s.len() < 2 {
        return Ok((s, 10));
    }

    let val = match &s[..2] {
        | b"0x" | b"0X" => (&s[..2], 16),
        | b"0o" | b"0O" => (&s[..2], 8),
        | b"0b" | b"0B" => (&s[..2], 2),
        | _ => (s, 10),
    };

    Ok(val)
}

fn get_values(s: &[u8], radix: u8) -> Result<Vec<u8>, TryFromStrError> {
    s.iter()
        .map(|&ch| match ch {
            | b'0'..=b'9' if ch - b'0' < radix => Ok(ch - b'0'),
            | b'a'..=b'f' if ch - b'a' + 10 < radix => Ok(ch - b'a' + 10),
            | b'A'..=b'F' if ch - b'A' + 10 < radix => Ok(ch - b'A' + 10),
            | _ => Err(TryFromStrError::InvalidSymbol { ch: ch as char, radix }),
        })
        .collect::<Result<Vec<u8>, TryFromStrError>>()
}

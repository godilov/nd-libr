use self::digit::{Double, Single};
use crate::num::Sign;
use std::str::FromStr;
use thiserror::Error;

pub use self::fixed::{
    S128, S192, S256, S384, S512, S1024, S2048, S3072, S4096, U128, U192, U256, U384, U512, U1024, U2048, U3072, U4096,
};

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromBytesError {
    #[error("Exceeded maximum length of {max} with {len}")]
    ExceedLength { len: usize, max: usize },
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromStrError {
    #[error("Found empty during parsing from String")]
    Empty,
    #[error("Found negative number during parsing of Unsigned from String")]
    UnsignedNegative,
}

#[cfg(target_pointer_width = "64")]
mod digit {
    pub(super) type Single = u32;
    pub(super) type Double = u64;

    pub(super) const DEC_MAX: Single = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;

    pub(super) const OCT_MAX: Single = 1 << 30;
    pub(super) const OCT_WIDTH: u8 = 10;
}

#[cfg(target_pointer_width = "64")]
mod fixed {
    use super::{SignedFixed, UnsignedFixed};

    pub type S128 = SignedFixed<4>;
    pub type S192 = SignedFixed<6>;
    pub type S256 = SignedFixed<8>;
    pub type S384 = SignedFixed<12>;
    pub type S512 = SignedFixed<16>;
    pub type S1024 = SignedFixed<32>;
    pub type S2048 = SignedFixed<64>;
    pub type S3072 = SignedFixed<96>;
    pub type S4096 = SignedFixed<128>;

    pub type U128 = UnsignedFixed<4>;
    pub type U192 = UnsignedFixed<6>;
    pub type U256 = UnsignedFixed<8>;
    pub type U384 = UnsignedFixed<12>;
    pub type U512 = UnsignedFixed<16>;
    pub type U1024 = UnsignedFixed<32>;
    pub type U2048 = UnsignedFixed<64>;
    pub type U3072 = UnsignedFixed<96>;
    pub type U4096 = UnsignedFixed<128>;
}

#[cfg(target_pointer_width = "32")]
mod digit {
    pub(super) type Single = u16;
    pub(super) type Double = u32;

    pub(super) const DEC_MAX: Single = 10_000;
    pub(super) const DEC_WIDTH: u8 = 4;

    pub(super) const OCT_MAX: Single = 1 << 15;
    pub(super) const OCT_WIDTH: u8 = 5;
}

#[cfg(target_pointer_width = "32")]
mod fixed {
    use super::{SignedFixed, UnsignedFixed};

    pub type S128 = SignedFixed<8>;
    pub type S192 = SignedFixed<12>;
    pub type S256 = SignedFixed<16>;
    pub type S384 = SignedFixed<24>;
    pub type S512 = SignedFixed<32>;
    pub type S1024 = SignedFixed<64>;
    pub type S2048 = SignedFixed<128>;
    pub type S3072 = SignedFixed<192>;
    pub type S4096 = SignedFixed<256>;

    pub type U128 = UnsignedFixed<8>;
    pub type U192 = UnsignedFixed<12>;
    pub type U256 = UnsignedFixed<16>;
    pub type U384 = UnsignedFixed<24>;
    pub type U512 = UnsignedFixed<32>;
    pub type U1024 = UnsignedFixed<64>;
    pub type U2048 = UnsignedFixed<128>;
    pub type U3072 = UnsignedFixed<192>;
    pub type U4096 = UnsignedFixed<256>;
}

#[allow(unused)]
mod radix {
    use super::{
        Single,
        digit::{DEC_MAX, DEC_WIDTH, OCT_MAX, OCT_WIDTH},
    };

    pub trait Radix {
        const MAX: Single = Single::MAX;
        const WIDTH: u8;
        const PREFIX: &str;
        const ALPHABET: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Radix for Bin {
        const MAX: Single = Single::MAX;
        const WIDTH: u8 = Single::BITS as u8;
        const PREFIX: &str = "0b";
        const ALPHABET: &str = "01";
    }

    impl Radix for Oct {
        const MAX: Single = OCT_MAX;
        const WIDTH: u8 = OCT_WIDTH;
        const PREFIX: &str = "0o";
        const ALPHABET: &str = "01234567";
    }

    impl Radix for Dec {
        const MAX: Single = DEC_MAX;
        const WIDTH: u8 = DEC_WIDTH;
        const PREFIX: &str = "";
        const ALPHABET: &str = "0123456789";
    }

    impl Radix for Hex {
        const MAX: Single = Single::MAX;
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
            #[allow(arithmetic_overflow, clippy::manual_div_ceil)]
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
            #[allow(arithmetic_overflow)]
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
    pub fn from_slice(slice: &[u8]) -> Result<Self, TryFromBytesError> {
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
    pub fn from_slice(slice: &[u8]) -> Result<Self, TryFromBytesError> {
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

#[allow(clippy::manual_div_ceil)]
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

#[allow(clippy::manual_div_ceil)]
fn from_slice_fixed<const L: usize>(slice: &[u8]) -> Result<([Single; L], usize), TryFromBytesError> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (slice.len() + RATIO - 1) / RATIO;
    if len > L {
        return Err(TryFromBytesError::ExceedLength { len, max: L });
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

    todo!()
}

fn try_from_str_fixed<const L: usize>(s: &str) -> Result<(Sign, [Single; L], usize), TryFromStrError> {
    let s = s.as_bytes();
    let (s, sign) = get_sign(s)?;
    let (s, radix) = get_radix(s)?;

    todo!()
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
        return Err(TryFromStrError::Empty);
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
        return Err(TryFromStrError::Empty);
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

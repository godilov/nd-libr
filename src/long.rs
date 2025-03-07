use self::digit::{Double, Single};
use crate::num::Sign;
use std::str::FromStr;
use thiserror::Error;

pub use self::fixed::{
    S128, S192, S256, S384, S512, S1024, S2048, S3072, S4096, U128, U192, U256, U384, U512, U1024, U2048, U3072, U4096,
};

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryFromIteratorError {
    #[error("Iterator exceeds maximum length of {len}")]
    ExceedLength { len: usize },
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedLong {
    sign: Sign,
    data: Vec<Single>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedLong {
    data: Vec<Single>,
}

impl Default for SignedLong {
    fn default() -> Self {
        Self { sign: Sign::NIL, data: vec![0] }
    }
}

impl Default for UnsignedLong {
    fn default() -> Self {
        Self { data: vec![0] }
    }
}

// TODO: Make from u8
// impl FromIterator<Single> for SignedLong {
//     fn from_iter<T: IntoIterator<Item = Single>>(iter: T) -> Self {
//         Self::new(Sign::POS, iter.into_iter().collect())
//     }
// }
//
// impl FromIterator<Single> for UnsignedLong {
//     fn from_iter<T: IntoIterator<Item = Single>>(iter: T) -> Self {
//         Self::new(iter.into_iter().collect())
//     }
// }

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

impl SignedLong {
    fn new(sign: Sign, mut data: Vec<Single>) -> Self {
        let len = get_len(&data);

        data.truncate(len);

        let sign = if data.is_empty() { Sign::NIL } else { sign };

        Self { sign, data }
    }

    pub fn from_bytes(sign: Sign, data: &[u8]) -> Self {
        todo!()
    }

    pub fn into_radix(self, radix: usize) -> impl Iterator<Item = usize> {
        IntoRadixLongIter { radix, data: self.data }
    }

    pub fn to_radix(&self, radix: usize) -> impl Iterator<Item = usize> {
        self.clone().into_radix(radix)
    }
}

impl UnsignedLong {
    fn new(mut data: Vec<Single>) -> Self {
        let len = get_len(&data);

        data.truncate(len);

        Self { data }
    }

    pub fn from_bytes(sign: Sign, data: &[u8]) -> Self {
        todo!()
    }

    pub fn into_radix(self, radix: usize) -> impl Iterator<Item = usize> {
        IntoRadixLongIter { radix, data: self.data }
    }

    pub fn to_radix(&self, radix: usize) -> impl Iterator<Item = usize> {
        self.clone().into_radix(radix)
    }
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
            sign: Sign::NIL,
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

// TODO: Make from u8
// impl<const L: usize> TryFromIterator<Single> for SignedFixed<L> {
//     type Error = TryFromIteratorError;
//
//     fn try_from_iter<T: IntoIterator<Item = Single>>(iter: T) -> Result<Self, Self::Error> {
//         let (data, len) = try_from_iter(iter)?;
//
//         Ok(Self { sign: Sign::POS, data, len })
//     }
// }
//
// impl<const L: usize> TryFromIterator<Single> for UnsignedFixed<L> {
//     type Error = TryFromIteratorError;
//
//     fn try_from_iter<T: IntoIterator<Item = Single>>(iter: T) -> Result<Self, Self::Error> {
//         let (data, len) = try_from_iter(iter)?;
//
//         Ok(Self { data, len })
//     }
// }

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

impl<const L: usize> SignedFixed<L> {
    fn new(sign: Sign, data: [Single; L]) -> Self {
        let len = get_len(&data);

        Self { sign, data, len }
    }

    pub fn from_bytes(sign: Sign, data: &[u8]) -> Self {
        todo!()
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
    fn new(data: [Single; L]) -> Self {
        let len = get_len(&data);

        Self { data, len }
    }

    pub fn from_bytes(sign: Sign, data: &[u8]) -> Self {
        todo!()
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

// fn try_from_iter<const L: usize, T: IntoIterator<Item = Single>>(
//     iter: T,
// ) -> Result<([Single; L], usize), TryFromIteratorError> {
//     let mut data = [0; L];
//     let mut len = 0;
//
//     for (i, digit) in iter.into_iter().enumerate() {
//         if i == L {
//             return Err(TryFromIteratorError::ExceedLength { len: L });
//         }
//
//         if digit != 0 {
//             data[i] = digit;
//             len = i + 1;
//         }
//     }
//
//     Ok((data, len))
// }

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

use std::{
    cmp::Ordering,
    fmt::Formatter,
    io::{Cursor, Write},
    marker::PhantomData,
};

use thiserror::Error;
use zerocopy::{IntoBytes, transmute_mut};

use crate::{
    long::{_macro::*, radix::*, uops::*},
    num::*,
    ops::*,
    word::*,
};

pub mod bytes;
pub mod num;

macro_rules! signed {
    ($bits:expr) => {
        $crate::long::num::Signed<{ ($bits as usize).div_ceil($crate::word::BITS as usize) }>
    };
}

macro_rules! unsigned {
    ($bits:expr) => {
        $crate::long::num::Unsigned<{ ($bits as usize).div_ceil($crate::word::BITS as usize) }>
    };
}

macro_rules! bytes {
    ($bits:expr) => {
        $crate::long::bytes::Bytes<{ ($bits as usize).div_ceil($crate::word::BITS as usize) }>
    };
}

macro_rules! from_primitive {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!(@bytes $primitive);)+
    };
    (@signed $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Signed<L> {
            #[allow(unused_comparisons)]
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr_trunc(&bytes, if value >= 0 { 0 } else { MAX });

                Self(res)
            }
        }
    };
    (@unsigned $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Unsigned<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr_trunc(&bytes, 0);

                Self(res)
            }
        }
    };
    (@bytes $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Bytes<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr_trunc(&bytes, 0);

                Self(res)
            }
        }
    };
}

macro_rules! from_primitive_const {
    (@signed [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(from_primitive_const!(@signed $fn, $primitive);)+
    };
    (@unsigned [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(from_primitive_const!(@unsigned $fn, $primitive);)+
    };
    (@bytes [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(from_primitive_const!(@unsigned $fn, $primitive);)+
    };
    (@signed $fn:ident, $primitive:ty) => {
        pub const fn $fn(val: $primitive) -> Self {
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
    (@bytes $fn:ident, $primitive:ty) => {
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
            return Err(FromDigitsError::InvalidRadix {
                radix: $radix.as_single() as usize,
            });
        }

        if let Some(digit) = $digits.find(|&digit| digit >= $radix) {
            return Err(FromDigitsError::InvalidDigit {
                digit: digit.as_single() as usize,
                radix: $radix.as_single() as usize,
            });
        }

        Ok(())
    }};
}

macro_rules! from_digits_impl {
    ($digits:expr, $len:expr, $exp:expr) => {{
        let bits = $exp as usize;
        let mask = (1 << BITS) - 1;

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

macro_rules! from_digits_arb_impl {
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

pub mod radix {
    use super::*;

    pub struct Dec;
    pub struct Bin;
    pub struct Oct;
    pub struct Hex;

    pub struct Radix {
        pub prefix: &'static str,
        pub value: Double,
        pub width: u8,
    }

    pub trait NumRadix {}
    pub trait BytesRadix {}

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

    impl NumRadix for Dec {}
    impl NumRadix for Bin {}
    impl NumRadix for Oct {}
    impl NumRadix for Hex {}

    impl BytesRadix for Bin {}
    impl BytesRadix for Oct {}
    impl BytesRadix for Hex {}
}

#[allow(unused)]
mod uops {
    use super::*;

    macro_rules! inc_impl {
        ($digits:expr) => {{
            #[allow(unused_mut)]
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
            #[allow(unused_mut)]
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

    macro_rules! shl_impl {
        ($digits:expr, $digits_ret:expr, $shift:expr, $default:expr, $fn:expr) => {{
            let shift = $shift;
            let offset = shift / BITS;
            let shl = shift % BITS;
            let shr = BITS - shl;

            if offset >= L {
                return ($fn)($digits_ret);
            }

            #[allow(unused_mut)]
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
        ($digits:expr, $digits_ret:expr, $shift:expr, $default:expr, $fn:expr) => {{
            let shift = $shift;
            let offset = shift / BITS;
            let shr = shift % BITS;
            let shl = BITS - shr;

            if offset >= L {
                return ($fn)($digits_ret);
            }

            #[allow(unused_mut)]
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

    #[allow(unused_variables)]
    pub(super) fn shl<const L: usize>(digits: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shl_impl!(*digits, digits, shift, default, |digits: &[Single; L]| { [default; L] })
    }

    #[allow(unused_variables)]
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

#[rustfmt::skip]
mod _macro {
    pub(crate) use from_primitive;
    pub(crate) use from_primitive_const;
    pub(crate) use from_digits_validate;
    pub(crate) use from_digits_impl;
    pub(crate) use from_digits_arb_impl;
}

pub type S8 = signed!(8);
pub type S12 = signed!(12);
pub type S16 = signed!(16);
pub type S24 = signed!(24);
pub type S32 = signed!(32);
pub type S48 = signed!(48);
pub type S64 = signed!(64);
pub type S96 = signed!(96);
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

pub type U8 = unsigned!(8);
pub type U12 = unsigned!(12);
pub type U16 = unsigned!(16);
pub type U24 = unsigned!(24);
pub type U32 = unsigned!(32);
pub type U48 = unsigned!(48);
pub type U64 = unsigned!(64);
pub type U96 = unsigned!(96);
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

pub type B8 = bytes!(8);
pub type B12 = bytes!(12);
pub type B16 = bytes!(16);
pub type B24 = bytes!(24);
pub type B32 = bytes!(32);
pub type B48 = bytes!(48);
pub type B64 = bytes!(64);
pub type B96 = bytes!(96);
pub type B128 = bytes!(128);
pub type B192 = bytes!(192);
pub type B256 = bytes!(256);
pub type B384 = bytes!(384);
pub type B512 = bytes!(512);
pub type B768 = bytes!(768);
pub type B1024 = bytes!(1024);
pub type B1536 = bytes!(1536);
pub type B2048 = bytes!(2048);
pub type B3072 = bytes!(3072);
pub type B4096 = bytes!(4096);
pub type B6144 = bytes!(6144);
pub type B8192 = bytes!(8192);

#[derive(Debug, Clone)]
pub struct DigitsIter<'digits, const L: usize, W: Word> {
    digits: &'digits [Single; L],
    bits: usize,
    mask: Double,
    cnt: usize,
    len: usize,
    acc: Double,
    shl: usize,
    idx: usize,
    _phantom: PhantomData<W>,
}

#[derive(Debug, Clone)]
pub struct DigitsArbIter<const L: usize, W: Word> {
    digits: [Single; L],
    radix: W,
    len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromArrError {
    #[error("Found invalid length during initializing from array")]
    InvalidLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromSliceError {
    #[error("Found invalid length during initializing from slice")]
    InvalidLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromStrError {
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
    #[error("Found invalid symbol '{ch}' during parsing from string of radix '{radix}'")]
    InvalidSymbol { ch: char, radix: u8 },
}

impl<'digits, const L: usize, W: Word> ExactSizeIterator for DigitsIter<'digits, L, W> {}
impl<'digits, const L: usize, W: Word> Iterator for DigitsIter<'digits, L, W> {
    type Item = W;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.cnt {
            if self.acc == 0 {
                return None;
            }

            let val = self.acc;

            self.acc >>= self.bits;
            self.shl = self.shl.saturating_sub(self.bits);

            return Some(W::from_double(val & self.mask));
        }

        if self.shl < self.bits {
            self.acc |= (self.digits[self.idx] as Double) << self.shl;
            self.shl += BITS;
            self.idx += 1;
        }

        let val = self.acc;

        self.acc >>= self.bits;
        self.shl -= self.bits;

        Some(W::from_double(val & self.mask))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<const L: usize, W: Word> ExactSizeIterator for DigitsArbIter<L, W> {}
impl<const L: usize, W: Word> Iterator for DigitsArbIter<L, W> {
    type Item = W;

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

        Some(W::from_double(acc))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

const fn from_bytes<const L: usize>(bytes: &[u8]) -> [Single; L] {
    let (bytes, bytes_) = bytes.as_chunks::<BYTES>();

    let mut idx = 0;
    let mut idx_ = 0;
    let mut res = [0; L];

    #[allow(clippy::modulo_one)]
    while idx < bytes.len() && idx < L * BYTES {
        let offset = idx / BYTES;
        let shift = idx % BYTES;
        let byte = bytes[offset][shift] as Single;

        idx += 1;
        res[offset] |= byte << shift;
    }

    #[allow(clippy::modulo_one)]
    while idx_ < bytes_.len() && idx < L * BYTES {
        let offset = idx / BYTES;
        let shift = idx % BYTES;
        let shift_ = idx_ % BYTES;
        let byte = bytes_[shift_] as Single;

        idx += 1;
        idx_ += 1;
        res[offset] |= byte << shift;
    }

    res
}

fn from_arr<const L: usize, const N: usize, W: Word>(
    arr: &[W; N],
    default: Single,
) -> Result<[Single; L], FromArrError> {
    match (N * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_arr_trunc(arr, default)),
        Ordering::Equal => Ok(from_arr_trunc(arr, default)),
        Ordering::Greater => Err(FromArrError::InvalidLength),
    }
}

fn from_slice<const L: usize, W: Word>(slice: &[W]) -> Result<[Single; L], FromSliceError> {
    match (slice.len() * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_slice_trunc(slice)),
        Ordering::Equal => Ok(from_slice_trunc(slice)),
        Ordering::Greater => Err(FromSliceError::InvalidLength),
    }
}

fn from_arr_trunc<const L: usize, const N: usize, W: Word>(arr: &[W; N], default: Single) -> [Single; L] {
    let len = N.min(L * BYTES / W::BYTES);

    let mut res = [default; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])[..len].copy_from_slice(&arr[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_slice_trunc<const L: usize, W: Word>(slice: &[W]) -> [Single; L] {
    let len = slice.len().min(L * BYTES / W::BYTES);

    let mut res = [0; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])[..len].copy_from_slice(&slice[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_iter<const L: usize, W: Word, Iter: Iterator<Item = W>>(iter: Iter) -> [Single; L] {
    let mut res = [0; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])
        .iter_mut()
        .zip(iter)
        .for_each(|(ptr, val)| *ptr = val);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_str_validate(s: &str, radix: u8) -> Result<(), FromStrError> {
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
        return Err(FromStrError::InvalidSymbol { ch, radix });
    }

    Ok(())
}

fn from_str<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    from_str_validate(s, 1 << exp)?;

    let mut res = from_digits_impl!(s.bytes().rev().filter_map(get_digit_from_byte), s.len(), exp);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn from_str_arb<const L: usize>(s: &str, radix: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    if radix.is_pow2() {
        return from_str(s, radix.order() as u8, sign);
    }

    from_str_validate(s, radix)?;

    let mut res = from_digits_arb_impl!(s.bytes().filter_map(get_digit_from_byte), radix);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn write_dec(mut cursor: Cursor<&mut [u8]>, word: Single, width: usize) -> std::fmt::Result {
    match cursor.write_fmt(format_args!("{word:0width$}")) {
        Ok(()) => (),
        Err(_) => return Err(std::fmt::Error),
    }

    Ok(())
}

fn write_bin(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    #[allow(clippy::unnecessary_cast)]
    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (word % 2) as u8;
        word /= 2;
    }

    Ok(())
}

fn write_oct(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    #[allow(clippy::unnecessary_cast)]
    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (word % 8) as u8;
        word /= 8;
    }

    Ok(())
}

fn write_lhex(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[(word % 16) as usize];
        word /= 16;
    }

    Ok(())
}

fn write_uhex(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D', b'E', b'F',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[(word % 16) as usize];
        word /= 16;
    }

    Ok(())
}

fn write<const L: usize, F: Fn(Cursor<&mut [u8]>, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    words: &[Single; L],
    radix: Radix,
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
    let len = get_len_arr(words);

    let mut buf = vec![b'0'; len * width];

    for (i, &word) in words[..len].iter().enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), word, width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, prefix, str)
}

fn write_iter<Words: WordsIterator, F: Fn(Cursor<&mut [u8]>, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    words: Words,
    radix: Radix,
    sign: Sign,
    func: F,
) -> std::fmt::Result
where
    <Words as Iterator>::Item: Word,
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
    let len = words.len();

    let mut buf = vec![b'0'; len * width];

    for (i, word) in words.enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), word.as_single(), width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, prefix, str)
}

fn get_sign_from_str(s: &str) -> Result<(&str, Sign), FromStrError> {
    if s.is_empty() {
        return Err(FromStrError::InvalidLength);
    }

    Ok(match &s[..1] {
        "+" => (&s[1..], Sign::POS),
        "-" => (&s[1..], Sign::NEG),
        _ => (s, Sign::POS),
    })
}

fn get_radix_from_str(s: &str, default: u8) -> Result<(&str, u8), FromStrError> {
    if s.is_empty() {
        return Err(FromStrError::InvalidLength);
    }

    if s.len() < 2 {
        return Ok((s, 10));
    }

    Ok(match &s[..2] {
        "0x" | "0X" => (&s[2..], 16),
        "0o" | "0O" => (&s[2..], 8),
        "0b" | "0B" => (&s[2..], 2),
        _ => (s, default),
    })
}

fn get_digit_from_byte(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn get_len_arr<W: Word, const L: usize>(words: &[W; L]) -> usize {
    for (i, word) in words.iter().enumerate().rev() {
        if word != &W::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_len_slice<W: Word>(words: &[W]) -> usize {
    for (i, word) in words.iter().enumerate().rev() {
        if word != &W::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_sign<W: Word, const L: usize>(words: &[W; L], sign: Sign) -> Sign {
    if words != &[W::ZERO; L] { sign } else { Sign::ZERO }
}

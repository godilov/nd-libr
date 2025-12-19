#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    iter::{once, repeat},
    marker::PhantomData,
    str::FromStr,
};

use ndproc::ops_impl;
use thiserror::Error;
use zerocopy::IntoBytes;

use crate::long::*;

macro_rules! ops_primitive_native_impl {
    (@signed [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_native_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_native_impl!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: $primitive| -> Signed::<L>,
            + Signed::<L>(add_signed(&a.0, (b.unsigned_abs() as Single, Sign::from(b)))),
            - Signed::<L>(sub_signed(&a.0, (b.unsigned_abs() as Single, Sign::from(b)))),
            * Signed::<L>(mul_signed(&a.0, (b.unsigned_abs() as Single, Sign::from(b)))),
            / Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).0).with_sign(a.sign() * Sign::from(b)),
            % Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).1).with_sign(a.sign()),
            | Signed::<L>(bit_single(&a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop | bop)),
            & Signed::<L>(bit_single(&a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop & bop)),
            ^ Signed::<L>(bit_single(&a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Signed<L>, b: $primitive|,
            += add_signed_mut(&mut a.0, (b.unsigned_abs() as Single, Sign::from(b))),
            -= sub_signed_mut(&mut a.0, (b.unsigned_abs() as Single, Sign::from(b))),
            *= mul_signed_mut(&mut a.0, (b.unsigned_abs() as Single, Sign::from(b))),
            /= { *a = Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).0).with_sign(a.sign() * Sign::from(b)); },
            %= { *a = Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).1).with_sign(a.sign()); },
            |= bit_single_mut(&mut a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop | bop),
            &= bit_single_mut(&mut a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop & bop),
            ^= bit_single_mut(&mut a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop ^ bop));
    };
    (@unsigned $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: $primitive| -> Unsigned::<L>,
            + Unsigned::<L>(add_single(&a.0, b as Single)),
            - Unsigned::<L>(sub_single(&a.0, b as Single)),
            * Unsigned::<L>(mul_single(&a.0, b as Single)),
            / Unsigned::<L>(div_single(&a.0, b as Single).0),
            % Unsigned::<L>(div_single(&a.0, b as Single).1),
            | Unsigned::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop | bop)),
            & Unsigned::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop & bop)),
            ^ Unsigned::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, b: $primitive|,
            += add_single_mut(&mut a.0, b as Single),
            -= sub_single_mut(&mut a.0, b as Single),
            *= mul_single_mut(&mut a.0, b as Single),
            /= div_single_mut(&mut a.0, b as Single),
            %= rem_single_mut(&mut a.0, b as Single),
            |= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop | bop),
            &= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop & bop),
            ^= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop ^ bop));
    };
}

macro_rules! ops_primitive_impl {
    (@signed [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_impl!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: $primitive| -> Signed::<L>,
            + Signed::<L>(add_long(&a.0, &Signed::<L>::from(b).0)),
            - Signed::<L>(sub_long(&a.0, &Signed::<L>::from(b).0)),
            * Signed::<L>(mul_long(&a.0, &Signed::<L>::from(b).0)),
            / Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).0).with_sign(a.sign() * Sign::from(b)),
            % Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).1).with_sign(a.sign()),
            | Signed::<L>(bit_long(&a.0, &Signed::<L>::from(b).0, |aop, bop| aop | bop)),
            & Signed::<L>(bit_long(&a.0, &Signed::<L>::from(b).0, |aop, bop| aop & bop)),
            ^ Signed::<L>(bit_long(&a.0, &Signed::<L>::from(b).0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Signed<L>, b: $primitive|,
            += add_long_mut(&mut a.0, &Signed::<L>::from(b).0),
            -= sub_long_mut(&mut a.0, &Signed::<L>::from(b).0),
            *= mul_long_mut(&mut a.0, &Signed::<L>::from(b).0),
            /= { *a = Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).0).with_sign(a.sign() * Sign::from(b)); },
            %= { *a = Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).1).with_sign(a.sign()); },
            |= bit_long_mut(&mut a.0, &Signed::<L>::from(b).0, |aop, bop| aop | bop),
            &= bit_long_mut(&mut a.0, &Signed::<L>::from(b).0, |aop, bop| aop & bop),
            ^= bit_long_mut(&mut a.0, &Signed::<L>::from(b).0, |aop, bop| aop ^ bop));
    };
    (@unsigned $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: $primitive| -> Unsigned::<L>,
            + Unsigned::<L>(add_long(&a.0, &Unsigned::<L>::from(b).0)),
            - Unsigned::<L>(sub_long(&a.0, &Unsigned::<L>::from(b).0)),
            * Unsigned::<L>(mul_long(&a.0, &Unsigned::<L>::from(b).0)),
            / Unsigned::<L>(div_long(&a.0, &Unsigned::<L>::from(b).0).0),
            % Unsigned::<L>(div_long(&a.0, &Unsigned::<L>::from(b).0).1),
            | Unsigned::<L>(bit_long(&a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop | bop)),
            & Unsigned::<L>(bit_long(&a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop & bop)),
            ^ Unsigned::<L>(bit_long(&a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, b: $primitive|,
            += add_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            -= sub_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            *= mul_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            /= div_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            %= rem_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            |= bit_long_mut(&mut a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop | bop),
            &= bit_long_mut(&mut a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop & bop),
            ^= bit_long_mut(&mut a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop ^ bop));
    };
}

macro_rules! from_str_impl {
    ($str:expr) => {{
        let (s, sign) = get_sign_from_str($str)?;
        let (s, radix) = get_radix_from_str(s, 10)?;

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, sign)
        } else {
            from_str_arb(s, radix, sign)
        }
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
    (@overflow $a:expr, $b:expr, $acc:expr) => {
        $a.scan($b as Double, |_, a| {
            let val = a as Double + $acc;

            $acc = val / RADIX;

            Some(val as Single)
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
    (@overflow $a:expr, $b:expr, $acc:expr) => {{
        $a.scan(0, |_, a| {
            let val = a as Double * $b as Double + $acc;

            $acc = val / RADIX;

            Some(val as Single)
        })
    }};
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
        #[allow(unused_mut)]
        let mut div = $a;
        let mut rem = [0; L];

        for val in div.iter_mut().rev() {
            cycle!(rem, *val);

            let digit = search!(@upper 0, RADIX, |m: Double| {
                let mut acc = 0;

                let mul = mul_single_impl!(@overflow $b, m, acc).collect_with([0; L]);

                if acc > 0 {
                    return Ordering::Greater;
                }

                mul.iter().rev().cmp(rem.iter().rev())
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
        #[allow(unused_mut)]
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

macro_rules! cycle {
    ($arr:expr, $val:expr) => {{
        for i in (1..$arr.len()).rev() {
            $arr[i] = $arr[i - 1];
        }

        $arr[0] = $val;
    }};
}

macro_rules! search {
    (@lower $l:expr, $r:expr, $fn:expr) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match ($fn)(m) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => r = m,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
    (@upper $l:expr, $r:expr, $fn:expr) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match ($fn)(m) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
}

#[cfg(all(target_pointer_width = "64", not(test)))]
mod _impl {
    use super::*;

    ops_primitive_native_impl!(@signed [i8, i16, i32, i64]);
    ops_primitive_native_impl!(@unsigned [u8, u16, u32, u64]);

    ops_primitive_impl!(@signed [i128]);
    ops_primitive_impl!(@unsigned [u128]);
}

#[cfg(all(target_pointer_width = "32", not(test)))]
mod _impl {
    use super::*;

    ops_primitive_native_impl!(@signed [i8, i16, i32]);
    ops_primitive_native_impl!(@unsigned [u8, u16, u32]);

    ops_primitive_impl!(@signed [i64, i128]);
    ops_primitive_impl!(@unsigned [u64, u128]);
}

#[cfg(test)]
mod _impl {
    use super::*;

    ops_primitive_native_impl!(@signed [i8]);
    ops_primitive_native_impl!(@unsigned [u8]);

    ops_primitive_impl!(@signed [i16, i32, i64, i128]);
    ops_primitive_impl!(@unsigned [u16, u32, u64, u128]);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
    #[error("Found invalid digit '{digit}' during parsing from slice of radix '{radix}'")]
    InvalidDigit { digit: usize, radix: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum ToDigitsError {
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum IntoDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
}

#[ndproc::align]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Signed<const L: usize>(pub [Single; L]);

#[ndproc::align]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

from_primitive!(@signed [i8, i16, i32, i64, i128, isize]);
from_primitive!(@unsigned [u8, u16, u32, u64, u128, usize]);

impl From<ToDigitsError> for IntoDigitsError {
    fn from(value: ToDigitsError) -> Self {
        match value {
            ToDigitsError::InvalidExponent { exp } => Self::InvalidRadix { radix: exp.order() },
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

impl<const L: usize, W: Word> FromIterator<W> for Signed<L> {
    fn from_iter<T: IntoIterator<Item = W>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Unsigned<L> {
    fn from_iter<T: IntoIterator<Item = W>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(from_str_impl!(s)?))
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(from_str_impl!(s)?))
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

impl<const L: usize> PartialOrd for Signed<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> PartialOrd for Unsigned<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> Ord for Signed<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        let x = self.sign();
        let y = other.sign();

        if x != y {
            return x.cmp(&y);
        }

        let ord = self.0.iter().rev().cmp(other.0.iter().rev());

        match x {
            Sign::ZERO => ord,
            Sign::NEG => match ord {
                Ordering::Less => Ordering::Greater,
                Ordering::Equal => Ordering::Equal,
                Ordering::Greater => Ordering::Less,
            },
            Sign::POS => ord,
        }
    }
}

impl<const L: usize> Ord for Unsigned<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.iter().rev().cmp(other.0.iter().rev())
    }
}

impl<const L: usize> Display for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.with_sign(Sign::POS).into_digits_iter(Dec::RADIX as Single) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Dec.into(), get_sign(&self.0, self.sign()), write_dec)
    }
}

impl<const L: usize> Display for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.into_digits_iter(Dec::RADIX as Single) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Dec.into(), get_sign(&self.0, self.sign()), write_dec)
    }
}

impl<const L: usize> Binary for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Octal for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(Oct::EXP) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(Oct::EXP) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> LowerHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> UpperHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
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

ops_impl!(@mut <const L: usize> |a: mut Signed<L>, *b: &Signed<L>|,
    += add_long_mut(&mut a.0, &b.0),
    -= sub_long_mut(&mut a.0, &b.0),
    *= mul_long_mut(&mut a.0, &b.0),
    /= { *a = Signed::<L>(div_long(&a.abs().0, &b.abs().0).0).with_sign(a.sign() * b.sign()); },
    %= { *a = Signed::<L>(div_long(&a.abs().0, &b.abs().0).1).with_sign(a.sign()); },
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, *b: &Unsigned<L>|,
    += add_long_mut(&mut a.0, &b.0),
    -= sub_long_mut(&mut a.0, &b.0),
    *= mul_long_mut(&mut a.0, &b.0),
    /= div_long_mut(&mut a.0, &b.0),
    %= rem_long_mut(&mut a.0, &b.0),
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: usize| -> Signed::<L>,
    << Signed::<L>(shl_signed(&a.0, b)),
    >> Signed::<L>(shr_signed(&a.0, b)));

ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: usize| -> Unsigned::<L>,
    << Unsigned::<L>(shl(&a.0, b, 0)),
    >> Unsigned::<L>(shr(&a.0, b, 0)));

ops_impl!(@mut <const L: usize> |a: mut Signed<L>, b: usize|,
    <<= { shl_signed_mut(&mut a.0, b); },
    >>= { shr_signed_mut(&mut a.0, b); });

ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, b: usize|,
    <<= { shl_mut(&mut a.0, b, 0); },
    >>= { shr_mut(&mut a.0, b, 0); });

impl<const L: usize> Signed<L> {
    from_primitive_const!(@signed [
        (from_i8, i8),
        (from_i16, i16),
        (from_i32, i32),
        (from_i64, i64),
        (from_i128, i128),
        (from_isize, isize),
    ]);

    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }

    pub fn from_arr<const N: usize, W: Word>(arr: &[W; N]) -> Result<Self, FromArrError> {
        Ok(Self(from_arr(arr, 0)?))
    }

    pub fn from_slice<W: Word>(slice: &[W]) -> Result<Self, FromSliceError> {
        Ok(Self(from_slice(slice)?))
    }

    pub fn from_arr_trunc<const N: usize, W: Word>(arr: &[W; N]) -> Self {
        Self(from_arr_trunc(arr, 0))
    }

    pub fn from_slice_trunc<W: Word>(arr: &[W]) -> Self {
        Self(from_slice_trunc(arr))
    }

    pub fn from_digits<W: Word>(digits: impl AsRef<[W]>, exp: u8) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), exp).map(Self)
    }

    pub fn from_digits_iter<W: Word, Words: WordsIterator<Item = W>>(
        digits: Words,
        exp: u8,
    ) -> Result<Self, FromDigitsError> {
        from_digits_iter(digits, exp).map(Self)
    }

    pub fn from_digits_arb<W: Word>(digits: impl AsRef<[W]>, radix: W) -> Result<Self, FromDigitsError> {
        from_digits_arb(digits.as_ref(), radix).map(Self)
    }

    pub fn from_digits_arb_iter<W: Word, Words: WordsIterator<Item = W> + DoubleEndedIterator>(
        digits: Words,
        radix: W,
    ) -> Result<Self, FromDigitsError> {
        from_digits_arb_iter(digits, radix).map(Self)
    }

    pub fn to_digits<W: Word>(&self, exp: u8) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, exp)
    }

    pub fn to_digits_iter<W: Word>(&self, exp: u8) -> Result<DigitsIter<'_, L, W>, ToDigitsError> {
        to_digits_iter(&self.0, exp)
    }

    pub fn into_digits<W: Word>(self, radix: W) -> Result<Vec<W>, IntoDigitsError> {
        into_digits(self.0, radix)
    }

    pub fn into_digits_iter<W: Word>(self, radix: W) -> Result<DigitsArbIter<L, W>, IntoDigitsError> {
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
    from_primitive_const!(@unsigned [
        (from_u8, u8),
        (from_u16, u16),
        (from_u32, u32),
        (from_u64, u64),
        (from_u128, u128),
        (from_usize, usize),
    ]);

    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }

    pub fn from_arr<const N: usize, W: Word>(arr: &[W; N]) -> Result<Self, FromArrError> {
        Ok(Self(from_arr(arr, 0)?))
    }

    pub fn from_slice<W: Word>(slice: &[W]) -> Result<Self, FromSliceError> {
        Ok(Self(from_slice(slice)?))
    }

    pub fn from_arr_trunc<const N: usize, W: Word>(arr: &[W; N]) -> Self {
        Self(from_arr_trunc(arr, 0))
    }

    pub fn from_slice_trunc<W: Word>(arr: &[W]) -> Self {
        Self(from_slice_trunc(arr))
    }

    pub fn from_digits<W: Word>(digits: impl AsRef<[W]>, exp: u8) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), exp).map(Self)
    }

    pub fn from_digits_iter<W: Word, Words: WordsIterator<Item = W>>(
        digits: Words,
        exp: u8,
    ) -> Result<Self, FromDigitsError> {
        from_digits_iter(digits, exp).map(Self)
    }

    pub fn from_digits_arb<W: Word>(digits: impl AsRef<[W]>, radix: W) -> Result<Self, FromDigitsError> {
        from_digits_arb(digits.as_ref(), radix).map(Self)
    }

    pub fn from_digits_arb_iter<W: Word, Words: WordsIterator<Item = W> + DoubleEndedIterator>(
        digits: Words,
        radix: W,
    ) -> Result<Self, FromDigitsError> {
        from_digits_arb_iter(digits, radix).map(Self)
    }

    pub fn to_digits<W: Word>(&self, exp: u8) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, exp)
    }

    pub fn to_digits_iter<W: Word>(&self, exp: u8) -> Result<DigitsIter<'_, L, W>, ToDigitsError> {
        to_digits_iter(&self.0, exp)
    }

    pub fn into_digits<W: Word>(self, radix: W) -> Result<Vec<W>, IntoDigitsError> {
        into_digits(self.0, radix)
    }

    pub fn into_digits_iter<W: Word>(self, radix: W) -> Result<DigitsArbIter<L, W>, IntoDigitsError> {
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

fn to_digits_validate<W: Word>(exp: u8) -> Result<(), ToDigitsError> {
    if exp == 0 || exp >= W::BITS as u8 {
        return Err(ToDigitsError::InvalidExponent { exp });
    }

    Ok(())
}

fn into_digits_validate<W: Word>(radix: W) -> Result<(), IntoDigitsError> {
    let radix = radix.as_single() as usize;

    if radix < 2 {
        return Err(IntoDigitsError::InvalidRadix { radix });
    }

    Ok(())
}

fn from_digits<const L: usize, W: Word>(digits: &[W], exp: u8) -> Result<[Single; L], FromDigitsError> {
    if exp >= W::BITS as u8 {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate!(digits.iter().copied(), W::from_single(1 << exp))?;

    let res = from_digits_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn from_digits_iter<const L: usize, W: Word, Words: WordsIterator<Item = W>>(
    digits: Words,
    exp: u8,
) -> Result<[Single; L], FromDigitsError> {
    if exp >= W::BITS as u8 {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate!(digits.clone(), W::from_single(1 << exp))?;

    let res = from_digits_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn from_digits_arb<const L: usize, W: Word>(digits: &[W], radix: W) -> Result<[Single; L], FromDigitsError> {
    if radix.is_pow2() {
        return from_digits(digits, radix.order() as u8);
    }

    from_digits_validate!(digits.iter().copied(), radix)?;

    let res = from_digits_arb_impl!(digits.iter().rev(), radix);

    Ok(res)
}

fn from_digits_arb_iter<const L: usize, W: Word, Words: WordsIterator<Item = W> + DoubleEndedIterator>(
    digits: Words,
    radix: W,
) -> Result<[Single; L], FromDigitsError> {
    if radix.is_pow2() {
        return from_digits_iter(digits, radix.order() as u8);
    }

    from_digits_validate!(digits.clone(), radix)?;

    let res = from_digits_arb_impl!(digits.rev(), radix);

    Ok(res)
}

fn to_digits<const L: usize, W: Word>(digits: &[Single; L], exp: u8) -> Result<Vec<W>, ToDigitsError> {
    to_digits_validate::<W>(exp)?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![W::ZERO; len + 1];

    for &digit in digits {
        acc |= (digit as Double) << shl;
        shl += BITS;
        res[idx] = W::from_double(acc & mask);

        while shl >= bits {
            acc >>= bits;
            shl -= bits;
            idx += 1;
            res[idx] = W::from_double(acc & mask);
        }
    }

    res.truncate(get_len_slice(&res));

    Ok(res)
}

fn to_digits_iter<const L: usize, W: Word>(
    digits: &[Single; L],
    exp: u8,
) -> Result<DigitsIter<'_, L, W>, ToDigitsError> {
    to_digits_validate::<W>(exp)?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let cnt = get_len_arr(digits);
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

fn into_digits<const L: usize, W: Word>(mut digits: [Single; L], radix: W) -> Result<Vec<W>, IntoDigitsError> {
    if radix.is_pow2() {
        return Ok(to_digits(&digits, radix.order() as u8)?);
    }

    into_digits_validate(radix)?;

    let bits = radix.order();
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut idx = 0;
    let mut res = vec![W::ZERO; len + 1];

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

        res[idx] = W::from_double(acc);
        idx += 1;
    }

    res.truncate(get_len_slice(&res));

    Ok(res)
}

fn into_digits_iter<const L: usize, W: Word>(
    digits: [Single; L],
    radix: W,
) -> Result<DigitsArbIter<L, W>, IntoDigitsError> {
    into_digits_validate(radix)?;

    let bits = radix.order();
    let cnt = get_len_arr(&digits);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsArbIter { digits, radix, len })
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

    (div, from_arr_trunc(&rem.to_le_bytes(), 0))
}

fn bit_single<const L: usize, F>(a: &[Single; L], b: Single, default: Single, f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    a.iter()
        .copied()
        .zip(once(b).chain(repeat(default)))
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

fn add_signed<const L: usize>(a: &[Single; L], (b, sign): (Single, Sign)) -> [Single; L] {
    match sign {
        Sign::ZERO => sub_single(a, b),
        Sign::NEG => sub_single(a, b),
        Sign::POS => add_single(a, b),
    }
}

fn sub_signed<const L: usize>(a: &[Single; L], (b, sign): (Single, Sign)) -> [Single; L] {
    match sign {
        Sign::ZERO => add_single(a, b),
        Sign::NEG => add_single(a, b),
        Sign::POS => sub_single(a, b),
    }
}

fn mul_signed<const L: usize>(a: &[Single; L], (b, sign): (Single, Sign)) -> [Single; L] {
    let mut mul = mul_single(a, b);

    if sign == Sign::NEG {
        neg_mut(&mut mul);
    }

    mul
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

    *a = from_arr_trunc(&rem.to_le_bytes(), 0);
}

fn bit_single_mut<const L: usize, F>(a: &mut [Single; L], b: Single, default: Single, f: F)
where
    F: Fn(Single, Single) -> Single,
{
    a.iter_mut()
        .zip(once(b).chain(repeat(default)))
        .for_each(|(ptr, val)| *ptr = f(*ptr, val));
}

fn add_signed_mut<const L: usize>(a: &mut [Single; L], (b, sign): (Single, Sign)) {
    match sign {
        Sign::ZERO => sub_single_mut(a, b),
        Sign::NEG => sub_single_mut(a, b),
        Sign::POS => add_single_mut(a, b),
    }
}

fn sub_signed_mut<const L: usize>(a: &mut [Single; L], (b, sign): (Single, Sign)) {
    match sign {
        Sign::ZERO => add_single_mut(a, b),
        Sign::NEG => add_single_mut(a, b),
        Sign::POS => sub_single_mut(a, b),
    }
}

fn mul_signed_mut<const L: usize>(a: &mut [Single; L], (b, sign): (Single, Sign)) {
    mul_single_mut(a, b);

    if sign == Sign::NEG {
        neg_mut(a);
    }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat;

    use anyhow::Result;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;
    use crate::long::{S64, U64};

    const PRIMES_48BIT: [usize; 2] = [281_415_416_265_077, 281_397_419_487_323];
    const PRIMES_56BIT: [usize; 2] = [72_057_582_686_044_051, 72_051_998_136_909_223];

    macro_rules! assert_ops {
        ($type:ty, $iter_a:expr, $iter_b:expr, [$(($fn_lval:expr) ($fn_rval:expr)),+ $(,)?]) => {
            for a in $iter_a {
                for b in $iter_b {
                    let along = <$type>::from(a);
                    let blong = <$type>::from(b);

                    $({
                        let lval = ($fn_lval)(along, blong);
                        let rval = ($fn_rval)(a, b);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };
    }

    macro_rules! assert_ops_primitive {
        ($type:ty, $iter_a:expr, $iter_b:expr, [$(($fn_lval:expr) ($fn_rval:expr)),+ $(,)?]) => {
            for a in $iter_a {
                for b in $iter_b {
                    let long = <$type>::from(a);

                    $({
                        let lval = ($fn_lval)(long, b);
                        let rval = ($fn_rval)(a, b);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };
    }

    macro_rules! assert_ops_shift {
        ($type:ty, $iter_val:expr, $iter_shift:expr, [$(($fn_lval:expr) ($fn_rval:expr)),+ $(,)?]) => {
            for val in $iter_val {
                for shift in $iter_shift {
                    let long = <$type>::from(val);

                    $({
                        let lval = ($fn_lval)(long, shift);
                        let rval = ($fn_rval)(val, shift);

                        assert_eq!(lval, rval);
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
    fn from_bytes() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_eq!(S64::from_bytes(&bytes), S64 { 0: pos(&bytes) });
            assert_eq!(U64::from_bytes(&bytes), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_arr() -> Result<()> {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_eq!(S64::from_arr(&bytes)?, S64 { 0: pos(&bytes) });
            assert_eq!(U64::from_arr(&bytes)?, U64 { 0: pos(&bytes) });
        }

        Ok(())
    }

    #[test]
    fn from_slice() -> Result<()> {
        let empty = &[] as &[u8];

        assert_eq!(S64::from_slice(empty)?, S64::default());
        assert_eq!(U64::from_slice(empty)?, U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();
            let slice = bytes.as_slice();

            assert_eq!(S64::from_slice(slice)?, S64 { 0: pos(&bytes) });
            assert_eq!(U64::from_slice(slice)?, U64 { 0: pos(&bytes) });
        }

        Ok(())
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
        assert_ops!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: S64, b: S64| { a + b })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|a: S64, b: S64| { a - b })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|a: S64, b: S64| { a * b })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|a: S64, b: S64| { a / b })(|a: i64, b: i64| { S64::from(a / b) }),
                (|a: S64, b: S64| { a % b })(|a: i64, b: i64| { S64::from(a % b) }),
                (|a: S64, b: S64| { a | b })(|a: i64, b: i64| { S64::from(a | b) }),
                (|a: S64, b: S64| { a & b })(|a: i64, b: i64| { S64::from(a & b) }),
                (|a: S64, b: S64| { a ^ b })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops() {
        assert_ops!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: U64, b: U64| { a + b })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|a: U64, b: U64| { a - b })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|a: U64, b: U64| { a * b })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|a: U64, b: U64| { a / b })(|a: u64, b: u64| { U64::from(a / b) }),
                (|a: U64, b: U64| { a % b })(|a: u64, b: u64| { U64::from(a % b) }),
                (|a: U64, b: U64| { a | b })(|a: u64, b: u64| { U64::from(a | b) }),
                (|a: U64, b: U64| { a & b })(|a: u64, b: u64| { U64::from(a & b) }),
                (|a: U64, b: U64| { a ^ b })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn signed_ops_primitive_native() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i8::MIN..i8::MAX).filter(|&x| x != 0),
            [
                (|a: S64, b: i8| { a + b })(|a: i64, b: i8| { S64::from(a.wrapping_add(b as i64)) }),
                (|a: S64, b: i8| { a - b })(|a: i64, b: i8| { S64::from(a.wrapping_sub(b as i64)) }),
                (|a: S64, b: i8| { a * b })(|a: i64, b: i8| { S64::from(a.wrapping_mul(b as i64)) }),
                (|a: S64, b: i8| { a / b })(|a: i64, b: i8| { S64::from(a / b as i64) }),
                (|a: S64, b: i8| { a % b })(|a: i64, b: i8| { S64::from(a % b as i64) }),
                (|a: S64, b: i8| { a | b })(|a: i64, b: i8| { S64::from(a | b as i64) }),
                (|a: S64, b: i8| { a & b })(|a: i64, b: i8| { S64::from(a & b as i64) }),
                (|a: S64, b: i8| { a ^ b })(|a: i64, b: i8| { S64::from(a ^ b as i64) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops_primitive_native() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            1..u8::MAX,
            [
                (|a: U64, b: u8| { a + b })(|a: u64, b: u8| { U64::from(a.wrapping_add(b as u64)) }),
                (|a: U64, b: u8| { a - b })(|a: u64, b: u8| { U64::from(a.wrapping_sub(b as u64)) }),
                (|a: U64, b: u8| { a * b })(|a: u64, b: u8| { U64::from(a.wrapping_mul(b as u64)) }),
                (|a: U64, b: u8| { a / b })(|a: u64, b: u8| { U64::from(a / b as u64) }),
                (|a: U64, b: u8| { a % b })(|a: u64, b: u8| { U64::from(a % b as u64) }),
                (|a: U64, b: u8| { a | b })(|a: u64, b: u8| { U64::from(a | b as u64) }),
                (|a: U64, b: u8| { a & b })(|a: u64, b: u8| { U64::from(a & b as u64) }),
                (|a: U64, b: u8| { a ^ b })(|a: u64, b: u8| { U64::from(a ^ b as u64) }),
            ]
        );
    }

    #[test]
    fn signed_ops_primitive() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: S64, b: i64| { a + b })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|a: S64, b: i64| { a - b })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|a: S64, b: i64| { a * b })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|a: S64, b: i64| { a / b })(|a: i64, b: i64| { S64::from(a / b) }),
                (|a: S64, b: i64| { a % b })(|a: i64, b: i64| { S64::from(a % b) }),
                (|a: S64, b: i64| { a | b })(|a: i64, b: i64| { S64::from(a | b) }),
                (|a: S64, b: i64| { a & b })(|a: i64, b: i64| { S64::from(a & b) }),
                (|a: S64, b: i64| { a ^ b })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops_primitive() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: U64, b: u64| { a + b })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|a: U64, b: u64| { a - b })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|a: U64, b: u64| { a * b })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|a: U64, b: u64| { a / b })(|a: u64, b: u64| { U64::from(a / b) }),
                (|a: U64, b: u64| { a % b })(|a: u64, b: u64| { U64::from(a % b) }),
                (|a: U64, b: u64| { a | b })(|a: u64, b: u64| { U64::from(a | b) }),
                (|a: U64, b: u64| { a & b })(|a: u64, b: u64| { U64::from(a & b) }),
                (|a: U64, b: u64| { a ^ b })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_mut() {
        assert_ops!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: S64, b: S64| { a += b; a })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|mut a: S64, b: S64| { a -= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|mut a: S64, b: S64| { a *= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|mut a: S64, b: S64| { a /= b; a })(|a: i64, b: i64| { S64::from(a / b) }),
                (|mut a: S64, b: S64| { a %= b; a })(|a: i64, b: i64| { S64::from(a % b) }),
                (|mut a: S64, b: S64| { a |= b; a })(|a: i64, b: i64| { S64::from(a | b) }),
                (|mut a: S64, b: S64| { a &= b; a })(|a: i64, b: i64| { S64::from(a & b) }),
                (|mut a: S64, b: S64| { a ^= b; a })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_mut() {
        assert_ops!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: U64, b: U64| { a += b; a })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|mut a: U64, b: U64| { a -= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|mut a: U64, b: U64| { a *= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|mut a: U64, b: U64| { a /= b; a })(|a: u64, b: u64| { U64::from(a / b) }),
                (|mut a: U64, b: U64| { a %= b; a })(|a: u64, b: u64| { U64::from(a % b) }),
                (|mut a: U64, b: U64| { a |= b; a })(|a: u64, b: u64| { U64::from(a | b) }),
                (|mut a: U64, b: U64| { a &= b; a })(|a: u64, b: u64| { U64::from(a & b) }),
                (|mut a: U64, b: U64| { a ^= b; a })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_primitive_native_mut() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i8::MIN..i8::MAX).filter(|&x| x != 0),
            [
                (|mut a: S64, b: i8| { a += b; a })(|a: i64, b: i8| { S64::from(a.wrapping_add(b as i64)) }),
                (|mut a: S64, b: i8| { a -= b; a })(|a: i64, b: i8| { S64::from(a.wrapping_sub(b as i64)) }),
                (|mut a: S64, b: i8| { a *= b; a })(|a: i64, b: i8| { S64::from(a.wrapping_mul(b as i64)) }),
                (|mut a: S64, b: i8| { a /= b; a })(|a: i64, b: i8| { S64::from(a / b as i64) }),
                (|mut a: S64, b: i8| { a %= b; a })(|a: i64, b: i8| { S64::from(a % b as i64) }),
                (|mut a: S64, b: i8| { a |= b; a })(|a: i64, b: i8| { S64::from(a | b as i64) }),
                (|mut a: S64, b: i8| { a &= b; a })(|a: i64, b: i8| { S64::from(a & b as i64) }),
                (|mut a: S64, b: i8| { a ^= b; a })(|a: i64, b: i8| { S64::from(a ^ b as i64) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_primitive_native_mut() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            1..u8::MAX,
            [
                (|mut a: U64, b: u8| { a += b; a })(|a: u64, b: u8| { U64::from(a.wrapping_add(b as u64)) }),
                (|mut a: U64, b: u8| { a -= b; a })(|a: u64, b: u8| { U64::from(a.wrapping_sub(b as u64)) }),
                (|mut a: U64, b: u8| { a *= b; a })(|a: u64, b: u8| { U64::from(a.wrapping_mul(b as u64)) }),
                (|mut a: U64, b: u8| { a /= b; a })(|a: u64, b: u8| { U64::from(a / b as u64) }),
                (|mut a: U64, b: u8| { a %= b; a })(|a: u64, b: u8| { U64::from(a % b as u64) }),
                (|mut a: U64, b: u8| { a |= b; a })(|a: u64, b: u8| { U64::from(a | b as u64) }),
                (|mut a: U64, b: u8| { a &= b; a })(|a: u64, b: u8| { U64::from(a & b as u64) }),
                (|mut a: U64, b: u8| { a ^= b; a })(|a: u64, b: u8| { U64::from(a ^ b as u64) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_primitive_mut() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: S64, b: i64| { a += b; a })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|mut a: S64, b: i64| { a -= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|mut a: S64, b: i64| { a *= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|mut a: S64, b: i64| { a /= b; a })(|a: i64, b: i64| { S64::from(a / b) }),
                (|mut a: S64, b: i64| { a %= b; a })(|a: i64, b: i64| { S64::from(a % b) }),
                (|mut a: S64, b: i64| { a |= b; a })(|a: i64, b: i64| { S64::from(a | b) }),
                (|mut a: S64, b: i64| { a &= b; a })(|a: i64, b: i64| { S64::from(a & b) }),
                (|mut a: S64, b: i64| { a ^= b; a })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_primitive_mut() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: U64, b: u64| { a += b; a })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|mut a: U64, b: u64| { a -= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|mut a: U64, b: u64| { a *= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|mut a: U64, b: u64| { a /= b; a })(|a: u64, b: u64| { U64::from(a / b) }),
                (|mut a: U64, b: u64| { a %= b; a })(|a: u64, b: u64| { U64::from(a % b) }),
                (|mut a: U64, b: u64| { a |= b; a })(|a: u64, b: u64| { U64::from(a | b) }),
                (|mut a: U64, b: u64| { a &= b; a })(|a: u64, b: u64| { U64::from(a & b) }),
                (|mut a: U64, b: u64| { a ^= b; a })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn signed_ops_shift() {
        assert_ops_shift!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_48BIT[0]),
            0..64,
            [
                (|val: S64, shift: usize| { val << shift })(|val: i64, shift: usize| { S64::from(val << shift) }),
                (|val: S64, shift: usize| { val >> shift })(|val: i64, shift: usize| { S64::from(val >> shift) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops_shift() {
        assert_ops_shift!(
            U64,
            (1..u64::MAX).step_by(PRIMES_48BIT[0]),
            0..64,
            [
                (|val: U64, shift: usize| { val << shift })(|val: u64, shift: usize| { U64::from(val << shift) }),
                (|val: U64, shift: usize| { val >> shift })(|val: u64, shift: usize| { U64::from(val >> shift) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_shift_mut() {
        assert_ops_shift!(S64, (i64::MIN + 1..i64::MAX).step_by(PRIMES_48BIT[0]), 0..64, [
            (|mut val: S64, shift: usize| { val <<= shift; val })(|val: i64, shift: usize| { S64::from(val << shift) }),
            (|mut val: S64, shift: usize| { val >>= shift; val })(|val: i64, shift: usize| { S64::from(val >> shift) }),
        ]);
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_shift_mut() {
        assert_ops_shift!(U64, (1..u64::MAX).step_by(PRIMES_48BIT[0]), 0..64, [
            (|mut val: U64, shift: usize| { val <<= shift; val })(|val: u64, shift: usize| { U64::from(val << shift) }),
            (|mut val: U64, shift: usize| { val >>= shift; val })(|val: u64, shift: usize| { U64::from(val >> shift) }),
        ]);
    }
}

#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Display, Formatter, LowerHex, Octal, UpperHex, Write},
    iter::repeat_n,
    str::FromStr,
};

use digit::{Double, Single};
use ndproc::ops_impl;
use prime::{PRIMES, Primality};
use radix::{Bin, Dec, Hex, Oct, RADIX, Radix};
use rand::Rng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use thiserror::Error;

use crate::ops::{IteratorExt, Ops, OpsAssign, OpsFrom};

#[macro_export]
macro_rules! signed_fixed {
    ($bits:expr) => {
        $crate::num::SignedFixed<{ ($bits as usize).div_ceil($crate::num::digit::Single::BITS as usize) }>
    };
}

#[macro_export]
macro_rules! unsigned_fixed {
    ($bits:expr) => {
        $crate::num::UnsignedFixed<{ ($bits as usize).div_ceil($crate::num::digit::Single::BITS as usize) }>
    };
}

macro_rules! sign_from {
    (@unsigned [$($type:ty),+]) => {
        $(sign_from!(@unsigned $type);)+
    };
    (@signed [$($type:ty),+]) => {
        $(sign_from!(@signed $type);)+
    };
    (@unsigned $type:ty) => {
        impl From<$type> for Sign {
            fn from(value: $type) -> Self {
                if value == 0 { Sign::ZERO } else { Sign::POS }
            }
        }
    };
    (@signed $type:ty) => {
        impl From<$type> for Sign {
            fn from(value: $type) -> Self {
                match value.cmp(&0) {
                    Ordering::Less => Sign::NEG,
                    Ordering::Equal => Sign::ZERO,
                    Ordering::Greater => Sign::POS,
                }
            }
        }
    };
}

macro_rules! scalar_from {
    (@unsigned [$($type:ty),+]) => {
        $(scalar_from!(@unsigned $type);)+
    };
    (@signed [$($type:ty),+]) => {
        $(scalar_from!(@signed $type);)+
    };
    (@unsigned $type:ty) => {
        impl From<$type> for ScalarOperand {
            fn from(value: $type) -> Self {
                Self {
                    digit: value as Single,
                    sign: Sign::from(value),
                }
            }
        }
    };
    (@signed $type:ty) => {
        impl From<$type> for ScalarOperand {
            fn from(value: $type) -> Self {
                Self {
                    digit: value.unsigned_abs() as Single,
                    sign: Sign::from(value),
                }
            }
        }
    };
}

macro_rules! long_from_bool {
    ([$($long:ident),+] $(,)?) => {
        $(long_from_bool!($long);)+
    };
    ($long:ident) => {
        impl From<bool> for $long {
            fn from(value: bool) -> Self {
                Self::from(value as u8)
            }
        }
    };
}

macro_rules! fixed_from_bool {
    ([$($fixed:ident),+] $(,)?) => {
        $(fixed_from_bool!($fixed);)+
    };
    ($fixed:ident) => {
        impl<const L: usize> From<bool> for $fixed<L> {
            fn from(value: bool) -> Self {
                Self::from(value as u8)
            }
        }
    };
}

macro_rules! long_from {
    ($long:ident, [$($type:ty),+] $(,)?) => {
        $(long_from!($long, $type);)+
    };
    ($long:ident, [$pos:expr], [$($type:ty),+] $(,)?) => {
        $(long_from!($long, $type, $pos);)+
    };
    ($long:ident, $type:ty $(, $pos:expr)?) => {
        impl From<$type> for $long {
            fn from(value: $type) -> Self {
                const LEN: usize = ((<$type>::BITS + Single::BITS - 1) / Single::BITS) as usize;

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

                Self { digits: res $(, sign: $pos * Sign::from(value))? }
            }
        }
    };
}

macro_rules! fixed_from {
    ($fixed:ident, [$($type:ty),+] $(,)?) => {
        $(fixed_from!($fixed, $type);)+
    };
    ($fixed:ident, [$pos:expr], [$($type:ty),+] $(,)?) => {
        $(fixed_from!($fixed, $type, $pos);)+
    };
    ($fixed:ident, $type:ty $(, $pos:expr)?) => {
        impl<const L: usize> From<$type> for $fixed<L> {
            fn from(value: $type) -> Self {
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

                Self { raw: res, len $(, sign: if len > 0 { $pos * Sign::from(value) } else { Sign::ZERO })? }
            }
        }
    };
}

macro_rules! num_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(num_impl!($trait, $type,);)+
    };
    ($trait:ty, $type:ty $(,)?) => {
        impl NumBuilder for $type {
            fn bitor_offset(&mut self, mask: u64, offset: usize) {
                *self |= (mask.checked_shl(offset as u32).unwrap_or(0)) as $type;
            }

            fn bitand_offset(&mut self, mask: u64, offset: usize) {
                *self &= (mask.checked_shl(offset as u32).unwrap_or(0)) as $type;
            }
        }

        impl Num for $type {
            fn bits(&self) -> usize {
                <$type>::BITS as usize
            }

            fn order(&self) -> usize {
                self.ilog2() as usize
            }

            fn sqrt(&self) -> Self {
                self.isqrt()
            }

            fn log(&self) -> Self {
                self.ilog2() as $type
            }

            fn is_even(&self) -> bool {
                *self % 2 == 0
            }
        }

        impl Fixed for $type {
            const BITS: usize = <$type>::BITS as usize;
            const ZERO: Self = 0;
            const ONE: Self = 1;
        }

        impl $trait for $type {}
    };
}

macro_rules! prime_impl {
    ($([$type:ty, $count:expr]),+) => {
        $(prime_impl!($type, $count,);)+
    };
    ($type:ty, $count:expr $(,)?) => {
        impl Primality for $type {
            fn primes() -> impl Iterator<Item = Self> {
                PRIMES.iter().map(|&p| p as $type).take($count).take_while(|&p| p <= Self::MAX.isqrt())
            }

            fn as_count_estimate(&self) -> usize {
                *self as usize
            }

            fn as_limit_estimate(&self) -> usize {
                let val = *self as f64;
                let inv = 1.0 / val.ln();

                let est = val * inv * (1.0 + inv + 2.0 * inv * inv + 7.59 * inv * inv * inv);
                let est = est.max(val);

                est.ceil() as usize
            }

            fn as_count_check_estimate(&self) -> usize {
                let val = *self as f64;
                let val = val * (val.ln() + val.ln().ln());
                let val = val.max(6.0).sqrt();
                let inv = 1.0 / val.ln();

                let est = val * inv * (1.0 + inv + 2.0 * inv * inv + 7.59 * inv * inv * inv);
                let est = est.max(val);

                est.ceil() as usize
            }

            fn as_limit_check_estimate(&self) -> usize {
                let val = (*self as f64).sqrt();
                let inv = 1.0 / val.ln();

                let est = val * inv * (1.0 + inv + 2.0 * inv * inv + 7.59 * inv * inv * inv);
                let est = est.max(val);

                est.ceil() as usize
            }
        }
    };
}

macro_rules! radix_impl {
    ([$($type:ty),+]) => {
        $(radix_impl!($type);)+
    };
    ($type:ty) => {
        impl Radix for $type {
            const WIDTH: u8 = Self::WIDTH;
            const PREFIX: &str = Self::PREFIX;
        }
    };
}

macro_rules! div_cycle {
    ($arr:expr, $len:expr, $val:expr) => {
        for i in (1..$arr.len()).rev() {
            $arr[i] = $arr[i - 1];
        }

        $arr[0] = $val;
        $len += 1;
    };
}

macro_rules! div_apply {
    ($mul_fn:path, $sub_fn:path, $div:expr, $rem:expr, $len:expr, $bpos:expr, $digit:expr) => {
        if $digit > 1 {
            $div = ($digit - 1) as Single;

            let dop = [$div];
            let mul = $mul_fn(VectorOperand::from_raw(&dop), $bpos);
            let sub = $sub_fn(VectorOperand::from_raw(&$rem[..$len]), (&mul).into());

            $rem.fill(0);
            $rem[..sub.len()].copy_from_slice(sub.digits());
            $len = sub.len();
        };
    };
}

macro_rules! div_digit {
    (@vector $mul:expr, $div:expr) => {{}};
    (@scalar $mul:expr, $div:expr) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match ($mul as Double * m).cmp(&$div) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
}

macro_rules! ops_impl_mut {
    (@ref $fn:ident, $a:expr, $b:expr) => {{
        let repr = $fn($a.into(), (&$b).into());

        $a.apply_mut_repr(repr);
    }};
    (@val $fn:ident, $a:expr, $b:expr) => {{
        let repr = $fn($a.into(), $b);

        $a.apply_mut_repr(repr);
    }};
}

pub type S128 = signed_fixed!(128);
pub type S192 = signed_fixed!(192);
pub type S256 = signed_fixed!(256);
pub type S384 = signed_fixed!(384);
pub type S512 = signed_fixed!(512);
pub type S768 = signed_fixed!(768);
pub type S1024 = signed_fixed!(1024);
pub type S1536 = signed_fixed!(1536);
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
pub type U768 = unsigned_fixed!(768);
pub type U1024 = unsigned_fixed!(1024);
pub type U1536 = unsigned_fixed!(1536);
pub type U2048 = unsigned_fixed!(2048);
pub type U3072 = unsigned_fixed!(3072);
pub type U4096 = unsigned_fixed!(4096);
pub type U6144 = unsigned_fixed!(6144);
pub type U8192 = unsigned_fixed!(8192);

#[cfg(all(target_pointer_width = "64", not(test)))]
pub mod digit {
    use super::{ScalarOperand, Sign};

    pub type Single = u64;
    pub type Double = u128;

    pub(super) const OCT_VAL: Double = (1 as Double) << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_VAL: Double = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;

    scalar_from!(@unsigned [u8, u16, u32, u64]);
    scalar_from!(@signed [i8, i16, i32, i64]);
}

#[cfg(all(target_pointer_width = "32", not(test)))]
pub mod digit {
    use super::{ScalarOperand, Sign};

    pub type Single = u32;
    pub type Double = u64;

    pub(super) const OCT_VAL: Double = (1 as Double) << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_VAL: Double = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;

    scalar_from!(@unsigned [u8, u16, u32]);
    scalar_from!(@signed [i8, i16, i32]);
}

#[cfg(test)]
pub mod digit {
    use super::{ScalarOperand, Sign};

    pub type Single = u8;
    pub type Double = u16;

    pub(super) const OCT_VAL: Double = (1 as Double) << 6;
    pub(super) const OCT_WIDTH: u8 = 2;

    pub(super) const DEC_VAL: Double = 100;
    pub(super) const DEC_WIDTH: u8 = 2;

    scalar_from!(@unsigned [u8]);
    scalar_from!(@signed [i8]);
}

mod radix {
    use super::{
        Double, Single,
        digit::{DEC_VAL, DEC_WIDTH, OCT_VAL, OCT_WIDTH},
    };

    pub(super) const RADIX: Double = Single::MAX as Double + 1;

    pub trait Radix {
        const WIDTH: u8;
        const PREFIX: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Bin {
        pub(super) const RADIX: Double = Single::MAX as Double + 1;
        pub(super) const WIDTH: u8 = Single::BITS as u8;
        pub(super) const PREFIX: &str = "0b";
    }

    impl Oct {
        pub(super) const RADIX: Double = OCT_VAL;
        pub(super) const WIDTH: u8 = OCT_WIDTH;
        pub(super) const PREFIX: &str = "0o";
    }

    impl Dec {
        pub(super) const RADIX: Double = DEC_VAL;
        pub(super) const WIDTH: u8 = DEC_WIDTH;
        pub(super) const PREFIX: &str = "";
    }

    impl Hex {
        pub(super) const RADIX: Double = Single::MAX as Double + 1;
        pub(super) const WIDTH: u8 = Single::BITS as u8 / 4;
        pub(super) const PREFIX: &str = "0x";
    }

    radix_impl!([Bin, Oct, Dec, Hex]);
}

pub mod prime {
    use std::mem::{replace, take};

    use super::Unsigned;
    use crate::ops::Ops;

    pub(super) const PRIMES: [u16; 128] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
        109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
        233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
        367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491,
        499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641,
        643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
    ];

    pub struct Primes;

    impl Primes {
        pub fn by_count_full<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFullIter {
                next: Prime::from(2),
                primes: Vec::with_capacity(count.as_count_check_estimate()),
                count: count.as_count_estimate(),
                limit: None,
            }
        }

        pub fn by_limit_full<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFullIter {
                next: Prime::from(2),
                primes: Vec::with_capacity(limit.as_limit_check_estimate()),
                count: limit.as_limit_estimate(),
                limit: Some(limit),
            }
        }

        pub fn by_count_fast<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFastIter {
                next: Prime::from(2),
                count: count.as_count_estimate(),
                limit: None,
            }
        }

        pub fn by_limit_fast<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFastIter {
                next: Prime::from(2),
                count: limit.as_limit_estimate(),
                limit: Some(limit),
            }
        }
    }

    pub trait Primality: Unsigned
    where
        for<'s> &'s Self: Ops,
    {
        fn primes() -> impl Iterator<Item = Self>;

        fn as_count_estimate(&self) -> usize;

        fn as_limit_estimate(&self) -> usize;

        fn as_count_check_estimate(&self) -> usize;

        fn as_limit_check_estimate(&self) -> usize;
    }

    struct PrimesFullIter<Prime: Primality>
    where
        for<'s> &'s Prime: Ops,
    {
        next: Prime,
        primes: Vec<Prime>,
        count: usize,
        limit: Option<Prime>,
    }

    struct PrimesFastIter<Prime: Primality>
    where
        for<'s> &'s Prime: Ops,
    {
        next: Prime,
        count: usize,
        limit: Option<Prime>,
    }

    impl<Prime: Primality> Iterator for PrimesFullIter<Prime>
    where
        for<'s> &'s Prime: Ops,
    {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
                return None;
            }

            if self.primes.len() < self.primes.capacity() {
                self.primes.push(self.next.clone());
            }

            let zero = Prime::from(0);
            let one = Prime::from(1);
            let two = Prime::from(2);

            let offset = Prime::from(&self.next & &one);
            let offset = Prime::from(&offset + &one);

            let mut val = Prime::from(&self.next + &offset);

            while self
                .primes
                .iter()
                .take_while(|&p| Prime::from(p * p) <= val)
                .any(|p| Prime::from(&val % p) == zero)
            {
                val += &two;

                if self.limit.as_ref().is_some_and(|limit| &val > limit) {
                    self.count = 0;

                    return Some(take(&mut self.next));
                }
            }

            self.count -= 1;

            Some(replace(&mut self.next, val))
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.count, Some(self.count))
        }
    }

    impl<Prime: Primality> Iterator for PrimesFastIter<Prime>
    where
        for<'s> &'s Prime: Ops,
    {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
                return None;
            }

            let one = Prime::from(1);
            let two = Prime::from(2);

            let offset = Prime::from(&self.next & &one);
            let offset = Prime::from(&offset + &one);

            let mut val = Prime::from(&self.next + &offset);

            while !val.is_prime() {
                val += &two;

                if self.limit.as_ref().is_some_and(|limit| &val > limit) {
                    self.count = 0;

                    return Some(take(&mut self.next));
                }
            }

            self.count -= 1;

            Some(replace(&mut self.next, val))
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.count, Some(self.count))
        }
    }

    impl<Prime: Primality> ExactSizeIterator for PrimesFullIter<Prime> where for<'s> &'s Prime: Ops {}
    impl<Prime: Primality> ExactSizeIterator for PrimesFastIter<Prime> where for<'s> &'s Prime: Ops {}
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
pub struct SignedLong {
    digits: Vec<Single>,
    sign: Sign,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedLong {
    digits: Vec<Single>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedFixed<const L: usize> {
    raw: [Single; L],
    len: usize,
    sign: Sign,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedFixed<const L: usize> {
    raw: [Single; L],
    len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SignedFixedVec<const L: usize, const N: usize> {
    raws: [[Single; L]; N],
    lens: [usize; N],
    signs: [Sign; N],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsignedFixedVec<const L: usize, const N: usize> {
    raws: [[Single; L]; N],
    lens: [usize; N],
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct ScalarOperand {
    digit: Single,
    sign: Sign,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct VectorOperand<'load> {
    digits: &'load [Single],
    sign: Sign,
}

#[derive(Debug, PartialEq, Eq)]
struct LongMutOperand<'load> {
    digits: &'load mut Vec<Single>,
    sign: Sign,
}

#[derive(Debug, PartialEq, Eq)]
struct FixedMutOperand<'load, const L: usize> {
    raw: &'load mut [Single; L],
    len: usize,
    sign: Sign,
}

#[derive(Debug, Default)]
struct LongRepr {
    digits: Vec<Single>,
    sign: Sign,
}

#[derive(Debug)]
struct FixedRepr<const L: usize> {
    raw: [Single; L],
    len: usize,
    sign: Sign,
    overflow_val: Single,
    overflow: bool,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct MutRepr {
    len: usize,
    sign: Sign,
}

pub trait NumBuilder: Num
where
    for<'s> &'s Self: Ops,
{
    fn bitor_offset(&mut self, mask: u64, offset: usize);

    fn bitand_offset(&mut self, mask: u64, offset: usize);

    fn with_bitor_offset(mut self, mask: u64, offset: usize) -> Self {
        self.bitor_offset(mask, offset);
        self
    }

    fn with_bitand_offset(mut self, mask: u64, offset: usize) -> Self {
        self.bitand_offset(mask, offset);
        self
    }

    fn with_odd(mut self) -> Self {
        self.bitor_offset(1, 0);
        self
    }

    fn with_even(mut self) -> Self {
        self.bitand_offset(u64::MAX - 1, 0);
        self
    }
}

pub trait Num: Sized + Default + Display + Clone + Eq + Ord + From<bool>
where
    for<'s> Self: Ops + OpsAssign + OpsAssign<&'s Self> + OpsFrom + OpsFrom<&'s Self, &'s Self>,
    for<'s> &'s Self: Ops,
{
    fn bits(&self) -> usize;

    fn order(&self) -> usize;

    fn sqrt(&self) -> Self;

    fn log(&self) -> Self;

    fn is_even(&self) -> bool;

    fn zero() -> Self {
        false.into()
    }

    fn one() -> Self {
        true.into()
    }

    fn gcd(self, val: Self) -> Self {
        let zero = Self::zero();

        let (mut a, mut b) = match self.cmp(&val) {
            Ordering::Less => (val, self),
            Ordering::Equal => (self, val),
            Ordering::Greater => (self, val),
        };

        while b != zero {
            let rem = Self::from(&a % &b);

            a = b;
            b = rem;
        }

        a
    }

    fn lcm(mut self, val: Self) -> Self {
        let gcd = Self::gcd(self.clone(), val.clone());

        self /= &gcd;
        self *= &val;
        self
    }

    fn pow_rem(self, mut pow: Self, rem: &Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while pow != zero {
            if !pow.is_even() {
                res *= &acc;
                res %= rem;
            }

            acc = (&acc * &acc).into();
            acc %= rem;
            pow >>= 1;
        }

        res
    }

    fn rand<R: ?Sized + Rng>(order: usize, rng: &mut R) -> Self
    where
        Self: NumBuilder,
    {
        let shift = order - 1;
        let div = shift / u64::BITS as usize;
        let rem = shift % u64::BITS as usize;

        let mut res = Self::zero();

        res.bitor_offset((1 << rem) | rng.next_u64() & ((1 << rem) - 1), shift - rem);

        for idx in 0..div {
            res.bitor_offset(rng.next_u64(), shift - rem - idx * div);
        }

        res
    }

    fn rand_prime(order: usize) -> Self
    where
        Self: NumBuilder + Primality,
    {
        let mut rng = rand::rng();
        let mut val = Self::rand(order, &mut rng).with_odd();

        while !val.is_prime() {
            val = Self::rand(order, &mut rng).with_odd();
        }

        val
    }

    fn rand_primes(order: usize, count: usize) -> Vec<Self>
    where
        Self: NumBuilder + Primality,
    {
        (0..count).map(|_| Self::rand_prime(order)).collect::<Vec<Self>>()
    }

    fn rand_prime_par(order: usize) -> Self
    where
        Self: Send + NumBuilder + Primality,
    {
        let threads = std::thread::available_parallelism().map(|val| val.get()).unwrap_or(1);

        (0..threads)
            .into_par_iter()
            .find_map_first(|_| Some(Self::rand_prime(order)))
            .unwrap_or_default()
    }

    fn rand_primes_par(order: usize, count: usize) -> Vec<Self>
    where
        Self: Send + NumBuilder + Primality,
    {
        (0..count)
            .into_par_iter()
            .map(|_| Self::rand_prime(order))
            .collect::<Vec<Self>>()
    }

    fn is_prime(&self) -> bool
    where
        Self: Primality,
    {
        let sqrt = self.sqrt();

        Self::primes().take_while(|p| p <= &sqrt).all(|p| {
            let one = Self::one();

            let x = Self::from(self - &one);

            let shr = Self::from(&x - &one);
            let shr = Self::from(&x ^ &shr);
            let shr = shr.order();

            let mut any = false;
            let mut pow = Self::from(&x >> shr);
            let mut exp = p.pow_rem(pow.clone(), self);

            while pow < x && one < exp && exp < x {
                any |= true;
                pow <<= 1;
                exp *= &exp.clone();
                exp %= self;
            }

            !any && exp == one || exp == x
        })
    }
}

pub trait Signed: Num + From<i8>
where
    for<'s> &'s Self: Ops,
{
    fn gcde(&self, val: &Self) -> (Self, Self, Self) {
        let zero = Self::from(0);
        let one = Self::from(1);

        let a = self;
        let b = val;

        if b == &zero {
            return (a.clone(), one, zero);
        }

        let rem = Self::from(a % b);

        let (g, x, y) = Self::gcde(b, &rem);

        let val = Self::from(a / b);
        let val = Self::from(&val * &y);
        let val = Self::from(&x - &val);

        (g, y, val)
    }
}

pub trait Unsigned: Num + From<u8>
where
    for<'s> &'s Self: Ops,
{
}

pub trait Long: Num
where
    for<'s> &'s Self: Ops,
{
}

pub trait Fixed: Num + Copy
where
    for<'s> &'s Self: Ops,
{
    const BITS: usize;
    const ZERO: Self;
    const ONE: Self;
}

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

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

long_from_bool!([SignedLong, UnsignedLong]);
fixed_from_bool!([SignedFixed, UnsignedFixed]);

long_from!(UnsignedLong, [u8, u16, u32, u64, u128, usize]);
fixed_from!(UnsignedFixed, [u8, u16, u32, u64, u128, usize]);

num_impl!(Signed, [i8, i16, i32, i64, i128, isize]);
num_impl!(Unsigned, [u8, u16, u32, u64, u128, usize]);
prime_impl!([u8, 1], [u16, 2], [u32, 5], [u64, 12], [u128, 20], [usize, 12]);

impl<const L: usize> Default for SignedFixed<L> {
    fn default() -> Self {
        Self {
            raw: [0; L],
            len: 0,
            sign: Sign::ZERO,
        }
    }
}

impl<const L: usize> Default for UnsignedFixed<L> {
    fn default() -> Self {
        Self { raw: [0; L], len: 0 }
    }
}

impl<'load> From<&'load SignedLong> for VectorOperand<'load> {
    fn from(value: &'load SignedLong) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load> From<&'load UnsignedLong> for VectorOperand<'load> {
    fn from(value: &'load UnsignedLong) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}
impl<'load, const L: usize> From<&'load SignedFixed<L>> for VectorOperand<'load> {
    fn from(value: &'load SignedFixed<L>) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load, const L: usize> From<&'load UnsignedFixed<L>> for VectorOperand<'load> {
    fn from(value: &'load UnsignedFixed<L>) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load> From<&&'load SignedLong> for VectorOperand<'load> {
    fn from(value: &&'load SignedLong) -> Self {
        Self::from(*value)
    }
}

impl<'load> From<&&'load UnsignedLong> for VectorOperand<'load> {
    fn from(value: &&'load UnsignedLong) -> Self {
        Self::from(*value)
    }
}

impl<'load, const L: usize> From<&&'load SignedFixed<L>> for VectorOperand<'load> {
    fn from(value: &&'load SignedFixed<L>) -> Self {
        Self::from(*value)
    }
}

impl<'load, const L: usize> From<&&'load UnsignedFixed<L>> for VectorOperand<'load> {
    fn from(value: &&'load UnsignedFixed<L>) -> Self {
        Self::from(*value)
    }
}

impl<'load> From<&'load mut SignedLong> for LongMutOperand<'load> {
    fn from(value: &'load mut SignedLong) -> Self {
        Self {
            sign: value.sign(),
            digits: value.raw_mut(),
        }
    }
}

impl<'load> From<&'load mut UnsignedLong> for LongMutOperand<'load> {
    fn from(value: &'load mut UnsignedLong) -> Self {
        Self {
            sign: value.sign(),
            digits: value.raw_mut(),
        }
    }
}

impl<'load, const L: usize> From<&'load mut SignedFixed<L>> for FixedMutOperand<'load, L> {
    fn from(value: &'load mut SignedFixed<L>) -> Self {
        Self {
            len: value.len(),
            sign: value.sign(),
            raw: value.raw_mut(),
        }
    }
}

impl<'load, const L: usize> From<&'load mut UnsignedFixed<L>> for FixedMutOperand<'load, L> {
    fn from(value: &'load mut UnsignedFixed<L>) -> Self {
        Self {
            len: value.len(),
            sign: value.sign(),
            raw: value.raw_mut(),
        }
    }
}

impl From<VectorOperand<'_>> for LongRepr {
    fn from(value: VectorOperand<'_>) -> Self {
        Self {
            digits: value.digits().to_vec(),
            sign: value.sign(),
        }
    }
}

impl<const L: usize> From<VectorOperand<'_>> for FixedRepr<L> {
    fn from(value: VectorOperand<'_>) -> Self {
        Self {
            raw: value.digits().iter().copied().collect_with([0; L]),
            len: value.len().min(L),
            sign: value.sign(),
            overflow_val: 0,
            overflow: false,
        }
    }
}

impl From<ScalarOperand> for LongRepr {
    fn from(value: ScalarOperand) -> Self {
        Self::from_single(value.digit()).with_sign(value.sign())
    }
}

impl<const L: usize> From<ScalarOperand> for FixedRepr<L> {
    fn from(value: ScalarOperand) -> Self {
        Self::from_single(value.digit()).with_sign(value.sign())
    }
}

impl<'load> From<&'load LongRepr> for VectorOperand<'load> {
    fn from(value: &'load LongRepr) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load, const L: usize> From<&'load FixedRepr<L>> for VectorOperand<'load> {
    fn from(value: &'load FixedRepr<L>) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load> From<LongMutOperand<'load>> for MutRepr {
    fn from(value: LongMutOperand<'load>) -> Self {
        Self {
            len: value.len(),
            sign: value.sign(),
        }
    }
}

impl<'load, const L: usize> From<FixedMutOperand<'load, L>> for MutRepr {
    fn from(value: FixedMutOperand<'load, L>) -> Self {
        Self {
            len: value.len(),
            sign: value.sign(),
        }
    }
}

impl From<LongRepr> for SignedLong {
    fn from(value: LongRepr) -> Self {
        Self {
            digits: value.digits,
            sign: value.sign,
        }
    }
}

impl From<LongRepr> for UnsignedLong {
    fn from(value: LongRepr) -> Self {
        match value.sign() {
            Sign::ZERO => Default::default(),
            Sign::NEG => Default::default(),
            Sign::POS => Self { digits: value.digits },
        }
    }
}

impl<const L: usize> From<FixedRepr<L>> for SignedFixed<L> {
    fn from(value: FixedRepr<L>) -> Self {
        Self {
            raw: value.raw,
            len: value.len,
            sign: value.sign,
        }
    }
}

impl<const L: usize> From<FixedRepr<L>> for UnsignedFixed<L> {
    fn from(value: FixedRepr<L>) -> Self {
        match value.sign() {
            Sign::ZERO => Default::default(),
            Sign::NEG => Default::default(),
            Sign::POS => Self { raw: value.raw, len: value.len },
        }
    }
}

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

        (val.sign() != Sign::NEG)
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
        let val = try_from_str_fixed(s)?;

        (val.sign() != Sign::NEG)
            .then_some(val.into())
            .ok_or(TryFromStrError::UnsignedNegative)
    }
}

impl SignedLong {
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        from_bytes_long(bytes.as_ref()).into()
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        self.clone().into_radix(radix)
    }

    pub fn into_unsigned(self) -> UnsignedLong {
        UnsignedLong { digits: self.digits }
    }

    pub fn to_fixed<const L: usize>(&self) -> SignedFixed<L> {
        fixed_from_long(self.digits()).with_sign(self.sign()).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.digits
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    pub fn sign(&self) -> Sign {
        self.sign
    }

    pub fn drain(self) -> (Vec<Single>, Sign) {
        (self.digits, self.sign)
    }

    pub fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    pub fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }

    fn raw_mut(&mut self) -> &mut Vec<Single> {
        &mut self.digits
    }

    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.digits
    }

    fn apply_mut_repr(&mut self, repr: MutRepr) {
        self.digits.truncate(repr.len);
        self.sign = repr.sign;
    }
}

impl UnsignedLong {
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        from_bytes_long(bytes.as_ref()).into()
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        self.clone().into_radix(radix)
    }

    pub fn into_signed(self, sign: Sign) -> SignedLong {
        let len = self.len();
        let sign = get_sign(len, sign);

        SignedLong { digits: self.digits, sign }
    }

    pub fn to_fixed<const L: usize>(&self) -> UnsignedFixed<L> {
        fixed_from_long(self.digits()).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.digits
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    pub fn sign(&self) -> Sign {
        Sign::from(self.len())
    }

    pub fn drain(self) -> Vec<Single> {
        self.digits
    }

    fn raw_mut(&mut self) -> &mut Vec<Single> {
        &mut self.digits
    }

    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.digits
    }

    fn apply_mut_repr(&mut self, repr: MutRepr) {
        match repr.sign {
            Sign::ZERO => *self = Default::default(),
            Sign::NEG => *self = Default::default(),
            Sign::POS => self.digits.truncate(repr.len),
        }
    }
}

impl<const L: usize> SignedFixed<L> {
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        from_bytes_fixed(bytes.as_ref()).into()
    }

    pub fn try_from_bytes(bytes: impl AsRef<[u8]>) -> (Self, bool) {
        let repr = from_bytes_fixed(bytes.as_ref());
        let over = repr.overflow;

        (repr.into(), over)
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        (*self).into_radix(radix)
    }

    pub fn into_unsigned(self) -> UnsignedFixed<L> {
        UnsignedFixed::<L> { raw: self.raw, len: self.len }
    }

    pub fn to_long(&self) -> SignedLong {
        long_from_fixed::<L>(self.digits()).with_sign(self.sign()).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn sign(&self) -> Sign {
        self.sign
    }

    pub fn drain(self) -> ([Single; L], usize, Sign) {
        (self.raw, self.len, self.sign)
    }

    pub fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    pub fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }

    fn raw_mut(&mut self) -> &mut [Single; L] {
        &mut self.raw
    }

    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.raw[..self.len]
    }

    fn apply_mut_repr(&mut self, repr: MutRepr) {
        self.digits_mut().iter_mut().for_each(|ptr| *ptr = 0);
        self.len = repr.len;
        self.sign = repr.sign;
    }
}

impl<const L: usize> UnsignedFixed<L> {
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        from_bytes_fixed(bytes.as_ref()).into()
    }

    pub fn try_from_bytes(bytes: impl AsRef<[u8]>) -> (Self, bool) {
        let repr = from_bytes_fixed(bytes.as_ref());
        let over = repr.overflow;

        (repr.into(), over)
    }

    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed(digits, radix, Sign::POS)?.into())
    }

    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed_bin(digits, pow, Sign::POS)?.into())
    }

    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        (*self).into_radix(radix)
    }

    pub fn into_signed(self, sign: Sign) -> SignedFixed<L> {
        let len = self.len();
        let sign = get_sign(len, sign);

        SignedFixed::<L> { raw: self.raw, len, sign }
    }

    pub fn to_long(&self) -> SignedLong {
        long_from_fixed::<L>(self.digits()).into()
    }

    pub fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn sign(&self) -> Sign {
        Sign::from(self.len())
    }

    pub fn drain(self) -> ([Single; L], usize) {
        (self.raw, self.len)
    }

    fn raw_mut(&mut self) -> &mut [Single; L] {
        &mut self.raw
    }

    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.raw[..self.len]
    }

    fn apply_mut_repr(&mut self, repr: MutRepr) {
        match repr.sign {
            Sign::ZERO => *self = Default::default(),
            Sign::NEG => *self = Default::default(),
            Sign::POS => {
                self.digits_mut().iter_mut().for_each(|ptr| *ptr = 0);
                self.len = repr.len;
            },
        }
    }
}

impl ScalarOperand {
    fn digit(&self) -> Single {
        self.digit
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl<'digits> VectorOperand<'digits> {
    const ONE: Self = VectorOperand { digits: &[1], sign: Sign::POS };

    fn from_raw(digits: &'digits [Single]) -> Self {
        let len = get_len(digits);
        let sign = get_sign(len, Sign::POS);

        Self { digits: &digits[..len], sign }
    }

    fn clone_into_vec(&self, len: usize) -> Vec<Single> {
        let mut res = vec![0; len];

        let len = self.len().min(len);

        res[..len].copy_from_slice(&self.digits()[..len]);
        res
    }

    fn clone_into_arr<const L: usize>(&self) -> [Single; L] {
        let mut res = [0; L];

        let len = self.len().min(L);

        res[..len].copy_from_slice(&self.digits()[..len]);
        res
    }

    fn digits(&self) -> &[Single] {
        self.digits
    }

    fn len(&self) -> usize {
        self.digits.len()
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl LongMutOperand<'_> {
    fn clone_from_single(&mut self, val: Single) -> MutRepr {
        if val == 0 {
            self.raw_mut().clear();

            return MutRepr::ZERO;
        }

        self.raw_mut().resize(1, 0);
        self.raw_mut()[0] = val;

        MutRepr::from_raw(&[val], Sign::POS)
    }

    fn clone_from_double(&mut self, val: Double) -> MutRepr {
        if val == 0 {
            self.raw_mut().clear();

            return MutRepr::ZERO;
        }

        self.raw_mut().resize(2, 0);
        self.raw_mut()[0] = val as Single;
        self.raw_mut()[1] = (val >> Single::BITS) as Single;

        MutRepr::from_raw(self.digits(), Sign::POS)
    }

    fn clone_from_vector(&mut self, vec: VectorOperand<'_>) -> MutRepr {
        self.raw_mut().resize(vec.len(), 0);
        self.raw_mut().iter_mut().zip(vec.digits()).for_each(|(ptr, op)| *ptr = *op);

        MutRepr::from_raw(vec.digits(), vec.sign())
    }

    fn clone_from_repr(&mut self, repr: LongRepr) -> MutRepr {
        *self.raw_mut() = repr.digits;

        MutRepr::from_raw(self.digits(), repr.sign)
    }

    fn raw_mut(&mut self) -> &mut Vec<Single> {
        self.digits
    }

    fn raw(&self) -> &Vec<Single> {
        self.digits
    }

    fn digits(&self) -> &[Single] {
        self.digits
    }

    fn len(&self) -> usize {
        self.digits.len()
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_cloned_from(mut self, vec: VectorOperand<'_>) -> Self {
        self.raw_mut().resize(vec.len(), 0);
        self.raw_mut().iter_mut().zip(vec.digits()).for_each(|(ptr, op)| *ptr = *op);
        self.with_sign(vec.sign())
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl<const L: usize> FixedMutOperand<'_, L> {
    fn clone_from_single(&mut self, val: Single) -> MutRepr {
        self.raw_mut()[0] = val;

        MutRepr::from_raw(&[val], Sign::POS)
    }

    fn clone_from_double(&mut self, val: Double) -> MutRepr {
        self.raw_mut()[0] = val as Single;
        self.raw_mut()[1] = (val >> Single::BITS) as Single;

        MutRepr::from_raw(self.digits(), Sign::POS)
    }

    fn clone_from_vector(&mut self, vec: VectorOperand<'_>) -> MutRepr {
        self.raw_mut().iter_mut().zip(vec.digits()).for_each(|(ptr, op)| *ptr = *op);

        MutRepr::from_raw(vec.digits(), vec.sign())
    }

    fn clone_from_repr(&mut self, repr: FixedRepr<L>) -> MutRepr {
        *self.raw_mut() = repr.raw;

        MutRepr::from_raw(self.digits(), repr.sign)
    }

    fn raw_mut(&mut self) -> &mut [Single; L] {
        self.raw
    }

    fn raw(&self) -> &[Single; L] {
        self.raw
    }

    fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    fn len(&self) -> usize {
        self.len
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_cloned_from(mut self, vec: VectorOperand<'_>) -> Self {
        self.raw_mut().iter_mut().zip(vec.digits()).for_each(|(ptr, op)| *ptr = *op);
        self.with_sign(vec.sign())
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl LongRepr {
    const ZERO: Self = LongRepr {
        digits: vec![],
        sign: Sign::ZERO,
    };

    fn from_single(digit: Single) -> Self {
        match digit {
            0 => LongRepr::ZERO,
            x => Self {
                digits: vec![x],
                sign: Sign::POS,
            },
        }
    }

    fn from_double(digits: Double) -> Self {
        Self::from_raw(vec![digits as Single, (digits >> Single::BITS) as Single], Sign::POS)
    }

    fn from_raw(mut digits: Vec<Single>, sign: Sign) -> Self {
        let len = get_len(&digits);
        let sign = get_sign(len, sign);

        digits.truncate(len);

        Self { digits, sign }
    }

    fn digits(&self) -> &[Single] {
        &self.digits
    }

    fn len(&self) -> usize {
        self.digits.len()
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl<const L: usize> FixedRepr<L> {
    const ZERO: Self = Self::from_single(0);
    const ONE: Self = Self::from_single(1);

    const fn from_single(digit: Single) -> Self {
        let mut res = [0; L];

        res[0] = digit;

        let len = if digit > 0 { 1 } else { 0 };
        let sign = if digit > 0 { Sign::POS } else { Sign::ZERO };

        Self {
            raw: res,
            len,
            sign,
            overflow_val: 0,
            overflow: false,
        }
    }

    fn from_double(digits: Double) -> Self {
        let mut res = [0; L];

        res[0] = digits as Single;
        res[1] = (digits >> Single::BITS) as Single;

        Self::from_raw(res, Sign::POS)
    }

    fn from_raw(digits: [Single; L], sign: Sign) -> Self {
        let len = get_len(&digits);
        let sign = get_sign(len, sign);

        Self {
            raw: digits,
            len,
            sign,
            overflow_val: 0,
            overflow: false,
        }
    }

    fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    fn len(&self) -> usize {
        self.len
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }

    fn with_overflow_val(mut self, val: Single) -> Self {
        self.overflow_val = val;
        self
    }

    fn with_overflow(mut self, over: bool) -> Self {
        self.overflow = over;
        self
    }
}

impl MutRepr {
    const ZERO: Self = MutRepr { len: 0, sign: Sign::ZERO };

    fn from_raw(slice: &[Single], sign: Sign) -> Self {
        let len = get_len(slice);
        let sign = get_sign(len, sign);

        Self { len, sign }
    }

    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

fn from_bytes_long(bytes: &[u8]) -> LongRepr {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (bytes.len() + RATIO - 1) / RATIO;

    if len == 0 {
        return LongRepr::ZERO;
    }

    let (chunks, chunk) = bytes.as_chunks::<RATIO>();

    let mut res = chunks
        .iter()
        .map(|&bytes| Single::from_le_bytes(bytes))
        .collect_with(vec![0; len]);

    if !chunk.is_empty() {
        res[len - 1] = Single::from_le_bytes(chunk.iter().copied().collect_with([0; RATIO]));
    }

    LongRepr::from_raw(res, Sign::POS)
}

fn from_bytes_fixed<const L: usize>(bytes: &[u8]) -> FixedRepr<L> {
    const RATIO: usize = (Single::BITS / u8::BITS) as usize;

    let len = (bytes.len() + RATIO - 1) / RATIO;

    if len == 0 {
        return FixedRepr::ZERO;
    }

    let (chunks, chunk) = bytes.as_chunks::<RATIO>();

    let mut res = chunks.iter().map(|&bytes| Single::from_le_bytes(bytes)).collect_with([0; L]);

    if !chunk.is_empty() && len < L {
        res[len - 1] = Single::from_le_bytes(chunk.iter().copied().collect_with([0; RATIO]));
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
    let mut res = vec![0; len + 1];
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
    FixedRepr::from_raw(digits.iter().copied().collect_with([0; L]), Sign::POS).with_overflow(digits.len() > L)
}

fn long_from_fixed<const L: usize>(digits: &[Single]) -> LongRepr {
    LongRepr::from_raw(digits.iter().copied().collect_with(vec![0; digits.len()]), Sign::POS)
}

fn write_num_bin(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$b}")
}

fn write_num_oct(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$o}")
}

fn write_num_dec(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$}")
}

fn write_num_lhex(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$x}")
}

fn write_num_uhex(buf: &mut String, digit: Single, width: usize) -> std::fmt::Result {
    write!(buf, "{digit:0width$X}")
}

fn write_num<R: Radix, F>(_: R, fmt: &mut Formatter<'_>, digits: &[Single], sign: Sign, func: F) -> std::fmt::Result
where
    F: Fn(&mut String, Single, usize) -> std::fmt::Result,
{
    let sign = get_sign(digits.len(), sign);

    let prefix = if fmt.alternate() { R::PREFIX } else { "" };

    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{prefix}0");
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

        write_num(Dec, fmt, &digits, self.sign, write_num_dec)
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

        write_num(Dec, fmt, &digits, self.sign, write_num_dec)
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

        write_num(Bin, fmt, &digits, self.sign, write_num_bin)
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

        write_num(Bin, fmt, &digits, self.sign, write_num_bin)
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

        write_num(Oct, fmt, &digits, self.sign, write_num_oct)
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

        write_num(Oct, fmt, &digits, self.sign, write_num_oct)
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

        write_num(Hex, fmt, &digits, self.sign, write_num_lhex)
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

        write_num(Hex, fmt, &digits, self.sign, write_num_lhex)
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

        write_num(Hex, fmt, &digits, self.sign, write_num_uhex)
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

        write_num(Hex, fmt, &digits, self.sign, write_num_uhex)
    }
}

impl<const L: usize> UpperHex for UnsignedFixed<L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let digits = self.to_radix_bin(Hex::RADIX.ilog2() as u8).unwrap_or_default();

        write_num(Hex, fmt, &digits, Sign::POS, write_num_uhex)
    }
}

fn zip_nums<'a, 'b>(a: &'a [Single], b: &'b [Single], zeros: usize) -> impl Iterator<Item = (&'a Single, &'b Single)> {
    let len = a.len().max(b.len());

    let iter_a = a.iter().chain(repeat_n(&0, len - a.len() + zeros));
    let iter_b = b.iter().chain(repeat_n(&0, len - b.len() + zeros));

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

fn cmp_nums_ext(a: &[Single], ax: Single, b: &[Single], bx: Single) -> Ordering {
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

fn add_long_vector(a: VectorOperand<'_>, b: VectorOperand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return b.into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_long_vector(a, -b);
    }

    let len = a.len().max(b.len()) + 1;

    let mut acc = 0;

    let res = zip_nums(a.digits(), b.digits(), 1)
        .map(|(&aop, &bop)| {
            let digit = acc + aop as Double + bop as Double;

            acc = digit >> Single::BITS;

            digit as Single
        })
        .collect_with(vec![0; len]);

    LongRepr::from_raw(res, a.sign())
}

fn add_fixed_vector<const L: usize>(a: VectorOperand<'_>, b: VectorOperand<'_>) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return b.into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_fixed_vector(a, -b);
    }

    let mut acc = 0;

    let res = zip_nums(a.digits(), b.digits(), 1)
        .map(|(&aop, &bop)| {
            let digit = acc + aop as Double + bop as Double;

            acc = digit >> Single::BITS;

            digit as Single
        })
        .collect_with([0; L]);

    FixedRepr::from_raw(res, a.sign())
        .with_overflow_val(acc as Single)
        .with_overflow(acc > 0)
}

fn add_long_scalar(a: VectorOperand<'_>, b: ScalarOperand) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return b.into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return sub_long_scalar(a, -b);
    }

    let mut acc = b.digit() as Double;
    let mut res = a.clone_into_vec(a.len() + 1);

    for ptr in res.iter_mut() {
        acc += *ptr as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;

        if acc == 0 {
            break;
        }
    }

    LongRepr::from_raw(res, a.sign())
}

fn add_fixed_scalar<const L: usize>(a: VectorOperand<'_>, b: ScalarOperand) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return b.into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return sub_fixed_scalar(a, -b);
    }

    let mut acc = b.digit() as Double;
    let mut res = a.clone_into_arr();

    for ptr in res.iter_mut() {
        acc += *ptr as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;

        if acc == 0 {
            break;
        }
    }

    FixedRepr::from_raw(res, a.sign())
        .with_overflow_val(acc as Single)
        .with_overflow(acc > 0)
}

fn add_long_vector_mut(mut a: LongMutOperand<'_>, b: VectorOperand<'_>) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_vector(b),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_long_vector_mut(a, -b);
    }

    let len = a.len().max(b.len()) + 1;
    let res = a.raw_mut();

    res.resize(len, 0);

    let mut acc = 0;

    for (i, &bop) in b.digits().iter().enumerate() {
        acc += res[i] as Double + bop as Double;

        res[i] = acc as Single;

        acc >>= Single::BITS;
    }

    res[b.len()] += acc as Single;

    MutRepr::from_raw(a.raw(), a.sign())
}

fn add_fixed_vector_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: VectorOperand<'_>) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_vector(b),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_fixed_vector_mut(a, -b);
    }

    let len = (a.len().max(b.len()) + 1).min(L);
    let res = a.raw_mut();

    let mut acc = 0;

    for (i, &bop) in b.digits().iter().take(len).enumerate() {
        acc += res[i] as Double + bop as Double;

        res[i] = acc as Single;

        acc >>= Single::BITS;
    }

    if b.len() < L {
        res[b.len()] += acc as Single;
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn add_long_scalar_mut(mut a: LongMutOperand<'_>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_single(b.digit()),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return sub_long_scalar_mut(a, -b);
    }

    let res = a.raw_mut();

    let mut acc = b.digit() as Double;

    for ptr in res.iter_mut() {
        acc += *ptr as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;

        if acc == 0 {
            break;
        }
    }

    if acc > 0 {
        res.push(acc as Single);
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn add_fixed_scalar_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_single(b.digit()),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return sub_fixed_scalar_mut(a, -b);
    }

    let res = a.raw_mut();

    let mut acc = b.digit() as Double;

    for ptr in res.iter_mut() {
        acc += *ptr as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;

        if acc == 0 {
            break;
        }
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn sub_long_vector(a: VectorOperand<'_>, b: VectorOperand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return (-b).into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return add_long_vector(a, -b);
    }

    let (a, b, sign) = match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => (b, a, -a.sign()),
        Ordering::Equal => return LongRepr::ZERO,
        Ordering::Greater => (a, b, a.sign()),
    };

    let mut acc = false;

    let res = zip_nums(a.digits(), b.digits(), 0)
        .map(|(&aop, &bop)| {
            let digit = RADIX + aop as Double - bop as Double - acc as Double;

            acc = digit < RADIX;

            digit as Single
        })
        .collect_with(vec![0; a.len()]);

    LongRepr::from_raw(res, sign)
}

fn sub_fixed_vector<const L: usize>(a: VectorOperand<'_>, b: VectorOperand<'_>) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return (-b).into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return add_fixed_vector(a, -b);
    }

    let (a, b, sign) = match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => (b, a, -a.sign()),
        Ordering::Equal => return FixedRepr::ZERO,
        Ordering::Greater => (a, b, a.sign()),
    };

    let mut acc = false;

    let res = zip_nums(a.digits(), b.digits(), 0)
        .map(|(&aop, &bop)| {
            let digit = RADIX + aop as Double - bop as Double - acc as Double;

            acc = digit < RADIX;

            digit as Single
        })
        .collect_with([0; L]);

    FixedRepr::from_raw(res, sign)
}

fn sub_long_scalar(a: VectorOperand<'_>, b: ScalarOperand) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return b.with_neg().into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return add_long_scalar(a, -b);
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return LongRepr::from_single(b.digit() - *a.digits().first().unwrap_or(&0)).with_neg(),
        Ordering::Equal => return LongRepr::ZERO,
        Ordering::Greater => (),
    };

    let mut acc = b.digit();
    let mut res = a.clone_into_vec(a.len());

    for ptr in res.iter_mut() {
        let digit = RADIX + *ptr as Double - acc as Double;

        acc = (digit < RADIX) as Single;

        *ptr = digit as Single;

        if acc == 0 {
            break;
        }
    }

    LongRepr::from_raw(res, a.sign())
}

fn sub_fixed_scalar<const L: usize>(a: VectorOperand<'_>, b: ScalarOperand) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return b.with_neg().into(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return add_fixed_scalar(-a, b);
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return FixedRepr::from_single(b.digit() - *a.digits().first().unwrap_or(&0)).with_neg(),
        Ordering::Equal => return FixedRepr::ZERO,
        Ordering::Greater => (),
    };

    let mut acc = b.digit();
    let mut res = a.clone_into_arr();

    for ptr in res.iter_mut() {
        let digit = RADIX + *ptr as Double - acc as Double;

        acc = (digit < RADIX) as Single;

        *ptr = digit as Single;

        if acc == 0 {
            break;
        }
    }

    FixedRepr::from_raw(res, a.sign())
}

fn sub_long_vector_mut(mut a: LongMutOperand<'_>, b: VectorOperand<'_>) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_vector(b).with_neg(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return add_long_vector_mut(a, -b);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => {
            let digits = a.digits().to_vec();
            let sign = a.sign();

            let vop = VectorOperand::from_raw(&digits).with_sign(sign);

            return sub_long_vector_mut(a.with_cloned_from(b), vop);
        },
        Ordering::Equal => return MutRepr::ZERO,
        Ordering::Greater => (),
    };

    let res = a.raw_mut();

    let mut acc = false;

    for (i, &bop) in b.digits().iter().enumerate() {
        let digit = RADIX + res[i] as Double - bop as Double - acc as Double;

        acc = digit < RADIX;

        res[i] = digit as Single;
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn sub_fixed_vector_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: VectorOperand<'_>) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_vector(b).with_neg(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return add_fixed_vector_mut(a, -b);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => {
            let digits = a.digits().to_vec();
            let sign = a.sign();

            let vop = VectorOperand::from_raw(&digits).with_sign(sign);

            return sub_fixed_vector_mut(a.with_cloned_from(b), vop);
        },
        Ordering::Equal => return MutRepr::ZERO,
        Ordering::Greater => (),
    };

    let res = a.raw_mut();

    let mut acc = false;

    for (i, &bop) in b.digits().iter().enumerate() {
        let digit = RADIX + res[i] as Double - bop as Double - acc as Double;

        acc = digit < RADIX;

        res[i] = digit as Single;
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn sub_long_scalar_mut(mut a: LongMutOperand<'_>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_single(b.digit()).with_neg(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return add_long_scalar_mut(-a, b);
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return a.clone_from_single(b.digit() - *a.digits().first().unwrap_or(&0)).with_neg(),
        Ordering::Equal => return MutRepr::ZERO,
        Ordering::Greater => (),
    };

    let res = a.raw_mut();

    let mut acc = b.digit();

    for ptr in res.iter_mut() {
        let digit = RADIX + *ptr as Double - acc as Double;

        acc = (digit < RADIX) as Single;

        *ptr = digit as Single;

        if acc == 0 {
            break;
        }
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn sub_fixed_scalar_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.clone_from_single(b.digit()).with_neg(),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() == Sign::NEG {
        return add_fixed_scalar_mut(a, -b);
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return a.clone_from_single(b.digit() - *a.digits().first().unwrap_or(&0)).with_neg(),
        Ordering::Equal => return MutRepr::ZERO,
        Ordering::Greater => (),
    };

    let res = a.raw_mut();

    let mut acc = b.digit();

    for ptr in res.iter_mut() {
        let digit = RADIX + *ptr as Double - acc as Double;

        acc = (digit < RADIX) as Single;

        *ptr = digit as Single;

        if acc == 0 {
            break;
        }
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn mul_long_vector(a: VectorOperand<'_>, b: VectorOperand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return LongRepr::ZERO,
        (_, Sign::ZERO) => return LongRepr::ZERO,
        _ => (),
    }

    let mut res = vec![0; a.len() + b.len()];

    for (i, &aop) in a.digits().iter().enumerate() {
        let mut acc = 0;

        for (j, &bop) in b.digits().iter().enumerate() {
            acc += res[i + j] as Double + aop as Double * bop as Double;

            res[i + j] = acc as Single;

            acc >>= Single::BITS;
        }

        res[i + b.len()] += acc as Single;
    }

    LongRepr::from_raw(res, a.sign() * b.sign())
}

fn mul_fixed_vector<const L: usize>(a: VectorOperand<'_>, b: VectorOperand<'_>) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return FixedRepr::ZERO,
        (_, Sign::ZERO) => return FixedRepr::ZERO,
        _ => (),
    }

    let mut res = [0; L];
    let mut over = false;
    let mut next = 0;

    for (i, &aop) in a.digits().iter().enumerate() {
        let mut acc = 0;

        for (j, &bop) in b.digits().iter().take(L - i).enumerate() {
            acc += res[i + j] as Double + aop as Double * bop as Double;

            res[i + j] = acc as Single;

            acc >>= Single::BITS;
        }

        let idx = i + b.len();

        if idx < L {
            res[idx] += acc as Single;
            acc >>= Single::BITS;
        }

        over |= acc > 0 || i + b.len() > L;
        next = (next + acc) % RADIX;
    }

    FixedRepr::from_raw(res, a.sign() * b.sign())
        .with_overflow_val(next as Single)
        .with_overflow(over)
}

fn mul_long_scalar(a: VectorOperand<'_>, b: ScalarOperand) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return LongRepr::ZERO,
        (_, Sign::ZERO) => return LongRepr::ZERO,
        _ => (),
    }

    let mut acc = 0;
    let mut res = a.clone_into_vec(a.len() + 1);

    for ptr in res.iter_mut() {
        acc += *ptr as Double * b.digit() as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;
    }

    LongRepr::from_raw(res, a.sign())
}

fn mul_fixed_scalar<const L: usize>(a: VectorOperand<'_>, b: ScalarOperand) -> FixedRepr<L> {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return FixedRepr::ZERO,
        (_, Sign::ZERO) => return FixedRepr::ZERO,
        _ => (),
    }

    let mut acc = 0;
    let mut res = a.clone_into_arr();

    for ptr in res.iter_mut() {
        acc += *ptr as Double * b.sign() as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;
    }

    FixedRepr::from_raw(res, a.sign())
        .with_overflow_val(acc as Single)
        .with_overflow(acc > 0)
}

fn mul_long_vector_mut(mut a: LongMutOperand<'_>, b: VectorOperand<'_>) -> MutRepr {
    let repr = mul_long_vector(VectorOperand::from_raw(a.digits()).with_sign(a.sign()), b);

    a.clone_from_repr(repr)
}

fn mul_fixed_vector_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: VectorOperand<'_>) -> MutRepr {
    let repr = mul_fixed_vector(VectorOperand::from_raw(a.digits()).with_sign(a.sign()), b);

    a.clone_from_repr(repr)
}

fn mul_long_scalar_mut(mut a: LongMutOperand<'_>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return MutRepr::ZERO,
        (_, Sign::ZERO) => return MutRepr::ZERO,
        _ => (),
    }

    let res = a.raw_mut();

    let mut acc = 0;

    for ptr in res.iter_mut() {
        acc += *ptr as Double * b.digit() as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;

        if acc == 0 {
            break;
        }
    }

    if acc > 0 {
        res.push(acc as Single);
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn mul_fixed_scalar_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return MutRepr::ZERO,
        (_, Sign::ZERO) => return MutRepr::ZERO,
        _ => (),
    }

    let res = a.raw_mut();

    let mut acc = 0;

    for ptr in res.iter_mut() {
        acc += *ptr as Double * b.digit() as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;

        if acc == 0 {
            break;
        }
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn div_long_vector(a: VectorOperand<'_>, b: VectorOperand<'_>) -> (LongRepr, LongRepr) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return (LongRepr::ZERO, LongRepr::ZERO),
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b == VectorOperand::ONE {
        return (a.into(), LongRepr::ZERO);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => return (LongRepr::ZERO, a.into()),
        Ordering::Equal => return (LongRepr::from_single(1).with_sign(a.sign() * b.sign()), LongRepr::ZERO),
        Ordering::Greater => (),
    }

    let sign_div = a.sign() * b.sign();
    let sign_rem = a.sign();

    let mut div = vec![0; a.len()];
    let mut rem = vec![0; b.len() + 1];
    let mut len = 0;

    let a = a.with_sign(Sign::POS);
    let b = b.with_sign(Sign::POS);

    for (i, &aop) in a.digits().iter().enumerate().rev() {
        div_cycle!(rem, len, aop);

        if len < b.len() {
            continue;
        }

        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            let val = mul_long_scalar(b, (m as Single).into());

            match cmp_nums(val.digits(), &rem[..len]) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        div_apply!(mul_long_vector, sub_long_vector, div[i], rem, len, b, l);
    }

    (LongRepr::from_raw(div, sign_div), LongRepr::from_raw(rem, sign_rem))
}

fn div_fixed_vector<const L: usize>(a: VectorOperand<'_>, b: VectorOperand<'_>) -> (FixedRepr<L>, FixedRepr<L>) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => {
            return (FixedRepr::ZERO, FixedRepr::ZERO);
        },
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b == VectorOperand::ONE {
        return (a.into(), FixedRepr::ZERO);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => return (FixedRepr::ZERO, a.into()),
        Ordering::Equal => return (FixedRepr::ONE.with_sign(a.sign() * b.sign()), FixedRepr::ZERO),
        Ordering::Greater => (),
    }

    let sign_div = a.sign() * b.sign();
    let sign_rem = a.sign();

    let mut div = [0; L];
    let mut rem = [0; L];
    #[allow(unused_assignments)]
    let mut remx = 0;
    let mut len = 0;

    let a = a.with_sign(Sign::POS);
    let b = b.with_sign(Sign::POS);

    for (i, &aop) in a.digits().iter().enumerate().rev() {
        remx = rem[L - 1];

        div_cycle!(rem, len, aop);

        if len < b.len() {
            continue;
        }

        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            let val = mul_fixed_scalar::<L>(b, (m as Single).into());

            match cmp_nums_ext(&val.raw, val.overflow_val, &rem, remx) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        div_apply!(mul_fixed_vector::<L>, sub_fixed_vector::<L>, div[i], rem, len, b, l);
    }

    (FixedRepr::from_raw(div, sign_div), FixedRepr::from_raw(rem, sign_rem))
}

fn div_long_scalar(a: VectorOperand<'_>, b: ScalarOperand) -> (LongRepr, LongRepr) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return (LongRepr::ZERO, LongRepr::ZERO),
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b.digit() == 1 {
        return (a.into(), LongRepr::ZERO);
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return (LongRepr::ZERO, a.into()),
        Ordering::Equal => return (LongRepr::from_single(1).with_sign(a.sign()), LongRepr::ZERO),
        Ordering::Greater => (),
    }

    let mut div = vec![0; a.len()];
    let mut rem = 0 as Double;

    for (i, &aop) in a.digits().iter().enumerate().rev() {
        rem <<= Single::BITS;
        rem |= aop as Double;

        let digit = div_digit!(@scalar b.digit(), rem).saturating_sub(1) as Single;

        if digit > 0 {
            div[i] = digit;
            rem -= digit as Double * b.digit() as Double;
        }
    }

    (LongRepr::from_raw(div, a.sign()), LongRepr::from_double(rem))
}

fn div_fixed_scalar<const L: usize>(a: VectorOperand<'_>, b: ScalarOperand) -> (FixedRepr<L>, FixedRepr<L>) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return (FixedRepr::ZERO, FixedRepr::ZERO),
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b.digit() == 1 {
        return (a.into(), FixedRepr::ZERO);
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return (FixedRepr::ZERO, a.into()),
        Ordering::Equal => return (FixedRepr::from_single(1).with_sign(a.sign()), FixedRepr::ZERO),
        Ordering::Greater => (),
    }

    let mut div = [0; L];
    let mut rem = 0 as Double;

    for (i, &aop) in a.digits().iter().enumerate().rev() {
        rem <<= Single::BITS;
        rem |= aop as Double;

        let digit = div_digit!(@scalar b.digit(), rem).saturating_sub(1) as Single;

        if digit > 0 {
            div[i] = digit;
            rem -= digit as Double * b.digit() as Double;
        }
    }

    (FixedRepr::from_raw(div, a.sign()), FixedRepr::from_double(rem))
}

fn div_long_vector_mut(mut a: LongMutOperand<'_>, b: VectorOperand<'_>) -> MutRepr {
    let repr = div_long_vector(VectorOperand::from_raw(a.digits()).with_sign(a.sign()), b);

    a.clone_from_repr(repr.0)
}

fn div_fixed_vector_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: VectorOperand<'_>) -> MutRepr {
    let repr = div_fixed_vector(VectorOperand::from_raw(a.digits()).with_sign(a.sign()), b);

    a.clone_from_repr(repr.0)
}

fn rem_long_vector_mut(mut a: LongMutOperand<'_>, b: VectorOperand<'_>) -> MutRepr {
    let repr = div_long_vector(VectorOperand::from_raw(a.digits()).with_sign(a.sign()), b);

    a.clone_from_repr(repr.1)
}

fn rem_fixed_vector_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: VectorOperand<'_>) -> MutRepr {
    let repr = div_fixed_vector(VectorOperand::from_raw(a.digits()).with_sign(a.sign()), b);

    a.clone_from_repr(repr.1)
}

fn div_long_scalar_mut(mut a: LongMutOperand<'_>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return MutRepr::ZERO,
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b.digit() == 1 {
        return a.into();
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return MutRepr::ZERO,
        Ordering::Equal => return a.clone_from_single(1),
        Ordering::Greater => (),
    }

    let res = a.raw_mut();

    let mut rem = 0 as Double;

    for op in res.iter_mut().rev() {
        rem <<= Single::BITS;
        rem |= *op as Double;

        let digit = div_digit!(@scalar b.digit(), rem).saturating_sub(1) as Single;

        *op = digit;
        rem -= digit as Double * b.digit() as Double;
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn div_fixed_scalar_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return MutRepr::ZERO,
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b.digit() == 1 {
        return a.into();
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return MutRepr::ZERO,
        Ordering::Equal => return a.clone_from_single(1),
        Ordering::Greater => (),
    }

    let res = a.raw_mut();

    let mut rem = 0 as Double;

    for op in res.iter_mut().rev() {
        rem <<= Single::BITS;
        rem |= *op as Double;

        let digit = div_digit!(@scalar b.digit(), rem).saturating_sub(1) as Single;

        *op = digit;
        rem -= digit as Double * b.digit() as Double;
    }

    MutRepr::from_raw(a.raw(), a.sign())
}

fn rem_long_scalar_mut(mut a: LongMutOperand<'_>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return MutRepr::ZERO,
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b.digit() == 1 {
        return a.into();
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return a.into(),
        Ordering::Equal => return MutRepr::ZERO,
        Ordering::Greater => (),
    }

    let res = a.raw_mut();

    let mut rem = 0 as Double;

    for op in res.iter().rev() {
        rem <<= Single::BITS;
        rem |= *op as Double;

        let digit = div_digit!(@scalar b.digit(), rem).saturating_sub(1) as Single;

        rem -= digit as Double * b.digit() as Double;
    }

    a.clone_from_double(rem)
}

fn rem_fixed_scalar_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: ScalarOperand) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return MutRepr::ZERO,
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b.digit() == 1 {
        return a.into();
    }

    match cmp_nums(a.digits(), &[b.digit()]) {
        Ordering::Less => return a.into(),
        Ordering::Equal => return MutRepr::ZERO,
        Ordering::Greater => (),
    }

    let res = a.raw_mut();

    let mut rem = 0 as Double;

    for op in res.iter().rev() {
        rem <<= Single::BITS;
        rem |= *op as Double;

        let digit = div_digit!(@scalar b.digit(), rem).saturating_sub(1) as Single;

        rem -= digit as Double * b.digit() as Double;
    }

    a.clone_from_double(rem)
}

fn bit_long_vector<F>(a: VectorOperand<'_>, b: VectorOperand<'_>, func: F) -> LongRepr
where
    F: Fn(Single, Single) -> Single,
{
    let len = a.len().max(b.len());
    let res = zip_nums(a.digits(), b.digits(), 0)
        .map(|(&aop, &bop)| func(aop, bop))
        .collect_with(vec![0; len]);

    LongRepr::from_raw(res, Sign::POS)
}

fn bit_fixed_vector<const L: usize, F>(a: VectorOperand<'_>, b: VectorOperand<'_>, func: F) -> FixedRepr<L>
where
    F: Fn(Single, Single) -> Single,
{
    let res = zip_nums(a.digits(), b.digits(), 0)
        .map(|(&aop, &bop)| func(aop, bop))
        .collect_with([0; L]);

    FixedRepr::from_raw(res, Sign::POS)
}

fn bit_long_scalar<F>(a: VectorOperand<'_>, b: ScalarOperand, func: F) -> LongRepr
where
    F: Fn(Single, Single) -> Single,
{
    bit_long_vector(a, VectorOperand::from_raw(&[b.digit()]), func)
}

fn bit_fixed_scalar<const L: usize, F>(a: VectorOperand<'_>, b: ScalarOperand, func: F) -> FixedRepr<L>
where
    F: Fn(Single, Single) -> Single,
{
    bit_fixed_vector(a, VectorOperand::from_raw(&[b.digit()]), func)
}

fn bit_long_vector_mut<F>(mut a: LongMutOperand<'_>, b: VectorOperand<'_>, func: F)
where
    F: Fn(Single, Single) -> Single,
{
    let len = a.len().max(b.len());

    a.raw_mut().resize(len, 0);

    for (i, ptr) in &mut a.raw_mut().iter_mut().enumerate() {
        let bop = *b.digits().get(i).unwrap_or(&0);

        *ptr = func(*ptr, bop);
    }
}

fn bit_fixed_vector_mut<const L: usize, F>(mut a: FixedMutOperand<'_, L>, b: VectorOperand<'_>, func: F)
where
    F: Fn(Single, Single) -> Single,
{
    for (i, ptr) in &mut a.raw_mut().iter_mut().enumerate() {
        let bop = *b.digits().get(i).unwrap_or(&0);

        *ptr = func(*ptr, bop);
    }
}

fn bit_long_scalar_mut<F>(a: LongMutOperand<'_>, b: ScalarOperand, func: F)
where
    F: Fn(Single, Single) -> Single,
{
    bit_long_vector_mut(a, VectorOperand::from_raw(&[b.digit()]), func)
}

fn bit_fixed_scalar_mut<const L: usize, F>(a: FixedMutOperand<'_, L>, b: ScalarOperand, func: F)
where
    F: Fn(Single, Single) -> Single,
{
    bit_fixed_vector_mut(a, VectorOperand::from_raw(&[b.digit()]), func)
}

fn shl_long(a: VectorOperand<'_>, val: usize) -> LongRepr {
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

    for (i, ptr) in res.iter_mut().skip(offset).enumerate() {
        let val_h = a.digits().get(i).unwrap_or(&0);
        let val_l = a.digits().get(i.wrapping_sub(1)).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *ptr = val_h | val_l;
    }

    LongRepr::from_raw(res, sign)
}

fn shl_fixed<const L: usize>(a: VectorOperand<'_>, val: usize) -> FixedRepr<L> {
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

    for (i, ptr) in res.iter_mut().skip(offset).enumerate() {
        let val_h = a.digits().get(i).unwrap_or(&0);
        let val_l = a.digits().get(i.wrapping_sub(1)).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *ptr = val_h | val_l;
    }

    FixedRepr::from_raw(res, sign)
}

fn shl_long_mut(mut a: LongMutOperand<'_>, val: usize) -> MutRepr {
    const BITS: usize = Single::BITS as usize;

    let sign = a.sign();

    if val == 0 {
        return a.into();
    }

    if sign == Sign::ZERO {
        return MutRepr::ZERO;
    }

    let offset = val / BITS;
    let shl = val % BITS;
    let shr = BITS - shl;
    let len = a.len() + (val + BITS - 1) / BITS;
    let res = a.raw_mut();

    res.resize(len, 0);

    for i in offset..len {
        let val_h = res.get(i - offset).unwrap_or(&0);
        let val_l = res.get((i - offset).wrapping_sub(1)).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        res[i] = val_h | val_l;
    }

    MutRepr::from_raw(res, sign)
}

fn shl_fixed_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, val: usize) -> MutRepr {
    const BITS: usize = Single::BITS as usize;

    let sign = a.sign();

    if val == 0 {
        return a.into();
    }

    if sign == Sign::ZERO {
        return MutRepr::ZERO;
    }

    let offset = val / BITS;
    let shl = val % BITS;
    let shr = BITS - shl;
    let len = a.len() + (val + BITS - 1) / BITS;
    let len = len.min(L);
    let res = a.raw_mut();

    for i in offset..len {
        let val_h = res.get(i - offset).unwrap_or(&0);
        let val_l = res.get((i - offset).wrapping_sub(1)).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        res[i] = val_h | val_l;
    }

    MutRepr::from_raw(res, sign)
}

fn shr_long(a: VectorOperand<'_>, val: usize) -> LongRepr {
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

    for (i, ptr) in res.iter_mut().enumerate() {
        let val_h = a.digits().get(i + offset + 1).unwrap_or(&0);
        let val_l = a.digits().get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *ptr = val_h | val_l;
    }

    LongRepr::from_raw(res, sign)
}

fn shr_fixed<const L: usize>(a: VectorOperand<'_>, val: usize) -> FixedRepr<L> {
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

    for (i, ptr) in res.iter_mut().take(len).enumerate() {
        let val_h = a.digits().get(i + offset + 1).unwrap_or(&0);
        let val_l = a.digits().get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        *ptr = val_h | val_l;
    }

    FixedRepr::from_raw(res, sign)
}

fn shr_long_mut(mut a: LongMutOperand, val: usize) -> MutRepr {
    const BITS: usize = Single::BITS as usize;

    let len = a.len();
    let sign = a.sign();

    if val >= a.len() * BITS {
        return MutRepr::ZERO;
    }

    let offset = val / BITS;
    let shr = val % BITS;
    let shl = BITS - shr;

    let res = a.raw_mut();

    for i in 0..len - offset {
        let val_h = res.get(i + offset + 1).unwrap_or(&0);
        let val_l = res.get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        res[i] = val_h | val_l;
    }

    MutRepr::from_raw(res, sign)
}

fn shr_fixed_mut<const L: usize>(mut a: FixedMutOperand<L>, val: usize) -> MutRepr {
    const BITS: usize = Single::BITS as usize;

    let len = a.len();
    let sign = a.sign();

    if val >= a.len() * BITS {
        return MutRepr::ZERO;
    }

    let offset = val / BITS;
    let shr = val % BITS;
    let shl = BITS - shr;

    let res = a.raw_mut();

    for i in 0..len - offset {
        let val_h = res.get(i + offset + 1).unwrap_or(&0);
        let val_l = res.get(i + offset).unwrap_or(&0);

        let val_h = val_h.checked_shl(shl as u32).unwrap_or(0);
        let val_l = val_l.checked_shr(shr as u32).unwrap_or(0);

        res[i] = val_h | val_l;
    }

    MutRepr::from_raw(res, sign)
}

ops_impl!(@bin |a: Sign, b: Sign| -> Sign, * Sign::from((a as i8) * (b as i8)));

ops_impl!(@un |a: Sign| -> Sign, - Sign::from(-(a as i8)));

ops_impl!(@un |a: SignedLong| -> SignedLong, - a.with_neg());
ops_impl!(@un |a: &SignedLong| -> SignedLong, - a.clone().with_neg());

ops_impl!(@un <const L: usize> |a: SignedFixed<L>| -> SignedFixed<L>, - a.with_neg());
ops_impl!(@un <const L: usize> |a: &SignedFixed<L>| -> SignedFixed<L>, - (*a).with_neg());

ops_impl!(@un |a: ScalarOperand| -> ScalarOperand, - a.with_neg());
ops_impl!(@un <'digits> |*a: &VectorOperand<'digits>| -> VectorOperand<'digits>, - a.with_neg());
ops_impl!(@un <'digits> |a: LongMutOperand<'digits>| -> LongMutOperand<'digits>, - a.with_neg());
ops_impl!(@un <'digits, const L: usize> |a: FixedMutOperand<'digits, L>| -> FixedMutOperand<'digits, L>, - a.with_neg());

ops_impl!(@bin |*a: &SignedLong, *b: &SignedLong| -> SignedLong,
    + add_long_vector((&a).into(), (&b).into()),
    - sub_long_vector((&a).into(), (&b).into()),
    * mul_long_vector((&a).into(), (&b).into()),
    / div_long_vector((&a).into(), (&b).into()).0,
    % div_long_vector((&a).into(), (&b).into()).1,
    | bit_long_vector((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_long_vector((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_long_vector((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |*a: &UnsignedLong, *b: &UnsignedLong| -> UnsignedLong,
    + add_long_vector((&a).into(), (&b).into()),
    - sub_long_vector((&a).into(), (&b).into()),
    * mul_long_vector((&a).into(), (&b).into()),
    / div_long_vector((&a).into(), (&b).into()).0,
    % div_long_vector((&a).into(), (&b).into()).1,
    | bit_long_vector((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_long_vector((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_long_vector((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |*a: &SignedLong, b: Single| -> SignedLong,
    + add_long_scalar((&a).into(), b.into()),
    - sub_long_scalar((&a).into(), b.into()),
    * mul_long_scalar((&a).into(), b.into()),
    / div_long_scalar((&a).into(), b.into()).0,
    % div_long_scalar((&a).into(), b.into()).1,
    | bit_long_scalar((&a).into(), b.into(), |aop, bop| aop | bop),
    & bit_long_scalar((&a).into(), b.into(), |aop, bop| aop & bop),
    ^ bit_long_scalar((&a).into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |*a: &UnsignedLong, b: Single| -> UnsignedLong,
    + add_long_scalar((&a).into(), b.into()),
    - sub_long_scalar((&a).into(), b.into()),
    * mul_long_scalar((&a).into(), b.into()),
    / div_long_scalar((&a).into(), b.into()).0,
    % div_long_scalar((&a).into(), b.into()).1,
    | bit_long_scalar((&a).into(), b.into(), |aop, bop| aop | bop),
    & bit_long_scalar((&a).into(), b.into(), |aop, bop| aop & bop),
    ^ bit_long_scalar((&a).into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |a: Single, *b: &SignedLong| -> SignedLong,
    + add_long_scalar((&b).into(), a.into()),
    - sub_long_scalar((&b).into(), a.into()),
    * mul_long_scalar((&b).into(), a.into()),
    / div_long_scalar((&b).into(), a.into()).0,
    % div_long_scalar((&b).into(), a.into()).1,
    | bit_long_scalar((&b).into(), a.into(), |aop, bop| aop | bop),
    & bit_long_scalar((&b).into(), a.into(), |aop, bop| aop & bop),
    ^ bit_long_scalar((&b).into(), a.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |a: Single, *b: &UnsignedLong| -> UnsignedLong,
    + add_long_scalar((&b).into(), a.into()),
    - sub_long_scalar((&b).into(), a.into()),
    * mul_long_scalar((&b).into(), a.into()),
    / div_long_scalar((&b).into(), a.into()).0,
    % div_long_scalar((&b).into(), a.into()).1,
    | bit_long_scalar((&b).into(), a.into(), |aop, bop| aop | bop),
    & bit_long_scalar((&b).into(), a.into(), |aop, bop| aop & bop),
    ^ bit_long_scalar((&b).into(), a.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |*a: &SignedLong, *b: usize| -> SignedLong,
    << shl_long((&a).into(), b),
    >> shr_long((&a).into(), b));

ops_impl!(@bin |*a: &UnsignedLong, *b: usize| -> UnsignedLong,
    << shl_long((&a).into(), b),
    >> shr_long((&a).into(), b));

ops_impl!(@mut |a: mut SignedLong, *b: &SignedLong|,
    += ops_impl_mut!(@ref add_long_vector_mut, a, b),
    -= ops_impl_mut!(@ref sub_long_vector_mut, a, b),
    *= ops_impl_mut!(@ref mul_long_vector_mut, a, b),
    /= ops_impl_mut!(@ref div_long_vector_mut, a, b),
    %= ops_impl_mut!(@ref rem_long_vector_mut, a, b),
    |= bit_long_vector_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_long_vector_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_long_vector_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut |a: mut UnsignedLong, *b: &UnsignedLong|,
    += ops_impl_mut!(@ref add_long_vector_mut, a, b),
    -= ops_impl_mut!(@ref sub_long_vector_mut, a, b),
    *= ops_impl_mut!(@ref mul_long_vector_mut, a, b),
    /= ops_impl_mut!(@ref div_long_vector_mut, a, b),
    %= ops_impl_mut!(@ref rem_long_vector_mut, a, b),
    |= bit_long_vector_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_long_vector_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_long_vector_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut |a: mut SignedLong, b: Single|,
    += ops_impl_mut!(@val add_long_scalar_mut, a, b.into()),
    -= ops_impl_mut!(@val sub_long_scalar_mut, a, b.into()),
    *= ops_impl_mut!(@val mul_long_scalar_mut, a, b.into()),
    /= ops_impl_mut!(@val div_long_scalar_mut, a, b.into()),
    %= ops_impl_mut!(@val rem_long_scalar_mut, a, b.into()),
    |= bit_long_scalar_mut(a.into(), b.into(), |aop, bop| aop | bop),
    &= bit_long_scalar_mut(a.into(), b.into(), |aop, bop| aop & bop),
    ^= bit_long_scalar_mut(a.into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@mut |a: mut UnsignedLong, b: Single|,
    += ops_impl_mut!(@val add_long_scalar_mut, a, b.into()),
    -= ops_impl_mut!(@val sub_long_scalar_mut, a, b.into()),
    *= ops_impl_mut!(@val mul_long_scalar_mut, a, b.into()),
    /= ops_impl_mut!(@val div_long_scalar_mut, a, b.into()),
    %= ops_impl_mut!(@val rem_long_scalar_mut, a, b.into()),
    |= bit_long_scalar_mut(a.into(), b.into(), |aop, bop| aop | bop),
    &= bit_long_scalar_mut(a.into(), b.into(), |aop, bop| aop & bop),
    ^= bit_long_scalar_mut(a.into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@mut |a: mut SignedLong, b: usize|,
    <<= shl_long_mut(a.into(), b),
    >>= shr_long_mut(a.into(), b));

ops_impl!(@mut |a: mut UnsignedLong, b: usize|,
    <<= shl_long_mut(a.into(), b),
    >>= shr_long_mut(a.into(), b));

ops_impl!(@bin <const L: usize> |*a: &SignedFixed<L>, *b: &SignedFixed<L>| -> SignedFixed::<L>,
    + add_fixed_vector((&a).into(), (&b).into()),
    - sub_fixed_vector((&a).into(), (&b).into()),
    * mul_fixed_vector((&a).into(), (&b).into()),
    / div_fixed_vector((&a).into(), (&b).into()).0,
    % div_fixed_vector((&a).into(), (&b).into()).1,
    | bit_fixed_vector((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_fixed_vector((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_fixed_vector((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &UnsignedFixed<L>, *b: &UnsignedFixed<L>| -> UnsignedFixed::<L>,
    + add_fixed_vector((&a).into(), (&b).into()),
    - sub_fixed_vector((&a).into(), (&b).into()),
    * mul_fixed_vector((&a).into(), (&b).into()),
    / div_fixed_vector((&a).into(), (&b).into()).0,
    % div_fixed_vector((&a).into(), (&b).into()).1,
    | bit_fixed_vector((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_fixed_vector((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_fixed_vector((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &SignedFixed<L>, b: Single| -> SignedFixed::<L>,
    + add_fixed_scalar((&a).into(), b.into()),
    - sub_fixed_scalar((&a).into(), b.into()),
    * mul_fixed_scalar((&a).into(), b.into()),
    / div_fixed_scalar((&a).into(), b.into()).0,
    % div_fixed_scalar((&a).into(), b.into()).1,
    | bit_fixed_scalar((&a).into(), b.into(), |aop, bop| aop | bop),
    & bit_fixed_scalar((&a).into(), b.into(), |aop, bop| aop & bop),
    ^ bit_fixed_scalar((&a).into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &UnsignedFixed<L>, b: Single| -> UnsignedFixed::<L>,
    + add_fixed_scalar((&a).into(), b.into()),
    - sub_fixed_scalar((&a).into(), b.into()),
    * mul_fixed_scalar((&a).into(), b.into()),
    / div_fixed_scalar((&a).into(), b.into()).0,
    % div_fixed_scalar((&a).into(), b.into()).1,
    | bit_fixed_scalar((&a).into(), b.into(), |aop, bop| aop | bop),
    & bit_fixed_scalar((&a).into(), b.into(), |aop, bop| aop & bop),
    ^ bit_fixed_scalar((&a).into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |a: Single, *b: &SignedFixed<L>| -> SignedFixed::<L>,
    + add_fixed_scalar((&b).into(), a.into()),
    - sub_fixed_scalar((&b).into(), a.into()),
    * mul_fixed_scalar((&b).into(), a.into()),
    / div_fixed_scalar((&b).into(), a.into()).0,
    % div_fixed_scalar((&b).into(), a.into()).1,
    | bit_fixed_scalar((&b).into(), a.into(), |aop, bop| aop | bop),
    & bit_fixed_scalar((&b).into(), a.into(), |aop, bop| aop & bop),
    ^ bit_fixed_scalar((&b).into(), a.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |a: Single, *b: &UnsignedFixed<L>| -> UnsignedFixed::<L>,
    + add_fixed_scalar((&b).into(), a.into()),
    - sub_fixed_scalar((&b).into(), a.into()),
    * mul_fixed_scalar((&b).into(), a.into()),
    / div_fixed_scalar((&b).into(), a.into()).0,
    % div_fixed_scalar((&b).into(), a.into()).1,
    | bit_fixed_scalar((&b).into(), a.into(), |aop, bop| aop | bop),
    & bit_fixed_scalar((&b).into(), a.into(), |aop, bop| aop & bop),
    ^ bit_fixed_scalar((&b).into(), a.into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &SignedFixed<L>, b: usize| -> SignedFixed::<L>,
    << shl_fixed((&a).into(), b),
    >> shr_fixed((&a).into(), b));

ops_impl!(@bin <const L: usize> |*a: &UnsignedFixed<L>, b: usize| -> UnsignedFixed::<L>,
    << shl_fixed((&a).into(), b),
    >> shr_fixed((&a).into(), b));

ops_impl!(@mut <const L: usize> |a: mut SignedFixed<L>, *b: &SignedFixed<L>|,
    += ops_impl_mut!(@ref add_fixed_vector_mut, a, b),
    -= ops_impl_mut!(@ref sub_fixed_vector_mut, a, b),
    *= ops_impl_mut!(@ref mul_fixed_vector_mut, a, b),
    /= ops_impl_mut!(@ref div_fixed_vector_mut, a, b),
    %= ops_impl_mut!(@ref rem_fixed_vector_mut, a, b),
    |= bit_fixed_vector_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_fixed_vector_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_fixed_vector_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut UnsignedFixed<L>, *b: &UnsignedFixed<L>|,
    += ops_impl_mut!(@ref add_fixed_vector_mut, a, b),
    -= ops_impl_mut!(@ref sub_fixed_vector_mut, a, b),
    *= ops_impl_mut!(@ref mul_fixed_vector_mut, a, b),
    /= ops_impl_mut!(@ref div_fixed_vector_mut, a, b),
    %= ops_impl_mut!(@ref rem_fixed_vector_mut, a, b),
    |= bit_fixed_vector_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_fixed_vector_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_fixed_vector_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut SignedFixed<L>, b: Single|,
    += ops_impl_mut!(@val add_fixed_scalar_mut, a, b.into()),
    -= ops_impl_mut!(@val sub_fixed_scalar_mut, a, b.into()),
    *= ops_impl_mut!(@val mul_fixed_scalar_mut, a, b.into()),
    /= ops_impl_mut!(@val div_fixed_scalar_mut, a, b.into()),
    %= ops_impl_mut!(@val rem_fixed_scalar_mut, a, b.into()),
    |= bit_fixed_scalar_mut(a.into(), b.into(), |aop, bop| aop | bop),
    &= bit_fixed_scalar_mut(a.into(), b.into(), |aop, bop| aop & bop),
    ^= bit_fixed_scalar_mut(a.into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut UnsignedFixed<L>, b: Single|,
    += ops_impl_mut!(@val add_fixed_scalar_mut, a, b.into()),
    -= ops_impl_mut!(@val sub_fixed_scalar_mut, a, b.into()),
    *= ops_impl_mut!(@val mul_fixed_scalar_mut, a, b.into()),
    /= ops_impl_mut!(@val div_fixed_scalar_mut, a, b.into()),
    %= ops_impl_mut!(@val rem_fixed_scalar_mut, a, b.into()),
    |= bit_fixed_scalar_mut(a.into(), b.into(), |aop, bop| aop | bop),
    &= bit_fixed_scalar_mut(a.into(), b.into(), |aop, bop| aop & bop),
    ^= bit_fixed_scalar_mut(a.into(), b.into(), |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut SignedFixed<L>, b: usize|,
    <<= ops_impl_mut!(@val shl_fixed_mut, a, b),
    >>= ops_impl_mut!(@val shr_fixed_mut, a, b));

ops_impl!(@mut <const L: usize> |a: mut UnsignedFixed<L>, b: usize|,
    <<= ops_impl_mut!(@val shl_fixed_mut, a, b),
    >>= ops_impl_mut!(@val shr_fixed_mut, a, b));

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

fn get_radix_from_str(s: &str) -> Result<(&str, u16), TryFromStrError> {
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

fn get_digits_from_str(s: &str, radix: u16) -> Result<Vec<u8>, TryFromStrError> {
    let r = radix as u8;

    let mut res = s
        .chars()
        .rev()
        .filter_map(|ch| {
            let byte = ch as u8;

            match ch {
                '0'..='9' if byte - b'0' < r => Some(Ok(byte - b'0')),
                'a'..='f' if byte - b'a' + 10 < r => Some(Ok(byte - b'a' + 10)),
                'A'..='F' if byte - b'A' + 10 < r => Some(Ok(byte - b'A' + 10)),
                '_' => None,
                _ => Some(Err(TryFromStrError::InvalidSymbol { ch, radix })),
            }
        })
        .collect::<Result<Vec<u8>, TryFromStrError>>()?;

    res.truncate(get_len(&res));

    Ok(res)
}

fn get_sign<F: Fixed>(val: F, default: Sign) -> Sign
where
    for<'f> &'f F: Ops,
{
    let zero = F::zero();

    if val != zero { default } else { Sign::ZERO }
}

fn get_len<F: Fixed>(digits: &[F]) -> usize
where
    for<'f> &'f F: Ops,
{
    let zero = F::zero();

    let mut len = digits.len();

    for digit in digits.iter().rev() {
        if digit != &zero {
            return len;
        }

        len -= 1;
    }

    0
}

fn get_len_rev<F: Fixed>(digits: &[F], val: F) -> usize
where
    for<'f> &'f F: Ops,
{
    for (idx, digit) in digits.iter().enumerate() {
        if digit != &val {
            return idx;
        }
    }

    0
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRIMES_16BIT: [usize; 1] = [65_519];
    const PRIMES_24BIT: [usize; 2] = [16_773_439, 16_718_813];

    type S32 = signed_fixed!(32);
    type U32 = unsigned_fixed!(32);

    macro_rules! assert_long_from_std {
        (@signed $expr:expr, $digits:expr) => {
            assert_eq!(
                SignedLong::from($expr),
                SignedLong {
                    digits: $digits,
                    sign: Sign::from($expr),
                }
            );
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from($expr), UnsignedLong { digits: $digits });
        };
    }

    macro_rules! assert_fixed_from_std {
        (@signed $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(
                S32::from($expr),
                SignedFixed {
                    raw: $digits,
                    len: $len,
                    sign: Sign::from($expr),
                }
            );
        };
        (@unsigned $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::from($expr), UnsignedFixed { raw: $digits, len: $len });
        };
    }

    macro_rules! assert_long_from_bytes {
        (@signed $expr:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::from_bytes($expr), SignedLong { digits: $digits, sign: $sign });
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from_bytes($expr), UnsignedLong { digits: $digits });
        };
    }

    macro_rules! assert_fixed_from_bytes {
        (@signed $expr:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::from_bytes($expr),
                SignedFixed {
                    raw: $digits,
                    len: $len,
                    sign: $sign
                }
            );
        };
        (@unsigned $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::from_bytes($expr), UnsignedFixed { raw: $digits, len: $len });
        };
    }

    macro_rules! assert_long_from_digits {
        (@signed $expr:expr, $radix:expr, $digits:expr, $sign:expr) => {
            assert_eq!(
                SignedLong::try_from_digits($expr, $radix),
                Ok(SignedLong { digits: $digits, sign: $sign })
            );
        };
        (@unsigned $expr:expr, $radix:expr, $digits:expr) => {
            assert_eq!(
                UnsignedLong::try_from_digits($expr, $radix),
                Ok(UnsignedLong { digits: $digits })
            );
        };
    }

    macro_rules! assert_fixed_from_digits {
        (@signed $expr:expr, $radix:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::try_from_digits($expr, $radix),
                Ok(SignedFixed {
                    raw: $digits,
                    len: $len,
                    sign: $sign
                })
            );
        };
        (@unsigned $expr:expr, $radix:expr, $digits:expr, $len:expr) => {
            assert_eq!(
                U32::try_from_digits($expr, $radix),
                Ok(UnsignedFixed { raw: $digits, len: $len })
            );
        };
    }

    macro_rules! assert_long_from_str {
        (@signed $expr:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::from_str($expr), Ok(SignedLong { digits: $digits, sign: $sign }));
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from_str($expr), Ok(UnsignedLong { digits: $digits }));
        };
    }

    macro_rules! assert_fixed_from_str {
        (@signed $expr:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::from_str($expr),
                Ok(SignedFixed {
                    raw: $digits,
                    len: $len,
                    sign: $sign
                })
            );
        };
        (@unsigned $expr:expr, $digits:expr, $len:expr) => {
            assert_eq!(U32::from_str($expr), Ok(UnsignedFixed { raw: $digits, len: $len }));
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

    macro_rules! assert_ops {
        ($fn:ident, $type_std:ty, $type_ext:ty, $type:ty, |$a:ident, $b:ident, $aop:ident, $bop:ident| [$({ $expr_lval:expr } { $expr_rval:expr })+]) => {
            #[test]
            fn $fn() {
                for a in ((<$type_std>::MIN + 1) as $type_ext..<$type_std>::MAX as $type_ext).step_by(PRIMES_24BIT[0]) {
                    for b in ((<$type_std>::MIN + 1) as $type_ext..<$type_std>::MAX as $type_ext).step_by(PRIMES_24BIT[1]) {
                        let aop = &<$type>::from(a);
                        let bop = &<$type>::from(b);

                        $({
                            let lval = (|$a: $type_ext, $b: $type_ext| $expr_lval)(a, b);
                            let rval = (|$aop: &$type, $bop: &$type| $expr_rval)(aop, bop);

                            assert_eq!(lval, rval);
                        })+
                    }
                }
            }
        };

        (@shift $fn:ident, $type_std:ty, $type_ext:ty, $type:ty, $range:expr, |$val:ident, $valop:ident, $shift:ident| [$({ $expr_lval:expr } { $expr_rval:expr })+]) => {
            #[test]
            fn $fn() {
                for val in ((<$type_std>::MIN + 1) as $type_ext..<$type_std>::MAX as $type_ext).step_by(PRIMES_16BIT[0]) {
                    for shift in $range {
                        let valop = &<$type>::from(val);

                        $({
                            let lval = (|$val: $type_ext, $shift: usize| $expr_lval)(val, shift);
                            let rval = (|$valop: &$type, $shift: usize| $expr_rval)(valop, shift);

                            assert_eq!(lval, rval);
                        })+
                    }
                }
            }
        };
    }

    fn normalized(val: &[u8]) -> Vec<u8> {
        let len = get_len(val);

        val[..len].to_vec()
    }

    fn value(digits: &[u8], radix: u16) -> u32 {
        digits.iter().rev().fold(0, |acc, &x| acc * radix as u32 + x as u32)
    }

    fn add(digits: &mut [u8], radix: u16, val: u16) -> bool {
        let mut acc = val;

        for digit in digits {
            acc += *digit as u16;

            *digit = (acc % radix) as Single;

            acc /= radix;
        }

        acc > 0
    }

    #[test]
    fn from_std_long() {
        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i64;
            let nval = -pval;

            assert_long_from_std!(@signed pval, normalized(&bytes));
            assert_long_from_std!(@signed nval, normalized(&bytes));
            assert_long_from_std!(@unsigned val, normalized(&bytes));
        }
    }

    #[test]
    fn from_std_fixed() {
        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i64;
            let nval = -pval;

            assert_fixed_from_std!(@signed pval, bytes, get_len(&bytes));
            assert_fixed_from_std!(@signed nval, bytes, get_len(&bytes));
            assert_fixed_from_std!(@unsigned val, bytes, get_len(&bytes));
        }
    }

    #[test]
    fn from_bytes_long() {
        assert_eq!(SignedLong::from_bytes([]), SignedLong::default());
        assert_eq!(UnsignedLong::from_bytes([]), UnsignedLong::default());

        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_long_from_bytes!(@signed &bytes, normalized(&bytes), Sign::from(val));
            assert_long_from_bytes!(@unsigned &bytes, normalized(&bytes));
        }
    }

    #[test]
    fn from_bytes_fixed() {
        assert_eq!(S32::from_bytes([]), S32::default());
        assert_eq!(U32::from_bytes([]), U32::default());

        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_fixed_from_bytes!(@signed &bytes, bytes, get_len(&bytes), Sign::from(val));
            assert_fixed_from_bytes!(@unsigned &bytes, bytes, get_len(&bytes));
        }
    }

    #[test]
    fn from_digits_long() {
        assert_eq!(SignedLong::try_from_digits(&[], 31), Ok(SignedLong::default()));
        assert_eq!(UnsignedLong::try_from_digits(&[], 31), Ok(UnsignedLong::default()));

        for radix in 8..=40 {
            let mut digits = [0; 4];

            while !add(&mut digits, radix, radix - 5) {
                let val = value(&digits, radix);
                let bytes = val.to_le_bytes();

                assert_long_from_digits!(@signed &digits, radix, normalized(&bytes), Sign::from(val));
                assert_long_from_digits!(@unsigned &digits, radix, normalized(&bytes));
            }
        }
    }

    #[test]
    fn from_digits_fixed() {
        assert_eq!(S32::try_from_digits(&[], 31), Ok(S32::default()));
        assert_eq!(U32::try_from_digits(&[], 31), Ok(U32::default()));

        for radix in 8..=40 {
            let mut digits = [0; 4];

            while !add(&mut digits, radix, radix - 5) {
                let val = value(&digits, radix);
                let len = get_len(&val.to_le_bytes());
                let bytes = val.to_le_bytes();

                assert_fixed_from_digits!(@signed &digits, radix, bytes, len, Sign::from(val));
                assert_fixed_from_digits!(@unsigned &digits, radix, bytes, len);
            }
        }
    }

    #[test]
    fn from_str_long() {
        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let dec_pos = format!("{val:#020}");
            let bin_pos = format!("{val:#020b}");
            let oct_pos = format!("{val:#020o}");
            let hex_pos = format!("{val:#020x}");

            let dec_neg = format!("-{val:#020}");
            let bin_neg = format!("-{val:#020b}");
            let oct_neg = format!("-{val:#020o}");
            let hex_neg = format!("-{val:#020x}");

            let bytes = val.to_le_bytes();

            let sign_pos = Sign::from(val);
            let sign_neg = -sign_pos;

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

            assert!(
                val == 0 || UnsignedLong::from_str(&dec_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative)
            );
            assert!(
                val == 0 || UnsignedLong::from_str(&bin_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative)
            );
            assert!(
                val == 0 || UnsignedLong::from_str(&oct_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative)
            );
            assert!(
                val == 0 || UnsignedLong::from_str(&hex_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative)
            );
        }
    }

    #[test]
    fn from_str_fixed() {
        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let dec_pos = format!("{val:#020}");
            let bin_pos = format!("{val:#020b}");
            let oct_pos = format!("{val:#020o}");
            let hex_pos = format!("{val:#020x}");

            let dec_neg = format!("-{val:#020}");
            let bin_neg = format!("-{val:#020b}");
            let oct_neg = format!("-{val:#020o}");
            let hex_neg = format!("-{val:#020x}");

            let bytes = val.to_le_bytes();

            let sign_pos = Sign::from(val);
            let sign_neg = -sign_pos;

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

            assert!(val == 0 || U32::from_str(&dec_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative));
            assert!(val == 0 || U32::from_str(&bin_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative));
            assert!(val == 0 || U32::from_str(&oct_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative));
            assert!(val == 0 || U32::from_str(&hex_neg).is_err_and(|err| err == TryFromStrError::UnsignedNegative));
        }
    }

    #[test]
    fn into_radix_long() -> anyhow::Result<()> {
        assert_eq!(SignedLong::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());
        assert_eq!(UnsignedLong::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());

        for radix in 8..=40 {
            let mut digits = [0; 4];

            while !add(&mut digits, radix, radix - 5) {
                assert_long_into_radix!(@signed &digits, radix);
                assert_long_into_radix!(@unsigned &digits, radix);
            }
        }

        Ok(())
    }

    #[test]
    fn into_radix_fixed() -> anyhow::Result<()> {
        assert_eq!(S32::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());
        assert_eq!(U32::try_from_digits(&[], 31)?.into_radix(31)?, Vec::<Single>::new());

        for radix in 8..=40 {
            let mut digits = [0; 4];

            while !add(&mut digits, radix, radix - 5) {
                assert_fixed_into_radix!(@signed &digits, get_len(&digits), radix);
                assert_fixed_into_radix!(@unsigned &digits, get_len(&digits), radix);
            }
        }

        Ok(())
    }

    #[test]
    fn to_str_long() {
        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let pval = val as i64;
            let nval = -pval;
            let sign = if val > 0 { "-" } else { "" };

            assert_eq!(format!("{:#}", SignedLong::from(pval)), format!("{:#}", val));
            assert_eq!(format!("{:#b}", SignedLong::from(pval)), format!("{:#b}", val));
            assert_eq!(format!("{:#o}", SignedLong::from(pval)), format!("{:#o}", val));
            assert_eq!(format!("{:#x}", SignedLong::from(pval)), format!("{:#x}", val));

            assert_eq!(format!("{:#}", SignedLong::from(nval)), format!("{}{:#}", sign, val));
            assert_eq!(format!("{:#b}", SignedLong::from(nval)), format!("{}{:#b}", sign, val));
            assert_eq!(format!("{:#o}", SignedLong::from(nval)), format!("{}{:#o}", sign, val));
            assert_eq!(format!("{:#x}", SignedLong::from(nval)), format!("{}{:#x}", sign, val));

            assert_eq!(format!("{:#}", UnsignedLong::from(val)), format!("{:#}", val));
            assert_eq!(format!("{:#b}", UnsignedLong::from(val)), format!("{:#b}", val));
            assert_eq!(format!("{:#o}", UnsignedLong::from(val)), format!("{:#o}", val));
            assert_eq!(format!("{:#x}", UnsignedLong::from(val)), format!("{:#x}", val));
        }
    }

    #[test]
    fn to_str_fixed() {
        for val in (u32::MIN..=u32::MAX).step_by(PRIMES_16BIT[0]) {
            let pval = val as i64;
            let nval = -pval;
            let sign = if val > 0 { "-" } else { "" };

            assert_eq!(format!("{:#}", S32::from(pval)), format!("{:#}", val));
            assert_eq!(format!("{:#b}", S32::from(pval)), format!("{:#b}", val));
            assert_eq!(format!("{:#o}", S32::from(pval)), format!("{:#o}", val));
            assert_eq!(format!("{:#x}", S32::from(pval)), format!("{:#x}", val));

            assert_eq!(format!("{:#}", S32::from(nval)), format!("{}{:#}", sign, val));
            assert_eq!(format!("{:#b}", S32::from(nval)), format!("{}{:#b}", sign, val));
            assert_eq!(format!("{:#o}", S32::from(nval)), format!("{}{:#o}", sign, val));
            assert_eq!(format!("{:#x}", S32::from(nval)), format!("{}{:#x}", sign, val));

            assert_eq!(format!("{:#}", U32::from(val)), format!("{:#}", val));
            assert_eq!(format!("{:#b}", U32::from(val)), format!("{:#b}", val));
            assert_eq!(format!("{:#o}", U32::from(val)), format!("{:#o}", val));
            assert_eq!(format!("{:#x}", U32::from(val)), format!("{:#x}", val));
        }
    }

    assert_ops!(signed_long_ops, i32, i64, SignedLong, |a, b, aop, bop| [
        { SignedLong::from(a + b) } { aop + bop }
        { SignedLong::from(a - b) } { aop - bop }
        { SignedLong::from(a * b) } { aop * bop }
        { SignedLong::from(a / b) } { aop / bop }
        { SignedLong::from(a % b) } { aop % bop }
        { SignedLong::from(a.unsigned_abs() | b.unsigned_abs()) } { aop | bop }
        { SignedLong::from(a.unsigned_abs() & b.unsigned_abs()) } { aop & bop }
        { SignedLong::from(a.unsigned_abs() ^ b.unsigned_abs()) } { aop ^ bop }
    ]);

    assert_ops!(unsigned_long_ops, u32, u64, UnsignedLong, |a, b, aop, bop| [
        { UnsignedLong::from(a + b) } { aop + bop }
        { UnsignedLong::from(a.saturating_sub(b)) } { aop - bop }
        { UnsignedLong::from(a * b) } { aop * bop }
        { UnsignedLong::from(a / b) } { aop / bop }
        { UnsignedLong::from(a % b) } { aop % bop }
        { UnsignedLong::from(a | b) } { aop | bop }
        { UnsignedLong::from(a & b) } { aop & bop }
        { UnsignedLong::from(a ^ b) } { aop ^ bop }
    ]);

    assert_ops!(signed_fixed_ops, i32, i64, S32, |a, b, aop, bop| [
        { S32::from(a + b) } { aop + bop }
        { S32::from(a - b) } { aop - bop }
        { S32::from(a * b) } { aop * bop }
        { S32::from(a / b) } { aop / bop }
        { S32::from(a % b) } { aop % bop }
        { S32::from(a.unsigned_abs() | b.unsigned_abs()) } { aop | bop }
        { S32::from(a.unsigned_abs() & b.unsigned_abs()) } { aop & bop }
        { S32::from(a.unsigned_abs() ^ b.unsigned_abs()) } { aop ^ bop }
    ]);

    assert_ops!(unsigned_fixed_ops, u32, u64, U32, |a, b, aop, bop| [
        { U32::from(a + b) } { aop + bop }
        { U32::from(a.saturating_sub(b)) } { aop - bop }
        { U32::from(a * b) } { aop * bop }
        { U32::from(a / b) } { aop / bop }
        { U32::from(a % b) } { aop % bop }
        { U32::from(a | b) } { aop | bop }
        { U32::from(a & b) } { aop & bop }
        { U32::from(a ^ b) } { aop ^ bop }
    ]);

    assert_ops!(@shift shift_signed_long, i32, i64, SignedLong, 0..32, |val, valop, shift| [
        { SignedLong::from(val.unsigned_abs() << shift).with_sign(get_sign(val.unsigned_abs() << shift, Sign::from(val))) } { valop << shift }
        { SignedLong::from(val.unsigned_abs() >> shift).with_sign(get_sign(val.unsigned_abs() >> shift, Sign::from(val))) } { valop >> shift }
    ]);

    assert_ops!(@shift shift_unsigned_long, u32, u64, UnsignedLong, 0..32, |val, valop, shift| [
        { UnsignedLong::from(val << shift) } { valop << shift }
        { UnsignedLong::from(val >> shift) } { valop >> shift }
    ]);

    assert_ops!(@shift shift_signed_fixed, i32, i64, S32, 0..32, |val, valop, shift| [
        { S32::from(val.unsigned_abs() << shift).with_sign(get_sign(val.unsigned_abs() << shift, Sign::from(val))) } { valop << shift }
        { S32::from(val.unsigned_abs() >> shift).with_sign(get_sign(val.unsigned_abs() >> shift, Sign::from(val))) } { valop >> shift }
    ]);

    assert_ops!(@shift shift_unsigned_fixed, u32, u64, U32, 0..32, |val, valop, shift| [
        { U32::from(val << shift) } { valop << shift }
        { U32::from(val >> shift) } { valop >> shift }
    ]);
}

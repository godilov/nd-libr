#![allow(unused)]
#![allow(clippy::manual_div_ceil)]

use std::{cmp::Ordering, fmt::Display, str::FromStr};

use digit::{BITS, BYTES, Double, Single};
use prime::{PRIMES, Primality};
use rand::Rng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use thiserror::Error;
use zerocopy::{IntoBytes, transmute};

use crate::{
    num::{radix::*, uops::*},
    ops::*,
};

#[macro_export]
macro_rules! signed {
    ($bits:expr) => {
        $crate::num::Signed<{ ($bits as usize).div_ceil($crate::num::digit::BITS as usize) }>
    };
}

#[macro_export]
macro_rules! unsigned {
    ($bits:expr) => {
        $crate::num::Unsigned<{ ($bits as usize).div_ceil($crate::num::digit::BITS as usize) }>
    };
}

macro_rules! num_impl {
    ($trait:ty, [$($primitive:ty),+] $(,)?) => {
        $(num_impl!($trait, $primitive);)+
    };
    ($trait:ty, $primitive:ty $(,)?) => {
        impl NumBuilder for $primitive {
            fn bitor_offset(&mut self, mask: u64, offset: usize) {
                *self |= (mask.checked_shl(offset as u32).unwrap_or(0)) as $primitive;
            }

            fn bitand_offset(&mut self, mask: u64, offset: usize) {
                *self &= (mask.checked_shl(offset as u32).unwrap_or(0)) as $primitive;
            }
        }

        impl Num for $primitive {
            fn bits(&self) -> usize {
                <$primitive>::BITS as usize
            }

            fn order(&self) -> usize {
                self.ilog2() as usize
            }

            fn sqrt(&self) -> Self {
                self.isqrt()
            }

            fn log(&self) -> Self {
                self.ilog2() as $primitive
            }

            fn is_even(&self) -> bool {
                *self % 2 == 0
            }
        }

        impl NumStatic for $primitive {
            const BITS: usize = <$primitive>::BITS as usize;
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
        }

        impl $trait for $primitive {}
    };
}

macro_rules! prime_impl {
    ($([$primitive:ty, $count:expr]),+) => {
        $(prime_impl!($primitive, $count,);)+
    };
    ($primitive:ty, $count:expr $(,)?) => {
        impl Primality for $primitive {
            fn primes() -> impl Iterator<Item = Self> {
                PRIMES.iter().map(|&p| p as $primitive).take($count).take_while(|&p| p <= Self::MAX.isqrt())
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

macro_rules! sign_from {
    (@unsigned [$($primitive:ty),+]) => {
        $(sign_from!(@unsigned $primitive);)+
    };
    (@signed [$($primitive:ty),+]) => {
        $(sign_from!(@signed $primitive);)+
    };
    (@unsigned $primitive:ty) => {
        impl From<$primitive> for Sign {
            fn from(value: $primitive) -> Self {
                if value == 0 { Sign::ZERO } else { Sign::POS }
            }
        }
    };
    (@signed $primitive:ty) => {
        impl From<$primitive> for Sign {
            fn from(value: $primitive) -> Self {
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
    (@signed [$($primitive:ty),+]) => {
        $(long_from!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+]) => {
        $(long_from!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Signed<L> {
            fn from(value: $primitive) -> Self {
                let sign = Sign::from(value);
                let bytes = value.to_le_bytes();
                let res = from_bytes_arr(&bytes, if sign == Sign::NEG { Single::MAX } else { 0 });

                Self(res)
            }
        }
    };
    (@unsigned $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Unsigned<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_bytes_arr(&bytes, 0);

                Self(res)
            }
        }
    };
}

#[cfg(all(target_pointer_width = "64", not(test)))]
pub mod digit {
    pub type Half = u32;
    pub type Single = u64;
    pub type Double = u128;

    pub(super) const MAX: Single = Single::MAX;
    pub(super) const MIN: Single = Single::MIN;
    pub(super) const BITS: usize = Single::BITS as usize;
    pub(super) const BYTES: usize = Single::BITS as usize / u8::BITS as usize;

    pub(super) const OCT_VAL: Double = (1 as Double) << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_VAL: Double = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;
}

#[cfg(all(target_pointer_width = "32", not(test)))]
pub mod digit {
    pub type Half = u16;
    pub type Single = u32;
    pub type Double = u64;

    pub(super) const MAX: Single = Single::MAX;
    pub(super) const MIN: Single = Single::MIN;
    pub(super) const BITS: usize = Single::BITS as usize;
    pub(super) const BYTES: usize = Single::BITS as usize / u8::BITS as usize;

    pub(super) const OCT_VAL: Double = (1 as Double) << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_VAL: Double = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;
}

#[cfg(test)]
pub mod digit {
    pub type Half = u8;
    pub type Single = u16;
    pub type Double = u32;

    pub(super) const MAX: Single = Single::MAX;
    pub(super) const MIN: Single = Single::MIN;
    pub(super) const BITS: usize = Single::BITS as usize;
    pub(super) const BYTES: usize = Single::BITS as usize / u8::BITS as usize;

    pub(super) const OCT_VAL: Double = (1 as Double) << 6;
    pub(super) const OCT_WIDTH: u8 = 2;

    pub(super) const DEC_VAL: Double = 100;
    pub(super) const DEC_WIDTH: u8 = 2;
}

pub mod prime {
    use std::mem::{replace, take};

    use super::NumUnsigned;
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

    pub trait Primality: NumUnsigned
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

mod radix {
    use super::digit::*;

    pub(super) const RADIX: Double = MAX as Double + 1;

    pub trait Radix {
        const WIDTH: u8;
        const PREFIX: &str;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Bin {
        pub(super) const PREFIX: &str = "0b";
        pub(super) const RADIX: Double = MAX as Double + 1;
        pub(super) const WIDTH: u8 = BITS as u8;
    }

    impl Oct {
        pub(super) const PREFIX: &str = "0o";
        pub(super) const RADIX: Double = OCT_VAL;
        pub(super) const WIDTH: u8 = OCT_WIDTH;
    }

    impl Dec {
        pub(super) const PREFIX: &str = "";
        pub(super) const RADIX: Double = DEC_VAL;
        pub(super) const WIDTH: u8 = DEC_WIDTH;
    }

    impl Hex {
        pub(super) const PREFIX: &str = "0x";
        pub(super) const RADIX: Double = MAX as Double + 1;
        pub(super) const WIDTH: u8 = BITS as u8 / 4;
    }

    impl Radix for Bin {
        const PREFIX: &str = Self::PREFIX;
        const WIDTH: u8 = Self::WIDTH;
    }

    impl Radix for Oct {
        const PREFIX: &str = Self::PREFIX;
        const WIDTH: u8 = Self::WIDTH;
    }

    impl Radix for Dec {
        const PREFIX: &str = Self::PREFIX;
        const WIDTH: u8 = Self::WIDTH;
    }

    impl Radix for Hex {
        const PREFIX: &str = Self::PREFIX;
        const WIDTH: u8 = Self::WIDTH;
    }
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

pub trait NumSigned: Num + From<i8>
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

pub trait NumUnsigned: Num + From<u8>
where
    for<'s> &'s Self: Ops,
{
}

pub trait NumStatic: Num + Copy
where
    for<'s> &'s Self: Ops,
{
    const BITS: usize;
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

trait ToBytes<const N: usize> {
    fn to_le_bytes(self) -> [u8; N];
    fn to_be_bytes(self) -> [u8; N];
    fn to_ne_bytes(self) -> [u8; N];
}

num_impl!(NumSigned, [i8, i16, i32, i64, i128, isize]);
num_impl!(NumUnsigned, [u8, u16, u32, u64, u128, usize]);
prime_impl!([u8, 1], [u16, 2], [u32, 5], [u64, 12], [u128, 20], [usize, 12]);

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);
long_from!(@signed [i8, i16, i32, i64, i128, isize]);
long_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromStrError {
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error("Found invalid symbol '{ch}' during parsing from string of radix '{radix}'")]
    InvalidSymbol { ch: char, radix: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: u8 },
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
    #[error("Found invalid digit '{digit}' during parsing from slice of radix '{radix}'")]
    InvalidDigits { digit: u8, radix: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryIntoDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: u8 },
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signed<const L: usize>(pub [Single; L]);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unsigned<const L: usize>(pub [Single; L]);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SignedFixed<const L: usize>(pub [Single; L], pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsignedFixed<const L: usize>(pub [Single; L], pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DigitsIterBin<'digits, const L: usize> {
    bits: usize,
    mask: Double,
    acc: Double,
    shl: usize,
    idx: usize,
    len: usize,
    digits: &'digits [Single; L],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DigitsIter<'digits, const L: usize> {
    acc: Double,
    shl: usize,
    idx: usize,
    len: usize,
    digits: &'digits [Single; L],
}

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

impl<const L: usize> From<&[u8]> for Signed<L> {
    fn from(value: &[u8]) -> Self {
        Self::from_bytes(value)
    }
}

impl<const L: usize> From<&[u8]> for Unsigned<L> {
    fn from(value: &[u8]) -> Self {
        Self::from_bytes(value)
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(s)
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = TryFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(s)
    }
}

impl<const L: usize> From<Signed<L>> for Unsigned<L> {
    fn from(value: Signed<L>) -> Self {
        Self(value.0)
    }
}

impl<const L: usize> From<Unsigned<L>> for Signed<L> {
    fn from(value: Unsigned<L>) -> Self {
        Self(value.0)
    }
}

impl<const L: usize> Signed<L> {
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        Self(from_bytes(bytes.as_ref()))
    }

    pub fn try_from_str(s: &str) -> Result<Self, TryFromStrError> {
        try_from_str(s).map(Self)
    }

    pub fn try_from_digits_bin(digits: impl AsRef<[u8]>, exp: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits_bin(digits.as_ref(), exp).map(Self)
    }

    pub fn try_from_digits(digits: impl AsRef<[u8]>, radix: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits(digits.as_ref(), radix).map(Self)
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn try_into_digits_bin(&self, exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits_bin(&self.0, exp)
    }

    pub fn try_into_digits(self, radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits(self.0, radix)
    }

    pub fn sign(&self) -> Sign {
        if self.0 == [0; L] {
            return Sign::ZERO;
        }

        if self.0[L - 1] >> (BITS - 1) == 0 {
            Sign::POS
        } else {
            Sign::NEG
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
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        Self(from_bytes(bytes.as_ref()))
    }

    pub fn try_from_str(s: &str) -> Result<Self, TryFromStrError> {
        try_from_str(s).map(Self)
    }

    pub fn try_from_digits_bin(digits: impl AsRef<[u8]>, exp: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits_bin(digits.as_ref(), exp).map(Self)
    }

    pub fn try_from_digits(digits: impl AsRef<[u8]>, radix: u8) -> Result<Self, TryFromDigitsError> {
        try_from_digits(digits.as_ref(), radix).map(Self)
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn try_into_digits_bin(&self, exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits_bin(&self.0, exp)
    }

    pub fn try_into_digits(self, radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits(self.0, radix)
    }
}

fn from_bytes<const L: usize>(bytes: &[u8]) -> [Single; L] {
    let len = bytes.len().min(BYTES * L);

    let mut res = [0; L];

    res.as_mut_bytes()[..len].copy_from_slice(&bytes[..len]);

    res.iter_mut().for_each(|ptr| *ptr = (*ptr as Single).to_le());

    res
}

fn from_bytes_arr<const L: usize, const N: usize>(bytes: &[u8; N], default: Single) -> [Single; L] {
    let len = bytes.len().min(BYTES * L);

    let mut res = [default; L];

    res.as_mut_bytes()[..len].copy_from_slice(&bytes[..len]);

    res.iter_mut().for_each(|ptr| *ptr = (*ptr as Single).to_le());

    res
}

fn try_from_str_validate(s: &str, radix: u8) -> Result<(), TryFromStrError> {
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
        return Err(TryFromStrError::InvalidSymbol { ch, radix });
    }

    Ok(())
}

fn try_from_digits_validate(digits: &[u8], radix: u8) -> Result<(), TryFromDigitsError> {
    if radix < 2 {
        return Err(TryFromDigitsError::InvalidRadix { radix });
    }

    if let Some(&digit) = digits.iter().find(|&&digit| digit >= radix) {
        return Err(TryFromDigitsError::InvalidDigits { digit, radix });
    }

    Ok(())
}

fn try_into_digits_validate(radix: u8) -> Result<(), TryIntoDigitsError> {
    if radix < 2 {
        return Err(TryIntoDigitsError::InvalidRadix { radix });
    }

    Ok(())
}

// [!NOTE]: Try to implement with iterators after tests and benches
fn try_from_str<const L: usize>(s: &str) -> Result<[Single; L], TryFromStrError> {
    let (s, sign) = get_sign_from_str(s)?;
    let (s, radix) = get_radix_from_str(s)?;

    if radix & (radix - 1) == 0 {
        return try_from_str_bin(s, radix.ilog2() as u8, sign);
    }

    try_from_str_validate(s, radix)?;

    let mut idx = 0;
    let mut res = [0; L];

    for digit in s.bytes().filter_map(get_digit_from_byte) {
        let mut acc = digit as Double;

        for ptr in res.iter_mut().take(idx + 1) {
            acc += *ptr as Double * radix as Double;

            *ptr = acc as Single;

            acc >>= BITS;
        }

        if idx < L && res[idx] > 0 {
            idx += 1;
        }
    }

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

// [!NOTE]: Try to implement with iterators after tests and benches
fn try_from_digits<const L: usize>(digits: &[u8], radix: u8) -> Result<[Single; L], TryFromDigitsError> {
    if radix & (radix - 1) == 0 {
        return try_from_digits_bin(digits, radix.ilog2() as u8);
    }

    try_from_digits_validate(digits, radix)?;

    let mut idx = 0;
    let mut res = [0; L];

    for &digit in digits.iter().rev() {
        let mut acc = digit as Double;

        for ptr in res.iter_mut().take(idx + 1) {
            acc += *ptr as Double * radix as Double;

            *ptr = acc as Single;

            acc >>= BITS;
        }

        if idx < L && res[idx] > 0 {
            idx += 1;
        }
    }

    Ok(res)
}

// [!NOTE]: Try to implement with iterators after tests and benches
fn try_into_digits<const L: usize>(mut digits: [Single; L], radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
    if radix & (radix - 1) == 0 {
        return try_into_digits_bin(&digits, radix.ilog2() as u8);
    }

    try_into_digits_validate(radix)?;

    let bits = 1 + radix.ilog2() as usize;
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut idx = 0;
    let mut res = vec![0; len + 1];

    loop {
        let mut any = 0;
        let mut acc = 0;

        for digit in digits.as_mut_bytes().iter_mut().rev() {
            any |= *digit;
            acc = (acc << u8::BITS) | *digit as u16;

            *digit = (acc / radix as u16) as u8;

            acc %= radix as u16;
        }

        if any == 0 {
            break;
        }

        res[idx] = acc as u8;
        idx += 1;
    }

    Ok(res)
}

// [!NOTE]: Try to implement with iterators after tests and benches
fn try_from_str_bin<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], TryFromStrError> {
    try_from_str_validate(s, 1 << exp)?;

    let bits = exp as usize;
    let mask = (1 << BITS) - 1;
    let len = (s.len() * bits + BITS - 1) / BITS;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = [0; L];

    for digit in s.bytes().rev().filter_map(get_digit_from_byte) {
        acc |= (digit as Double) << shl;
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

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

// [!NOTE]: Try to implement with iterators after tests and benches
fn try_from_digits_bin<const L: usize>(digits: &[u8], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
    if exp >= u8::BITS as u8 {
        return Err(TryFromDigitsError::InvalidExponent { exp });
    }

    try_from_digits_validate(digits, 1 << exp)?;

    let bits = exp as usize;
    let mask = (1 << BITS) - 1;
    let len = (digits.len() * bits + BITS - 1) / BITS;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = [0; L];

    for &digit in digits {
        acc |= (digit as Double) << shl;
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

    Ok(res)
}

// [!NOTE]: Try to implement with iterators after tests and benches
fn try_into_digits_bin<const L: usize>(digits: &[Single; L], exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
    if exp >= u8::BITS as u8 {
        return Err(TryIntoDigitsError::InvalidExponent { exp });
    }

    try_into_digits_validate(1 << exp)?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let len = (digits.len() * BITS + bits - 1) / bits;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![0; len];

    for &digit in digits {
        acc |= (digit as Double) << shl;
        shl += BITS;
        res[idx] = (acc & mask) as u8;

        while shl >= bits {
            acc >>= bits;
            shl -= bits;
            idx += 1;
            res[idx] = (acc & mask) as u8;
        }
    }

    Ok(res)
}

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

fn get_radix_from_str(s: &str) -> Result<(&str, u8), TryFromStrError> {
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

fn get_digit_from_byte(byte: u8) -> Option<Single> {
    match byte {
        b'0'..=b'9' => Some((byte - b'0') as Single),
        b'a'..=b'f' => Some((byte - b'a' + 10) as Single),
        b'A'..=b'F' => Some((byte - b'A' + 10) as Single),
        _ => None,
    }
}

mod uops {
    use super::*;

    pub(super) fn pos<const L: usize>(digits: [Single; L]) -> [Single; L] {
        digits
    }

    pub(super) fn neg<const L: usize>(digits: [Single; L]) -> [Single; L] {
        inc(not(digits))
    }

    pub(super) fn not<const L: usize>(digits: [Single; L]) -> [Single; L] {
        digits.iter().map(|&x| !x).collect_with([0; L])
    }

    pub(super) fn inc<const L: usize>(mut digits: [Single; L]) -> [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = *ptr as Double + acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }

    pub(super) fn dec<const L: usize>(mut digits: [Single; L]) -> [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = RADIX + *ptr as Double - acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }

    pub(super) fn pos_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        digits
    }

    pub(super) fn neg_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(digits);
        inc_mut(digits);

        digits
    }

    pub(super) fn not_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        digits.iter_mut().for_each(|x| *x = !*x);
        digits
    }

    pub(super) fn inc_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = *ptr as Double + acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }

    pub(super) fn dec_mut<const L: usize>(digits: &mut [Single; L]) -> &mut [Single; L] {
        let mut acc = 1;

        for ptr in digits.iter_mut() {
            let digit = RADIX + *ptr as Double - acc as Double;

            *ptr = digit as Single;

            acc = (digit >> BITS) as Single;

            if acc == 0 {
                break;
            }
        }

        digits
    }
}

pub mod asm {
    use super::*;

    const L: usize = 4096 / BITS;
    const N: usize = 256 / BITS;

    #[inline(never)]
    pub fn from_bytes_(bytes: &[u8]) -> [Single; L] {
        from_bytes(bytes)
    }

    #[inline(never)]
    pub fn from_bytes_arr_(bytes: &[u8; N]) -> [Single; L] {
        from_bytes_arr(bytes, 0)
    }

    #[inline(never)]
    pub fn try_from_str_(s: &str) -> Result<[Single; L], TryFromStrError> {
        try_from_str(s)
    }

    #[inline(never)]
    pub fn try_from_digits_(digits: &[u8], radix: u8) -> Result<[Single; L], TryFromDigitsError> {
        try_from_digits(digits, radix)
    }

    #[inline(never)]
    pub fn try_into_digits_(digits: [Single; L], radix: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits(digits, radix)
    }

    #[inline(never)]
    pub fn try_from_str_bin_(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], TryFromStrError> {
        try_from_str_bin(s, exp, sign)
    }

    #[inline(never)]
    pub fn try_from_digits_bin_(digits: &[u8], exp: u8) -> Result<[Single; L], TryFromDigitsError> {
        try_from_digits_bin(digits, exp)
    }

    #[inline(never)]
    pub fn try_into_digits_bin_(digits: &[Single; L], exp: u8) -> Result<Vec<u8>, TryIntoDigitsError> {
        try_into_digits_bin(digits, exp)
    }

    #[inline(never)]
    pub fn neg_(digits: [Single; L]) -> [Single; L] {
        neg(digits)
    }

    #[inline(never)]
    pub fn not_(digits: [Single; L]) -> [Single; L] {
        not(digits)
    }

    #[inline(never)]
    pub fn inc_(digits: [Single; L]) -> [Single; L] {
        inc(digits)
    }

    #[inline(never)]
    pub fn dec_(digits: [Single; L]) -> [Single; L] {
        dec(digits)
    }

    #[inline(never)]
    pub fn neg_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        neg_mut(digits)
    }

    #[inline(never)]
    pub fn not_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(digits)
    }

    #[inline(never)]
    pub fn inc_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        inc_mut(digits)
    }

    #[inline(never)]
    pub fn dec_mut_(digits: &mut [Single; L]) -> &mut [Single; L] {
        dec_mut(digits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type S64 = signed!(64);
    type U64 = unsigned!(64);

    const PRIMES: [usize; 2] = [281_415_416_265_077, 281_397_419_487_323];

    fn add(digits: &mut [u8], radix: u8, val: u8) -> bool {
        let mut acc = val as u16;

        for digit in digits {
            acc += *digit as u16;

            *digit = (acc % radix as u16) as u8;

            acc /= radix as u16;
        }

        acc > 0
    }

    fn value(digits: &[u8], radix: u8) -> u64 {
        digits.iter().rev().fold(0, |acc, &x| acc * radix as u64 + x as u64)
    }

    #[test]
    fn from_primitives() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i128;
            let nval = -pval;

            assert_eq!(S64::from(pval), S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(S64::from(nval), S64 { 0: neg(transmute!(bytes)) });
            assert_eq!(U64::from(val), U64 { 0: pos(transmute!(bytes)) });
        }
    }

    #[test]
    fn from_bytes() {
        assert_eq!(S64::from_bytes([]), S64::default());
        assert_eq!(U64::from_bytes([]), U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES[0]) {
            let bytes = val.to_le_bytes();

            assert_eq!(S64::from_bytes(bytes), S64 { 0: pos(transmute!(bytes)) });
            assert_eq!(U64::from_bytes(bytes), U64 { 0: pos(transmute!(bytes)) });
        }
    }

    #[test]
    fn try_from_str() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES[0]) {
            let bytes = val.to_le_bytes();

            let pos_dec = format!("{val:#064}");
            let pos_bin = format!("{val:#064b}");
            let pos_oct = format!("{val:#064o}");
            let pos_hex = format!("{val:#064x}");

            let neg_dec = format!("-{val:#064}");
            let neg_bin = format!("-{val:#064b}");
            let neg_oct = format!("-{val:#064o}");
            let neg_hex = format!("-{val:#064x}");

            assert_eq!(S64::try_from_str(&pos_dec), Ok(S64 { 0: pos(transmute!(bytes)) }));
            assert_eq!(S64::try_from_str(&pos_bin), Ok(S64 { 0: pos(transmute!(bytes)) }));
            assert_eq!(S64::try_from_str(&pos_oct), Ok(S64 { 0: pos(transmute!(bytes)) }));
            assert_eq!(S64::try_from_str(&pos_hex), Ok(S64 { 0: pos(transmute!(bytes)) }));

            assert_eq!(S64::try_from_str(&neg_dec), Ok(S64 { 0: neg(transmute!(bytes)) }));
            assert_eq!(S64::try_from_str(&neg_bin), Ok(S64 { 0: neg(transmute!(bytes)) }));
            assert_eq!(S64::try_from_str(&neg_oct), Ok(S64 { 0: neg(transmute!(bytes)) }));
            assert_eq!(S64::try_from_str(&neg_hex), Ok(S64 { 0: neg(transmute!(bytes)) }));

            assert_eq!(U64::try_from_str(&pos_dec), Ok(U64 { 0: pos(transmute!(bytes)) }));
            assert_eq!(U64::try_from_str(&pos_bin), Ok(U64 { 0: pos(transmute!(bytes)) }));
            assert_eq!(U64::try_from_str(&pos_oct), Ok(U64 { 0: pos(transmute!(bytes)) }));
            assert_eq!(U64::try_from_str(&pos_hex), Ok(U64 { 0: pos(transmute!(bytes)) }));
        }
    }

    #[test]
    fn try_from_digits() {
        assert_eq!(S64::try_from_digits([], 31), Ok(S64::default()));
        assert_eq!(U64::try_from_digits([], 31), Ok(U64::default()));

        for radix in 2..=u8::MAX {
            let step = radix.saturating_sub(3).max(1);

            let mut digits = [0; 8];

            for _ in 0..u16::MAX {
                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                assert_eq!(S64::try_from_digits(digits, radix), Ok(S64 { 0: pos(transmute!(bytes)) }));
                assert_eq!(U64::try_from_digits(digits, radix), Ok(U64 { 0: pos(transmute!(bytes)) }));

                if !add(&mut digits, radix, radix) {
                    break;
                }
            }
        }
    }

    #[test]
    fn try_into_digits() {}
}

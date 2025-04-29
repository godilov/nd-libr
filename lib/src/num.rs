#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Display, Formatter, LowerHex, Octal, UpperHex, Write},
    iter::repeat_n,
    str::FromStr,
};

use digit::{Double, Single};
use ndproc::ops_impl;
use prime::{PrimeRel, PRIMES};
use radix::{Bin, Dec, Hex, Oct, Radix, RADIX};
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

macro_rules! num_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(num_impl!($trait, $type,);)+
    };
    ($trait:ty, $type:ty $(,)?) => {
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
        impl PrimeRel for $type {
            fn primes() -> impl Iterator<Item = Self> {
                PRIMES.iter().map(|&p| p as $type).take($count).take_while(|&p| p < Self::MAX.isqrt())
            }

            fn capacity(&self) -> usize {
                let val = *self as f64;

                (1.3 * val / val.log(std::f64::consts::E)).ceil() as usize + 1
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

macro_rules! long_from_bool {
    ([$($type:ident),+] $(,)?) => {
        $(long_from_bool!($type);)+
    };
    ($type:ident) => {
        impl From<bool> for $type {
            fn from(value: bool) -> Self {
                Self::from(value as u8)
            }
        }
    };
}

macro_rules! fixed_from_bool {
    ([$($type:ident),+] $(,)?) => {
        $(fixed_from_bool!($type);)+
    };
    ($type:ident) => {
        impl<const L: usize> From<bool> for $type<L> {
            fn from(value: bool) -> Self {
                Self::from(value as u8)
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

                Self { digits: res $(, sign: $pos * Sign::from(value))? }
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

                Self { raw: res, len $(, sign: if len > 0 { $pos * Sign::from(value) } else { Sign::ZERO })? }
            }
        }
    };
}

macro_rules! ops_impl_mut_fn {
    ($id:ident, $a:expr, $b:expr) => {{
        let repr = $id($a.into(), (&$b).into());

        $a.apply_mut_repr(repr);
    }};
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

#[cfg(all(target_pointer_width = "64", not(test), not(feature = "bytes")))]
pub mod digit {
    pub type Single = u64;
    pub type Double = u128;

    pub(super) const OCT_VAL: Double = (1 as Double) << 63;
    pub(super) const OCT_WIDTH: u8 = 21;

    pub(super) const DEC_VAL: Double = 10_000_000_000_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 19;
}

#[cfg(all(target_pointer_width = "32", not(test), not(feature = "bytes")))]
pub mod digit {
    pub type Single = u32;
    pub type Double = u64;

    pub(super) const OCT_VAL: Double = (1 as Double) << 30;
    pub(super) const OCT_WIDTH: u8 = 10;

    pub(super) const DEC_VAL: Double = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;
}

#[cfg(any(test, feature = "bytes"))]
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
        digit::{DEC_VAL, DEC_WIDTH, OCT_VAL, OCT_WIDTH},
        Double, Single,
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
    use std::mem::replace;

    use super::{Num, Unsigned};
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
        pub fn by_count<Prime: Unsigned>(len: usize) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFullIter {
                primes: Vec::with_capacity(len),
                next: Prime::from(2),
            }
            .take(len)
        }

        pub fn by_limit<Prime: Unsigned>(val: Prime) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFullIter {
                primes: Vec::with_capacity(val.capacity()),
                next: Prime::from(2),
            }
            .take_while(move |x| x < &val)
        }

        pub fn by_count_fast<Prime: Unsigned>(len: usize) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFastIter {
                next: Prime::from(2),
                capacity: len,
            }
            .take(len)
        }

        pub fn by_limit_fast<Prime: Unsigned>(val: Prime) -> impl Iterator<Item = Prime>
        where
            for<'s> &'s Prime: Ops,
        {
            PrimesFastIter {
                next: Prime::from(2),
                capacity: val.capacity(),
            }
            .take_while(move |p| p < &val)
        }
    }

    pub trait PrimeRel: Num
    where
        for<'s> &'s Self: Ops,
    {
        fn primes() -> impl Iterator<Item = Self>;

        fn capacity(&self) -> usize;

        fn is_prime(&self) -> bool {
            let sqrt = self.sqrt();

            Self::primes().take_while(|p| p <= &sqrt).all(|p| {
                let one = Self::one();

                let x = Self::from(self - &one);

                let shr = Self::from(&x - &one);
                let shr = Self::from(&x ^ &shr);
                let shr = shr.order();

                let mut idx = 0;
                let mut pow = Self::from(&x >> shr);
                let mut exp = p.clone().pow_mod(pow.clone(), self);

                while pow < x && one < exp && exp < x {
                    let val = Self::from(&exp * &exp);
                    let val = Self::from(&val % self);

                    idx += 1;
                    pow <<= 1;
                    exp = val;
                }

                idx == 0 && exp == one || exp == x
            })
        }
    }

    struct PrimesFullIter<Prime: Unsigned>
    where
        for<'s> &'s Prime: Ops,
    {
        primes: Vec<Prime>,
        next: Prime,
    }

    struct PrimesFastIter<Prime: Unsigned>
    where
        for<'s> &'s Prime: Ops,
    {
        next: Prime,
        capacity: usize,
    }

    impl<Prime: Unsigned> Iterator for PrimesFullIter<Prime>
    where
        for<'s> &'s Prime: Ops,
    {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            self.primes.push(self.next.clone());

            let zero = Prime::from(0);
            let one = Prime::from(1);
            let two = Prime::from(2);

            let offset = Prime::from(&self.next & &one);
            let offset = Prime::from(&offset + &one);

            let mut val = Prime::from(&self.next + &offset);

            while self.primes.iter().any(|p| Prime::from(&val % p) == zero) {
                val += &two;
            }

            self.next = val;
            self.primes.last().cloned()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.primes.capacity(), Some(self.primes.capacity()))
        }
    }

    impl<Prime: Unsigned> Iterator for PrimesFastIter<Prime>
    where
        for<'s> &'s Prime: Ops,
    {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            let one = Prime::from(1);
            let two = Prime::from(2);

            let offset = Prime::from(&self.next & &one);
            let offset = Prime::from(&offset + &one);

            let mut val = Prime::from(&self.next + &offset);

            while !val.is_prime() {
                val += &two;
            }

            Some(replace(&mut self.next, val))
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.capacity, (self.capacity > 0).then_some(self.capacity))
        }
    }

    impl<Prime: Unsigned> ExactSizeIterator for PrimesFullIter<Prime> where for<'s> &'s Prime: Ops {}
    impl<Prime: Unsigned> ExactSizeIterator for PrimesFastIter<Prime> where for<'s> &'s Prime: Ops {}
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

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Operand<'load> {
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

pub trait Num: Sized + Default + Display + Clone + Eq + Ord + From<bool>
where
    for<'s> Self: Ops + OpsAssign + OpsAssign<&'s Self> + OpsFrom + OpsFrom<&'s Self, &'s Self>,
    for<'s> &'s Self: Ops,
{
    fn bits(&self) -> usize;

    fn order(&self) -> usize;

    fn sqrt(&self) -> Self;

    fn log(&self) -> Self;

    fn zero() -> Self {
        false.into()
    }

    fn one() -> Self {
        true.into()
    }

    fn gcd(self, val: Self) -> Self {
        let zero = Self::zero();

        let mut a = self;
        let mut b = val;

        while b > zero {
            let x = b.clone();

            b = Self::from(a % b);
            a = x;
        }

        a
    }

    fn lcm(self, val: Self) -> Self {
        let g = Self::gcd(self.clone(), val.clone());

        Self::from(Self::from(self / g) * val)
    }

    fn pow_mod(self, mut pow: Self, modulus: &Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one.clone();

        while pow > zero {
            if Self::from(&pow & &one) == one {
                let val = Self::from(&res * &acc);
                let val = Self::from(&val % modulus);

                res = val;
            }

            let val = Self::from(&acc * &acc);
            let val = Self::from(&val % modulus);

            acc = val;
            pow >>= 1;
        }

        res
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

pub trait Unsigned: Num + From<u8> + PrimeRel
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

impl<'load> From<&'load SignedLong> for Operand<'load> {
    fn from(value: &'load SignedLong) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load> From<&'load UnsignedLong> for Operand<'load> {
    fn from(value: &'load UnsignedLong) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load> From<&&'load SignedLong> for Operand<'load> {
    fn from(value: &&'load SignedLong) -> Self {
        Self::from(*value)
    }
}

impl<'load> From<&&'load UnsignedLong> for Operand<'load> {
    fn from(value: &&'load UnsignedLong) -> Self {
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

impl From<Operand<'_>> for LongRepr {
    fn from(value: Operand<'_>) -> Self {
        Self {
            digits: value.digits().to_vec(),
            sign: value.sign(),
        }
    }
}

impl<'load> From<&'load LongRepr> for Operand<'load> {
    fn from(value: &'load LongRepr) -> Self {
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

impl<'load, const L: usize> From<&'load SignedFixed<L>> for Operand<'load> {
    fn from(value: &'load SignedFixed<L>) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load, const L: usize> From<&'load UnsignedFixed<L>> for Operand<'load> {
    fn from(value: &'load UnsignedFixed<L>) -> Self {
        Self {
            digits: value.digits(),
            sign: value.sign(),
        }
    }
}

impl<'load, const L: usize> From<&&'load SignedFixed<L>> for Operand<'load> {
    fn from(value: &&'load SignedFixed<L>) -> Self {
        Self::from(*value)
    }
}

impl<'load, const L: usize> From<&&'load UnsignedFixed<L>> for Operand<'load> {
    fn from(value: &&'load UnsignedFixed<L>) -> Self {
        Self::from(*value)
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

impl<const L: usize> From<Operand<'_>> for FixedRepr<L> {
    fn from(value: Operand<'_>) -> Self {
        Self {
            raw: value.digits().iter().copied().collect_with([0; L]),
            len: value.len().min(L),
            sign: value.sign(),
            overflow_val: 0,
            overflow: false,
        }
    }
}

impl<'load, const L: usize> From<&'load FixedRepr<L>> for Operand<'load> {
    fn from(value: &'load FixedRepr<L>) -> Self {
        Self {
            digits: value.digits(),
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

long_from_bool!([SignedLong, UnsignedLong]);
fixed_from_bool!([SignedFixed, UnsignedFixed]);

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
    #[inline(always)]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_long(bytes).into()
    }

    #[inline(always)]
    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long(digits, radix, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long_bin(digits, pow, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    #[inline(always)]
    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    #[inline(always)]
    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        self.clone().into_radix(radix)
    }

    #[inline(always)]
    pub fn into_unsigned(self) -> UnsignedLong {
        UnsignedLong { digits: self.digits }
    }

    #[inline(always)]
    pub fn to_fixed<const L: usize>(&self) -> SignedFixed<L> {
        fixed_from_long(self.digits()).with_sign(self.sign()).into()
    }

    #[inline(always)]
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

    pub fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    #[inline(always)]
    pub fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }

    #[inline(always)]
    fn raw_mut(&mut self) -> &mut Vec<Single> {
        &mut self.digits
    }

    #[inline(always)]
    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.digits
    }

    #[inline(always)]
    fn apply_mut_repr(&mut self, repr: MutRepr) {
        self.digits.truncate(repr.len);
        self.sign = repr.sign;
    }
}

impl UnsignedLong {
    #[inline(always)]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_long(bytes).into()
    }

    #[inline(always)]
    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long(digits, radix, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_long_bin(digits, pow, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    #[inline(always)]
    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    #[inline(always)]
    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        self.clone().into_radix(radix)
    }

    #[inline(always)]
    pub fn into_signed(self, sign: Sign) -> SignedLong {
        let len = self.len();
        let sign = get_sign(len, sign);

        SignedLong { digits: self.digits, sign }
    }

    #[inline(always)]
    pub fn to_fixed<const L: usize>(&self) -> UnsignedFixed<L> {
        fixed_from_long(self.digits()).into()
    }

    #[inline(always)]
    pub fn digits(&self) -> &[Single] {
        &self.digits
    }

    #[allow(clippy::len_without_is_empty)]
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    #[inline(always)]
    pub fn sign(&self) -> Sign {
        Sign::from(self.len())
    }

    #[inline(always)]
    fn raw_mut(&mut self) -> &mut Vec<Single> {
        &mut self.digits
    }

    #[inline(always)]
    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.digits
    }

    #[inline(always)]
    fn apply_mut_repr(&mut self, repr: MutRepr) {
        match repr.sign {
            Sign::ZERO => *self = Default::default(),
            Sign::NEG => *self = Default::default(),
            Sign::POS => self.digits.truncate(repr.len),
        }
    }
}

impl<const L: usize> SignedFixed<L> {
    #[inline(always)]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_fixed(bytes).into()
    }

    #[inline(always)]
    pub fn try_from_bytes(bytes: &[u8]) -> (Self, bool) {
        let repr = from_bytes_fixed(bytes);
        let over = repr.overflow;

        (repr.into(), over)
    }

    #[inline(always)]
    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed(digits, radix, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed_bin(digits, pow, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    #[inline(always)]
    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    #[inline(always)]
    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        (*self).into_radix(radix)
    }

    #[inline(always)]
    pub fn into_unsigned(self) -> UnsignedFixed<L> {
        UnsignedFixed::<L> { raw: self.raw, len: self.len }
    }

    #[inline(always)]
    pub fn to_long(&self) -> SignedLong {
        long_from_fixed::<L>(self.digits()).with_sign(self.sign()).into()
    }

    #[inline(always)]
    pub fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    #[allow(clippy::len_without_is_empty)]
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn sign(&self) -> Sign {
        self.sign
    }

    #[inline(always)]
    pub fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    #[inline(always)]
    pub fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }

    #[inline(always)]
    fn raw_mut(&mut self) -> &mut [Single; L] {
        &mut self.raw
    }

    #[inline(always)]
    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.raw[..self.len]
    }

    #[inline(always)]
    fn apply_mut_repr(&mut self, repr: MutRepr) {
        self.digits_mut().iter_mut().for_each(|val| *val = 0);
        self.len = repr.len;
        self.sign = repr.sign;
    }
}

impl<const L: usize> UnsignedFixed<L> {
    #[inline(always)]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        from_bytes_fixed(bytes).into()
    }

    #[inline(always)]
    pub fn try_from_bytes(bytes: &[u8]) -> (Self, bool) {
        let repr = from_bytes_fixed(bytes);
        let over = repr.overflow;

        (repr.into(), over)
    }

    #[inline(always)]
    pub fn try_from_digits(digits: &[u8], radix: u16) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed(digits, radix, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn try_from_digits_bin(digits: &[u8], pow: u8) -> Result<Self, TryFromDigitsError> {
        Ok(try_from_digits_fixed_bin(digits, pow, Sign::POS)?.into())
    }

    #[inline(always)]
    pub fn into_radix(mut self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        into_radix(self.digits_mut(), radix)
    }

    #[inline(always)]
    pub fn to_radix_bin(&self, pow: u8) -> Result<Vec<Single>, IntoRadixError> {
        into_radix_bin(self.digits(), pow)
    }

    #[inline(always)]
    pub fn to_radix(&self, radix: Double) -> Result<Vec<Single>, IntoRadixError> {
        if radix > 0 && radix & (radix - 1) == 0 {
            return self.to_radix_bin(radix.ilog2() as u8);
        }

        (*self).into_radix(radix)
    }

    #[inline(always)]
    pub fn into_signed(self, sign: Sign) -> SignedFixed<L> {
        let len = self.len();
        let sign = get_sign(len, sign);

        SignedFixed::<L> { raw: self.raw, len, sign }
    }

    #[inline(always)]
    pub fn to_long(&self) -> SignedLong {
        long_from_fixed::<L>(self.digits()).into()
    }

    #[inline(always)]
    pub fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    #[allow(clippy::len_without_is_empty)]
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn sign(&self) -> Sign {
        Sign::from(self.len())
    }

    #[inline(always)]
    fn raw_mut(&mut self) -> &mut [Single; L] {
        &mut self.raw
    }

    #[inline(always)]
    fn digits_mut(&mut self) -> &mut [Single] {
        &mut self.raw[..self.len]
    }

    #[inline(always)]
    fn apply_mut_repr(&mut self, repr: MutRepr) {
        match repr.sign {
            Sign::ZERO => *self = Default::default(),
            Sign::NEG => *self = Default::default(),
            Sign::POS => {
                self.digits_mut().iter_mut().for_each(|val| *val = 0);
                self.len = repr.len;
            },
        }
    }
}

impl LongRepr {
    const ZERO: Self = LongRepr {
        digits: vec![],
        sign: Sign::ZERO,
    };

    #[inline(always)]
    fn from_single(digit: Single) -> Self {
        match digit {
            0 => LongRepr::ZERO,
            x => Self {
                digits: vec![x],
                sign: Sign::POS,
            },
        }
    }

    #[inline(always)]
    fn from_raw(mut digits: Vec<Single>, sign: Sign) -> Self {
        let len = get_len(&digits);
        let sign = get_sign(len, sign);

        digits.truncate(len);

        Self { digits, sign }
    }

    #[inline(always)]
    fn digits(&self) -> &[Single] {
        &self.digits
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.digits.len()
    }

    #[inline(always)]
    fn sign(&self) -> Sign {
        self.sign
    }

    #[inline(always)]
    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
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

    #[inline(always)]
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

    #[inline(always)]
    fn digits(&self) -> &[Single] {
        &self.raw[..self.len]
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    fn sign(&self) -> Sign {
        self.sign
    }

    #[inline(always)]
    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    #[inline(always)]
    fn with_overflow_val(mut self, val: Single) -> Self {
        self.overflow_val = val;
        self
    }

    #[inline(always)]
    fn with_overflow(mut self, over: bool) -> Self {
        self.overflow = over;
        self
    }
}

impl<'digits> Operand<'digits> {
    const ONE: Self = Operand { digits: &[1], sign: Sign::POS };

    #[inline(always)]
    fn from_raw(digits: &'digits [Single]) -> Self {
        let len = get_len(digits);
        let sign = get_sign(len, Sign::POS);

        Self { digits: &digits[..len], sign }
    }

    #[inline(always)]
    fn iter<T: From<Single>>(&self) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator {
        self.digits().iter().map(|&x| T::from(x))
    }

    #[inline(always)]
    fn digits(&self) -> &[Single] {
        self.digits
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.digits.len()
    }

    #[inline(always)]
    fn sign(&self) -> Sign {
        self.sign
    }

    #[inline(always)]
    fn with_sign(mut self, sign: Sign) -> Self {
        self.sign = if self.sign != Sign::ZERO { sign } else { Sign::ZERO };
        self
    }

    #[inline(always)]
    fn with_neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl LongMutOperand<'_> {
    #[inline(always)]
    fn copy_from(&mut self, val: Operand<'_>) -> MutRepr {
        self.resize(val.len());

        self.iter_mut().zip(val.iter()).for_each(|(val, op)| *val = op);

        MutRepr::from_raw(val.digits(), val.sign())
    }

    #[inline(always)]
    fn iter_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Single> + ExactSizeIterator {
        self.raw_mut().iter_mut()
    }

    #[inline(always)]
    fn raw_mut(&mut self) -> &mut [Single] {
        self.digits
    }

    #[inline(always)]
    fn raw(&self) -> &[Single] {
        self.digits
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.digits.len()
    }

    #[inline(always)]
    fn sign(&self) -> Sign {
        self.sign
    }

    #[inline(always)]
    fn resize(&mut self, len: usize) {
        self.digits.resize(len, 0);
    }
}

impl<const L: usize> FixedMutOperand<'_, L> {
    #[inline(always)]
    fn copy_from(&mut self, val: Operand<'_>) -> MutRepr {
        self.iter_mut().zip(val.iter()).for_each(|(val, op)| *val = op);

        MutRepr::from_raw(val.digits(), val.sign())
    }

    #[inline(always)]
    fn iter_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Single> + ExactSizeIterator {
        self.raw_mut().iter_mut()
    }

    #[inline(always)]
    fn raw_mut(&mut self) -> &mut [Single; L] {
        self.raw
    }

    #[inline(always)]
    fn raw(&self) -> &[Single; L] {
        self.raw
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    fn sign(&self) -> Sign {
        self.sign
    }
}

impl MutRepr {
    const ZERO: Self = MutRepr { len: 0, sign: Sign::ZERO };

    #[inline(always)]
    fn from_raw(slice: &[Single], sign: Sign) -> Self {
        let len = get_len(slice);
        let sign = get_sign(len, sign);

        Self { len, sign }
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

    for (i, &byte) in bytes.iter().take(RATIO * L).enumerate() {
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

#[inline(always)]
fn fixed_from_long<const L: usize>(digits: &[Single]) -> FixedRepr<L> {
    FixedRepr::from_raw(digits.iter().copied().collect_with([0; L]), Sign::POS).with_overflow(digits.len() > L)
}

#[inline(always)]
fn long_from_fixed<const L: usize>(digits: &[Single]) -> LongRepr {
    LongRepr::from_raw(digits.iter().copied().collect_with(vec![0; digits.len()]), Sign::POS)
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

fn zip_nums<T: From<Single>>(a: &[Single], b: &[Single], zeros: usize) -> impl Iterator<Item = (T, T)> {
    let len = a.len().max(b.len());

    let iter_a = a.iter().chain(repeat_n(&0, len - a.len() + zeros)).map(|&x| T::from(x));
    let iter_b = b.iter().chain(repeat_n(&0, len - b.len() + zeros)).map(|&x| T::from(x));

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

#[allow(dead_code)]
fn add_single_long(a: Operand<'_>, b: Single) -> LongRepr {
    match (a.sign(), Sign::from(b)) {
        (Sign::ZERO, Sign::ZERO) => return LongRepr::ZERO,
        (Sign::ZERO, _) => return LongRepr::from_single(b),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    todo!()

    // LongRepr::from_raw(res, a.sign())
}

#[allow(dead_code)]
fn add_single_fixed<const L: usize>(a: Operand<'_>, b: Single) -> FixedRepr<L> {
    match (a.sign(), Sign::from(b)) {
        (Sign::ZERO, Sign::ZERO) => return FixedRepr::ZERO,
        (Sign::ZERO, _) => return FixedRepr::from_single(b),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    todo!()

    // FixedRepr::from_raw(res, a.sign())
    //     .with_overflow_val(acc as Single)
    //     .with_overflow(acc > 0)
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

    let mut acc = 0;

    let res = zip_nums::<Double>(a.digits(), b.digits(), 1)
        .scan(0, |_, (aop, bop)| {
            let digit = acc + aop + bop;

            acc = digit >> Single::BITS;

            Some(digit as Single)
        })
        .collect_with(vec![0; a.len().max(b.len()) + 1]);

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

    let res = zip_nums::<Double>(a.digits(), b.digits(), 1)
        .scan(0, |_, (aop, bop)| {
            let digit = acc + aop + bop;

            acc = digit >> Single::BITS;

            Some(digit as Single)
        })
        .collect_with([0; L]);

    FixedRepr::from_raw(res, a.sign())
        .with_overflow_val(acc as Single)
        .with_overflow(acc > 0)
}

fn add_long_mut(mut a: LongMutOperand<'_>, b: Operand<'_>) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.copy_from(b),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_long_mut(a, -b);
    }

    let len = a.len().max(b.len()) + 1;

    a.resize(len);

    let mut acc = 0;

    let res = a.raw_mut();

    for (i, bop) in b.iter::<Double>().enumerate() {
        let aop = res[i] as Double;

        acc += aop + bop;

        res[i] = acc as Single;

        acc >>= Single::BITS;
    }

    res[b.len()] += acc as Single;

    MutRepr::from_raw(a.raw(), a.sign())
}

fn add_fixed_mut<const L: usize>(mut a: FixedMutOperand<'_, L>, b: Operand<'_>) -> MutRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, Sign::ZERO) => return MutRepr::ZERO,
        (Sign::ZERO, _) => return a.copy_from(b),
        (_, Sign::ZERO) => return a.into(),
        _ => (),
    }

    if a.sign() != b.sign() {
        return sub_fixed_mut(a, -b);
    }

    let len = (a.len().max(b.len()) + 1).min(L);

    let mut acc = 0;

    let res = a.raw_mut();

    for (i, bop) in b.iter::<Double>().take(len).enumerate() {
        let aop = res[i] as Double;

        acc += aop + bop;

        res[i] = acc as Single;

        acc >>= Single::BITS;
    }

    if b.len() < L {
        res[b.len()] += acc as Single;
    }

    MutRepr::from_raw(a.raw(), a.sign())
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

    let mut acc = 0;

    let res = zip_nums::<Double>(a.digits(), b.digits(), 0)
        .scan(0, |_, (aop, bop)| {
            let digit = (RADIX + aop - bop - acc) as Single;

            acc = (aop < bop + acc) as Double;

            Some(digit)
        })
        .collect_with(vec![0; a.len()]);

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

    let res = zip_nums::<Double>(a.digits(), b.digits(), 0)
        .scan(0, |_, (aop, bop)| {
            let digit = (RADIX + aop - bop - acc) as Single;

            acc = (aop < bop + acc) as Double;

            Some(digit)
        })
        .collect_with([0; L]);

    FixedRepr::from_raw(res, sign)
}

#[allow(unused_variables)]
fn sub_long_mut(a: LongMutOperand<'_>, b: Operand<'_>) -> MutRepr {
    todo!()
}

#[allow(unused_variables)]
fn sub_fixed_mut<const L: usize>(a: FixedMutOperand<'_, L>, b: Operand<'_>) -> MutRepr {
    todo!()
}

fn mul_single_long(a: Operand<'_>, bop: Single) -> LongRepr {
    match (a.sign(), Sign::from(bop)) {
        (Sign::ZERO, _) => return LongRepr::ZERO,
        (_, Sign::ZERO) => return LongRepr::ZERO,
        _ => (),
    }

    let len = a.len() + 1;

    let mut acc = 0;
    let mut res = vec![0; len];

    for (ptr, aop) in res.iter_mut().zip(a.iter::<Double>()) {
        acc += aop * bop as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;
    }

    res[a.len()] = acc as Single;

    LongRepr::from_raw(res, a.sign())
}

fn mul_single_fixed<const L: usize>(a: Operand<'_>, bop: Single) -> FixedRepr<L> {
    match (a.sign(), Sign::from(bop)) {
        (Sign::ZERO, _) => return FixedRepr::ZERO,
        (_, Sign::ZERO) => return FixedRepr::ZERO,
        _ => (),
    }

    let mut acc = 0;
    let mut res = [0; L];

    for (ptr, aop) in res.iter_mut().zip(a.iter::<Double>()) {
        acc += aop * bop as Double;

        *ptr = acc as Single;

        acc >>= Single::BITS;
    }

    let idx = a.len();

    if idx < L {
        res[idx] = acc as Single;
        acc >>= Single::BITS;
    }

    FixedRepr::from_raw(res, a.sign())
        .with_overflow_val(acc as Single)
        .with_overflow(acc > 0)
}

fn mul_long(a: Operand<'_>, b: Operand<'_>) -> LongRepr {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return LongRepr::ZERO,
        (_, Sign::ZERO) => return LongRepr::ZERO,
        _ => (),
    }

    let mut res = vec![0; a.len() + b.len()];

    for (i, aop) in a.iter::<Double>().enumerate() {
        let mut acc = 0;

        for (j, bop) in b.iter::<Double>().enumerate() {
            acc += res[i + j] as Double + aop * bop;

            res[i + j] = acc as Single;

            acc >>= Single::BITS;
        }

        res[i + b.len()] += acc as Single;
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

        for (j, bop) in b.iter::<Double>().take(L - i).enumerate() {
            acc += res[i + j] as Double + aop * bop;

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

#[allow(unused_variables)]
fn mul_long_mut(a: LongMutOperand<'_>, b: Operand<'_>) -> MutRepr {
    todo!()
}

#[allow(unused_variables)]
fn mul_fixed_mut<const L: usize>(a: FixedMutOperand<'_, L>, b: Operand<'_>) -> MutRepr {
    todo!()
}

fn div_long(a: Operand<'_>, b: Operand<'_>) -> (LongRepr, LongRepr) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => return (LongRepr::ZERO, LongRepr::ZERO),
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b == Operand::ONE {
        return (a.into(), LongRepr::ZERO);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => return (LongRepr::ZERO, a.into()),
        Ordering::Equal => return (LongRepr::from_single(1).with_sign(a.sign() * b.sign()), LongRepr::ZERO),
        Ordering::Greater => (),
    }

    let mut div = vec![0; a.len()];
    let mut rem = vec![0; b.len() + 1];
    let mut len = 0;

    let sign_a = a.sign();
    let sign_b = b.sign();
    let apos = a.with_sign(Sign::POS);
    let bpos = b.with_sign(Sign::POS);

    for (i, aop) in apos.iter::<Single>().enumerate().rev() {
        cycle(&mut rem[..len + 1], aop);

        len += 1;

        if len < b.len() {
            continue;
        }

        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            let val = mul_single_long(bpos, m as Single);

            match cmp_nums(val.digits(), &rem[..len]) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        let digit = l.saturating_sub(1) as Single;

        if digit > 0 {
            div[i] = digit;

            let dop = [digit];
            let dop = Operand::from_raw(&dop);
            let rop = Operand::from_raw(&rem[..len]);

            let mul = mul_long(bpos, dop);
            let sub = sub_long(rop, (&mul).into());

            rem.fill(0);
            rem[..sub.len()].copy_from_slice(sub.digits());
            len = sub.len();
        };
    }

    (LongRepr::from_raw(div, sign_a * sign_b), LongRepr::from_raw(rem, sign_a))
}

fn div_fixed<const L: usize>(a: Operand<'_>, b: Operand<'_>) -> (FixedRepr<L>, FixedRepr<L>) {
    match (a.sign(), b.sign()) {
        (Sign::ZERO, _) => {
            return (FixedRepr::ZERO, FixedRepr::ZERO);
        },
        (_, Sign::ZERO) => panic!("Division by zero"),
        _ => (),
    }

    if b == Operand::ONE {
        return (a.into(), FixedRepr::ZERO);
    }

    match cmp_nums(a.digits(), b.digits()) {
        Ordering::Less => return (FixedRepr::ZERO, a.into()),
        Ordering::Equal => return (FixedRepr::ONE.with_sign(a.sign() * b.sign()), FixedRepr::ZERO),
        Ordering::Greater => (),
    }

    let mut div = [0; L];
    let mut rem = [0; L];
    #[allow(unused_assignments)]
    let mut remx = 0;
    let mut len = 0;

    let sign_a = a.sign();
    let sign_b = b.sign();
    let apos = a.with_sign(Sign::POS);
    let bpos = b.with_sign(Sign::POS);

    for (i, aop) in apos.iter::<Single>().enumerate().rev() {
        remx = rem[L - 1];

        cycle(&mut rem[..len + 1], aop);

        len += 1;

        if len < b.len() {
            continue;
        }

        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            let val = mul_single_fixed::<L>(bpos, m as Single);

            match cmp_nums_ext(&val.raw, val.overflow_val, &rem, remx) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        let digit = l.saturating_sub(1) as Single;

        if digit > 0 {
            div[i] = digit;

            let dop = [digit];
            let dop = Operand::from_raw(&dop);
            let rop = Operand::from_raw(&rem[..len]);

            let mul = mul_fixed::<L>(bpos, dop);
            let sub = sub_fixed::<L>(rop, (&mul).into());

            rem.fill(0);
            rem[..sub.len()].copy_from_slice(sub.digits());
            len = sub.len();
        };
    }

    (FixedRepr::from_raw(div, sign_a * sign_b), FixedRepr::from_raw(rem, sign_a))
}

#[allow(unused_variables)]
fn div_long_mut(a: LongMutOperand<'_>, b: Operand<'_>) -> MutRepr {
    todo!()
}

#[allow(unused_variables)]
fn div_fixed_mut<const L: usize>(a: FixedMutOperand<'_, L>, b: Operand<'_>) -> MutRepr {
    todo!()
}

#[allow(unused_variables)]
fn rem_long_mut(a: LongMutOperand<'_>, b: Operand<'_>) -> MutRepr {
    todo!()
}

#[allow(unused_variables)]
fn rem_fixed_mut<const L: usize>(a: FixedMutOperand<'_, L>, b: Operand<'_>) -> MutRepr {
    todo!()
}

fn bit_long<F>(a: Operand<'_>, b: Operand<'_>, func: F) -> LongRepr
where
    F: Fn(Single, Single) -> Single,
{
    let res = zip_nums::<Single>(a.digits(), b.digits(), 0)
        .map(|(aop, bop)| func(aop, bop))
        .collect_with(vec![0; a.len().max(b.len())]);

    LongRepr::from_raw(res, Sign::POS)
}

fn bit_fixed<const L: usize, F>(a: Operand<'_>, b: Operand<'_>, func: F) -> FixedRepr<L>
where
    F: Fn(Single, Single) -> Single,
{
    let res = zip_nums::<Single>(a.digits(), b.digits(), 0)
        .map(|(aop, bop)| func(aop, bop))
        .collect_with([0; L]);

    FixedRepr::from_raw(res, Sign::POS)
}

fn bit_long_mut<F>(mut a: LongMutOperand<'_>, b: Operand<'_>, func: F)
where
    F: Fn(Single, Single) -> Single,
{
    a.resize(a.len().max(b.len()));

    for (i, ptr) in &mut a.raw_mut().iter_mut().enumerate() {
        let bop = *b.digits().get(i).unwrap_or(&0);

        *ptr = func(*ptr, bop);
    }
}

fn bit_fixed_mut<const L: usize, F>(mut a: FixedMutOperand<'_, L>, b: Operand<'_>, func: F)
where
    F: Fn(Single, Single) -> Single,
{
    for (i, ptr) in &mut a.raw_mut().iter_mut().enumerate() {
        let bop = *b.digits().get(i).unwrap_or(&0);

        *ptr = func(*ptr, bop);
    }
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

    a.resize(len);

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

ops_impl!(@un |a: SignedLong| -> SignedLong, - a.with_neg());
ops_impl!(@un |a: &SignedLong| -> SignedLong, - a.clone().with_neg());

ops_impl!(@un <const L: usize> |a: SignedFixed<L>| -> SignedFixed<L>, - a.with_neg());
ops_impl!(@un <const L: usize> |a: &SignedFixed<L>| -> SignedFixed<L>, - (*a).with_neg());

ops_impl!(@un <'digits> |*a: &Operand<'digits>| -> Operand<'digits>, - a.with_neg());

ops_impl!(@bin |*a: &SignedLong, *b: &SignedLong| -> SignedLong,
    + add_long((&a).into(), (&b).into()),
    - sub_long((&a).into(), (&b).into()),
    * mul_long((&a).into(), (&b).into()),
    / div_long((&a).into(), (&b).into()).0,
    % div_long((&a).into(), (&b).into()).1,
    | bit_long((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_long((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_long((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |*a: &UnsignedLong, *b: &UnsignedLong| -> UnsignedLong,
    + add_long((&a).into(), (&b).into()),
    - sub_long((&a).into(), (&b).into()),
    * mul_long((&a).into(), (&b).into()),
    / div_long((&a).into(), (&b).into()).0,
    % div_long((&a).into(), (&b).into()).1,
    | bit_long((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_long((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_long((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin |*a: &SignedLong, *b: usize| -> SignedLong,
    << shl_long((&a).into(), b),
    >> shr_long((&a).into(), b));

ops_impl!(@bin |*a: &UnsignedLong, *b: usize| -> UnsignedLong,
    << shl_long((&a).into(), b),
    >> shr_long((&a).into(), b));

ops_impl!(@mut |a: mut SignedLong, *b: &SignedLong|,
    += ops_impl_mut_fn!(add_long_mut, a, b),
    -= ops_impl_mut_fn!(sub_long_mut, a, b),
    *= ops_impl_mut_fn!(mul_long_mut, a, b),
    /= ops_impl_mut_fn!(div_long_mut, a, b),
    %= ops_impl_mut_fn!(rem_long_mut, a, b),
    |= bit_long_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_long_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_long_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut |a: mut UnsignedLong, *b: &UnsignedLong|,
    += ops_impl_mut_fn!(add_long_mut, a, b),
    -= ops_impl_mut_fn!(sub_long_mut, a, b),
    *= ops_impl_mut_fn!(mul_long_mut, a, b),
    /= ops_impl_mut_fn!(div_long_mut, a, b),
    %= ops_impl_mut_fn!(rem_long_mut, a, b),
    |= bit_long_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_long_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_long_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut |a: mut SignedLong, b: usize|,
    <<= shl_long_mut(a.into(), b),
    >>= shr_long_mut(a.into(), b));

ops_impl!(@mut |a: mut UnsignedLong, b: usize|,
    <<= shl_long_mut(a.into(), b),
    >>= shr_long_mut(a.into(), b));

ops_impl!(@bin <const L: usize> |*a: &SignedFixed<L>, *b: &SignedFixed<L>| -> SignedFixed::<L>,
    + add_fixed((&a).into(), (&b).into()),
    - sub_fixed((&a).into(), (&b).into()),
    * mul_fixed((&a).into(), (&b).into()),
    / div_fixed((&a).into(), (&b).into()).0,
    % div_fixed((&a).into(), (&b).into()).1,
    | bit_fixed((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_fixed((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_fixed((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &UnsignedFixed<L>, *b: &UnsignedFixed<L>| -> UnsignedFixed::<L>,
    + add_fixed((&a).into(), (&b).into()),
    - sub_fixed((&a).into(), (&b).into()),
    * mul_fixed((&a).into(), (&b).into()),
    / div_fixed((&a).into(), (&b).into()).0,
    % div_fixed((&a).into(), (&b).into()).1,
    | bit_fixed((&a).into(), (&b).into(), |aop, bop| aop | bop),
    & bit_fixed((&a).into(), (&b).into(), |aop, bop| aop & bop),
    ^ bit_fixed((&a).into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &SignedFixed<L>, b: usize| -> SignedFixed::<L>,
    << shl_fixed((&a).into(), b),
    >> shr_fixed((&a).into(), b));

ops_impl!(@bin <const L: usize> |*a: &UnsignedFixed<L>, b: usize| -> UnsignedFixed::<L>,
    << shl_fixed((&a).into(), b),
    >> shr_fixed((&a).into(), b));

ops_impl!(@mut <const L: usize> |a: mut SignedFixed<L>, *b: &SignedFixed<L>|,
    += ops_impl_mut_fn!(add_fixed_mut, a, b),
    -= ops_impl_mut_fn!(sub_fixed_mut, a, b),
    *= ops_impl_mut_fn!(mul_fixed_mut, a, b),
    /= ops_impl_mut_fn!(div_fixed_mut, a, b),
    %= ops_impl_mut_fn!(rem_fixed_mut, a, b),
    |= bit_fixed_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_fixed_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_fixed_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut UnsignedFixed<L>, *b: &UnsignedFixed<L>|,
    += ops_impl_mut_fn!(add_fixed_mut, a, b),
    -= ops_impl_mut_fn!(sub_fixed_mut, a, b),
    *= ops_impl_mut_fn!(mul_fixed_mut, a, b),
    /= ops_impl_mut_fn!(div_fixed_mut, a, b),
    %= ops_impl_mut_fn!(rem_fixed_mut, a, b),
    |= bit_fixed_mut(a.into(), (&b).into(), |aop, bop| aop | bop),
    &= bit_fixed_mut(a.into(), (&b).into(), |aop, bop| aop & bop),
    ^= bit_fixed_mut(a.into(), (&b).into(), |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut SignedFixed<L>, b: usize|,
    <<= shl_fixed_mut(a.into(), b),
    >>= shr_fixed_mut(a.into(), b));

ops_impl!(@mut <const L: usize> |a: mut UnsignedFixed<L>, b: usize|,
    <<= shl_fixed_mut(a.into(), b),
    >>= shr_fixed_mut(a.into(), b));

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

fn get_sign<F: Fixed>(val: F, default: Sign) -> Sign
where
    for<'f> &'f F: Ops,
{
    let zero = F::zero();

    if val != zero {
        default
    } else {
        Sign::ZERO
    }
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

fn cycle(digits: &mut [Single], val: Single) {
    for i in (1..digits.len()).rev() {
        digits[i] = digits[i - 1];
    }

    digits[0] = val;
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRIMES: [usize; 2] = [10_570_841, 10_570_849];

    type S32 = signed_fixed!(32);
    type U32 = unsigned_fixed!(32);

    macro_rules! assert_long_from {
        (@signed $expr:expr, $digits:expr, $sign:expr) => {
            assert_eq!(SignedLong::from($expr), SignedLong { digits: $digits, sign: $sign });
        };
        (@unsigned $expr:expr, $digits:expr) => {
            assert_eq!(UnsignedLong::from($expr), UnsignedLong { digits: $digits });
        };
    }

    macro_rules! assert_fixed_from {
        (@signed $expr:expr, $digits:expr, $len:expr, $sign:expr) => {
            assert_eq!(
                S32::from($expr),
                SignedFixed {
                    raw: $digits,
                    len: $len,
                    sign: $sign
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

    fn normalized(val: &[u8]) -> Vec<u8> {
        let len = get_len(val);

        val[..len].to_vec()
    }

    fn trimmed(val: SignedLong, len: usize) -> SignedLong {
        let len = len.min(val.len());

        let digits = normalized(&val.digits()[..len]);
        let sign = get_sign(digits.len(), val.sign());

        SignedLong { digits, sign }
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
        assert_eq!(SignedLong::try_from_digits(&[], 31), Ok(SignedLong::default()));
        assert_eq!(UnsignedLong::try_from_digits(&[], 31), Ok(UnsignedLong::default()));

        for radix in 8..=40 {
            let mut digits = [0; 4];

            while !add(&mut digits, radix, radix - 5) {
                let val = value(&digits, radix);
                let sign = Sign::from(val);

                assert_long_from_digits!(@signed &digits, radix, normalized(&val.to_le_bytes()), sign);
                assert_long_from_digits!(@unsigned &digits, radix, normalized(&val.to_le_bytes()));
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
                let sign = Sign::from(val);

                assert_fixed_from_digits!(@signed &digits, radix, val.to_le_bytes(), len, sign);
                assert_fixed_from_digits!(@unsigned &digits, radix, val.to_le_bytes(), len);
            }
        }
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

            let sign_pos = Sign::from(val);
            let sign_neg = Sign::NEG * sign_pos;

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

            let sign_pos = Sign::from(val);
            let sign_neg = Sign::NEG * sign_pos;

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
        for aop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[0]) {
            for bop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[1]) {
                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                assert_eq!(a + b, SignedLong::from(aop + bop));
                assert_eq!(a - b, SignedLong::from(aop - bop));
            }
        }
    }

    #[test]
    fn addsub_fixed() {
        for aop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[0]) {
            for bop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[1]) {
                let a = &S32::from(aop);
                let b = &S32::from(bop);

                assert_eq!(a + b, S32::from(aop + bop));
                assert_eq!(a - b, S32::from(aop - bop));
            }
        }
    }

    #[test]
    fn muldiv_long() {
        for aop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[0]) {
            for bop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[1]) {
                let a = &SignedLong::from(aop);
                let b = &SignedLong::from(bop);

                assert_eq!(a * b, SignedLong::from(aop * bop));
                assert_eq!(a / b, SignedLong::from(aop / bop));
                assert_eq!(a % b, SignedLong::from(aop % bop));
            }
        }
    }

    #[test]
    fn muldiv_fixed() {
        for aop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[0]) {
            for bop in (i32::MIN as i64 + 1..=i32::MAX as i64).step_by(PRIMES[1]) {
                let a = &S32::from(aop);
                let b = &S32::from(bop);

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

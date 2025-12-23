use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    marker::PhantomData,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, DerefMut, Div,
        DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign,
    },
};

use rand::Rng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{num::prime::*, ops::*};

macro_rules! num_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(num_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl Extension for $primitive {
            fn bitor_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self {
                *self |= (mask.checked_shl(offset as u32).unwrap_or(0)) as $primitive;
                self
            }

            fn bitand_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self {
                *self &= (mask.checked_shl(offset as u32).unwrap_or(0)) as $primitive;
                self
            }

            fn bitxor_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self {
                *self ^= (mask.checked_shl(offset as u32).unwrap_or(0)) as $primitive;
                self
            }
        }

        impl Num for $primitive {
            fn bits(&self) -> usize {
                <$primitive>::BITS as usize
            }

            fn is_even(&self) -> bool {
                *self % 2 == 0
            }
        }

        impl Static for $primitive {
            const BITS: usize = <$primitive>::BITS as usize;
            const BYTES: usize = (<$primitive>::BITS as usize) / 8;
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
        }
    };
}

macro_rules! signed_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(signed_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl Signed for $primitive {}
    };
}

macro_rules! unsigned_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(unsigned_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl Unsigned for $primitive {
            fn order(&self) -> usize {
                self.ilog2() as usize
            }

            fn log(&self) -> Self {
                self.ilog2() as $primitive
            }

            fn sqrt(&self) -> Self {
                self.isqrt() as $primitive
            }
        }
    };
}

macro_rules! prime_impl {
    ($(($primitive:ty, $count:expr)),+ $(,)?) => {
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
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@unsigned $primitive);)+
    };
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@signed $primitive);)+
    };
    (@unsigned $primitive:ty $(,)?) => {
        impl From<$primitive> for Sign {
            fn from(value: $primitive) -> Self {
                match value {
                    0 => Sign::ZERO,
                    _ => Sign::POS,
                }
            }
        }
    };
    (@signed $primitive:ty $(,)?) => {
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

macro_rules! width_display_impl {
    ([$($display:ident),+ $(,)?]) => {
        $(width_display_impl!($display);)+
    };
    ($display:ident $(,)?) => {
        impl<N: Num + Extension + Static + $display, const BITS: usize> $display for Width<N, BITS>
        where
            for<'s> &'s N: Ops,
        {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}

macro_rules! modular_display_impl {
    ([$($display:ident),+ $(,)?]) => {
        $(modular_display_impl!($display);)+
    };
    ($display:ident $(,)?) => {
        impl<N: Num + Extension + Unsigned + Static + $display, M: Modulus<N>> $display for Modular<N, M>
        where
            for<'s> &'s N: Ops,
        {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}

macro_rules! width_ops_impl {
    ([$($op:ident => $fn:ident),+ $(,)?]) => {
        $(width_ops_impl!($op => $fn);)+
    };
    ($op:ident => $fn:ident $(,)?) => {
        impl<U, N: Num + Extension + Static + $op<U, Output = N>, const BITS: usize> $op<U> for Width<N, BITS>
        where
            for<'s> &'s N: Ops,
        {
            type Output = Width<N, BITS>;

            fn $fn(self, rhs: U) -> Self::Output {
                let mut res = Width::from(self.0.$fn(rhs));

                res.normalize();
                res
            }
        }
    };
}

macro_rules! modular_ops_impl {
    ([$($op:ident => $fn:ident),+ $(,)?]) => {
        $(modular_ops_impl!($op => $fn);)+
    };
    ($op:ident => $fn:ident $(,)?) => {
        impl<U, N: Num + Extension + Unsigned + Static + $op<U, Output = N>, M: Modulus<N>> $op<U> for Modular<N, M>
        where
            for<'s> &'s N: Ops,
        {
            type Output = Modular<N, M>;

            fn $fn(self, rhs: U) -> Self::Output {
                let mut res = Modular::from(self.0.$fn(rhs));

                res.normalize();
                res
            }
        }
    };
}

macro_rules! width_ops_mut_impl {
    ([$($op:ident => $fn:ident),+ $(,)?]) => {
        $(width_ops_mut_impl!($op => $fn);)+
    };
    ($op:ident => $fn:ident $(,)?) => {
        impl<U, N: Num + Extension + Static + $op<U>, const BITS: usize> $op<U> for Width<N, BITS>
        where
            for<'s> &'s N: Ops,
        {
            fn $fn(&mut self, rhs: U) {
                self.0.$fn(rhs);
                self.normalize();
            }
        }
    };
}

macro_rules! modular_ops_mut_impl {
    ([$($op:ident => $fn:ident),+ $(,)?]) => {
        $(modular_ops_mut_impl!($op => $fn);)+
    };
    ($op:ident => $fn:ident $(,)?) => {
        impl<U, N: Num + Extension + Unsigned + Static + $op<U>, M: Modulus<N>> $op<U> for Modular<N, M>
        where
            for<'s> &'s N: Ops,
        {
            fn $fn(&mut self, rhs: U) {
                self.0.$fn(rhs);
                self.normalize();
            }
        }
    };
}

pub mod prime {
    use std::mem::{replace, take};

    use super::*;

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

pub struct Width<N: Num + Extension + Static, const BITS: usize>(pub N)
where
    for<'s> &'s N: Ops;

pub struct Modular<N: Num + Extension + Static + Unsigned, M: Modulus<N>>(pub N, PhantomData<M>)
where
    for<'s> &'s N: Ops;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

pub trait Num: Sized + Default + Clone + Eq + Ord + From<bool>
where
    for<'s> Self: Ops + OpsAssign + OpsAssign<&'s Self> + OpsFrom + OpsFrom<&'s Self, &'s Self>,
    for<'s> &'s Self: Ops,
{
    fn bits(&self) -> usize;

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
        Self: Extension,
    {
        let shift = order - 1;
        let div = shift / u64::BITS as usize;
        let rem = shift % u64::BITS as usize;

        let mut res = Self::zero();

        res.bitor_offset_mut_ext((1 << rem) | rng.next_u64() & ((1 << rem) - 1), shift - rem);

        for idx in 0..div {
            res.bitor_offset_mut_ext(rng.next_u64(), shift - rem - idx * div);
        }

        res
    }

    fn rand_prime(order: usize) -> Self
    where
        Self: Extension + Primality,
    {
        let mut rng = rand::rng();
        let mut val = Self::rand(order, &mut rng).odd_ext();

        while !val.is_prime() {
            val = Self::rand(order, &mut rng).odd_ext();
        }

        val
    }

    fn rand_primes(order: usize, count: usize) -> Vec<Self>
    where
        Self: Extension + Primality,
    {
        (0..count).map(|_| Self::rand_prime(order)).collect::<Vec<Self>>()
    }

    fn rand_prime_par(order: usize) -> Self
    where
        Self: Send + Extension + Primality,
    {
        let threads = std::thread::available_parallelism().map(|val| val.get()).unwrap_or(1);

        (0..threads)
            .into_par_iter()
            .find_map_first(|_| Some(Self::rand_prime(order)))
            .unwrap_or_default()
    }

    fn rand_primes_par(order: usize, count: usize) -> Vec<Self>
    where
        Self: Send + Extension + Primality,
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

pub trait Extension: Num
where
    for<'s> &'s Self: Ops,
{
    fn bitor_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self;

    fn bitand_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self;

    fn bitxor_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self;

    fn bitor_mut_ext(&mut self, mask: u64) -> &mut Self {
        self.bitor_offset_mut_ext(mask, 0);
        self
    }

    fn bitand_mut_ext(&mut self, mask: u64) -> &mut Self {
        self.bitand_offset_mut_ext(mask, 0);
        self
    }

    fn bitxor_mut_ext(&mut self, mask: u64) -> &mut Self {
        self.bitxor_offset_mut_ext(mask, 0);
        self
    }

    fn odd_mut_ext(&mut self) -> &mut Self {
        self.bitor_mut_ext(1);
        self
    }

    fn even_mut_ext(&mut self) -> &mut Self {
        self.bitand_mut_ext(u64::MAX - 1);
        self
    }

    fn alt_mut_ext(&mut self) -> &mut Self {
        self.bitxor_mut_ext(1);
        self
    }

    fn bitor_offset_ext(mut self, mask: u64, offset: usize) -> Self {
        self.bitor_offset_mut_ext(mask, offset);
        self
    }

    fn bitand_offset_ext(mut self, mask: u64, offset: usize) -> Self {
        self.bitand_offset_mut_ext(mask, offset);
        self
    }

    fn bitxor_offset_ext(mut self, mask: u64, offset: usize) -> Self {
        self.bitxor_offset_mut_ext(mask, offset);
        self
    }

    fn bitor_ext(mut self, mask: u64) -> Self {
        self.bitor_offset_mut_ext(mask, 0);
        self
    }

    fn bitand_ext(mut self, mask: u64) -> Self {
        self.bitand_offset_mut_ext(mask, 0);
        self
    }

    fn bitxor_ext(mut self, mask: u64) -> Self {
        self.bitxor_offset_mut_ext(mask, 0);
        self
    }

    fn odd_ext(mut self) -> Self {
        self.odd_mut_ext();
        self
    }

    fn even_ext(mut self) -> Self {
        self.even_mut_ext();
        self
    }

    fn alt_ext(mut self) -> Self {
        self.alt_mut_ext();
        self
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
    fn order(&self) -> usize;

    fn log(&self) -> Self;

    fn sqrt(&self) -> Self;
}

pub trait Static: Num + Copy
where
    for<'s> &'s Self: Ops,
{
    const BITS: usize;
    const BYTES: usize;
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

pub trait Modulus<N: Num + Extension + Static + Unsigned>
where
    for<'s> &'s N: Ops,
{
    const MOD: N;
}

num_impl!([i8, i16, i32, i64, i128, isize]);
num_impl!([u8, u16, u32, u64, u128, usize]);

signed_impl!([i8, i16, i32, i64, i128, isize]);
unsigned_impl!([u8, u16, u32, u64, u128, usize]);

#[cfg(target_pointer_width = "64")]
prime_impl!((u8, 1), (u16, 2), (u32, 5), (u64, 12), (u128, 20), (usize, 12));

#[cfg(target_pointer_width = "32")]
prime_impl!((u8, 1), (u16, 2), (u32, 5), (u64, 12), (u128, 20), (usize, 5));

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

impl<N: Num + Extension + Static, const BITS: usize> From<N> for Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    fn from(value: N) -> Self {
        Width(value)
    }
}

impl<N: Num + Extension + Unsigned + Static, M: Modulus<N>> From<N> for Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    fn from(value: N) -> Self {
        Modular(value, PhantomData)
    }
}

impl<U, N: Num + Extension + Static + FromIterator<U>, const BITS: usize> FromIterator<U> for Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let mut res = Width::from(N::from_iter(iter));

        res.normalize();
        res
    }
}

impl<U, N: Num + Extension + Unsigned + Static + FromIterator<U>, M: Modulus<N>> FromIterator<U> for Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let mut res = Modular::from(N::from_iter(iter));

        res.normalize();
        res
    }
}

impl<N: Num + Extension + Static, const BITS: usize> Deref for Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    type Target = N;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<N: Num + Extension + Unsigned + Static, M: Modulus<N>> Deref for Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    type Target = N;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<N: Num + Extension + Static, const BITS: usize> DerefMut for Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<N: Num + Extension + Unsigned + Static, M: Modulus<N>> DerefMut for Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<U, N: Num + Extension + Static + AsRef<U>, const BITS: usize> AsRef<U> for Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    fn as_ref(&self) -> &U {
        self.0.as_ref()
    }
}

impl<U, N: Num + Extension + Unsigned + Static + AsRef<U>, M: Modulus<N>> AsRef<U> for Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    fn as_ref(&self) -> &U {
        self.0.as_ref()
    }
}

impl<U, N: Num + Extension + Static + AsMut<U>, const BITS: usize> AsMut<U> for Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    fn as_mut(&mut self) -> &mut U {
        self.0.as_mut()
    }
}

impl<U, N: Num + Extension + Unsigned + Static + AsMut<U>, M: Modulus<N>> AsMut<U> for Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    fn as_mut(&mut self) -> &mut U {
        self.0.as_mut()
    }
}

width_display_impl!([Display, Binary, Octal, LowerHex, UpperHex]);
modular_display_impl!([Display, Binary, Octal, LowerHex, UpperHex]);

width_ops_impl!([
    Add => add,
    Sub => sub,
    Mul => mul,
    Div => div,
    Rem => rem,
    BitOr => bitor,
    BitAnd => bitand,
    BitXor => bitxor,
]);

modular_ops_impl!([
    Add => add,
    Sub => sub,
    Mul => mul,
    Div => div,
    Rem => rem,
    BitOr => bitor,
    BitAnd => bitand,
    BitXor => bitxor,
]);

width_ops_mut_impl!([
    AddAssign => add_assign,
    SubAssign => sub_assign,
    MulAssign => mul_assign,
    DivAssign => div_assign,
    RemAssign => rem_assign,
    BitOrAssign => bitor_assign,
    BitAndAssign => bitand_assign,
    BitXorAssign => bitxor_assign,
]);

modular_ops_mut_impl!([
    AddAssign => add_assign,
    SubAssign => sub_assign,
    MulAssign => mul_assign,
    DivAssign => div_assign,
    RemAssign => rem_assign,
    BitOrAssign => bitor_assign,
    BitAndAssign => bitand_assign,
    BitXorAssign => bitxor_assign,
]);

impl<N: Num + Extension + Static, const BITS: usize> Width<N, BITS>
where
    for<'s> &'s N: Ops,
{
    #[allow(unused)]
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> Self {
        todo!()
    }
}

impl<N: Num + Extension + Unsigned + Static, M: Modulus<N>> Modular<N, M>
where
    for<'s> &'s N: Ops,
{
    #[allow(unused)]
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> Self {
        todo!()
    }
}

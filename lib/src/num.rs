use std::{cmp::Ordering, fmt::Debug, marker::PhantomData};

use ndproc::{
    forward_cmp, forward_decl, forward_def, forward_fmt, forward_into, forward_self, forward_std, forward_with,
};
use rand::Rng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{num::prime::*, ops::*};

macro_rules! num_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(num_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl NumExtension for $primitive {
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

            fn zero() -> Self {
                0
            }

            fn one() -> Self {
                1
            }
        }

        impl Zero for $primitive {
            const ZERO: Self = 0;
        }

        impl One for $primitive {
            const ONE: Self = 1;
        }

        impl Min for $primitive {
            const MIN: Self = Self::MIN;
        }

        impl Max for $primitive {
            const MAX: Self = Self::MAX;
        }
    };
}

macro_rules! signed_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(signed_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl Signed for $primitive {
            fn new(value: isize) -> Self {
                value as Self
            }
        }
    };
}

macro_rules! unsigned_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(unsigned_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl Unsigned for $primitive {
            fn new(value: usize) -> Self {
                value as Self
            }

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
            for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
        {
            PrimesFullIter {
                next: Prime::new(2),
                primes: Vec::with_capacity(count.as_count_check_estimate()),
                count: count.as_count_estimate(),
                limit: None,
            }
        }

        pub fn by_limit_full<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime>
        where
            for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
        {
            PrimesFullIter {
                next: Prime::new(2),
                primes: Vec::with_capacity(limit.as_limit_check_estimate()),
                count: limit.as_limit_estimate(),
                limit: Some(limit),
            }
        }

        pub fn by_count_fast<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime>
        where
            for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
        {
            PrimesFastIter {
                next: Prime::new(2),
                count: count.as_count_estimate(),
                limit: None,
            }
        }

        pub fn by_limit_fast<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime>
        where
            for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
        {
            PrimesFastIter {
                next: Prime::new(2),
                count: limit.as_limit_estimate(),
                limit: Some(limit),
            }
        }
    }

    pub trait Primality: Unsigned
    where
        for<'rhs, 'lhs> &'lhs Self: Ops<&'rhs Self, Type = Self>,
    {
        fn primes() -> impl Iterator<Item = Self>;

        fn as_count_estimate(&self) -> usize;

        fn as_limit_estimate(&self) -> usize;

        fn as_count_check_estimate(&self) -> usize;

        fn as_limit_check_estimate(&self) -> usize;

        fn is_prime(&self) -> bool {
            let sqrt = self.sqrt();

            Self::primes().take_while(|p| p <= &sqrt).all(|p| {
                let one = Self::one();

                let x = self - &one;

                let shr = &x - &one;
                let shr = &x ^ &shr;
                let shr = shr.order();

                let mut any = false;
                let mut pow = &x >> shr;
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

    pub trait PrimalityExtension: Send + Primality + NumExtension
    where
        for<'rhs, 'lhs> &'lhs Self: Ops<&'rhs Self, Type = Self>,
    {
        fn rand_prime(order: usize) -> Self {
            let mut rng = rand::rng();
            let mut val = Self::rand(order, &mut rng).odd_ext();

            while !val.is_prime() {
                val = Self::rand(order, &mut rng).odd_ext();
            }

            val
        }

        fn rand_primes(order: usize, count: usize) -> Vec<Self> {
            (0..count).map(|_| Self::rand_prime(order)).collect::<Vec<Self>>()
        }

        fn rand_prime_par(order: usize) -> Self {
            let threads = std::thread::available_parallelism().map(|val| val.get()).unwrap_or(1);

            (0..threads)
                .into_par_iter()
                .find_map_first(|_| Some(Self::rand_prime(order)))
                .unwrap_or_default()
        }

        fn rand_primes_par(order: usize, count: usize) -> Vec<Self> {
            (0..count)
                .into_par_iter()
                .map(|_| Self::rand_prime(order))
                .collect::<Vec<Self>>()
        }
    }

    struct PrimesFullIter<Prime: Primality>
    where
        for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
    {
        next: Prime,
        primes: Vec<Prime>,
        count: usize,
        limit: Option<Prime>,
    }

    struct PrimesFastIter<Prime: Primality>
    where
        for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
    {
        next: Prime,
        count: usize,
        limit: Option<Prime>,
    }

    impl<Prime: Primality> Iterator for PrimesFullIter<Prime>
    where
        for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
    {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
                return None;
            }

            if self.primes.len() < self.primes.capacity() {
                self.primes.push(self.next.clone());
            }

            let zero = Prime::new(0);
            let one = Prime::new(1);
            let two = Prime::new(2);

            let offset = &self.next & &one;
            let offset = &offset + &one;

            let mut val = &self.next + &offset;

            while self.primes.iter().take_while(|&p| p * p <= val).any(|p| &val % p == zero) {
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
        for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>,
    {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
                return None;
            }

            let one = Prime::new(1);
            let two = Prime::new(2);

            let offset = &self.next & &one;
            let offset = &offset + &one;

            let mut val = &self.next + &offset;

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

    impl<Prime: Primality> ExactSizeIterator for PrimesFullIter<Prime> where
        for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>
    {
    }

    impl<Prime: Primality> ExactSizeIterator for PrimesFastIter<Prime> where
        for<'rhs, 'lhs> &'lhs Prime: Ops<&'rhs Prime, Type = Prime>
    {
    }

    impl<Any: Send + Primality + NumExtension> PrimalityExtension for Any where
        for<'rhs, 'lhs> &'lhs Any: Ops<&'rhs Any, Type = Any>
    {
    }
}

#[forward_std(self.0 with N)]
#[forward_cmp(self.0 with N)]
#[forward_fmt(self.0 with N)]
#[forward_def(self.0 with N: crate::num::Num            where N: Num,           for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>)]
#[forward_def(self.0 with N: crate::num::NumExtension   where N: NumExtension,  for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>)]
#[forward_def(self.0 with N: crate::num::Unsigned       where N: Unsigned,      for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Width<N: Num + NumExtension + Unsigned, const BITS: usize>(pub N)
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>;

#[forward_std(self.0 with N)]
#[forward_cmp(self.0 with N)]
#[forward_fmt(self.0 with N)]
#[forward_def(self.0 with N: crate::num::Num            where N: Num,           for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>)]
#[forward_def(self.0 with N: crate::num::NumExtension   where N: NumExtension,  for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>)]
#[forward_def(self.0 with N: crate::num::Unsigned       where N: Unsigned,      for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Modular<N: Num + NumExtension + Unsigned, M: Modulus<N>>(pub N, pub PhantomData<M>)
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

#[forward_decl]
pub trait Num: Sized + Default + Clone + Eq + Ord
where
    for<'rhs> Self: Ops<Type = Self> + OpsAssign + OpsAssign<&'rhs Self>,
    for<'rhs, 'lhs> &'lhs Self: Ops<&'rhs Self, Type = Self>,
{
    fn bits(&self) -> usize;

    fn is_even(&self) -> bool;

    #[forward_into]
    fn zero() -> Self;

    #[forward_into]
    fn one() -> Self;

    #[forward_into]
    fn gcd(self, val: Self) -> Self {
        let zero = Self::zero();

        let (mut a, mut b) = match self.cmp(&val) {
            Ordering::Less => (val, self),
            Ordering::Equal => (self, val),
            Ordering::Greater => (self, val),
        };

        while b != zero {
            let rem = &a % &b;

            a = b;
            b = rem;
        }

        a
    }

    #[forward_into]
    fn lcm(mut self, val: Self) -> Self {
        let gcd = Self::gcd(self.clone(), val.clone());

        self /= &gcd;
        self *= &val;
        self
    }

    #[forward_into]
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

            acc = &acc * &acc;
            acc %= rem;
            pow >>= 1;
        }

        res
    }
}

#[forward_decl]
pub trait NumExtension: Num
where
    for<'rhs, 'lhs> &'lhs Self: Ops<&'rhs Self, Type = Self>,
{
    #[forward_self]
    fn bitor_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self;

    #[forward_self]
    fn bitand_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self;

    #[forward_self]
    fn bitxor_offset_mut_ext(&mut self, mask: u64, offset: usize) -> &mut Self;

    #[forward_self]
    fn bitor_mut_ext(&mut self, mask: u64) -> &mut Self {
        self.bitor_offset_mut_ext(mask, 0);
        self
    }

    #[forward_self]
    fn bitand_mut_ext(&mut self, mask: u64) -> &mut Self {
        self.bitand_offset_mut_ext(mask, 0);
        self
    }

    #[forward_self]
    fn bitxor_mut_ext(&mut self, mask: u64) -> &mut Self {
        self.bitxor_offset_mut_ext(mask, 0);
        self
    }

    #[forward_self]
    fn odd_mut_ext(&mut self) -> &mut Self {
        self.bitor_mut_ext(1);
        self
    }

    #[forward_self]
    fn even_mut_ext(&mut self) -> &mut Self {
        self.bitand_mut_ext(u64::MAX - 1);
        self
    }

    #[forward_self]
    fn alt_mut_ext(&mut self) -> &mut Self {
        self.bitxor_mut_ext(1);
        self
    }

    #[forward_into]
    fn bitor_offset_ext(mut self, mask: u64, offset: usize) -> Self {
        self.bitor_offset_mut_ext(mask, offset);
        self
    }

    #[forward_into]
    fn bitand_offset_ext(mut self, mask: u64, offset: usize) -> Self {
        self.bitand_offset_mut_ext(mask, offset);
        self
    }

    #[forward_into]
    fn bitxor_offset_ext(mut self, mask: u64, offset: usize) -> Self {
        self.bitxor_offset_mut_ext(mask, offset);
        self
    }

    #[forward_into]
    fn bitor_ext(mut self, mask: u64) -> Self {
        self.bitor_offset_mut_ext(mask, 0);
        self
    }

    #[forward_into]
    fn bitand_ext(mut self, mask: u64) -> Self {
        self.bitand_offset_mut_ext(mask, 0);
        self
    }

    #[forward_into]
    fn bitxor_ext(mut self, mask: u64) -> Self {
        self.bitxor_offset_mut_ext(mask, 0);
        self
    }

    #[forward_into]
    fn odd_ext(mut self) -> Self {
        self.odd_mut_ext();
        self
    }

    #[forward_into]
    fn even_ext(mut self) -> Self {
        self.even_mut_ext();
        self
    }

    #[forward_into]
    fn alt_ext(mut self) -> Self {
        self.alt_mut_ext();
        self
    }

    fn rand<R: ?Sized + Rng>(order: usize, rng: &mut R) -> Self {
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
}

#[forward_decl]
pub trait Signed: Num
where
    for<'rhs, 'lhs> &'lhs Self: Ops<&'rhs Self, Type = Self>,
{
    fn new(value: isize) -> Self;

    #[forward_with(|(x, y, z)| (Self::from(x), Self::from(y), Self::from(z)))]
    fn gcde(&self, val: &Self) -> (Self, Self, Self) {
        let zero = Self::zero();
        let one = Self::one();

        let a = self;
        let b = val;

        if b == &zero {
            return (a.clone(), one, zero);
        }

        let rem = a % b;

        let (g, x, y) = Self::gcde(b, &rem);

        let val = a / b;
        let val = &val * &y;
        let val = &x - &val;

        (g, y, val)
    }
}

#[forward_decl]
pub trait Unsigned: Num
where
    for<'rhs, 'lhs> &'lhs Self: Ops<&'rhs Self, Type = Self>,
{
    #[forward_into]
    fn new(value: usize) -> Self;

    fn order(&self) -> usize;

    #[forward_into]
    fn log(&self) -> Self;

    #[forward_into]
    fn sqrt(&self) -> Self;
}

pub trait Zero {
    const ZERO: Self;
}

pub trait One {
    const ONE: Self;
}

pub trait Min {
    const MIN: Self;
}

pub trait Max {
    const MAX: Self;
}

pub trait ZeroDyn {
    fn zero() -> Self;
}

pub trait OneDyn {
    fn one() -> Self;
}

pub trait MinDyn {
    fn min() -> Self;
}

pub trait MaxDyn {
    fn max() -> Self;
}

pub trait Modulus<N: Num>: Default + Debug + Clone + Copy
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>,
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

impl<N: Num + NumExtension + Unsigned, const BITS: usize> From<N> for Width<N, BITS>
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>,
{
    fn from(value: N) -> Self {
        Self(value).normalized()
    }
}

impl<N: Num + NumExtension + Unsigned, M: Modulus<N>> From<N> for Modular<N, M>
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>,
{
    fn from(value: N) -> Self {
        Self(value, PhantomData).normalized()
    }
}

impl<N: Num + NumExtension + Unsigned, const BITS: usize> Width<N, BITS>
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>,
{
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> &mut Self {
        todo!()
    }
}

impl<N: Num + NumExtension + Unsigned, M: Modulus<N>> Modular<N, M>
where
    for<'rhs, 'lhs> &'lhs N: Ops<&'rhs N, Type = N>,
{
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> &mut Self {
        self.0 %= M::MOD;
        self
    }
}

impl<Any: Zero> ZeroDyn for Any {
    fn zero() -> Self {
        Any::ZERO
    }
}

impl<Any: One> OneDyn for Any {
    fn one() -> Self {
        Any::ONE
    }
}

impl<Any: Min> MinDyn for Any {
    fn min() -> Self {
        Any::MIN
    }
}

impl<Any: Max> MaxDyn for Any {
    fn max() -> Self {
        Any::MAX
    }
}

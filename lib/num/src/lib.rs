use std::{
    cmp::Ordering,
    fmt::Debug,
    marker::PhantomData,
    mem::{replace, take},
};

use ndcore::ops::*;

use crate::prime::*;

pub mod arch;
pub mod long;

macro_rules! num_impl {
    (@signed [$($primitive:ty),+] $(,)?) => {
        $(num_impl!(@impl $primitive);)+
        $(num_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+] $(,)?) => {
        $(num_impl!(@impl $primitive);)+
        $(num_impl!(@unsigned $primitive);)+
    };
    (@impl $primitive:ty $(,)?) => {
        impl NumCore for $primitive {}

        impl Num for $primitive {}

        impl NumExt for $primitive {
            fn read(&self, offset: Offset) -> u64 {
                match offset {
                    Offset::Left(val) => self.unbounded_shr(val as u32) as u64,
                    Offset::Right(val) => self.unbounded_shr(<$primitive>::BITS.saturating_sub(val as u32)) as u64,
                }
            }

            fn write_bitor(&mut self, mask: u64, offset: Offset) -> &mut Self {
                match offset {
                    Offset::Left(val) => *self |= (mask as $primitive).unbounded_shl(val as u32),
                    Offset::Right(val) => *self |= (mask as $primitive).unbounded_shl(<$primitive>::BITS.saturating_sub(val as u32)),
                }

                self
            }

            fn write_bitand(&mut self, mask: u64, offset: Offset) -> &mut Self {
                use std::ops::Not;

                match offset {
                    Offset::Left(val) => *self &= (mask.not() as $primitive).unbounded_shl(val as u32).not(),
                    Offset::Right(val) => *self &= (mask.not() as $primitive).unbounded_shl(<$primitive>::BITS.saturating_sub(val as u32)).not(),
                }

                self
            }

            fn write_bitxor(&mut self, mask: u64, offset: Offset) -> &mut Self {
                match offset {
                    Offset::Left(val) => *self ^= (mask as $primitive).unbounded_shl(val as u32),
                    Offset::Right(val) => *self ^= (mask as $primitive).unbounded_shl(<$primitive>::BITS.saturating_sub(val as u32)),
                }

                self
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

        impl Binary for $primitive {
            const BITS: usize = <$primitive>::BITS as usize;
            const BYTES: usize = <$primitive>::BITS as usize / 8;
        }
    };
    (@signed $primitive:ty $(,)?) => {
        impl NumSigned for $primitive {}
    };
    (@unsigned $primitive:ty $(,)?) => {
        impl NumUnsigned for $primitive {
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

#[cfg(feature = "const-time")]
macro_rules! num_ct_impl {
    (@signed [$($signed:ty:$unsigned:ty),+ $(,)?]) => {
        $(num_ct_impl!(@signed $signed:$unsigned);)+
    };
    (@unsigned [$($unsigned:ty),+ $(,)?]) => {
        $(num_ct_impl!(@unsigned $unsigned);)+
    };
    (@signed $signed:ty:$unsigned:ty $(,)?) => {
        impl EqCt for $signed {
            fn eq_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let diff = lhs ^ rhs;
                let diff = (diff | diff.wrapping_neg()) >> (<$signed>::BITS - 1);

                diff.wrapping_sub(1) as MaskCt
            }
        }

        impl LtCt for $signed {
            fn lt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let lt = (lhs.wrapping_sub(rhs) >> (<$unsigned>::BITS - 1)) as u8;

                let lhs_neg = (lhs >> (<$unsigned>::BITS - 1)) as u8;
                let rhs_neg = (rhs >> (<$unsigned>::BITS - 1)) as u8;

                let xor = lhs_neg ^ rhs_neg;
                let res = xor & lhs_neg | !xor & lt;

                MaskCt::ZERO.wrapping_sub(res)
            }
        }

        impl GtCt for $signed {
            fn gt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let gt = (rhs.wrapping_sub(lhs) >> (<$unsigned>::BITS - 1)) as u8;

                let lhs_neg = (lhs >> (<$unsigned>::BITS - 1)) as u8;
                let rhs_neg = (rhs >> (<$unsigned>::BITS - 1)) as u8;

                let xor = lhs_neg ^ rhs_neg;
                let res = xor & rhs_neg | !xor & gt;

                MaskCt::ZERO.wrapping_sub(res)
            }
        }

        impl LeCt for $signed {}
        impl GeCt for $signed {}
        impl CmpCt for $signed {}

        num_ct_impl!(@min $signed);
        num_ct_impl!(@max $signed);
        num_ct_impl!(@select $signed);
    };
    (@unsigned $unsigned:ty $(,)?) => {
        impl EqCt for $unsigned {
            fn eq_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let diff = lhs ^ rhs;
                let diff = (diff | diff.wrapping_neg()) >> (<$unsigned>::BITS - 1);

                diff.wrapping_sub(1) as MaskCt
            }
        }

        impl LtCt for $unsigned {
            fn lt_ct(&self, other: &Self) -> MaskCt {
                let lhs = self;
                let rhs = other;

                let neg = (lhs.wrapping_sub(*rhs) >> (<$unsigned>::BITS - 1)) as MaskCt;

                MaskCt::ZERO.wrapping_sub(neg)
            }
        }

        impl GtCt for $unsigned {
            fn gt_ct(&self, other: &Self) -> MaskCt {
                let lhs = self;
                let rhs = other;

                let neg = (rhs.wrapping_sub(*lhs) >> (<$unsigned>::BITS - 1)) as MaskCt;

                MaskCt::ZERO.wrapping_sub(neg)
            }
        }

        impl LeCt for $unsigned {}
        impl GeCt for $unsigned {}
        impl CmpCt for $unsigned {}

        num_ct_impl!(@min $unsigned);
        num_ct_impl!(@max $unsigned);
        num_ct_impl!(@select $unsigned);
    };
    (@min $primitive:ty $(,)?) => {
        impl MinCt for $primitive {
            fn min_ct(&self, other: &Self) -> Self {
                let lhs = self;
                let rhs = other;

                let lt = lhs.lt_ct(rhs);
                let lt = <$primitive>::from_ne_bytes([lt; (<$primitive>::BITS / 8) as usize]);

                lt & lhs | !lt & rhs
            }
        }
    };
    (@max $primitive:ty $(,)?) => {
        impl MaxCt for $primitive {
            fn max_ct(&self, other: &Self) -> Self {
                let lhs = self;
                let rhs = other;

                let gt = lhs.gt_ct(rhs);
                let gt = <$primitive>::from_ne_bytes([gt; (<$primitive>::BITS / 8) as usize]);

                gt & lhs | !gt & rhs
            }
        }
    };
    (@select $primitive:ty $(,)?) => {
        impl SelectCt for $primitive {
            fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
                let mask_lhs = <$primitive>::from_ne_bytes([mask; (<$primitive>::BITS / 8) as usize]);
                let mask_rhs = <$primitive>::from_ne_bytes([!mask; (<$primitive>::BITS / 8) as usize]);

                mask_lhs & lhs | mask_rhs & rhs
            }
        }
    };
}

macro_rules! prime_impl {
    ($(($primitive:ty, $count:expr)),+ $(,)?) => {
        $(prime_impl!($primitive, $count);)+
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
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@unsigned $primitive);)+
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
}

pub mod prime {
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
        pub fn by_count_full<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime> {
            PrimesFullIter {
                next: Prime::from(2),
                primes: Vec::with_capacity(count.as_count_check_estimate()),
                count: count.as_count_estimate(),
                limit: None,
            }
        }

        pub fn by_limit_full<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime> {
            PrimesFullIter {
                next: Prime::from(2),
                primes: Vec::with_capacity(limit.as_limit_check_estimate()),
                count: limit.as_limit_estimate(),
                limit: Some(limit),
            }
        }

        pub fn by_count_fast<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime> {
            PrimesFastIter {
                next: Prime::from(2),
                count: count.as_count_estimate(),
                limit: None,
            }
        }

        pub fn by_limit_fast<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime> {
            PrimesFastIter {
                next: Prime::from(2),
                count: limit.as_limit_estimate(),
                limit: Some(limit),
            }
        }
    }

    pub trait Primality: NumExt + NumUnsigned {
        fn primes() -> impl Iterator<Item = Self>;

        fn as_count_estimate(&self) -> usize;

        fn as_limit_estimate(&self) -> usize;

        fn as_count_check_estimate(&self) -> usize;

        fn as_limit_check_estimate(&self) -> usize;

        fn is_prime(&self) -> bool {
            let sqrt = self.sqrt();

            Self::primes().take_while(|p| p <= &sqrt).all(|p| {
                let one = Self::one();

                let x = Self::sub(self, &one);

                let shr = Self::sub(&x, &one);
                let shr = Self::bitxor(&x, &shr);
                let shr = shr.order();

                let mut any = false;
                let mut pow = Self::shr(&x, shr);
                let mut exp = p.powrem(pow.clone(), self);

                while pow < x && one < exp && exp < x {
                    any |= true;

                    let val = exp.clone();

                    Self::shl_assign(&mut pow, 1);
                    Self::mul_assign(&mut exp, &val);
                    Self::rem_assign(&mut exp, self);
                }

                !any && exp == one || exp == x
            })
        }
    }

    pub trait PrimalityExt: Send + Primality {
        #[cfg(feature = "rand")]
        fn rand_prime(order: usize) -> Self {
            let mut rng = rand::rng();
            let mut val = Self::rand(order, &mut rng).into_odd();

            while !val.is_prime() {
                val = Self::rand(order, &mut rng).into_odd();
            }

            val
        }

        #[cfg(feature = "rand")]
        fn rand_primes(order: usize, count: usize) -> Vec<Self> {
            (0..count).map(|_| Self::rand_prime(order)).collect::<Vec<Self>>()
        }

        #[cfg(all(feature = "rand", feature = "rayon"))]
        fn rand_prime_par(order: usize) -> Self {
            use rayon::iter::{IntoParallelIterator, ParallelIterator};

            let threads = std::thread::available_parallelism().map(|val| val.get()).unwrap_or(1);

            (0..threads)
                .into_par_iter()
                .find_map_first(|_| Some(Self::rand_prime(order)))
                .unwrap_or_default()
        }

        #[cfg(all(feature = "rand", feature = "rayon"))]
        fn rand_primes_par(order: usize, count: usize) -> Vec<Self> {
            use rayon::iter::{IntoParallelIterator, ParallelIterator};

            (0..count)
                .into_par_iter()
                .map(|_| Self::rand_prime(order))
                .collect::<Vec<Self>>()
        }
    }

    struct PrimesFullIter<Prime: Primality> {
        next: Prime,
        primes: Vec<Prime>,
        count: usize,
        limit: Option<Prime>,
    }

    struct PrimesFastIter<Prime: Primality> {
        next: Prime,
        count: usize,
        limit: Option<Prime>,
    }

    impl<Prime: Primality> Iterator for PrimesFullIter<Prime> {
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

            let offset = Prime::bitand(&self.next, &one);
            let offset = Prime::add(&offset, &one);

            let mut val = Prime::add(&self.next, &offset);

            while self
                .primes
                .iter()
                .take_while(|&p| Prime::mul(p, p) <= val)
                .any(|p| Prime::rem(&val, p) == zero)
            {
                Prime::add_assign(&mut val, &two);

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

    impl<Prime: Primality> Iterator for PrimesFastIter<Prime> {
        type Item = Prime;

        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
                return None;
            }

            let one = Prime::from(1);
            let two = Prime::from(2);

            let offset = Prime::bitand(&self.next, &one);
            let offset = Prime::add(&offset, &one);

            let mut val = Prime::add(&self.next, &offset);

            while !val.is_prime() {
                Prime::add_assign(&mut val, &two);

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

    impl<Prime: Primality> ExactSizeIterator for PrimesFullIter<Prime> {}
    impl<Prime: Primality> ExactSizeIterator for PrimesFastIter<Prime> {}

    impl<Any: Send + Primality + NumExt> PrimalityExt for Any {}
}

#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumExt)]
pub struct Wrapping<N: Num + NumExt + NdOpsWrapping + NdOpsAssignWrapping>(pub N);

#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumExt)]
pub struct Saturating<N: Num + NumExt + NdOpsSaturating + NdOpsAssignSaturating>(pub N);

#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumExt)]
pub struct Unbounded<N: Num + NumExt + NdOpsUnbounded + NdOpsAssignUnbounded>(pub N);

#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Width<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize>(pub N);

#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Modular<N: Num + NumExt + NumUnsigned, M: Modulus<N>>(pub N, pub PhantomData<M>);

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Offset {
    Left(usize),
    Right(usize),
}

#[cfg(feature = "const-time")]
type MaskCt = u8;

#[cfg(feature = "const-time")]
type SignCt = i8;

#[ndfwd::decl]
pub trait NumCore:
    Sized + Default + Clone + PartialEq + Eq + PartialOrd + Ord + NdOps<All = Self> + NdOpsAssign + ZeroFn + OneFn
{
    #[ndfwd::as_into]
    fn gcd(mut lhs: Self, mut rhs: Self) -> Self {
        let zero = Self::zero();

        while rhs != zero {
            let rem = Self::rem(&lhs, &rhs);

            lhs = rhs;
            rhs = rem;
        }

        lhs
    }

    #[ndfwd::as_into]
    fn gcd_checked(mut lhs: Self, mut rhs: Self) -> Option<Self>
    where
        Self: NdOpsChecked<All = Self>,
    {
        let zero = Self::zero();

        while rhs != zero {
            let rem = Self::rem_checked(&lhs, &rhs)?;

            lhs = rhs;
            rhs = rem;
        }

        Some(lhs)
    }

    #[ndfwd::as_expr(|(x, y, z)| (Self::from(x), Self::from(y), Self::from(z)))]
    fn gcde(lhs: Self, rhs: Self) -> (Self, Self, Self) {
        let zero = Self::zero();
        let one = Self::one();

        let mut r0 = lhs;
        let mut r1 = rhs;
        let mut x0 = one.clone();
        let mut x1 = zero.clone();
        let mut y0 = zero.clone();
        let mut y1 = one.clone();

        while r1 != zero {
            let div = Self::div(&r0, &r1);

            let r = Self::sub(&r0, &Self::mul(&div, &r1));
            let x = Self::sub(&x0, &Self::mul(&div, &x1));
            let y = Self::sub(&y0, &Self::mul(&div, &y1));

            r0 = r1;
            r1 = r;

            x0 = x1;
            x1 = x;

            y0 = y1;
            y1 = y;
        }

        (r0, x0, y0)
    }

    #[ndfwd::as_expr(|(x, y, z)| (Self::from(x), Self::from(y), Self::from(z)))]
    fn gcde_checked(lhs: Self, rhs: Self) -> Option<(Self, Self, Self)>
    where
        Self: NdOpsChecked<All = Self>,
    {
        let zero = Self::zero();
        let one = Self::one();

        let mut r0 = lhs;
        let mut r1 = rhs;
        let mut x0 = one.clone();
        let mut x1 = zero.clone();
        let mut y0 = zero.clone();
        let mut y1 = one.clone();

        while r1 != zero {
            let div = Self::div(&r0, &r1);

            let r = Self::sub_checked(&r0, &Self::mul_checked(&div, &r1)?)?;
            let x = Self::sub_checked(&x0, &Self::mul_checked(&div, &x1)?)?;
            let y = Self::sub_checked(&y0, &Self::mul_checked(&div, &y1)?)?;

            r0 = r1;
            r1 = r;

            x0 = x1;
            x1 = x;

            y0 = y1;
            y1 = y;
        }

        Some((r0, x0, y0))
    }

    #[ndfwd::as_into]
    fn lcm(lhs: Self, rhs: Self) -> Self {
        let val = Self::gcd(lhs.clone(), rhs.clone());
        let val = Self::div(&lhs, &val);

        Self::mul(&val, &rhs)
    }

    #[ndfwd::as_into]
    fn lcm_checked(lhs: Self, rhs: Self) -> Option<Self>
    where
        Self: NdOpsChecked<All = Self>,
    {
        let val = Self::gcd_checked(lhs.clone(), rhs.clone())?;
        let val = Self::div_checked(&lhs, &val)?;

        Self::mul_checked(&val, &rhs)
    }
}

#[ndfwd::decl]
pub trait Num: NumCore + Zero + One + Copy {}

#[ndfwd::decl]
pub trait NumDyn: NumCore {}

#[ndfwd::decl]
pub trait NumExt: NumCore {
    fn read(&self, offset: Offset) -> u64;

    #[ndfwd::as_self]
    fn write_bitor(&mut self, mask: u64, offset: Offset) -> &mut Self;

    #[ndfwd::as_self]
    fn write_bitand(&mut self, mask: u64, offset: Offset) -> &mut Self;

    #[ndfwd::as_self]
    fn write_bitxor(&mut self, mask: u64, offset: Offset) -> &mut Self;

    #[ndfwd::as_self]
    fn write_odd(&mut self) -> &mut Self {
        self.write_bitor(1, Offset::Left(0));
        self
    }

    #[ndfwd::as_self]
    fn write_even(&mut self) -> &mut Self {
        self.write_bitand(u64::MAX - 1, Offset::Left(0));
        self
    }

    #[ndfwd::as_self]
    fn write_alt(&mut self) -> &mut Self {
        self.write_bitxor(1, Offset::Left(0));
        self
    }

    #[ndfwd::as_into]
    fn into_bitor(mut self, mask: u64, offset: Offset) -> Self {
        self.write_bitor(mask, offset);
        self
    }

    #[ndfwd::as_into]
    fn into_bitand(mut self, mask: u64, offset: Offset) -> Self {
        self.write_bitand(mask, offset);
        self
    }

    #[ndfwd::as_into]
    fn into_bitxor(mut self, mask: u64, offset: Offset) -> Self {
        self.write_bitxor(mask, offset);
        self
    }

    #[ndfwd::as_into]
    fn into_odd(mut self) -> Self {
        self.write_odd();
        self
    }

    #[ndfwd::as_into]
    fn into_even(mut self) -> Self {
        self.write_even();
        self
    }

    #[ndfwd::as_into]
    fn into_alt(mut self) -> Self {
        self.write_alt();
        self
    }

    fn is_odd(&self) -> bool {
        self.read(Offset::Left(0)) & 1 != 0
    }

    fn is_even(&self) -> bool {
        self.read(Offset::Left(0)) & 1 == 0
    }

    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn rand<Rng: rand::Rng>(order: usize, rng: &mut Rng) -> Self {
        let shift = order - 1;
        let div = shift / 64;
        let rem = shift % 64;
        let bit = 1 << rem;

        let mut res = Self::zero();

        res.write_bitor(bit | (bit - 1) & rng.next_u64(), Offset::Left(div * 64));

        for idx in 0..div {
            res.write_bitor(rng.next_u64(), Offset::Left(idx * 64));
        }

        res
    }

    #[ndfwd::as_into]
    fn pow(self, mut exp: Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            if exp.is_odd() {
                Self::mul_assign(&mut res, &acc);
            }

            let val = acc.clone();

            Self::mul_assign(&mut acc, &val);
            Self::shr_assign(&mut exp, 1);
        }

        res
    }

    #[ndfwd::as_into]
    fn powrem(self, mut exp: Self, rem: &Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            if exp.is_odd() {
                Self::mul_assign(&mut res, &acc);
                Self::rem_assign(&mut res, rem);
            }

            let val = acc.clone();

            Self::mul_assign(&mut acc, &val);
            Self::rem_assign(&mut acc, rem);
            Self::shr_assign(&mut exp, 1);
        }

        res
    }
}

#[ndfwd::decl]
pub trait NumSigned: NumCore + From<i8> {}

#[ndfwd::decl]
pub trait NumUnsigned: NumCore + From<u8> {
    fn order(&self) -> usize;

    #[ndfwd::as_into]
    fn log(&self) -> Self;

    #[ndfwd::as_into]
    fn sqrt(&self) -> Self;
}

pub trait Modulus<N: Num>: Default + Debug + Clone + Copy {
    const MOD: N;
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

#[ndfwd::decl]
pub trait Binary {
    const BITS: usize;
    const BYTES: usize;
}

#[ndfwd::decl]
pub trait ZeroFn {
    #[ndfwd::as_into]
    fn zero() -> Self;
}

#[ndfwd::decl]
pub trait OneFn {
    #[ndfwd::as_into]
    fn one() -> Self;
}

#[ndfwd::decl]
pub trait MinFn {
    #[ndfwd::as_into]
    fn min() -> Self;
}

#[ndfwd::decl]
pub trait MaxFn {
    #[ndfwd::as_into]
    fn max() -> Self;
}

#[ndfwd::decl]
pub trait BinaryFn {
    fn bits(&self) -> usize;
    fn bytes(&self) -> usize;
}

#[cfg(feature = "const-time")]
pub trait EqCt {
    fn eq_ct(&self, other: &Self) -> MaskCt;
}

#[cfg(feature = "const-time")]
pub trait LtCt {
    fn lt_ct(&self, other: &Self) -> MaskCt;
}

#[cfg(feature = "const-time")]
pub trait GtCt {
    fn gt_ct(&self, other: &Self) -> MaskCt;
}

#[cfg(feature = "const-time")]
pub trait LeCt {
    fn le_ct(&self, other: &Self) -> MaskCt
    where
        Self: GtCt,
    {
        !self.gt_ct(other)
    }
}

#[cfg(feature = "const-time")]
pub trait GeCt {
    fn ge_ct(&self, other: &Self) -> MaskCt
    where
        Self: LtCt,
    {
        !self.lt_ct(other)
    }
}

#[cfg(feature = "const-time")]
pub trait CmpCt {
    fn cmp_ct(&self, other: &Self) -> SignCt
    where
        Self: EqCt + LtCt + GtCt,
    {
        let lt = self.lt_ct(other) as SignCt;
        let gt = self.gt_ct(other) as SignCt;

        lt | gt & 1
    }
}

#[cfg(feature = "const-time")]
pub trait MinCt: Copy {
    fn min_ct(&self, other: &Self) -> Self;
}

#[cfg(feature = "const-time")]
pub trait MaxCt: Copy {
    fn max_ct(&self, other: &Self) -> Self;
}

#[cfg(feature = "const-time")]
pub trait SelectCt: Copy {
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self;
}

num_impl!(@signed [i8, i16, i32, i64, i128, isize]);
num_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);

#[cfg(feature = "const-time")]
num_ct_impl!(@signed [i8:u8, i16:u16, i32:u32, i64:u64, i128:u128, isize:usize]);

#[cfg(feature = "const-time")]
num_ct_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);

#[cfg(target_pointer_width = "64")]
prime_impl!((u8, 1), (u16, 2), (u32, 5), (u64, 12), (u128, 20), (usize, 12));

#[cfg(target_pointer_width = "32")]
prime_impl!((u8, 1), (u16, 2), (u32, 5), (u64, 12), (u128, 20), (usize, 5));

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

ndops::all! { @stdbin (lhs: Sign, rhs: Sign) -> Sign, [* (lhs as i8) * (rhs as i8)] }

impl<N: Num + NumExt + NdOpsWrapping + NdOpsAssignWrapping> From<N> for Wrapping<N> {
    fn from(value: N) -> Self {
        Wrapping(value)
    }
}

impl<N: Num + NumExt + NdOpsSaturating + NdOpsAssignSaturating> From<N> for Saturating<N> {
    fn from(value: N) -> Self {
        Saturating(value)
    }
}

impl<N: Num + NumExt + NdOpsUnbounded + NdOpsAssignUnbounded> From<N> for Unbounded<N> {
    fn from(value: N) -> Self {
        Unbounded(value)
    }
}

impl<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize> From<N> for Width<N, BITS> {
    fn from(value: N) -> Self {
        Self(value).normalized()
    }
}

impl<N: Num + NumExt + NumUnsigned, M: Modulus<N>> From<N> for Modular<N, M> {
    fn from(value: N) -> Self {
        Self(value, PhantomData).normalized()
    }
}

impl<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize> Binary for Width<N, BITS> {
    const BITS: usize = BITS;
    const BYTES: usize = BITS / 8;
}

impl<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize> Width<N, BITS> {
    #[allow(unused)]
    const CHECK: () = assert!(0 < BITS && BITS <= N::BITS);

    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> &mut Self {
        if N::BITS <= BITS {
            return self;
        }

        let diff = N::BITS - BITS;
        let div = diff / 64;
        let rem = diff % 64;

        for idx in 0..div {
            self.write_bitand(0, Offset::Right((idx + 1) * 64));
        }

        self.write_bitand(u64::MAX.unbounded_shr(rem as u32), Offset::Right((div + 1) * 64));
        self
    }
}

impl<N: Num + NumExt + NumUnsigned, M: Modulus<N>> Modular<N, M> {
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> &mut Self {
        N::rem_assign(&mut self.0, &M::MOD);

        self
    }
}

impl<Any: Zero> ZeroFn for Any {
    fn zero() -> Self {
        Any::ZERO
    }
}

impl<Any: One> OneFn for Any {
    fn one() -> Self {
        Any::ONE
    }
}

impl<Any: Min> MinFn for Any {
    fn min() -> Self {
        Any::MIN
    }
}

impl<Any: Max> MaxFn for Any {
    fn max() -> Self {
        Any::MAX
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ext_gcd() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 40).map(|val| val + 1)) [
            (u64::gcd(val, 0), val),
            (u64::gcd(0, val), val),
            (u64::gcd(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 12,
            rhs in 1..=1 << 12,
        ) [
            (u64::gcd(lhs, rhs), u64::gcd(rhs, lhs)),
            (lhs % u64::gcd(lhs, rhs), 0),
            (rhs % u64::gcd(lhs, rhs), 0),
            (u64::gcd(lhs, rhs) * u64::lcm(lhs, rhs), lhs * rhs),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
              k in 1..=1 << 8,
        ) [
            (u64::gcd(k * lhs, k * rhs), k * u64::gcd(lhs, rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            {
                let gcd = u64::gcd(lhs, rhs);
                let limit = lhs.min(rhs);

                let res = (gcd + 1..limit.max(gcd + 1)).into_iter().any(|val| lhs.is_multiple_of(val) && rhs.is_multiple_of(val));

                (res, false)
            },
        ] }
    }

    #[test]
    fn ext_gcde() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 40).map(|val| val + 1)) [
            (i64::gcde(val, 0).0, val),
            (i64::gcde(0, val).0, val),
            (i64::gcde(val, val).0, val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 12,
            rhs in 1..=1 << 12,
        ) [
            (i64::gcde(lhs, rhs).0, i64::gcde(rhs, lhs).0),
            (lhs % i64::gcde(lhs, rhs).0, 0),
            (rhs % i64::gcde(lhs, rhs).0, 0),
            (i64::gcde(lhs, rhs).0 * i64::lcm(lhs, rhs), lhs * rhs),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
              k in 1..=1 << 8,
        ) [
            (i64::gcde(k * lhs, k * rhs).0, k * i64::gcde(lhs, rhs).0),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            {
                let gcde = i64::gcde(lhs, rhs).0;
                let limit = lhs.min(rhs);

                let res = (gcde + 1..limit.max(gcde + 1)).into_iter().any(|val| lhs % val == 0 && rhs % val == 0);

                (res, false)
            },
        ] }
    }

    #[test]
    fn ext_lcm() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 40).map(|val| val + 1)) [
            (u64::lcm(val, 0), 0),
            (u64::lcm(0, val), 0),
            (u64::lcm(val, 1), val),
            (u64::lcm(1, val), val),
            (u64::lcm(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 12,
            rhs in 1..=1 << 12,
        ) [
            (u64::lcm(lhs, rhs), u64::lcm(rhs, lhs)),
            (u64::lcm(lhs, rhs) % lhs, 0),
            (u64::lcm(lhs, rhs) % rhs, 0),
            (u64::lcm(lhs, rhs) * u64::gcd(lhs, rhs), lhs * rhs),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
              k in 1..=1 << 8,
        ) [
            (u64::lcm(k * lhs, k * rhs), k * u64::lcm(lhs, rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
        ) [
            {
                let lcm = u64::lcm(lhs, rhs);
                let limit = lhs.max(rhs);

                let res = (limit + 1..lcm.max(limit + 1)).into_iter().any(|val| val.is_multiple_of(lhs) && val.is_multiple_of(rhs));

                (res, false)
            },
        ] }
    }

    #[test]
    fn ext_pow() {}

    #[test]
    fn width() {}

    #[test]
    fn modular() {}
}

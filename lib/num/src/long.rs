#![doc = include_str!("../docs/long.md")]
#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    io::{Cursor, Write},
    marker::PhantomData,
    str::FromStr,
};

use ndext::{
    convert::{NdFrom, NdFromStr, NdTryFrom},
    iter::IteratorExt,
    ops::*,
};
use thiserror::Error;
use zerocopy::{IntoBytes, transmute_mut, transmute_ref};

use crate::{
    BytesFn, Max, Min, NdGcd, NdPow, NdRand, Num, NumFn, NumSigned, NumUnsigned, One, Sign, Zero,
    arch::{AsBytesMut, AsBytesRef, AsWordsIterator, AsWordsMut, AsWordsRef, BytesLen, Offset, word::*},
    long::{radix::*, uops::Expr},
};
#[cfg(feature = "const-time")]
use crate::{EqCt, GtCt, LtCt, MaskCt, RelCt, SelectCt, ZeroCt};

macro_rules! signed {
    ($bits:expr) => {
        $crate::long::Signed<{ ($bits as usize).div_ceil($crate::arch::word::BITS as usize) }>
    };
}

macro_rules! unsigned {
    ($bits:expr) => {
        $crate::long::Unsigned<{ ($bits as usize).div_ceil($crate::arch::word::BITS as usize) }>
    };
}

macro_rules! bytes {
    ($bits:expr) => {
        $crate::long::Bytes<{ ($bits as usize).div_ceil($crate::arch::word::BITS as usize) }>
    };
}

#[cfg(feature = "const-time")]
macro_rules! eq_ct {
    ($lhs:expr, $rhs:expr) => {{
        let diff = $lhs.zip($rhs).map(|(a, b)| a ^ b).fold(0, |acc, cmp| acc | cmp);

        std::hint::black_box(diff).zero_ct() as MaskCt
    }};
}

#[cfg(feature = "const-time")]
macro_rules! cmp_ct {
    ($lhs:expr, $rhs:expr) => {{
        let (lt, gt) =
            $lhs.zip($rhs)
                .map(|(a, b)| ((a < b) as i8, (a > b) as i8))
                .fold((0i8, 0i8), |(lt_, gt_), (lt, gt)| {
                    let eq = !lt & !gt;
                    let lt = lt_ & eq | lt;
                    let gt = gt_ & eq | gt;

                    (lt, gt)
                });

        std::hint::black_box(gt - lt) as RelCt
    }};
}

macro_rules! from_primitive {
    ($long:ident [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!($long, $primitive);)+
    };
    ($long:ident, $primitive:ty $(,)?) => {
        impl<const L: usize> From<$primitive> for $long<L> {
            #[inline]
            fn from(value: $primitive) -> Self {
                #![allow(unused_comparisons)]

                let bytes = value.to_le_bytes();
                let res = from_arr(&bytes, if value >= 0 { 0 } else { MAX });

                Self(res)
            }
        }
    };
}

macro_rules! from_primitive_const {
    ([$(($fn:ident, $primitive:ty)),+ $(,)?]) => {
        $(from_primitive_const!($fn, $primitive);)+
    };
    ($fn:ident, $primitive:ty $(,)?) => {
        /// Creates long number/bytes from primitive.
        ///
        /// Truncates on overflow.
        ///
        /// **Must** be used **ONLY** in const context.
        #[inline]
        pub const fn $fn(value: $primitive) -> Self {
            #![allow(unused_comparisons)]

            let default = if value >= 0 { 0 } else { MAX };

            let mut val = value as u128;
            let mut idx = 0;
            let mut res = [default; L];

            while idx < L && val > 0 {
                res[idx] = val as Single;
                idx += 1;
                val = val.unbounded_shr(BITS as u32);
            }

            Self(res)
        }
    };
}

macro_rules! from_str_impl {
    (@radix $str:expr, $radix:ty) => {{
        let (s, sign) = get_sign_from_str($str)?;
        let (s, radix) = get_radix_from_str(s, <$radix>::VALUE)?;

        if radix != <$radix>::VALUE {
            return Err(FromStrError::InvalidRadix { radix: radix as usize });
        }

        match radix.is_pow2() {
            false => from_str_radix(s, radix, sign),
            true => from_str(s, radix.order() as u8, sign),
        }
    }};
    (@long $str:expr) => {{
        let (s, sign) = get_sign_from_str($str)?;
        let (s, radix) = get_radix_from_str(s, 10)?;

        match radix.is_pow2() {
            false => from_str_radix(s, radix, sign),
            true => from_str(s, radix.order() as u8, sign),
        }
    }};
    (@bytes $str:expr) => {{
        let (s, radix) = get_radix_from_str($str, 16)?;

        match radix.is_pow2() {
            false => Err(FromStrError::InvalidRadix { radix: radix as usize }),
            true => from_str(s, radix.order() as u8, Sign::POS),
        }
    }};
}

macro_rules! nd_ops_primitive_impl {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_primitive_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_primitive_impl!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_primitive_impl!(@bytes $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, &rhs: &$primitive) -> Signed<L> for [Signed<L>, $primitive], [
            + uops::add_iter(lhs.0.iter().copied(), rhs.iter_words_default(if rhs < 0 { MAX } else { 0 })).with(Signed),
            - uops::sub_iter(lhs.0.iter().copied(), rhs.iter_words_default(if rhs < 0 { MAX } else { 0 })).with(Signed),

            * algo::mul(&lhs.0, &Signed::from(rhs).0).with(Signed),

            / algo::div(&lhs.abs().0, &Signed::from(rhs.wrapping_abs()).0).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed(res).signed(lhs.sign())).0,
            % algo::div(&lhs.abs().0, &Signed::from(rhs.wrapping_abs()).0).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed(res).signed(lhs.sign())).1,

            | uops::bitor(&lhs.0, &Signed::from(rhs).0).eval(),
            & uops::bitand(&lhs.0, &Signed::from(rhs).0).eval(),
            ^ uops::bitxor(&lhs.0, &Signed::from(rhs).0).eval(),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Signed<L>) -> Signed<L> for [Signed<L>, $primitive], [
            + uops::add_iter(lhs.iter_words_default(if lhs < 0 { MAX } else { 0 }), rhs.0.iter().copied()).with(Signed),

            * algo::mul(&Signed::from(lhs).0, &rhs.0).with(Signed),

            | uops::bitor(&Signed::from(lhs).0, &rhs.0).eval(),
            & uops::bitand(&Signed::from(lhs).0, &rhs.0).eval(),
            ^ uops::bitxor(&Signed::from(lhs).0, &rhs.0).eval(),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, &rhs: &$primitive), [
            += uops::add_iter(lhs.0.iter_mut(), rhs.iter_words_default(if rhs < 0 { MAX } else { 0 })).eval(),
            -= uops::sub_iter(lhs.0.iter_mut(), rhs.iter_words_default(if rhs < 0 { MAX } else { 0 })).eval(),

            *= algo::mul(&mut lhs.0, &Signed::from(rhs).0).eval(),

            /= { *lhs = algo::div(&lhs.abs().0, &Signed::from(rhs.wrapping_abs()).0).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed(res).signed(lhs.sign())).0; },
            %= { *lhs = algo::div(&lhs.abs().0, &Signed::from(rhs.wrapping_abs()).0).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed(res).signed(lhs.sign())).1; },

            |= uops::bitor(&mut lhs.0, &Signed::from(rhs).0).eval(),
            &= uops::bitand(&mut lhs.0, &Signed::from(rhs).0).eval(),
            ^= uops::bitxor(&mut lhs.0, &Signed::from(rhs).0).eval(),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, &rhs: &$primitive) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add_iter(lhs.0.iter().copied(), rhs.iter_words()).with(Unsigned),
            - uops::sub_iter(lhs.0.iter().copied(), rhs.iter_words()).with(Unsigned),

            * algo::mul(&lhs.0, &Unsigned::from(rhs).0).with(Unsigned),

            / algo::div(&lhs.0, &Unsigned::from(rhs).0).wrapping(Unsigned, Unsigned).0,
            % algo::div(&lhs.0, &Unsigned::from(rhs).0).wrapping(Unsigned, Unsigned).1,

            | uops::bitor(&lhs.0, &Unsigned::from(rhs).0).eval(),
            & uops::bitand(&lhs.0, &Unsigned::from(rhs).0).eval(),
            ^ uops::bitxor(&lhs.0, &Unsigned::from(rhs).0).eval(),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Unsigned<L>) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add_iter(lhs.iter_words(), rhs.0.iter().copied()).with(Unsigned),

            * algo::mul(&Unsigned::from(lhs).0, &rhs.0).with(Unsigned),

            | uops::bitor(&Unsigned::from(lhs).0, &rhs.0).eval(),
            & uops::bitand(&Unsigned::from(lhs).0, &rhs.0).eval(),
            ^ uops::bitxor(&Unsigned::from(lhs).0, &rhs.0).eval(),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, &rhs: &$primitive), [
            += uops::add_iter(lhs.0.iter_mut(), rhs.iter_words()).eval(),
            -= uops::sub_iter(lhs.0.iter_mut(), rhs.iter_words()).eval(),

            *= algo::mul(&mut lhs.0, &Unsigned::from(rhs).0).eval(),

            /= algo::div_mut(&mut lhs.0, &Unsigned::from(rhs).0).wrapping(),
            %= algo::rem_mut(&mut lhs.0, &Unsigned::from(rhs).0).wrapping(),

            |= uops::bitor(&mut lhs.0, &Unsigned::from(rhs).0).eval(),
            &= uops::bitand(&mut lhs.0, &Unsigned::from(rhs).0).eval(),
            ^= uops::bitxor(&mut lhs.0, &Unsigned::from(rhs).0).eval(),
        ] }
    };
    (@bytes $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, &rhs: &$primitive) -> Bytes<L> for [Bytes<L>, $primitive], [
            | uops::bitor(&lhs.0, &Bytes::from(rhs).0).eval(),
            & uops::bitand(&lhs.0, &Bytes::from(rhs).0).eval(),
            ^ uops::bitxor(&lhs.0, &Bytes::from(rhs).0).eval(),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Bytes<L>) -> Bytes<L> for [Bytes<L>, $primitive], [
            | uops::bitor(&Bytes::from(lhs).0, &rhs.0).eval(),
            & uops::bitand(&Bytes::from(lhs).0, &rhs.0).eval(),
            ^ uops::bitxor(&Bytes::from(lhs).0, &rhs.0).eval(),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, &rhs: &$primitive), [
            |= uops::bitor(&mut lhs.0, &Bytes::from(rhs).0).eval(),
            &= uops::bitand(&mut lhs.0, &Bytes::from(rhs).0).eval(),
            ^= uops::bitxor(&mut lhs.0, &Bytes::from(rhs).0).eval(),
        ] }
    };
}

macro_rules! nd_ops_primitive_native_impl {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_primitive_native_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_primitive_native_impl!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_primitive_native_impl!(@bytes $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, &rhs: &$primitive) -> Signed<L> for [Signed<L>, $primitive], [
            + uops::add(&lhs.0, rhs as <Single as Num>::Signed).with(Signed),
            - uops::sub(&lhs.0, rhs as <Single as Num>::Signed).with(Signed),
            * algo::mul(&lhs.0, rhs as <Single as Num>::Signed).with(Signed),

            / algo::div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed::<L>::from(res as $primitive).signed(lhs.sign())).0,
            % algo::div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed::<L>::from(res as $primitive).signed(lhs.sign())).1,

            | uops::bitor(&lhs.0, rhs as <Single as Num>::Signed).eval(),
            & uops::bitand(&lhs.0, rhs as <Single as Num>::Signed).eval(),
            ^ uops::bitxor(&lhs.0, rhs as <Single as Num>::Signed).eval(),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Signed<L>) -> Signed<L> for [Signed<L>, $primitive], [
            + uops::add(&rhs.0, lhs as <Single as Num>::Signed).with(Signed),
            * algo::mul(&rhs.0, lhs as <Single as Num>::Signed).with(Signed),

            | uops::bitor(&rhs.0, lhs as <Single as Num>::Signed).eval(),
            & uops::bitand(&rhs.0, lhs as <Single as Num>::Signed).eval(),
            ^ uops::bitxor(&rhs.0, lhs as <Single as Num>::Signed).eval(),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, &rhs: &$primitive), [
            += uops::add(&mut lhs.0, rhs as <Single as Num>::Signed).eval(),
            -= uops::sub(&mut lhs.0, rhs as <Single as Num>::Signed).eval(),
            *= algo::mul(&mut lhs.0, rhs as <Single as Num>::Signed).eval(),

            /= { *lhs = algo::div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed::<L>::from(res as $primitive).signed(lhs.sign())).0; },
            %= { *lhs = algo::div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).wrapping(|res| Signed(res).signed(lhs.sign() * Sign::from(rhs)), |res| Signed::<L>::from(res as $primitive).signed(lhs.sign())).1; },

            |= uops::bitor(&mut lhs.0, rhs as <Single as Num>::Signed).eval(),
            &= uops::bitand(&mut lhs.0, rhs as <Single as Num>::Signed).eval(),
            ^= uops::bitxor(&mut lhs.0, rhs as <Single as Num>::Signed).eval(),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, &rhs: &$primitive) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add(&lhs.0, rhs as Single).with(Unsigned),
            - uops::sub(&lhs.0, rhs as Single).with(Unsigned),
            * algo::mul(&lhs.0, rhs as Single).with(Unsigned),

            / algo::div_single(&lhs.0, rhs as Single).wrapping(Unsigned, Unsigned::<L>::from).0,
            % algo::div_single(&lhs.0, rhs as Single).wrapping(Unsigned, Unsigned::<L>::from).1,

            | uops::bitor(&lhs.0, rhs as Single).eval(),
            & uops::bitand(&lhs.0, rhs as Single).eval(),
            ^ uops::bitxor(&lhs.0, rhs as Single).eval(),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Unsigned<L>) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add(&rhs.0, lhs as Single).with(Unsigned),
            * algo::mul(&rhs.0, lhs as Single).with(Unsigned),

            | uops::bitor(&rhs.0, lhs as Single).eval(),
            & uops::bitand(&rhs.0, lhs as Single).eval(),
            ^ uops::bitxor(&rhs.0, lhs as Single).eval(),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, &rhs: &$primitive), [
            += uops::add(&mut lhs.0, rhs as Single).eval(),
            -= uops::sub(&mut lhs.0, rhs as Single).eval(),
            *= algo::mul(&mut lhs.0, rhs as Single).eval(),

            /= algo::div_single_mut(&mut lhs.0, rhs as Single).wrapping(),
            %= algo::rem_single_mut(&mut lhs.0, rhs as Single).wrapping(),

            |= uops::bitor(&mut lhs.0, rhs as Single).eval(),
            &= uops::bitand(&mut lhs.0, rhs as Single).eval(),
            ^= uops::bitxor(&mut lhs.0, rhs as Single).eval(),
        ] }
    };
    (@bytes $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, &rhs: &$primitive) -> Bytes<L> for [Bytes<L>, $primitive], [
            | uops::bitor(&lhs.0, rhs as Single).eval(),
            & uops::bitand(&lhs.0, rhs as Single).eval(),
            ^ uops::bitxor(&lhs.0, rhs as Single).eval(),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Bytes<L>) -> Bytes<L> for [Bytes<L>, $primitive], [
            | uops::bitor(&rhs.0, lhs as Single).eval(),
            & uops::bitand(&rhs.0, lhs as Single).eval(),
            ^ uops::bitxor(&rhs.0, lhs as Single).eval(),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, &rhs: &$primitive), [
            |= uops::bitor(&mut lhs.0, rhs as Single).eval(),
            &= uops::bitand(&mut lhs.0, rhs as Single).eval(),
            ^= uops::bitxor(&mut lhs.0, rhs as Single).eval(),
        ] }
    };
}

macro_rules! ops_primitive_impl {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(ops_primitive_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(ops_primitive_impl!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty),+ $(,)?]) => {
        $(ops_primitive_impl!(@bytes $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
        ndops::def! { @stdbin <const L: usize> (*lhs: &Signed<L>, rhs: $primitive) -> Signed<L>, [
            + <Signed<L> as NdAdd<Signed<L>, $primitive>>::nd_add(&lhs, &rhs),
            - <Signed<L> as NdSub<Signed<L>, $primitive>>::nd_sub(&lhs, &rhs),
            * <Signed<L> as NdMul<Signed<L>, $primitive>>::nd_mul(&lhs, &rhs),
            / <Signed<L> as NdDiv<Signed<L>, $primitive>>::nd_div(&lhs, &rhs),
            % <Signed<L> as NdRem<Signed<L>, $primitive>>::nd_rem(&lhs, &rhs),
            | <Signed<L> as NdBitOr<Signed<L>, $primitive>>::nd_bitor(&lhs, &rhs),
            & <Signed<L> as NdBitAnd<Signed<L>, $primitive>>::nd_bitand(&lhs, &rhs),
            ^ <Signed<L> as NdBitXor<Signed<L>, $primitive>>::nd_bitxor(&lhs, &rhs),
        ] }

        ndops::def! { @stdbin <const L: usize> (lhs: $primitive, *rhs: &Signed<L>) -> Signed<L>, [
            + <Signed<L> as NdAdd<Signed<L>, $primitive>>::nd_add(&rhs, &lhs),
            * <Signed<L> as NdMul<Signed<L>, $primitive>>::nd_mul(&rhs, &lhs),
            | <Signed<L> as NdBitOr<Signed<L>, $primitive>>::nd_bitor(&rhs, &lhs),
            & <Signed<L> as NdBitAnd<Signed<L>, $primitive>>::nd_bitand(&rhs, &lhs),
            ^ <Signed<L> as NdBitXor<Signed<L>, $primitive>>::nd_bitxor(&rhs, &lhs),
        ] }

        ndops::def! { @stdmut <const L: usize> (lhs: &mut Signed<L>, rhs: $primitive), [
            += <Signed<L> as NdAddAssign<Signed<L>, $primitive>>::nd_add_assign(lhs, &rhs),
            -= <Signed<L> as NdSubAssign<Signed<L>, $primitive>>::nd_sub_assign(lhs, &rhs),
            *= <Signed<L> as NdMulAssign<Signed<L>, $primitive>>::nd_mul_assign(lhs, &rhs),
            /= <Signed<L> as NdDivAssign<Signed<L>, $primitive>>::nd_div_assign(lhs, &rhs),
            %= <Signed<L> as NdRemAssign<Signed<L>, $primitive>>::nd_rem_assign(lhs, &rhs),
            |= <Signed<L> as NdBitOrAssign<Signed<L>, $primitive>>::nd_bitor_assign(lhs, &rhs),
            &= <Signed<L> as NdBitAndAssign<Signed<L>, $primitive>>::nd_bitand_assign(lhs, &rhs),
            ^= <Signed<L> as NdBitXorAssign<Signed<L>, $primitive>>::nd_bitxor_assign(lhs, &rhs),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @stdbin <const L: usize> (*lhs: &Unsigned<L>, rhs: $primitive) -> Unsigned<L>, [
            + <Unsigned<L> as NdAdd<Unsigned<L>, $primitive>>::nd_add(&lhs, &rhs),
            - <Unsigned<L> as NdSub<Unsigned<L>, $primitive>>::nd_sub(&lhs, &rhs),
            * <Unsigned<L> as NdMul<Unsigned<L>, $primitive>>::nd_mul(&lhs, &rhs),
            / <Unsigned<L> as NdDiv<Unsigned<L>, $primitive>>::nd_div(&lhs, &rhs),
            % <Unsigned<L> as NdRem<Unsigned<L>, $primitive>>::nd_rem(&lhs, &rhs),
            | <Unsigned<L> as NdBitOr<Unsigned<L>, $primitive>>::nd_bitor(&lhs, &rhs),
            & <Unsigned<L> as NdBitAnd<Unsigned<L>, $primitive>>::nd_bitand(&lhs, &rhs),
            ^ <Unsigned<L> as NdBitXor<Unsigned<L>, $primitive>>::nd_bitxor(&lhs, &rhs),
        ] }

        ndops::def! { @stdbin <const L: usize> (lhs: $primitive, *rhs: &Unsigned<L>) -> Unsigned<L>, [
            + <Unsigned<L> as NdAdd<Unsigned<L>, $primitive>>::nd_add(&rhs, &lhs),
            * <Unsigned<L> as NdMul<Unsigned<L>, $primitive>>::nd_mul(&rhs, &lhs),
            | <Unsigned<L> as NdBitOr<Unsigned<L>, $primitive>>::nd_bitor(&rhs, &lhs),
            & <Unsigned<L> as NdBitAnd<Unsigned<L>, $primitive>>::nd_bitand(&rhs, &lhs),
            ^ <Unsigned<L> as NdBitXor<Unsigned<L>, $primitive>>::nd_bitxor(&rhs, &lhs),
        ] }

        ndops::def! { @stdmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: $primitive), [
            += <Unsigned<L> as NdAddAssign<Unsigned<L>, $primitive>>::nd_add_assign(lhs, &rhs),
            -= <Unsigned<L> as NdSubAssign<Unsigned<L>, $primitive>>::nd_sub_assign(lhs, &rhs),
            *= <Unsigned<L> as NdMulAssign<Unsigned<L>, $primitive>>::nd_mul_assign(lhs, &rhs),
            /= <Unsigned<L> as NdDivAssign<Unsigned<L>, $primitive>>::nd_div_assign(lhs, &rhs),
            %= <Unsigned<L> as NdRemAssign<Unsigned<L>, $primitive>>::nd_rem_assign(lhs, &rhs),
            |= <Unsigned<L> as NdBitOrAssign<Unsigned<L>, $primitive>>::nd_bitor_assign(lhs, &rhs),
            &= <Unsigned<L> as NdBitAndAssign<Unsigned<L>, $primitive>>::nd_bitand_assign(lhs, &rhs),
            ^= <Unsigned<L> as NdBitXorAssign<Unsigned<L>, $primitive>>::nd_bitxor_assign(lhs, &rhs),
        ] }
    };
    (@bytes $primitive:ty $(,)?) => {
        ndops::def! { @stdbin <const L: usize> (*lhs: &Bytes<L>, rhs: $primitive) -> Bytes<L>, [
            | <Bytes<L> as NdBitOr<Bytes<L>, $primitive>>::nd_bitor(&lhs, &rhs),
            & <Bytes<L> as NdBitAnd<Bytes<L>, $primitive>>::nd_bitand(&lhs, &rhs),
            ^ <Bytes<L> as NdBitXor<Bytes<L>, $primitive>>::nd_bitxor(&lhs, &rhs),
        ] }

        ndops::def! { @stdbin <const L: usize> (lhs: $primitive, *rhs: &Bytes<L>) -> Bytes<L>, [
            | <Bytes<L> as NdBitOr<Bytes<L>, $primitive>>::nd_bitor(&rhs, &lhs),
            & <Bytes<L> as NdBitAnd<Bytes<L>, $primitive>>::nd_bitand(&rhs, &lhs),
            ^ <Bytes<L> as NdBitXor<Bytes<L>, $primitive>>::nd_bitxor(&rhs, &lhs),
        ] }

        ndops::def! { @stdmut <const L: usize> (lhs: &mut Bytes<L>, rhs: $primitive), [
            |= <Bytes<L> as NdBitOrAssign<Bytes<L>, $primitive>>::nd_bitor_assign(lhs, &rhs),
            &= <Bytes<L> as NdBitAndAssign<Bytes<L>, $primitive>>::nd_bitand_assign(lhs, &rhs),
            ^= <Bytes<L> as NdBitXorAssign<Bytes<L>, $primitive>>::nd_bitxor_assign(lhs, &rhs),
        ] }
    };
}

macro_rules! write_bitop_impl {
    ($words:expr, $mask:expr, $offset:expr, $op:tt $(, $($mod:tt)*)?) => {{
        let mask = $mask;
        let offset = $offset;

        let bits = u64::BITS as usize;

        #[allow(unused_mut)]
        let mut res = $words;

        for idx in 0..bits.div_ceil(BITS) {
            let shift = idx * BITS;
            let mask = ((mask >> shift) as Single) $($($mod)*)?;

            let shl = offset % BITS;
            let shr = BITS - shl;

            if let Some(elem) = res.get_mut((offset + shift) / BITS) {
                *elem $op mask.unbounded_shl(shl as u32) $($($mod)*)?;
            }

            if let Some(elem) = res.get_mut((offset + shift) / BITS + 1) {
                *elem $op mask.unbounded_shr(shr as u32) $($($mod)*)?;
            }
        }
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

#[allow(unused)]
fn search<N: Num, F: Fn(N) -> bool>(l: N, r: N, f: F) -> N {
    let mut idx = N::ZERO;
    let mut len = N::nd_sub(&r, &l);

    while len > N::ZERO {
        let half = N::nd_shr(&len, 1);
        let diff = [N::ZERO, N::nd_sub(&len, &half)][f(N::nd_add(&idx, &half)) as usize];

        N::nd_add_assign(&mut idx, &diff);

        len = half;
    }

    idx
}

macro_rules! search {
    (@min $l:expr, $r:expr, $fn:expr) => {{
        let mut l = $l;
        let mut r = $r;

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
    (@max $l:expr, $r:expr, $fn:expr) => {{
        let mut l = $l;
        let mut r = $r;

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

macro_rules! length {
    ($words:expr) => {
        length!($words, &0)
    };
    ($words:expr, $zero:expr) => {{
        let mut res = 0;

        for (i, word) in $words.iter().enumerate().rev() {
            if word != $zero {
                res = i + 1;

                break;
            }
        }

        res
    }};
}

pub mod alias {
    //! # Alias
    //!
    //! **Long aliases**

    /// Signed long of at least 8-bits length.
    pub type S8 = signed!(8);

    /// Signed long of at least 12-bits length.
    pub type S12 = signed!(12);

    /// Signed long of at least 16-bits length.
    pub type S16 = signed!(16);

    /// Signed long of at least 24-bits length.
    pub type S24 = signed!(24);

    /// Signed long of at least 32-bits length.
    pub type S32 = signed!(32);

    /// Signed long of at least 48-bits length.
    pub type S48 = signed!(48);

    /// Signed long of at least 64-bits length.
    pub type S64 = signed!(64);

    /// Signed long of at least 96-bits length.
    pub type S96 = signed!(96);

    /// Signed long of at least 128-bits length.
    pub type S128 = signed!(128);

    /// Signed long of at least 192-bits length.
    pub type S192 = signed!(192);

    /// Signed long of at least 256-bits length.
    pub type S256 = signed!(256);

    /// Signed long of at least 384-bits length.
    pub type S384 = signed!(384);

    /// Signed long of at least 512-bits length.
    pub type S512 = signed!(512);

    /// Signed long of at least 768-bits length.
    pub type S768 = signed!(768);

    /// Signed long of at least 1024-bits length.
    pub type S1024 = signed!(1024);

    /// Signed long of at least 1536-bits length.
    pub type S1536 = signed!(1536);

    /// Signed long of at least 2048-bits length.
    pub type S2048 = signed!(2048);

    /// Signed long of at least 3072-bits length.
    pub type S3072 = signed!(3072);

    /// Signed long of at least 4096-bits length.
    pub type S4096 = signed!(4096);

    /// Signed long of at least 6144-bits length.
    pub type S6144 = signed!(6144);

    /// Signed long of at least 8192-bits length.
    pub type S8192 = signed!(8192);

    /// Signed long of at least 12288-bits length.
    pub type S12288 = signed!(12288);

    /// Signed long of at least 16384-bits length.
    pub type S16384 = signed!(16384);

    /// Unsigned long of at least 8-bits length.
    pub type U8 = unsigned!(8);

    /// Unsigned long of at least 12-bits length.
    pub type U12 = unsigned!(12);

    /// Unsigned long of at least 16-bits length.
    pub type U16 = unsigned!(16);

    /// Unsigned long of at least 24-bits length.
    pub type U24 = unsigned!(24);

    /// Unsigned long of at least 32-bits length.
    pub type U32 = unsigned!(32);

    /// Unsigned long of at least 48-bits length.
    pub type U48 = unsigned!(48);

    /// Unsigned long of at least 64-bits length.
    pub type U64 = unsigned!(64);

    /// Unsigned long of at least 96-bits length.
    pub type U96 = unsigned!(96);

    /// Unsigned long of at least 128-bits length.
    pub type U128 = unsigned!(128);

    /// Unsigned long of at least 192-bits length.
    pub type U192 = unsigned!(192);

    /// Unsigned long of at least 256-bits length.
    pub type U256 = unsigned!(256);

    /// Unsigned long of at least 384-bits length.
    pub type U384 = unsigned!(384);

    /// Unsigned long of at least 512-bits length.
    pub type U512 = unsigned!(512);

    /// Unsigned long of at least 768-bits length.
    pub type U768 = unsigned!(768);

    /// Unsigned long of at least 1024-bits length.
    pub type U1024 = unsigned!(1024);

    /// Unsigned long of at least 1536-bits length.
    pub type U1536 = unsigned!(1536);

    /// Unsigned long of at least 2048-bits length.
    pub type U2048 = unsigned!(2048);

    /// Unsigned long of at least 3072-bits length.
    pub type U3072 = unsigned!(3072);

    /// Unsigned long of at least 4096-bits length.
    pub type U4096 = unsigned!(4096);

    /// Unsigned long of at least 6144-bits length.
    pub type U6144 = unsigned!(6144);

    /// Unsigned long of at least 8192-bits length.
    pub type U8192 = unsigned!(8192);

    /// Unsigned long of at least 12288-bits length.
    pub type U12288 = unsigned!(12288);

    /// Unsigned long of at least 16384-bits length.
    pub type U16384 = unsigned!(16384);

    /// Bytes long of at least 8-bits length.
    pub type B8 = bytes!(8);

    /// Bytes long of at least 12-bits length.
    pub type B12 = bytes!(12);

    /// Bytes long of at least 16-bits length.
    pub type B16 = bytes!(16);

    /// Bytes long of at least 24-bits length.
    pub type B24 = bytes!(24);

    /// Bytes long of at least 32-bits length.
    pub type B32 = bytes!(32);

    /// Bytes long of at least 48-bits length.
    pub type B48 = bytes!(48);

    /// Bytes long of at least 64-bits length.
    pub type B64 = bytes!(64);

    /// Bytes long of at least 96-bits length.
    pub type B96 = bytes!(96);

    /// Bytes long of at least 128-bits length.
    pub type B128 = bytes!(128);

    /// Bytes long of at least 192-bits length.
    pub type B192 = bytes!(192);

    /// Bytes long of at least 256-bits length.
    pub type B256 = bytes!(256);

    /// Bytes long of at least 384-bits length.
    pub type B384 = bytes!(384);

    /// Bytes long of at least 512-bits length.
    pub type B512 = bytes!(512);

    /// Bytes long of at least 768-bits length.
    pub type B768 = bytes!(768);

    /// Bytes long of at least 1024-bits length.
    pub type B1024 = bytes!(1024);

    /// Bytes long of at least 1536-bits length.
    pub type B1536 = bytes!(1536);

    /// Bytes long of at least 2048-bits length.
    pub type B2048 = bytes!(2048);

    /// Bytes long of at least 3072-bits length.
    pub type B3072 = bytes!(3072);

    /// Bytes long of at least 4096-bits length.
    pub type B4096 = bytes!(4096);

    /// Bytes long of at least 6144-bits length.
    pub type B6144 = bytes!(6144);

    /// Bytes long of at least 8192-bits length.
    pub type B8192 = bytes!(8192);

    /// Bytes long of at least 12288-bits length.
    pub type B12288 = bytes!(12288);

    /// Bytes long of at least 16384-bits length.
    pub type B16384 = bytes!(16384);
}

pub mod radix {
    //! # Radix
    //!
    //! **Radix related definitions**

    use super::*;

    /// Dec Radix.
    pub struct Dec;

    /// Bin Radix.
    pub struct Bin;

    /// Oct Radix.
    pub struct Oct;

    /// Hex Radix.
    pub struct Hex;

    /// Arbitrary Radix.
    pub struct Radix {
        /// Radix prefix in string.
        pub prefix: &'static str,

        /// Radix of a single entry to iterate when building a string.
        pub value: Double,

        /// Width of a single entry at `RADIX` when building a string.
        pub width: u8,
    }

    #[rustfmt::skip]
    impl Dec {
        /// Dec radix prefix in a string.
        pub const PREFIX: &str = "";

        /// Dec radix of a single entry to iterate when building a string.
        pub const RADIX: Double = DEC_RADIX;

        /// Dec width of a single entry at `RADIX` when building a string.
        pub const WIDTH: u8 = DEC_WIDTH;

        /// Dec radix value base.
        pub const VALUE: u8 = 10;
    }

    #[rustfmt::skip]
    impl Bin {
        /// Exponent of a radix, i.e. `RADIX = 1 << EXP`.
        pub const EXP: u8 = RADIX.ilog2() as u8;

        /// Bin radix prefix in a string.
        pub const PREFIX: &str = "0b";

        /// Bin radix of a single entry to iterate when building a string.
        pub const RADIX: Double = RADIX;

        /// Bin width of a single entry at `RADIX` when building a string.
        pub const WIDTH: u8 = BITS as u8;

        /// Bin radix value base.
        pub const VALUE: u8 = 2;
    }

    #[rustfmt::skip]
    impl Oct {
        /// Exponent of a radix, i.e. `RADIX = 1 << EXP`.
        pub const EXP: u8 = OCT_RADIX.ilog2() as u8;

        /// Oct radix prefix in a string.
        pub const PREFIX: &str = "0o";

        /// Oct radix of a single entry to iterate when building a string.
        pub const RADIX: Double = OCT_RADIX;

        /// Oct width of a single entry at `RADIX` when building a string.
        pub const WIDTH: u8 = OCT_WIDTH;

        /// Oct radix value base.
        pub const VALUE: u8 = 8;
    }

    #[rustfmt::skip]
    impl Hex {
        /// Exponent of a radix, i.e. `RADIX = 1 << EXP`.
        pub const EXP: u8 = RADIX.ilog2() as u8;

        /// Hex radix prefix in a string.
        pub const PREFIX: &str = "0x";

        /// Hex radix of a single entry to iterate when building a string.
        pub const RADIX: Double = RADIX;

        /// Hex width of a single entry at `RADIX` when building a string.
        pub const WIDTH: u8 = BITS as u8 / 4;

        /// Hex radix value base.
        pub const VALUE: u8 = 16;
    }

    impl From<Dec> for Radix {
        #[inline]
        fn from(_: Dec) -> Self {
            Self {
                prefix: Dec::PREFIX,
                value: Dec::RADIX,
                width: Dec::WIDTH,
            }
        }
    }

    impl From<Bin> for Radix {
        #[inline]
        fn from(_: Bin) -> Self {
            Self {
                prefix: Bin::PREFIX,
                value: Bin::RADIX,
                width: Bin::WIDTH,
            }
        }
    }

    impl From<Oct> for Radix {
        #[inline]
        fn from(_: Oct) -> Self {
            Self {
                prefix: Oct::PREFIX,
                value: Oct::RADIX,
                width: Oct::WIDTH,
            }
        }
    }

    impl From<Hex> for Radix {
        #[inline]
        fn from(_: Hex) -> Self {
            Self {
                prefix: Hex::PREFIX,
                value: Hex::RADIX,
                width: Hex::WIDTH,
            }
        }
    }
}

pub mod uops {
    //! # Uops
    //!
    //! **Long numbers/bytes uops**

    use super::*;

    /// Expression iterator for uops.
    ///
    /// Yields `lhs * mul + rhs + acc`.
    pub struct ExprIter<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> {
        /// Lhs iterator.
        pub lhs: Lhs,

        /// Rhs iterator.
        pub rhs: Rhs,

        /// Multiplier.
        pub mul: Single,

        /// Accumulator.
        pub acc: Single,
    }

    /// Expression iterator mutable for uops.
    ///
    /// Yields `lhs * mul + rhs + acc`.
    pub struct ExprIterMut<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> {
        /// Lhs iterator.
        pub lhs: Lhs,

        /// Rhs iterator.
        pub rhs: Rhs,

        /// Multiplier.
        pub mul: Single,

        /// Accumulator.
        pub acc: Single,
    }

    /// Not iterator expression.
    pub struct NotIter<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Pos iterator expression.
    pub struct PosIter<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Neg iterator expression.
    pub struct NegIter<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Not value expression.
    pub struct Not<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Pos value expression.
    pub struct Pos<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Neg value expression.
    pub struct Neg<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Pos (forced) value expression.
    pub struct Posx<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Neg (forced) value expression.
    pub struct Negx<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Sign (forced) expression.
    pub struct Sgx<Words> {
        /// Words of expression.
        pub words: Words,

        /// Sign of expression.
        pub sign: bool,
    }

    /// Add iterators expression.
    pub struct AddIter<Lhs, Rhs> {
        /// Lhs in `lhs + rhs`, `lhs += rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs + rhs`, `lhs += rhs`.
        pub rhs: Rhs,
    }

    /// Sub iterators expression.
    pub struct SubIter<Lhs, Rhs> {
        /// Lhs in `lhs - rhs`, `lhs -= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs - rhs`, `lhs -= rhs`.
        pub rhs: Rhs,
    }

    /// Add expression.
    pub struct Add<Lhs, Rhs> {
        /// Lhs in `lhs + rhs`, `lhs += rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs + rhs`, `lhs += rhs`.
        pub rhs: Rhs,
    }

    /// Sub expression.
    pub struct Sub<Lhs, Rhs> {
        /// Lhs in `lhs - rhs`, `lhs -= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs - rhs`, `lhs -= rhs`.
        pub rhs: Rhs,
    }

    /// Mul expression.
    pub struct Mul<Lhs, Rhs> {
        /// Lhs in `lhs * rhs`, `lhs *= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs * rhs`, `lhs *= rhs`.
        pub rhs: Rhs,
    }

    /// Bit-wise expression.
    pub struct Bit<Lhs, Rhs, F: Fn(Single, Single) -> Single> {
        /// Lhs in `lhs | rhs`, `lhs |= rhs`, `lhs & rhs`, `lhs &= rhs`, `lhs ^ rhs`, `lhs ^= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs | rhs`, `lhs |= rhs`, `lhs & rhs`, `lhs &= rhs`, `lhs ^ rhs`, `lhs ^= rhs`.
        pub rhs: Rhs,

        /// Bit-wise operation.
        pub func: F,
    }

    /// Shl expression.
    pub struct Shl<Words> {
        /// Lhs in `lhs << rhs`, `lhs <<= rhs`
        pub words: Words,

        /// Rhs in `lhs << rhs`, `lhs <<= rhs`
        pub shift: usize,

        /// Default value.
        pub default: Single,
    }

    /// Shr expression.
    pub struct Shr<Words> {
        /// Lhs in `lhs >> rhs`, `lhs >>= rhs`
        pub words: Words,

        /// Rhs in `lhs >> rhs`, `lhs >>= rhs`
        pub shift: usize,

        /// Default value.
        pub default: Single,
    }

    /// Expression.
    pub trait Expr<Words>: Sized {
        /// Evaluates expression as default.
        #[inline]
        fn default<Long, F: Fn(Words) -> Long>(self, func: F) -> Long {
            let (res, overflow) = self.eval_ext();

            debug_assert!(!overflow);

            func(res)
        }

        /// Evaluates expression as checked.
        #[inline]
        fn checked<Long, F: Fn(Words) -> Long>(self, func: F) -> Option<Long> {
            let (res, overflow) = self.eval_ext();

            match overflow {
                false => Some(func(res)),
                true => None,
            }
        }

        /// Evaluates expression as strict.
        #[inline]
        fn strict<Long, F: Fn(Words) -> Long>(self, func: F) -> Long {
            let (res, overflow) = self.eval_ext();

            assert!(!overflow);

            func(res)
        }

        /// Evaluates expression as overflowing.
        #[inline]
        fn overflowing<Long, F: Fn(Words) -> Long>(self, func: F) -> (Long, bool) {
            let (res, overflow) = self.eval_ext();

            (func(res), overflow)
        }

        /// Evaluates expression with func.
        #[inline]
        fn with<Long, F: Fn(Words) -> Long>(self, func: F) -> Long {
            func(self.eval())
        }

        /// Evaluates expression.
        fn eval(self) -> Words;

        /// Evaluates expression with overflow.
        fn eval_ext(self) -> (Words, bool);
    }

    impl<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> Iterator for ExprIter<Lhs, Rhs> {
        type Item = Single;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let lhs = self.lhs.next()? as Double;
            let rhs = self.rhs.next()? as Double;
            let mul = self.mul as Double;
            let acc = self.acc as Double;

            let val = lhs * mul + rhs + acc;

            self.acc = (val / RADIX) as Single;

            Some(val as Single)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let lhs = self.lhs.size_hint();
            let rhs = self.lhs.size_hint();

            (lhs.0.min(rhs.0), lhs.1.and_then(|l| rhs.1.map(|r| l.min(r))))
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> Iterator
        for ExprIterMut<'words, Lhs, Rhs>
    {
        type Item = Single;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let lhs = self.lhs.next()?;
            let rhs = self.rhs.next()? as Double;
            let mul = self.mul as Double;
            let acc = self.acc as Double;
            let elem = *lhs as Double;

            let val = elem * mul + rhs + acc;

            self.acc = (val / RADIX) as Single;

            *lhs = val as Single;

            Some(self.acc)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let lhs = self.lhs.size_hint();
            let rhs = self.lhs.size_hint();

            (lhs.0.min(rhs.0), lhs.1.and_then(|l| rhs.1.map(|r| l.min(r))))
        }
    }

    impl<Words: Iterator<Item = Single>> NotIter<Words> {
        /// Iterator for [Not] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            ExprIter {
                lhs: self.words.map(|word| !word),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<'words, Words: Iterator<Item = &'words mut Single>> NotIter<Words> {
        /// Iterator for [Not] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            ExprIterMut {
                lhs: self.words.map(|word| {
                    *word = !*word;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<Words: Iterator<Item = Single>> PosIter<Words> {
        /// Iterator for [Pos] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            ExprIter {
                lhs: self.words,
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<'words, Words: Iterator<Item = &'words mut Single>> PosIter<Words> {
        /// Iterator for [Pos] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            ExprIterMut {
                lhs: self.words,
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<Words: Iterator<Item = Single>> NegIter<Words> {
        /// Iterator for [Neg] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            ExprIter {
                lhs: self.words.map(|word| !word),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: 1,
            }
        }
    }

    impl<'words, Words: Iterator<Item = &'words mut Single>> NegIter<Words> {
        /// Iterator for [Neg] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            ExprIterMut {
                lhs: self.words.map(|word| {
                    *word = !*word;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: 1,
            }
        }
    }

    impl<const L: usize> Not<&[Single; L]> {
        /// Iterator for [Not] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let words = self.words.iter().copied();

            NotIter { words }.iter()
        }
    }

    impl<'words, const L: usize> Not<&'words mut [Single; L]> {
        /// Iterator for [Not] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let words = self.words.iter_mut();

            NotIter { words }.iter_mut()
        }
    }

    impl<const L: usize> Pos<&[Single; L]> {
        /// Iterator for [Pos] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let words = self.words.iter().copied();

            PosIter { words }.iter()
        }
    }

    impl<'words, const L: usize> Pos<&'words mut [Single; L]> {
        /// Iterator for [Pos] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let words = self.words.iter_mut();

            PosIter { words }.iter_mut()
        }
    }

    impl<const L: usize> Neg<&[Single; L]> {
        /// Iterator for [Neg] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let words = self.words.iter().copied();

            NegIter { words }.iter()
        }
    }

    impl<'words, const L: usize> Neg<&'words mut [Single; L]> {
        /// Iterator for [Neg] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let words = self.words.iter_mut();

            NegIter { words }.iter_mut()
        }
    }

    impl<const L: usize> Posx<&[Single; L]> {
        /// Iterator for [Posx] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let (xor, acc) = match self.words[L - 1] >> (BITS - 1) {
                0 => (0, 0),
                _ => (MAX, 1),
            };

            ExprIter {
                lhs: self.words.iter().copied().map(move |word| word ^ xor),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
            }
        }
    }

    impl<'words, const L: usize> Posx<&'words mut [Single; L]> {
        /// Iterator for [Posx] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let (xor, acc) = match self.words[L - 1] >> (BITS - 1) {
                0 => (0, 0),
                _ => (MAX, 1),
            };

            ExprIterMut {
                lhs: self.words.iter_mut().map(move |word| {
                    *word ^= xor;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
            }
        }
    }

    impl<const L: usize> Negx<&[Single; L]> {
        /// Iterator for [Negx] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let (xor, acc) = match self.words[L - 1] >> (BITS - 1) {
                0 => (MAX, 1),
                _ => (0, 0),
            };

            ExprIter {
                lhs: self.words.iter().copied().map(move |word| word ^ xor),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
            }
        }
    }

    impl<'words, const L: usize> Negx<&'words mut [Single; L]> {
        /// Iterator for [Negx] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let (xor, acc) = match self.words[L - 1] >> (BITS - 1) {
                0 => (MAX, 1),
                _ => (0, 0),
            };

            ExprIterMut {
                lhs: self.words.iter_mut().map(move |word| {
                    *word ^= xor;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
            }
        }
    }

    impl<const L: usize> Sgx<&[Single; L]> {
        /// Iterator for [Sgx] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let (xor, acc) = match self.words[L - 1] >> (BITS - 1) == self.sign as Single {
                false => (MAX, 1),
                true => (0, 0),
            };

            ExprIter {
                lhs: self.words.iter().copied().map(move |word| word ^ xor),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
            }
        }
    }

    impl<'words, const L: usize> Sgx<&'words mut [Single; L]> {
        /// Iterator for [Sgx] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let (xor, acc) = match self.words[L - 1] >> (BITS - 1) == self.sign as Single {
                false => (MAX, 1),
                true => (0, 0),
            };

            ExprIterMut {
                lhs: self.words.iter_mut().map(move |word| {
                    *word ^= xor;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
            }
        }
    }

    impl<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> AddIter<Lhs, Rhs> {
        /// Iterator for [AddIter] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs;
            let rhs = self.rhs;

            ExprIter { lhs, rhs, mul: 1, acc: 0 }
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> AddIter<Lhs, Rhs> {
        /// Iterator for [AddIter] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs;
            let rhs = self.rhs;

            ExprIterMut { lhs, rhs, mul: 1, acc: 0 }
        }
    }

    impl<const L: usize> Add<&[Single; L], &[Single; L]> {
        /// Iterator for [Add] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs.iter().copied();

            AddIter { lhs, rhs }.iter()
        }
    }

    impl<'words, const L: usize> Add<&'words mut [Single; L], &[Single; L]> {
        /// Iterator for [Add] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs.iter().copied();

            AddIter { lhs, rhs }.iter_mut()
        }
    }

    impl<const L: usize> Add<&[Single; L], <Single as Num>::Unsigned> {
        /// Iterator for [Add] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs;

            ExprIter {
                lhs,
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: rhs,
            }
        }
    }

    impl<'words, const L: usize> Add<&'words mut [Single; L], <Single as Num>::Unsigned> {
        /// Iterator for [Add] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs;

            ExprIterMut {
                lhs,
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: rhs,
            }
        }
    }

    impl<const L: usize> Add<&[Single; L], <Single as Num>::Signed> {
        /// Iterator for [Add] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs as Single;

            let ext = match rhs >> (BITS - 1) {
                0 => 0,
                _ => MAX,
            };

            ExprIter {
                lhs,
                rhs: (0..).map(move |idx| [rhs, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<'words, const L: usize> Add<&'words mut [Single; L], <Single as Num>::Signed> {
        /// Iterator for [Add] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs as Single;

            let ext = match rhs >> (BITS - 1) {
                0 => 0,
                _ => MAX,
            };

            ExprIterMut {
                lhs,
                rhs: (0..).map(move |idx| [rhs, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> SubIter<Lhs, Rhs> {
        /// Iterator for [SubIter] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs;
            let rhs = self.rhs;

            ExprIter {
                lhs,
                rhs: rhs.map(|word| !word),
                mul: 1,
                acc: 1,
            }
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> SubIter<Lhs, Rhs> {
        /// Iterator for [SubIter] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs;
            let rhs = self.rhs;

            ExprIterMut {
                lhs,
                rhs: rhs.map(|word| !word),
                mul: 1,
                acc: 1,
            }
        }
    }

    impl<const L: usize> Sub<&[Single; L], &[Single; L]> {
        /// Iterator for [Sub] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs.iter().copied();

            SubIter { lhs, rhs }.iter()
        }
    }

    impl<'words, const L: usize> Sub<&'words mut [Single; L], &[Single; L]> {
        /// Iterator for [Sub] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs.iter().copied();

            SubIter { lhs, rhs }.iter_mut()
        }
    }

    impl<const L: usize> Sub<&[Single; L], <Single as Num>::Unsigned> {
        /// Iterator for [Sub] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs as Single;

            let neg = rhs.wrapping_neg();

            let ext = match rhs != 0 {
                false => 0,
                true => MAX,
            };

            ExprIter {
                lhs,
                rhs: (0..).map(move |idx| [neg, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<'words, const L: usize> Sub<&'words mut [Single; L], <Single as Num>::Unsigned> {
        /// Iterator for [Sub] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs as Single;

            let neg = rhs.wrapping_neg();

            let ext = match rhs != 0 {
                false => 0,
                true => MAX,
            };

            ExprIterMut {
                lhs,
                rhs: (0..).map(move |idx| [neg, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<const L: usize> Sub<&[Single; L], <Single as Num>::Signed> {
        /// Iterator for [Sub] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs as Single;

            let neg = rhs.wrapping_neg();

            let ext = match (rhs != 0, rhs >> (BITS - 1)) {
                (true, 0) => MAX,
                (_, _) => 0,
            };

            ExprIter {
                lhs,
                rhs: (0..).map(move |idx| [neg, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<'words, const L: usize> Sub<&'words mut [Single; L], <Single as Num>::Signed> {
        /// Iterator for [Sub] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs as Single;

            let neg = rhs.wrapping_neg();

            let ext = match (rhs != 0, rhs >> (BITS - 1)) {
                (true, 0) => MAX,
                (_, _) => 0,
            };

            ExprIterMut {
                lhs,
                rhs: (0..).map(move |idx| [neg, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
            }
        }
    }

    impl<const L: usize> Mul<&[Single; L], Single> {
        /// Iterator for [Mul] expression.
        #[inline]
        pub fn iter(self) -> ExprIter<impl Iterator<Item = Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs;

            ExprIter {
                lhs,
                rhs: std::iter::repeat(0),
                mul: rhs,
                acc: 0,
            }
        }
    }

    impl<'words, const L: usize> Mul<&'words mut [Single; L], Single> {
        /// Iterator for [Mul] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<'words, impl Iterator<Item = &'words mut Single>, impl Iterator<Item = Single>> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs;

            ExprIterMut {
                lhs,
                rhs: std::iter::repeat(0),
                mul: rhs,
                acc: 0,
            }
        }
    }

    impl<const L: usize> Shl<&[Single; L]> {
        /// Shl expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            self
        }

        /// Shl expression with default value.
        #[inline]
        pub fn default(mut self, default: Single) -> Self {
            self.default = default;
            self
        }
    }

    impl<const L: usize> Shl<&mut [Single; L]> {
        /// Shl expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            self
        }

        /// Shl expression with default value.
        #[inline]
        pub fn default(mut self, default: Single) -> Self {
            self.default = default;
            self
        }
    }

    impl<const L: usize> Shr<&[Single; L]> {
        /// Shr expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            let bit = self.words[L - 1] >> (BITS - 1);

            Self {
                words: self.words,
                shift: self.shift,
                default: [0, MAX][(bit > 0) as usize],
            }
        }

        /// Shr expression with default value.
        #[inline]
        pub fn default(mut self, default: Single) -> Self {
            self.default = default;
            self
        }
    }

    impl<const L: usize> Shr<&mut [Single; L]> {
        /// Shr expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            let bit = self.words[L - 1] >> (BITS - 1);

            Self {
                words: self.words,
                shift: self.shift,
                default: [0, MAX][(bit > 0) as usize],
            }
        }

        /// Shr expression with default value.
        #[inline]
        pub fn default(mut self, default: Single) -> Self {
            self.default = default;
            self
        }
    }

    impl<const L: usize, Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> Expr<[Single; L]>
        for ExprIter<Lhs, Rhs>
    {
        #[inline]
        fn eval(mut self) -> [Single; L] {
            self.collect_arr()
        }

        #[inline]
        fn eval_ext(mut self) -> ([Single; L], bool) {
            let res = self.collect_arr();

            (res, self.acc > 0)
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> Expr<()>
        for ExprIterMut<'words, Lhs, Rhs>
    {
        #[inline]
        fn eval(self) {
            self.for_each(|_| ());
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            ((), self.last().unwrap_or_default() > 0)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Not<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Not<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Pos<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Pos<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Neg<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Neg<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Posx<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Posx<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Negx<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Negx<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sgx<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Sgx<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], &[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Add<&mut [Single; L], &[Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize, Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> Expr<[Single; L]>
        for AddIter<Lhs, Rhs>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> Expr<()> for AddIter<Lhs, Rhs> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], <Single as Num>::Unsigned> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Add<&mut [Single; L], <Single as Num>::Unsigned> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], <Single as Num>::Signed> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Add<&mut [Single; L], <Single as Num>::Signed> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], &[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Sub<&mut [Single; L], &[Single; L]> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize, Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> Expr<[Single; L]>
        for SubIter<Lhs, Rhs>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> Expr<()> for SubIter<Lhs, Rhs> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], <Single as Num>::Unsigned> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Sub<&mut [Single; L], <Single as Num>::Unsigned> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], <Single as Num>::Signed> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Sub<&mut [Single; L], <Single as Num>::Signed> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], Single> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Mul<&mut [Single; L], Single> {
        #[inline]
        fn eval(self) {
            self.iter_mut().eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext()
        }
    }

    impl<const L: usize, F: Fn(Single, Single) -> Single> Expr<[Single; L]> for Bit<&[Single; L], &[Single; L], F> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs;
            let func = self.func;

            lhs.iter()
                .copied()
                .zip(rhs.iter().copied())
                .map(|(lhs, rhs)| func(lhs, rhs))
                .collect_arr()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.eval(), false)
        }
    }

    impl<const L: usize, F: Fn(Single, Single) -> Single> Expr<()> for Bit<&mut [Single; L], &[Single; L], F> {
        #[inline]
        fn eval(self) {
            let lhs = self.lhs;
            let rhs = self.rhs;
            let func = self.func;

            lhs.iter_mut()
                .zip(rhs.iter().copied())
                .for_each(|(ptr, val)| *ptr = func(*ptr, val));
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            (self.eval(), false)
        }
    }

    impl<const L: usize, F: Fn(Single, Single) -> Single> Expr<[Single; L]>
        for Bit<&[Single; L], <Single as Num>::Unsigned, F>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs;
            let func = self.func;

            lhs.iter()
                .copied()
                .zip((0..).map(|idx| [rhs, 0][(idx > 0) as usize]))
                .map(|(lhs, rhs)| func(lhs, rhs))
                .collect_arr()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.eval(), false)
        }
    }

    impl<const L: usize, F: Fn(Single, Single) -> Single> Expr<()> for Bit<&mut [Single; L], <Single as Num>::Unsigned, F> {
        #[inline]
        fn eval(self) {
            let lhs = self.lhs;
            let rhs = self.rhs;
            let func = self.func;

            lhs.iter_mut()
                .zip((0..).map(|idx| [rhs, 0][(idx > 0) as usize]))
                .for_each(|(ptr, val)| *ptr = func(*ptr, val));
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            (self.eval(), false)
        }
    }

    impl<const L: usize, F: Fn(Single, Single) -> Single> Expr<[Single; L]>
        for Bit<&[Single; L], <Single as Num>::Signed, F>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs as Single;
            let func = self.func;

            let ext = match rhs >> (BITS - 1) {
                0 => 0,
                _ => MAX,
            };

            lhs.iter()
                .copied()
                .zip((0..).map(|idx| [rhs, ext][(idx > 0) as usize]))
                .map(|(lhs, rhs)| func(lhs, rhs))
                .collect_arr()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.eval(), false)
        }
    }

    impl<const L: usize, F: Fn(Single, Single) -> Single> Expr<()> for Bit<&mut [Single; L], <Single as Num>::Signed, F> {
        #[inline]
        fn eval(self) {
            let lhs = self.lhs;
            let rhs = self.rhs as Single;
            let func = self.func;

            let ext = match rhs >> (BITS - 1) {
                0 => 0,
                _ => MAX,
            };

            lhs.iter_mut()
                .zip((0..).map(|idx| [rhs, ext][(idx > 0) as usize]))
                .for_each(|(ptr, val)| *ptr = func(*ptr, val));
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            (self.eval(), false)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Shl<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.eval_ext().0
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            use std::iter::repeat_n;

            let words = self.words;
            let shift = self.shift;
            let default = self.default;

            let offset = (shift / BITS).min(L);
            let shl = shift % BITS;
            let shr = BITS - shl;

            let mut acc = default;
            let mut res = repeat_n(default, offset)
                .chain(words[..L - offset].iter().copied())
                .collect_arr();

            for ptr in res[offset..].iter_mut() {
                let val = *ptr;

                let val_h = ptr.unbounded_shl(shl as u32);
                let val_l = acc.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            (res, shift < BITS * L)
        }
    }

    impl<const L: usize> Expr<()> for Shl<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.eval_ext().0
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            use std::iter::repeat_n;

            let words = self.words;
            let shift = self.shift;
            let default = self.default;

            let offset = (shift / BITS).min(L);
            let shl = shift % BITS;
            let shr = BITS - shl;

            let mut acc = default;

            *words = repeat_n(default, offset)
                .chain(words[..L - offset].iter().copied())
                .collect_arr();

            for ptr in words[offset..].iter_mut() {
                let val = *ptr;

                let val_h = ptr.unbounded_shl(shl as u32);
                let val_l = acc.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            ((), shift < BITS * L)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Shr<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.eval_ext().0
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            use std::iter::repeat_n;

            let words = self.words;
            let shift = self.shift;
            let default = self.default;

            let offset = (shift / BITS).min(L);
            let shr = shift % BITS;
            let shl = BITS - shr;

            let mut acc = default;
            let mut res = words[offset..].iter().copied().chain(repeat_n(default, offset)).collect_arr();

            for ptr in res[..L - offset].iter_mut().rev() {
                let val = *ptr;

                let val_h = acc.unbounded_shl(shl as u32);
                let val_l = ptr.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            (res, shift < BITS * L)
        }
    }

    impl<const L: usize> Expr<()> for Shr<&mut [Single; L]> {
        #[inline]
        fn eval(self) {
            self.eval_ext().0
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            use std::iter::repeat_n;

            let words = self.words;
            let shift = self.shift;
            let default = self.default;

            let offset = (shift / BITS).min(L);
            let shr = shift % BITS;
            let shl = BITS - shr;

            let mut acc = default;

            *words = words[offset..].iter().copied().chain(repeat_n(default, offset)).collect_arr();

            for ptr in words[..L - offset].iter_mut().rev() {
                let val = *ptr;

                let val_h = acc.unbounded_shl(shl as u32);
                let val_l = ptr.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            ((), shift < BITS * L)
        }
    }

    /// Not iterator expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn not_iter<Words>(words: Words) -> NotIter<Words> {
        NotIter { words }
    }

    /// Pos iterator expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn pos_iter<Words>(words: Words) -> PosIter<Words> {
        PosIter { words }
    }

    /// Neg iterator expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn neg_iter<Words>(words: Words) -> NegIter<Words> {
        NegIter { words }
    }

    /// Not expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn not<Words>(words: Words) -> Not<Words> {
        Not { words }
    }

    /// Pos expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn pos<Words>(words: Words) -> Pos<Words> {
        Pos { words }
    }

    /// Neg expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn neg<Words>(words: Words) -> Neg<Words> {
        Neg { words }
    }

    /// Pos (forced) expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn posx<Words>(words: Words) -> Posx<Words> {
        Posx { words }
    }

    /// Neg (forced) expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn negx<Words>(words: Words) -> Negx<Words> {
        Negx { words }
    }

    /// Sign (forced) expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn sgx<Words>(words: Words, sign: bool) -> Sgx<Words> {
        Sgx { words, sign }
    }

    /// Add iterators expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn add_iter<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> AddIter<Lhs, Rhs> {
        AddIter { lhs, rhs }
    }

    /// Sub iterators expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn sub_iter<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> SubIter<Lhs, Rhs> {
        SubIter { lhs, rhs }
    }

    /// Add expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn add<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Add<Lhs, Rhs> {
        Add { lhs, rhs }
    }

    /// Sub expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn sub<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Sub<Lhs, Rhs> {
        Sub { lhs, rhs }
    }

    /// Mul expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn mul<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Mul<Lhs, Rhs> {
        Mul { lhs, rhs }
    }

    /// BitOr expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn bitor<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Bit<Lhs, Rhs, impl Fn(Single, Single) -> Single> {
        Bit {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs | rhs,
        }
    }

    /// BitAnd expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn bitand<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Bit<Lhs, Rhs, impl Fn(Single, Single) -> Single> {
        Bit {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs & rhs,
        }
    }

    /// BitXor expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn bitxor<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Bit<Lhs, Rhs, impl Fn(Single, Single) -> Single> {
        Bit {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs ^ rhs,
        }
    }

    /// Shl expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn shl<Words>(words: Words, shift: usize) -> Shl<Words> {
        Shl { words, shift, default: 0 }
    }

    /// Shr expression.
    ///
    /// Evaluated via [Expr] methods.
    #[inline]
    pub fn shr<Words>(words: Words, shift: usize) -> Shr<Words> {
        Shr { words, shift, default: 0 }
    }

    /// Reads `[offset; offset + Single::BITS]`.
    #[inline]
    pub fn read<const L: usize>(words: &[Single; L], offset: usize) -> Single {
        let idx = offset / BITS;
        let shr = offset % BITS;
        let shl = BITS - shr;

        let mut res = 0;

        if let Some(elem) = words.get(idx) {
            res |= elem.unbounded_shr(shr as u32);
        }

        if let Some(elem) = words.get(idx + 1) {
            res |= elem.unbounded_shl(shl as u32);
        }

        res
    }

    /// Returns `words` two's complement sign.
    #[inline]
    pub fn sign<const L: usize>(words: &[Single; L], pos: Sign, neg: Sign) -> Sign {
        if words == &[0; L] {
            return Sign::ZERO;
        }

        match words[L - 1] >> (BITS - 1) {
            0 => pos,
            _ => neg,
        }
    }

    /// Returns `words` two's complement sign in const-time.
    #[inline(never)]
    #[cfg(feature = "const-time")]
    pub fn sign_ct<const L: usize>(words: &[Single; L]) -> RelCt {
        let zero = zero_ct(words);
        let neg = neg_ct(words);
        let pos = !zero & !neg & 1;

        neg as RelCt | pos as RelCt
    }

    /// Checks `words > 0` in const-time.
    #[inline(never)]
    #[cfg(feature = "const-time")]
    pub fn pos_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        let zero = zero_ct(words);
        let neg = neg_ct(words);

        !zero & !neg
    }

    /// Checks `words < 0` in const-time.
    #[inline(never)]
    #[cfg(feature = "const-time")]
    pub fn neg_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        let neg = (words[L - 1] >> (BITS - 1)) as MaskCt;

        <MaskCt as Zero>::ZERO.wrapping_sub(neg)
    }

    /// Checks `words == 0` in const-time.
    #[inline(never)]
    #[cfg(feature = "const-time")]
    pub fn zero_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        std::hint::black_box(words.iter().fold(0, |acc, val| acc | val)).zero_ct()
    }
}

pub mod algo {
    //! # Algorithms
    //!
    //! **Long numbers/bytes algorithms**

    use super::uops::Expr;
    use super::*;

    /// Multiplication expression.
    pub struct Mul<Lhs, Rhs> {
        /// Lhs in `lhs * rhs`, `lhs *= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs * rhs`, `lhs *= rhs`.
        pub rhs: Rhs,
    }

    /// Division expression.
    pub struct Div<Lhs, Rhs> {
        /// Lhs in `lhs / rhs`, `lhs % rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs / rhs`, `lhs % rhs`.
        pub rhs: Rhs,
    }

    /// Division mutable expression.
    pub struct DivMut<Lhs, Rhs> {
        /// Lhs in `lhs /= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs /= rhs`.
        pub rhs: Rhs,
    }

    /// Remainder mutable expression.
    pub struct RemMut<Lhs, Rhs> {
        /// Lhs in `lhs %= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs %= rhs`.
        pub rhs: Rhs,
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], &[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut res = [0; L];

            for (idx, val) in rhs.iter().copied().enumerate() {
                uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval();
            }

            res
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut res = [0; L];
            let mut any = 0;

            for (idx, val) in rhs.iter().copied().enumerate() {
                any |= uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .last()
                    .unwrap_or(0);
            }

            (res, any > 0)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], <Single as Num>::Unsigned> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs;

            uops::mul(lhs, rhs).eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            uops::mul(lhs, rhs).eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], <Single as Num>::Signed> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs as Single;

            let ext = match rhs >> (BITS - 1) {
                0 => 0,
                _ => MAX,
            };

            let rhs = (0..L).map(|idx| [rhs, ext][(idx > 0) as usize]);

            let mut res = [0; L];

            for (idx, val) in rhs.enumerate() {
                uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval();
            }

            res
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let lhs = self.lhs;
            let rhs = self.rhs as Single;

            let ext = match rhs >> (BITS - 1) {
                0 => 0,
                _ => MAX,
            };

            let rhs = (0..L).map(|idx| [rhs, ext][(idx > 0) as usize]);

            let mut res = [0; L];
            let mut any = 0;

            for (idx, val) in rhs.enumerate() {
                any |= uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .last()
                    .unwrap_or(0);
            }

            (res, any > 0)
        }
    }

    impl<const L: usize> Expr<()> for Mul<&mut [Single; L], &[Single; L]> {
        #[inline]
        fn eval(self) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            *lhs = Mul { lhs: &*lhs, rhs }.eval();
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let (res, overflow) = Mul { lhs: &*lhs, rhs }.eval_ext();

            *lhs = res;

            ((), overflow)
        }
    }

    impl<const L: usize> Expr<()> for Mul<&mut [Single; L], <Single as Num>::Unsigned> {
        #[inline]
        fn eval(self) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            uops::mul(lhs, rhs).eval()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            uops::mul(lhs, rhs).eval_ext()
        }
    }

    impl<const L: usize> Expr<()> for Mul<&mut [Single; L], <Single as Num>::Signed> {
        #[inline]
        fn eval(self) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            *lhs = Mul { lhs: &*lhs, rhs }.eval();
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let (res, overflow) = Mul { lhs: &*lhs, rhs }.eval_ext();

            *lhs = res;

            ((), overflow)
        }
    }

    impl<const L: usize> Div<&[Single; L], &[Single; L]> {
        /// Calculates as default.
        #[inline]
        pub fn default<Long, DivF: Fn([Single; L]) -> Long, RemF: Fn([Single; L]) -> Long>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> (Long, Long) {
            debug_assert_ne!(self.rhs, &[0; L]);

            self.wrapping(div_func, rem_func)
        }

        /// Calculates as checked.
        #[inline]
        pub fn checked<Long, DivF: Fn([Single; L]) -> Long, RemF: Fn([Single; L]) -> Long>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> Option<(Long, Long)> {
            match self.rhs.eq(&[0; L]) {
                false => Some(self.wrapping(div_func, rem_func)),
                true => None,
            }
        }

        /// Calculates as strict.
        #[inline]
        pub fn strict<Long, DivF: Fn([Single; L]) -> Long, RemF: Fn([Single; L]) -> Long>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> (Long, Long) {
            assert_ne!(self.rhs, &[0; L]);

            self.wrapping(div_func, rem_func)
        }

        /// Calculates as wrapping.
        #[inline]
        pub fn wrapping<Long, DivF: Fn([Single; L]) -> Long, RemF: Fn([Single; L]) -> Long>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> (Long, Long) {
            let (div, rem) = self.calculate();

            (div_func(div), rem_func(rem))
        }

        /// Calculates as overflowing.
        #[inline]
        pub fn overflowing<Long, DivF: Fn([Single; L]) -> Long, RemF: Fn([Single; L]) -> Long>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> ((Long, Long), bool) {
            (self.wrapping(div_func, rem_func), false)
        }

        #[inline]
        fn calculate(self) -> ([Single; L], [Single; L]) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut div = [0; L];
            let mut rem = [0; L];

            for (ptr, val) in div.iter_mut().zip(lhs.iter().copied()).rev() {
                cycle!(rem, val);

                let digit = search!(@max 0, RADIX, |m: Double| {
                    let mut iter = uops::mul(rhs, m as Single).iter();

                    let cmp = (&mut iter).zip(rem.iter().copied()).fold(Ordering::Equal, |acc, (lhs, rhs)| match lhs.cmp(&rhs) {
                        Ordering::Less => Ordering::Less,
                        Ordering::Equal => acc,
                        Ordering::Greater => Ordering::Greater,
                    });

                    match iter.acc {
                        0 => cmp,
                        _ => Ordering::Greater,
                    }
                });

                *ptr = digit.saturating_sub(1) as Single;

                uops::sub_iter(rem.iter_mut(), uops::mul(rhs, *ptr).iter()).eval();
            }

            (div, rem)
        }
    }

    impl<const L: usize> Div<&[Single; L], Single> {
        /// Calculates as default.
        #[inline]
        pub fn default<Long, T, DivF: Fn([Single; L]) -> Long, RemF: Fn(Single) -> T>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> (Long, T) {
            debug_assert_ne!(self.rhs, 0);

            self.wrapping(div_func, rem_func)
        }

        /// Calculates as checked.
        #[inline]
        pub fn checked<Long, T, DivF: Fn([Single; L]) -> Long, RemF: Fn(Single) -> T>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> Option<(Long, T)> {
            match self.rhs.eq(&0) {
                false => Some(self.wrapping(div_func, rem_func)),
                true => None,
            }
        }

        /// Calculates as strict.
        #[inline]
        pub fn strict<Long, T, DivF: Fn([Single; L]) -> Long, RemF: Fn(Single) -> T>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> (Long, T) {
            assert_ne!(self.rhs, 0);

            self.wrapping(div_func, rem_func)
        }

        /// Calculates as wrapping.
        #[inline]
        pub fn wrapping<Long, T, DivF: Fn([Single; L]) -> Long, RemF: Fn(Single) -> T>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> (Long, T) {
            let (div, rem) = self.calculate();

            (div_func(div), rem_func(rem))
        }

        /// Calculates as overflowing.
        #[inline]
        pub fn overflowing<Long, T, DivF: Fn([Single; L]) -> Long, RemF: Fn(Single) -> T>(
            self,
            div_func: DivF,
            rem_func: RemF,
        ) -> ((Long, T), bool) {
            (self.wrapping(div_func, rem_func), false)
        }

        #[inline]
        fn calculate(self) -> ([Single; L], Single) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut div = [0; L];
            let mut rem = 0 as Double;

            for (ptr, val) in div.iter_mut().zip(lhs.iter().copied()).rev() {
                rem <<= BITS;
                rem |= val as Double;

                let digit = search!(@max 0, RADIX, |m: Double| (m * rhs as Double).cmp(&rem));
                let digit = digit.saturating_sub(1) as Single;

                *ptr = digit;
                rem -= digit as Double * rhs as Double;
            }

            (div, rem as Single)
        }
    }

    impl<const L: usize> DivMut<&mut [Single; L], &[Single; L]> {
        /// Calculates as default.
        #[inline]
        pub fn default(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.default(|res| res, |res| res).0;
        }

        /// Calculates as checked.
        #[inline]
        pub fn checked(self) -> Option<()> {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.checked(|res| res, |res| res)?.0;

            Some(())
        }

        /// Calculates as strict.
        #[inline]
        pub fn strict(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.strict(|res| res, |res| res).0;
        }

        /// Calculates as wrapping.
        #[inline]
        pub fn wrapping(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.wrapping(|res| res, |res| res).0;
        }

        /// Calculates as overflowing.
        #[inline]
        pub fn overflowing(self) -> ((), bool) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.overflowing(|res| res, |res| res).0.0;

            ((), false)
        }
    }

    impl<const L: usize> DivMut<&mut [Single; L], Single> {
        /// Calculates as default.
        #[inline]
        pub fn default(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.default(|res| res, |res| res).0;
        }

        /// Calculates as checked.
        #[inline]
        pub fn checked(self) -> Option<()> {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.checked(|res| res, |res| res)?.0;

            Some(())
        }

        /// Calculates as strict.
        #[inline]
        pub fn strict(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.strict(|res| res, |res| res).0;
        }

        /// Calculates as wrapping.
        #[inline]
        pub fn wrapping(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.wrapping(|res| res, |res| res).0;
        }

        /// Calculates as overflowing.
        #[inline]
        pub fn overflowing(self) -> ((), bool) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.overflowing(|res| res, |res| res).0.0;

            ((), false)
        }
    }

    impl<const L: usize> RemMut<&mut [Single; L], &[Single; L]> {
        /// Calculates as default.
        #[inline]
        pub fn default(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.default(|res| res, |res| res).1;
        }

        /// Calculates as checked.
        #[inline]
        pub fn checked(self) -> Option<()> {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.checked(|res| res, |res| res)?.1;

            Some(())
        }

        /// Calculates as strict.
        #[inline]
        pub fn strict(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.strict(|res| res, |res| res).1;
        }

        /// Calculates as wrapping.
        #[inline]
        pub fn wrapping(self) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.wrapping(|res| res, |res| res).1;
        }

        /// Calculates as overflowing.
        #[inline]
        pub fn overflowing(self) -> ((), bool) {
            *self.lhs = Div { lhs: &*self.lhs, rhs: self.rhs }.overflowing(|res| res, |res| res).0.1;

            ((), false)
        }
    }

    impl<const L: usize> RemMut<&mut [Single; L], Single> {
        /// Calculates as default.
        #[inline]
        pub fn default(self) {
            self.lhs[0] = Div { lhs: &*self.lhs, rhs: self.rhs }.default(|res| res, |res| res).1;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = 0);
        }

        /// Calculates as checked.
        #[inline]
        pub fn checked(self) -> Option<()> {
            self.lhs[0] = Div { lhs: &*self.lhs, rhs: self.rhs }.checked(|res| res, |res| res)?.1;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = 0);

            Some(())
        }

        /// Calculates as strict.
        #[inline]
        pub fn strict(self) {
            self.lhs[0] = Div { lhs: &*self.lhs, rhs: self.rhs }.strict(|res| res, |res| res).1;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = 0);
        }

        /// Calculates as wrapping.
        #[inline]
        pub fn wrapping(self) {
            self.lhs[0] = Div { lhs: &*self.lhs, rhs: self.rhs }.wrapping(|res| res, |res| res).1;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = 0);
        }

        /// Calculates as overflowing.
        #[inline]
        pub fn overflowing(self) -> ((), bool) {
            self.lhs[0] = Div { lhs: &*self.lhs, rhs: self.rhs }.overflowing(|res| res, |res| res).0.1;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = 0);

            ((), false)
        }
    }

    /// Calculates `lhs * rhs`, `lhs *= rhs`.
    #[inline]
    pub fn mul<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Mul<Lhs, Rhs> {
        Mul { lhs, rhs }
    }

    /// Calculates `(lhs / rhs, lhs % rhs)`.
    #[inline]
    #[must_use]
    pub fn div<'words, const L: usize>(
        lhs: &'words [Single; L],
        rhs: &'words [Single; L],
    ) -> Div<&'words [Single; L], &'words [Single; L]> {
        Div { lhs, rhs }
    }

    /// Calculates `(lhs / rhs, lhs % rhs)`, where `rhs` is single CPU-word.
    #[inline]
    #[must_use]
    pub fn div_single<const L: usize>(lhs: &[Single; L], rhs: Single) -> Div<&[Single; L], Single> {
        Div { lhs, rhs }
    }

    /// Calculates `lhs /= rhs`.
    #[inline]
    #[must_use]
    pub fn div_mut<'words, const L: usize>(
        lhs: &'words mut [Single; L],
        rhs: &'words [Single; L],
    ) -> DivMut<&'words mut [Single; L], &'words [Single; L]> {
        DivMut { lhs, rhs }
    }

    /// Calculates `lhs /= rhs`, where `rhs` is single CPU-word.
    #[inline]
    #[must_use]
    pub fn div_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) -> DivMut<&mut [Single; L], Single> {
        DivMut { lhs, rhs }
    }

    /// Calculates `lhs %= rhs`.
    #[inline]
    #[must_use]
    pub fn rem_mut<'words, const L: usize>(
        lhs: &'words mut [Single; L],
        rhs: &'words [Single; L],
    ) -> RemMut<&'words mut [Single; L], &'words [Single; L]> {
        RemMut { lhs, rhs }
    }

    /// Calculates `lhs %= rhs`, where `rhs` is single CPU-word.
    #[inline]
    #[must_use]
    pub fn rem_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) -> RemMut<&mut [Single; L], Single> {
        RemMut { lhs, rhs }
    }
}

#[cfg(all(target_pointer_width = "64", not(test)))]
mod _impl {
    use super::*;

    nd_ops_primitive_impl!(@signed [i128]);
    nd_ops_primitive_impl!(@unsigned [u128]);
    nd_ops_primitive_impl!(@bytes [u128]);

    nd_ops_primitive_native_impl!(@signed [i8, i16, i32, i64]);
    nd_ops_primitive_native_impl!(@unsigned [u8, u16, u32, u64]);
    nd_ops_primitive_native_impl!(@bytes [u8, u16, u32, u64]);

    ops_primitive_impl!(@signed [i8, i16, i32, i64, i128]);
    ops_primitive_impl!(@unsigned [u8, u16, u32, u64, u128]);
    ops_primitive_impl!(@bytes [u8, u16, u32, u64, u128]);
}

#[cfg(all(target_pointer_width = "32", not(test)))]
mod _impl {
    use super::*;

    nd_ops_primitive_impl!(@signed [i64, i128]);
    nd_ops_primitive_impl!(@unsigned [u64, u128]);
    nd_ops_primitive_impl!(@bytes [u64, u128]);

    nd_ops_primitive_native_impl!(@signed [i8, i16, i32]);
    nd_ops_primitive_native_impl!(@unsigned [u8, u16, u32]);
    nd_ops_primitive_native_impl!(@bytes [u8, u16, u32]);

    ops_primitive_impl!(@signed [i8, i16, i32, i64, i128]);
    ops_primitive_impl!(@unsigned [u8, u16, u32, u64, u128]);
    ops_primitive_impl!(@bytes [u8, u16, u32, u64, u128]);
}

#[cfg(test)]
mod _impl {
    use super::*;

    nd_ops_primitive_impl!(@signed [i16, i32, i64, i128]);
    nd_ops_primitive_impl!(@unsigned [u16, u32, u64, u128]);
    nd_ops_primitive_impl!(@bytes [u16, u32, u64, u128]);

    nd_ops_primitive_native_impl!(@signed [i8]);
    nd_ops_primitive_native_impl!(@unsigned [u8]);
    nd_ops_primitive_native_impl!(@bytes [u8]);

    ops_primitive_impl!(@signed [i8, i16, i32, i64, i128]);
    ops_primitive_impl!(@unsigned [u8, u16, u32, u64, u128]);
    ops_primitive_impl!(@bytes [u8, u16, u32, u64, u128]);
}

/// Signed long represented with `[Word; L]`, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Signed<const L: usize>(pub [Single; L]);

/// Signed long represented with `[Word; L]` by immutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SignedRef<'reference, const L: usize>(pub &'reference [Single; L]);

/// Signed long represented with `[Word; L]` by mutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, PartialEq, Eq)]
pub struct SignedMut<'reference, const L: usize>(pub &'reference mut [Single; L]);

/// Signed long dynamic number. (**WIP**)
#[cfg(feature = "dyn")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedDyn(Vec<Single>, Sign);

/// Unsigned long represented with `[Word; L]`, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unsigned<const L: usize>(pub [Single; L]);

/// Unsigned long represented with `[Word; L]` by immutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsignedRef<'reference, const L: usize>(pub &'reference [Single; L]);

/// Unsigned long represented with `[Word; L]` by mutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, PartialEq, Eq)]
pub struct UnsignedMut<'reference, const L: usize>(pub &'reference mut [Single; L]);

/// Unsigned long dynamic number. (**WIP**)
#[cfg(feature = "dyn")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsignedDyn(Vec<Single>);

/// Bytes long represented with `[Word; L]`, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bytes<const L: usize>(pub [Single; L]);

/// Bytes long represented with `[Word; L]` by immutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BytesRef<'reference, const L: usize>(pub &'reference [Single; L]);

/// Bytes long represented with `[Word; L]` by mutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, PartialEq, Eq)]
pub struct BytesMut<'reference, const L: usize>(pub &'reference mut [Single; L]);

/// Bytes long dynamic number. (**WIP**)
#[cfg(feature = "dyn")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BytesDyn(Vec<Single>);

/// Digits iterator by `exp`.
///
/// For more info, see [`ToDigitsIter`] documentation.
#[derive(Debug, Clone)]
pub struct DigitsIter<'words, const L: usize, W: Word> {
    words: &'words [Single; L],
    bits: usize,
    mask: Double,
    cnt: usize,
    len: usize,
    acc: Double,
    shl: usize,
    idx: usize,
    _phantom: PhantomData<W>,
}

/// Digits iterator by `radix`.
///
/// For more info, see [`IntoDigitsIter`] documentation.
#[derive(Debug, Clone)]
pub struct DigitsRadixIter<const L: usize, W: Word> {
    words: [Single; L],
    radix: W,
    len: usize,
}

/// Error type for failable long conversion from array.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromArrError {
    /// Found invalid length during initializing from array.
    ///
    /// Array doesn't fit long by type (without leading-zeroes check).
    #[error("Found invalid length during initializing from array")]
    InvalidLength,
}

/// Error type for failable long conversion from slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromSliceError {
    /// Found invalid length during initializing from slice
    ///
    /// Slice doesn't fit long by type (without leading-zeroes check).
    #[error("Found invalid length during initializing from slice")]
    InvalidLength,
}

/// Error type for failable long conversion from digits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromDigitsError {
    /// Found invalid radix.
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix {
        /// Radix value.
        radix: usize,
    },
    /// Found invalid exp.
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent {
        /// Exponent value.
        exp: usize,
    },
    /// Found invalid digit.
    #[error("Found invalid digit '{digit}' during parsing from slice of radix '{radix}'")]
    InvalidDigit {
        /// Digit value.
        digit: usize,
        /// Radix value.
        radix: usize,
    },
}

/// Error type for failable long conversion from string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromStrError {
    /// Found empty during parsing from string.
    #[error("Found empty during parsing from string")]
    InvalidLength,
    /// Found invalid radix.
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix {
        /// Radix value.
        radix: usize,
    },
    /// Found invalid char.
    #[error("Found invalid char '{char}' during parsing from string of radix '{radix}'")]
    InvalidSymbol {
        /// Char value.
        char: char,
        /// Radix value.
        radix: u8,
    },
}

/// Error type for failable long conversion to digits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum ToDigitsError {
    /// Found invalid exp.
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent {
        /// Exponent value.
        exp: usize,
    },
}

/// Error type for failable long conversion into digits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum IntoDigitsError {
    /// Found invalid radix.
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix {
        /// Radix value.
        radix: usize,
    },
}

/// `From`/`To`/`Into` digits conversion by `exp` details.
///
/// For more info, see [`FromDigits`], [`FromDigitsIter`], [`ToDigits`], [`ToDigitsIter`] documentation.
pub struct ExpImpl<W: Word> {
    /// Exponent used in conversions.
    ///
    /// Radix is `1 << exp`.
    pub exp: W,
}

/// `From`/`To`/`Into` digits conversion by `radix` details.
///
/// For more info, see [`FromDigits`], [`FromDigitsIter`], [`IntoDigits`], [`IntoDigitsIter`] documentation.
pub struct RadixImpl<W: Word> {
    /// Radix used in conversions.
    ///
    /// Radix is arbitrary.
    pub radix: W,
}

/// `From`/`To`/`Into` digits conversion implementation trait.
///
/// - [`ExpImpl`] - for conversion by `exp`.
/// - [`RadixImpl`] - for conversion by `radix`.
pub trait DigitsImpl<W: Word> {}

/// Conversion from arbitrary digits represented by [`Word`].
///
/// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
pub trait FromDigits<W: Word, Impl: DigitsImpl<W>>: Sized {
    /// Conversion function.
    fn from_digits(digits: impl AsRef<[W]>, arg: Impl) -> Result<Self, FromDigitsError>;
}

/// Conversion from arbitrary digits iterator represented by [`Word`].
///
/// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
pub trait FromDigitsIter<W: Word, Impl: DigitsImpl<W>>: Sized {
    /// Conversion function.
    fn from_digits_iter<Words>(digits: Words, arg: Impl) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W> + DoubleEndedIterator;
}

/// Conversion to arbitrary digits represented by [`Word`] with `exp`.
///
/// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
pub trait ToDigits<'words>: Sized {
    /// Conversion function.
    fn to_digits<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Vec<W>, ToDigitsError>;
}

/// Conversion to arbitrary digits iterator represented by [`Word`] with `exp`.
///
/// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
pub trait ToDigitsIter<'words>: Sized {
    /// Conversion iterator.
    type Iter<W: Word>: WordsIterator<Item = W> + ExactSizeIterator
    where
        Self: 'words;

    /// Conversion function.
    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Self::Iter<W>, ToDigitsError>;
}

/// Conversion into arbitrary digits represented by [`Word`] with `radix`.
///
/// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
pub trait IntoDigits: Sized {
    /// Conversion function.
    fn into_digits<W: Word>(self, arg: RadixImpl<W>) -> Result<Vec<W>, IntoDigitsError>;
}

/// Conversion into arbitrary digits iterator represented by [`Word`] with `radix`.
///
/// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
pub trait IntoDigitsIter: Sized {
    /// Conversion iterator.
    type Iter<W: Word>: WordsIterator<Item = W> + ExactSizeIterator;

    /// Conversion function.
    fn into_digits_iter<W: Word>(self, arg: RadixImpl<W>) -> Result<Self::Iter<W>, IntoDigitsError>;
}

impl<W: Word> DigitsImpl<W> for ExpImpl<W> {}
impl<W: Word> DigitsImpl<W> for RadixImpl<W> {}

impl From<ToDigitsError> for IntoDigitsError {
    #[inline]
    fn from(value: ToDigitsError) -> Self {
        match value {
            ToDigitsError::InvalidExponent { exp } => Self::InvalidRadix { radix: exp.order() },
        }
    }
}

impl<const L: usize> Default for Signed<L> {
    #[inline]
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> Default for Unsigned<L> {
    #[inline]
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> Default for Bytes<L> {
    #[inline]
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> From<bool> for Signed<L> {
    #[inline]
    fn from(value: bool) -> Self {
        Self::from(value as i8)
    }
}

impl<const L: usize> From<bool> for Unsigned<L> {
    #[inline]
    fn from(value: bool) -> Self {
        Self::from(value as u8)
    }
}

impl<const L: usize> From<bool> for Bytes<L> {
    #[inline]
    fn from(value: bool) -> Self {
        Self::from(value as u8)
    }
}

from_primitive!(Signed [i8, i16, i32, i64, i128, isize]);
from_primitive!(Unsigned [u8, u16, u32, u64, u128, usize]);
from_primitive!(Bytes [u8, u16, u32, u64, u128, usize]);

impl<const L: usize> From<[Single; L]> for Signed<L> {
    #[inline]
    fn from(value: [Single; L]) -> Self {
        Self(value)
    }
}

impl<const L: usize> From<[Single; L]> for Unsigned<L> {
    #[inline]
    fn from(value: [Single; L]) -> Self {
        Self(value)
    }
}

impl<const L: usize> From<[Single; L]> for Bytes<L> {
    #[inline]
    fn from(value: [Single; L]) -> Self {
        Self(value)
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N]> for Signed<L> {
    #[inline]
    fn nd_from(value: &[W; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N]> for Unsigned<L> {
    #[inline]
    fn nd_from(value: &[W; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N]> for Bytes<L> {
    #[inline]
    fn nd_from(value: &[W; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W]> for Signed<L> {
    #[inline]
    fn nd_from(value: &[W]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W]> for Unsigned<L> {
    #[inline]
    fn nd_from(value: &[W]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W]> for Bytes<L> {
    #[inline]
    fn nd_from(value: &[W]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N]> for Signed<L> {
    type Error = TryFromArrError;

    #[inline]
    fn nd_try_from(value: &[W; N]) -> Result<Self, Self::Error> {
        try_from_arr(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N]> for Unsigned<L> {
    type Error = TryFromArrError;

    #[inline]
    fn nd_try_from(value: &[W; N]) -> Result<Self, Self::Error> {
        try_from_arr(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N]> for Bytes<L> {
    type Error = TryFromArrError;

    #[inline]
    fn nd_try_from(value: &[W; N]) -> Result<Self, Self::Error> {
        try_from_arr(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W]> for Signed<L> {
    type Error = TryFromSliceError;

    #[inline]
    fn nd_try_from(value: &[W]) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W]> for Unsigned<L> {
    type Error = TryFromSliceError;

    #[inline]
    fn nd_try_from(value: &[W]) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W]> for Bytes<L> {
    type Error = TryFromSliceError;

    #[inline]
    fn nd_try_from(value: &[W]) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Signed<L> {
    #[inline]
    fn from_iter<Iter: IntoIterator<Item = W>>(iter: Iter) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Unsigned<L> {
    #[inline]
    fn from_iter<Iter: IntoIterator<Item = W>>(iter: Iter) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Bytes<L> {
    #[inline]
    fn from_iter<Iter: IntoIterator<Item = W>>(iter: Iter) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize> NdFromStr<Dec> for Signed<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Dec) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Dec).map(Self)
    }
}

impl<const L: usize> NdFromStr<Dec> for Unsigned<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Dec) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Dec).map(Self)
    }
}

impl<const L: usize> NdFromStr<Bin> for Signed<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Bin) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Bin).map(Self)
    }
}

impl<const L: usize> NdFromStr<Bin> for Unsigned<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Bin) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Bin).map(Self)
    }
}

impl<const L: usize> NdFromStr<Bin> for Bytes<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Bin) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Bin).map(Self)
    }
}

impl<const L: usize> NdFromStr<Oct> for Signed<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Oct) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Oct).map(Self)
    }
}

impl<const L: usize> NdFromStr<Oct> for Unsigned<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Oct) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Oct).map(Self)
    }
}

impl<const L: usize> NdFromStr<Oct> for Bytes<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Oct) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Oct).map(Self)
    }
}

impl<const L: usize> NdFromStr<Hex> for Signed<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Hex) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Hex).map(Self)
    }
}

impl<const L: usize> NdFromStr<Hex> for Unsigned<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Hex) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Hex).map(Self)
    }
}

impl<const L: usize> NdFromStr<Hex> for Bytes<L> {
    type Err = FromStrError;

    #[inline]
    fn nd_from_str(s: &str, _: Hex) -> Result<Self, Self::Err> {
        from_str_impl!(@radix s, Hex).map(Self)
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = FromStrError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_impl!(@long s).map(Self)
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = FromStrError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_impl!(@long s).map(Self)
    }
}

impl<const L: usize> FromStr for Bytes<L> {
    type Err = FromStrError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_impl!(@bytes s).map(Self)
    }
}

impl<const L: usize, W: Word> AsRef<[W]> for Signed<L> {
    #[inline]
    fn as_ref(&self) -> &[W] {
        self.as_words_ref()
    }
}

impl<const L: usize, W: Word> AsRef<[W]> for Unsigned<L> {
    #[inline]
    fn as_ref(&self) -> &[W] {
        self.as_words_ref()
    }
}

impl<const L: usize, W: Word> AsRef<[W]> for Bytes<L> {
    #[inline]
    fn as_ref(&self) -> &[W] {
        self.as_words_ref()
    }
}

impl<const L: usize, W: Word> AsMut<[W]> for Signed<L> {
    #[inline]
    fn as_mut(&mut self) -> &mut [W] {
        self.as_words_mut()
    }
}

impl<const L: usize, W: Word> AsMut<[W]> for Unsigned<L> {
    #[inline]
    fn as_mut(&mut self) -> &mut [W] {
        self.as_words_mut()
    }
}

impl<const L: usize, W: Word> AsMut<[W]> for Bytes<L> {
    #[inline]
    fn as_mut(&mut self) -> &mut [W] {
        self.as_words_mut()
    }
}

impl<const L: usize> Ord for Signed<L> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let lhs_bit = self.0[L - 1] >> (BITS - 1);
        let rhs_bit = other.0[L - 1] >> (BITS - 1);

        let (lhs_xor, lhs_acc) = match lhs_bit {
            1 => (MAX, 1),
            _ => (0, 0),
        };

        let (rhs_xor, rhs_acc) = match rhs_bit {
            1 => (MAX, 1),
            _ => (0, 0),
        };

        let (lt, gt) = match (lhs_bit, rhs_bit) {
            (0, 0) => (-1, 1),
            (0, 1) => (1, 1),
            (1, 0) => (-1, -1),
            _ => (1, -1),
        };

        let lhs = uops::ExprIter {
            lhs: self.0.iter().copied().map(|val| val ^ lhs_xor),
            rhs: std::iter::repeat(0),
            mul: 1,
            acc: lhs_acc,
        };

        let rhs = uops::ExprIter {
            lhs: other.0.iter().copied().map(|val| val ^ rhs_xor),
            rhs: std::iter::repeat(0),
            mul: 1,
            acc: rhs_acc,
        };

        let cmp = lhs.zip(rhs).fold(0i8, |acc, (x, y)| match x.cmp(&y) {
            Ordering::Less => lt,
            Ordering::Equal => acc,
            Ordering::Greater => gt,
        });

        match cmp {
            -1 => Ordering::Less,
            1 => Ordering::Greater,
            _ => Ordering::Equal,
        }
    }
}

impl<const L: usize> Ord for Unsigned<L> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.iter().rev().cmp(other.0.iter().rev())
    }
}

impl<const L: usize> PartialOrd for Signed<L> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> PartialOrd for Unsigned<L> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> Display for Signed<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.abs().into_digits_iter(RadixImpl { radix: Dec::RADIX as Single }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Dec.into(), self.sign(), write_dec)
    }
}

impl<const L: usize> Display for Unsigned<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.into_digits_iter(RadixImpl { radix: Dec::RADIX as Single }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Dec.into(), self.sign(), write_dec)
    }
}

impl<const L: usize> Display for Bytes<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> Binary for Signed<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Unsigned<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Bytes<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Octal for Signed<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter(ExpImpl { exp: Oct::EXP as Single }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Unsigned<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter(ExpImpl { exp: Oct::EXP as Single }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Bytes<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter(ExpImpl { exp: Oct::EXP as Single }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> LowerHex for Signed<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Unsigned<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Bytes<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> UpperHex for Signed<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Unsigned<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Bytes<L> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

ndops::def! { @ndun <const L: usize> (value: &Signed<L>) -> Signed<L>, [
    ! uops::not(&value.0).with(Signed),
    - uops::neg(&value.0).with(Signed),

    - @checked uops::neg(&value.0).checked(Signed),
    - @strict uops::neg(&value.0).strict(Signed),
    - @wrapping uops::neg(&value.0).with(Signed),
    - @saturating uops::neg(&value.0).checked(Signed).unwrap_or(Signed::MAX),
    - @overflowing uops::neg(&value.0).overflowing(Signed),
] }

ndops::def! { @ndun <const L: usize> (value: &Unsigned<L>) -> Unsigned<L>, [
    ! uops::not(&value.0).with(Unsigned),
] }

ndops::def! { @ndun <const L: usize> (value: &Bytes<L>) -> Bytes<L>, [
    ! uops::not(&value.0).with(Bytes),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, rhs: &Signed<L>) -> Signed<L>, [
    + uops::add(&lhs.0, &rhs.0).with(Signed),
    - uops::sub(&lhs.0, &rhs.0).with(Signed),
    * algo::mul(&lhs.0, &rhs.0).with(Signed),

    / algo::div(&lhs.abs().0, &rhs.abs().0).wrapping(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).0,
    % algo::div(&lhs.abs().0, &rhs.abs().0).wrapping(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).1,

    | uops::bitor(&lhs.0, &rhs.0).eval(),
    & uops::bitand(&lhs.0, &rhs.0).eval(),
    ^ uops::bitxor(&lhs.0, &rhs.0).eval(),

    + @checked uops::add(&lhs.0, &rhs.0).checked(Signed),
    - @checked uops::sub(&lhs.0, &rhs.0).checked(Signed),
    * @checked algo::mul(&lhs.0, &rhs.0).checked(Signed),

    / @checked algo::div(&lhs.abs().0, &rhs.abs().0).checked(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).map(|(res, _)| res),
    % @checked algo::div(&lhs.abs().0, &rhs.abs().0).checked(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).map(|(_, res)| res),

    + @strict uops::add(&lhs.0, &rhs.0).strict(Signed),
    - @strict uops::sub(&lhs.0, &rhs.0).strict(Signed),
    * @strict algo::mul(&lhs.0, &rhs.0).strict(Signed),

    / @strict algo::div(&lhs.abs().0, &rhs.abs().0).strict(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).0,
    % @strict algo::div(&lhs.abs().0, &rhs.abs().0).strict(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).1,

    + @wrapping uops::add(&lhs.0, &rhs.0).with(Signed),
    - @wrapping uops::sub(&lhs.0, &rhs.0).with(Signed),
    * @wrapping algo::mul(&lhs.0, &rhs.0).with(Signed),

    / @wrapping algo::div(&lhs.abs().0, &rhs.abs().0).wrapping(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).0,
    % @wrapping algo::div(&lhs.abs().0, &rhs.abs().0).wrapping(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).1,

    + @overflowing uops::add(&lhs.0, &rhs.0).overflowing(Signed),
    - @overflowing uops::sub(&lhs.0, &rhs.0).overflowing(Signed),
    * @overflowing algo::mul(&lhs.0, &rhs.0).overflowing(Signed),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, rhs: usize) -> Signed<L> for Signed<L>, [
    << uops::shl(&lhs.0, rhs).signed().with(Signed),
    >> uops::shr(&lhs.0, rhs).signed().with(Signed),

    << @unbounded uops::shl(&lhs.0, rhs).signed().with(Signed),
    >> @unbounded uops::shr(&lhs.0, rhs).signed().with(Signed),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, rhs: &Unsigned<L>) -> Unsigned<L>, [
    + uops::add(&lhs.0, &rhs.0).with(Unsigned),
    - uops::sub(&lhs.0, &rhs.0).with(Unsigned),
    * algo::mul(&lhs.0, &rhs.0).with(Unsigned),

    / algo::div(&lhs.0, &rhs.0).wrapping(Unsigned, Unsigned).0,
    % algo::div(&lhs.0, &rhs.0).wrapping(Unsigned, Unsigned).1,

    | uops::bitor(&lhs.0, &rhs.0).eval(),
    & uops::bitand(&lhs.0, &rhs.0).eval(),
    ^ uops::bitxor(&lhs.0, &rhs.0).eval(),

    + @checked uops::add(&lhs.0, &rhs.0).checked(Unsigned),
    - @checked uops::sub(&lhs.0, &rhs.0).checked(Unsigned),
    * @checked algo::mul(&lhs.0, &rhs.0).checked(Unsigned),

    / @checked algo::div(&lhs.0, &rhs.0).checked(Unsigned, Unsigned).map(|(res, _)| res),
    % @checked algo::div(&lhs.0, &rhs.0).checked(Unsigned, Unsigned).map(|(_, res)| res),

    + @strict uops::add(&lhs.0, &rhs.0).strict(Unsigned),
    - @strict uops::sub(&lhs.0, &rhs.0).strict(Unsigned),
    * @strict algo::mul(&lhs.0, &rhs.0).strict(Unsigned),

    / @strict algo::div(&lhs.0, &rhs.0).strict(Unsigned, Unsigned).0,
    % @strict algo::div(&lhs.0, &rhs.0).strict(Unsigned, Unsigned).1,

    + @wrapping uops::add(&lhs.0, &rhs.0).with(Unsigned),
    - @wrapping uops::sub(&lhs.0, &rhs.0).with(Unsigned),
    * @wrapping algo::mul(&lhs.0, &rhs.0).with(Unsigned),

    / @wrapping algo::div(&lhs.0, &rhs.0).wrapping(Unsigned, Unsigned).0,
    % @wrapping algo::div(&lhs.0, &rhs.0).wrapping(Unsigned, Unsigned).1,

    + @overflowing uops::add(&lhs.0, &rhs.0).overflowing(Unsigned),
    - @overflowing uops::sub(&lhs.0, &rhs.0).overflowing(Unsigned),
    * @overflowing algo::mul(&lhs.0, &rhs.0).overflowing(Unsigned),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, rhs: usize) -> Unsigned<L> for Unsigned<L>, [
    << uops::shl(&lhs.0, rhs).with(Unsigned),
    >> uops::shr(&lhs.0, rhs).with(Unsigned),

    << @unbounded uops::shl(&lhs.0, rhs).with(Unsigned),
    >> @unbounded uops::shr(&lhs.0, rhs).with(Unsigned),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, rhs: &Bytes<L>) -> Bytes<L>, [
    | uops::bitor(&lhs.0, &rhs.0).eval(),
    & uops::bitand(&lhs.0, &rhs.0).eval(),
    ^ uops::bitxor(&lhs.0, &rhs.0).eval(),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, rhs: usize) -> Bytes<L> for Bytes<L>, [
    << uops::shl(&lhs.0, rhs).with(Bytes),
    >> uops::shr(&lhs.0, rhs).with(Bytes),

    << @unbounded uops::shl(&lhs.0, rhs).with(Bytes),
    >> @unbounded uops::shr(&lhs.0, rhs).with(Bytes),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, rhs: &Signed<L>), [
    += uops::add(&mut lhs.0, &rhs.0).eval(),
    -= uops::sub(&mut lhs.0, &rhs.0).eval(),
    *= algo::mul(&mut lhs.0, &rhs.0).eval(),

    /= { *lhs = algo::div(&lhs.abs().0, &rhs.abs().0).wrapping(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).0; },
    %= { *lhs = algo::div(&lhs.abs().0, &rhs.abs().0).wrapping(|res| Signed(res).signed(lhs.sign() * rhs.sign()), |res| Signed(res).signed(lhs.sign())).1; },

    |= uops::bitor(&mut lhs.0, &rhs.0).eval(),
    &= uops::bitand(&mut lhs.0, &rhs.0).eval(),
    ^= uops::bitxor(&mut lhs.0, &rhs.0).eval(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, rhs: usize) for Signed<L>, [
    <<= uops::shl(&mut lhs.0, rhs).signed().eval(),
    >>= uops::shr(&mut lhs.0, rhs).signed().eval(),

    <<= @unbounded uops::shl(&mut lhs.0, rhs).signed().eval(),
    >>= @unbounded uops::shr(&mut lhs.0, rhs).signed().eval(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: &Unsigned<L>), [
    += uops::add(&mut lhs.0, &rhs.0).eval(),
    -= uops::sub(&mut lhs.0, &rhs.0).eval(),
    *= algo::mul(&mut lhs.0, &rhs.0).eval(),

    /= algo::div_mut(&mut lhs.0, &rhs.0).wrapping(),
    %= algo::rem_mut(&mut lhs.0, &rhs.0).wrapping(),

    |= uops::bitor(&mut lhs.0, &rhs.0).eval(),
    &= uops::bitand(&mut lhs.0, &rhs.0).eval(),
    ^= uops::bitxor(&mut lhs.0, &rhs.0).eval(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: usize) for Unsigned<L>, [
    <<= uops::shl(&mut lhs.0, rhs).eval(),
    >>= uops::shr(&mut lhs.0, rhs).eval(),

    <<= @unbounded uops::shl(&mut lhs.0, rhs).eval(),
    >>= @unbounded uops::shr(&mut lhs.0, rhs).eval(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, rhs: &Bytes<L>), [
    |= uops::bitor(&mut lhs.0, &rhs.0).eval(),
    &= uops::bitand(&mut lhs.0, &rhs.0).eval(),
    ^= uops::bitxor(&mut lhs.0, &rhs.0).eval(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, rhs: usize) for Bytes<L>, [
    <<= uops::shl(&mut lhs.0, rhs).eval(),
    >>= uops::shr(&mut lhs.0, rhs).eval(),

    <<= @unbounded uops::shl(&mut lhs.0, rhs).eval(),
    >>= @unbounded uops::shr(&mut lhs.0, rhs).eval(),
] }

ndops::def! { @stdun <const L: usize> (*value: &Signed<L>) -> Signed<L>, [
    ! <Signed<L> as NdNot>::nd_not(&value),
    - <Signed<L> as NdNeg>::nd_neg(&value),
] }

ndops::def! { @stdun <const L: usize> (*value: &Unsigned<L>) -> Unsigned<L>, [
    ! <Unsigned<L> as NdNot>::nd_not(&value),
] }

ndops::def! { @stdun <const L: usize> (*value: &Bytes<L>) -> Bytes<L>, [
    ! <Bytes<L> as NdNot>::nd_not(&value),
] }

ndops::def! { @stdbin <const L: usize> (*lhs: &Signed<L>, *rhs: &Signed<L>) -> Signed<L>, [
    + <Signed<L> as NdAdd>::nd_add(&lhs, &rhs),
    - <Signed<L> as NdSub>::nd_sub(&lhs, &rhs),
    * <Signed<L> as NdMul>::nd_mul(&lhs, &rhs),
    / <Signed<L> as NdDiv>::nd_div(&lhs, &rhs),
    % <Signed<L> as NdRem>::nd_rem(&lhs, &rhs),
    | <Signed<L> as NdBitOr>::nd_bitor(&lhs, &rhs),
    & <Signed<L> as NdBitAnd>::nd_bitand(&lhs, &rhs),
    ^ <Signed<L> as NdBitXor>::nd_bitxor(&lhs, &rhs),
] }

ndops::def! { @stdbin <const L: usize> (*lhs: &Signed<L>, rhs: usize) -> Signed<L>, [
    << <Signed<L> as NdShl>::nd_shl(&lhs, rhs),
    >> <Signed<L> as NdShr>::nd_shr(&lhs, rhs),
] }

ndops::def! { @stdbin <const L: usize> (*lhs: &Unsigned<L>, *rhs: &Unsigned<L>) -> Unsigned<L>, [
    + <Unsigned<L> as NdAdd>::nd_add(&lhs, &rhs),
    - <Unsigned<L> as NdSub>::nd_sub(&lhs, &rhs),
    * <Unsigned<L> as NdMul>::nd_mul(&lhs, &rhs),
    / <Unsigned<L> as NdDiv>::nd_div(&lhs, &rhs),
    % <Unsigned<L> as NdRem>::nd_rem(&lhs, &rhs),
    | <Unsigned<L> as NdBitOr>::nd_bitor(&lhs, &rhs),
    & <Unsigned<L> as NdBitAnd>::nd_bitand(&lhs, &rhs),
    ^ <Unsigned<L> as NdBitXor>::nd_bitxor(&lhs, &rhs),
] }

ndops::def! { @stdbin <const L: usize> (*lhs: &Unsigned<L>, rhs: usize) -> Unsigned<L>, [
    << <Unsigned<L> as NdShl>::nd_shl(&lhs, rhs),
    >> <Unsigned<L> as NdShr>::nd_shr(&lhs, rhs),
] }

ndops::def! { @stdbin <const L: usize> (*lhs: &Bytes<L>, *rhs: &Bytes<L>) -> Bytes<L>, [
    | <Bytes<L> as NdBitOr>::nd_bitor(&lhs, &rhs),
    & <Bytes<L> as NdBitAnd>::nd_bitand(&lhs, &rhs),
    ^ <Bytes<L> as NdBitXor>::nd_bitxor(&lhs, &rhs),
] }

ndops::def! { @stdbin <const L: usize> (*lhs: &Bytes<L>, rhs: usize) -> Bytes<L>, [
    << <Bytes<L> as NdShl>::nd_shl(&lhs, rhs),
    >> <Bytes<L> as NdShr>::nd_shr(&lhs, rhs),
] }

ndops::def! { @stdmut <const L: usize> (lhs: &mut Signed<L>, *rhs: &Signed<L>), [
    += <Signed<L> as NdAddAssign>::nd_add_assign(lhs, &rhs),
    -= <Signed<L> as NdSubAssign>::nd_sub_assign(lhs, &rhs),
    *= <Signed<L> as NdMulAssign>::nd_mul_assign(lhs, &rhs),
    /= <Signed<L> as NdDivAssign>::nd_div_assign(lhs, &rhs),
    %= <Signed<L> as NdRemAssign>::nd_rem_assign(lhs, &rhs),
    |= <Signed<L> as NdBitOrAssign>::nd_bitor_assign(lhs, &rhs),
    &= <Signed<L> as NdBitAndAssign>::nd_bitand_assign(lhs, &rhs),
    ^= <Signed<L> as NdBitXorAssign>::nd_bitxor_assign(lhs, &rhs),
] }

ndops::def! { @stdmut <const L: usize> (lhs: &mut Signed<L>, rhs: usize), [
    <<= <Signed<L> as NdShlAssign>::nd_shl_assign(lhs, rhs),
    >>= <Signed<L> as NdShrAssign>::nd_shr_assign(lhs, rhs),
] }

ndops::def! { @stdmut <const L: usize> (lhs: &mut Unsigned<L>, *rhs: &Unsigned<L>), [
    += <Unsigned<L> as NdAddAssign>::nd_add_assign(lhs, &rhs),
    -= <Unsigned<L> as NdSubAssign>::nd_sub_assign(lhs, &rhs),
    *= <Unsigned<L> as NdMulAssign>::nd_mul_assign(lhs, &rhs),
    /= <Unsigned<L> as NdDivAssign>::nd_div_assign(lhs, &rhs),
    %= <Unsigned<L> as NdRemAssign>::nd_rem_assign(lhs, &rhs),
    |= <Unsigned<L> as NdBitOrAssign>::nd_bitor_assign(lhs, &rhs),
    &= <Unsigned<L> as NdBitAndAssign>::nd_bitand_assign(lhs, &rhs),
    ^= <Unsigned<L> as NdBitXorAssign>::nd_bitxor_assign(lhs, &rhs),
] }

ndops::def! { @stdmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: usize), [
    <<= <Unsigned<L> as NdShlAssign>::nd_shl_assign(lhs, rhs),
    >>= <Unsigned<L> as NdShrAssign>::nd_shr_assign(lhs, rhs),
] }

ndops::def! { @stdmut <const L: usize> (lhs: &mut Bytes<L>, *rhs: &Bytes<L>), [
    |= <Bytes<L> as NdBitOrAssign>::nd_bitor_assign(lhs, &rhs),
    &= <Bytes<L> as NdBitAndAssign>::nd_bitand_assign(lhs, &rhs),
    ^= <Bytes<L> as NdBitXorAssign>::nd_bitxor_assign(lhs, &rhs),
] }

ndops::def! { @stdmut <const L: usize> (lhs: &mut Bytes<L>, rhs: usize), [
    <<= <Bytes<L> as NdShlAssign>::nd_shl_assign(lhs, rhs),
    >>= <Bytes<L> as NdShrAssign>::nd_shr_assign(lhs, rhs),
] }

impl<const L: usize> Signed<L> {
    #[allow(unused)]
    const CHECK: () = assert!(0 < L);

    from_primitive_const!([
        (from_i8, i8),
        (from_i16, i16),
        (from_i32, i32),
        (from_i64, i64),
        (from_i128, i128),
        (from_isize, isize),
    ]);

    /// Const conversion from bytes.
    ///
    /// Truncates on overflow.
    ///
    /// **Must** be used **ONLY** in const context.
    #[inline]
    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }

    /// Long number sign.
    #[inline]
    pub fn sign(&self) -> Sign {
        uops::sign(&self.0, Sign::POS, Sign::NEG)
    }

    /// Absolute value.
    #[inline]
    pub fn abs(&self) -> Signed<L> {
        Signed(uops::posx(&self.0).with(|res| res))
    }

    /// Absolute unsigned value.
    #[inline]
    pub fn abs_unsigned(&self) -> Unsigned<L> {
        uops::posx(&self.0).with(Unsigned)
    }

    /// Creates new signed with specified sign from raw `self.0`.
    #[inline]
    pub fn signed(&self, sign: Sign) -> Self {
        let bit = match self.sign() * sign {
            Sign::ZERO => false,
            Sign::NEG => true,
            Sign::POS => false,
        };

        uops::sgx(&self.0, bit).with(Self)
    }

    /// Creates new unsigned from raw `self.0`.
    #[inline]
    pub fn unsigned(self) -> Unsigned<L> {
        Unsigned(self.0)
    }
}

impl<const L: usize> Unsigned<L> {
    #[allow(unused)]
    const CHECK: () = assert!(0 < L);

    from_primitive_const!([
        (from_u8, u8),
        (from_u16, u16),
        (from_u32, u32),
        (from_u64, u64),
        (from_u128, u128),
        (from_usize, usize),
    ]);

    /// Const conversion from bytes.
    ///
    /// Truncates on overflow.
    ///
    /// **Must** be used **ONLY** in const context.
    #[inline]
    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }

    /// Long number sign.
    #[inline]
    pub fn sign(&self) -> Sign {
        uops::sign(&self.0, Sign::POS, Sign::POS)
    }

    /// Creates new signed with specified sign from raw `self.0`.
    #[inline]
    pub fn signed(&self, sign: Sign) -> Signed<L> {
        let bit = match sign {
            Sign::ZERO => false,
            Sign::NEG => true,
            Sign::POS => false,
        };

        uops::sgx(&self.0, bit).with(Signed)
    }

    /// Creates new unsigned from raw `self.0`.
    #[inline]
    pub fn unsigned(self) -> Self {
        Self(self.0)
    }
}

impl<const L: usize> Bytes<L> {
    #[allow(unused)]
    const CHECK: () = assert!(0 < L);

    from_primitive_const!([
        (from_u8, u8),
        (from_u16, u16),
        (from_u32, u32),
        (from_u64, u64),
        (from_u128, u128),
        (from_usize, usize),
    ]);

    /// Const conversion from bytes.
    ///
    /// Truncates on overflow.
    ///
    /// **Must** be used **ONLY** in const context.
    #[inline]
    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }
}

impl<const L: usize, W: Word> FromDigits<W, ExpImpl<W>> for Signed<L> {
    #[inline]
    fn from_digits(digits: impl AsRef<[W]>, arg: ExpImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, ExpImpl<W>> for Unsigned<L> {
    #[inline]
    fn from_digits(digits: impl AsRef<[W]>, arg: ExpImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, ExpImpl<W>> for Bytes<L> {
    #[inline]
    fn from_digits(digits: impl AsRef<[W]>, arg: ExpImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, ExpImpl<W>> for Signed<L> {
    #[inline]
    fn from_digits_iter<Words>(digits: Words, arg: ExpImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W>,
    {
        from_digits_iter(digits, arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, ExpImpl<W>> for Unsigned<L> {
    #[inline]
    fn from_digits_iter<Words>(digits: Words, arg: ExpImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W>,
    {
        from_digits_iter(digits, arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, ExpImpl<W>> for Bytes<L> {
    #[inline]
    fn from_digits_iter<Words>(digits: Words, arg: ExpImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W>,
    {
        from_digits_iter(digits, arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, RadixImpl<W>> for Signed<L> {
    #[inline]
    fn from_digits(digits: impl AsRef<[W]>, arg: RadixImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits_radix(digits.as_ref(), arg.radix).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, RadixImpl<W>> for Unsigned<L> {
    #[inline]
    fn from_digits(digits: impl AsRef<[W]>, arg: RadixImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits_radix(digits.as_ref(), arg.radix).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, RadixImpl<W>> for Signed<L> {
    #[inline]
    fn from_digits_iter<Words>(digits: Words, arg: RadixImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W> + DoubleEndedIterator,
    {
        from_digits_radix_iter(digits, arg.radix).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, RadixImpl<W>> for Unsigned<L> {
    #[inline]
    fn from_digits_iter<Words>(digits: Words, arg: RadixImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W> + DoubleEndedIterator,
    {
        from_digits_radix_iter(digits, arg.radix).map(Self)
    }
}

impl<'words, const L: usize> ToDigits<'words> for Signed<L> {
    #[inline]
    fn to_digits<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigits<'words> for Unsigned<L> {
    #[inline]
    fn to_digits<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigits<'words> for Bytes<L> {
    #[inline]
    fn to_digits<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigitsIter<'words> for Signed<L> {
    type Iter<W: Word> = DigitsIter<'words, L, W>;

    #[inline]
    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Self::Iter<W>, ToDigitsError> {
        to_digits_iter(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigitsIter<'words> for Unsigned<L> {
    type Iter<W: Word> = DigitsIter<'words, L, W>;

    #[inline]
    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Self::Iter<W>, ToDigitsError> {
        to_digits_iter(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigitsIter<'words> for Bytes<L> {
    type Iter<W: Word> = DigitsIter<'words, L, W>;

    #[inline]
    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl<W>) -> Result<Self::Iter<W>, ToDigitsError> {
        to_digits_iter(&self.0, arg.exp)
    }
}

impl<const L: usize> IntoDigits for Signed<L> {
    #[inline]
    fn into_digits<W: Word>(self, arg: RadixImpl<W>) -> Result<Vec<W>, IntoDigitsError> {
        into_digits(self.0, arg.radix)
    }
}

impl<const L: usize> IntoDigits for Unsigned<L> {
    #[inline]
    fn into_digits<W: Word>(self, arg: RadixImpl<W>) -> Result<Vec<W>, IntoDigitsError> {
        into_digits(self.0, arg.radix)
    }
}

impl<const L: usize> IntoDigitsIter for Signed<L> {
    type Iter<W: Word> = DigitsRadixIter<L, W>;

    #[inline]
    fn into_digits_iter<W: Word>(self, arg: RadixImpl<W>) -> Result<Self::Iter<W>, IntoDigitsError> {
        into_digits_iter(self.0, arg.radix)
    }
}

impl<const L: usize> IntoDigitsIter for Unsigned<L> {
    type Iter<W: Word> = DigitsRadixIter<L, W>;

    #[inline]
    fn into_digits_iter<W: Word>(self, arg: RadixImpl<W>) -> Result<Self::Iter<W>, IntoDigitsError> {
        into_digits_iter(self.0, arg.radix)
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> EqCt for Signed<L> {
    #[inline(never)]
    fn eq_ct(&self, other: &Self) -> MaskCt {
        eq_ct!(self.0.iter(), other.0.iter())
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> EqCt for Unsigned<L> {
    #[inline(never)]
    fn eq_ct(&self, other: &Self) -> MaskCt {
        eq_ct!(self.0.iter(), other.0.iter())
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> EqCt for Bytes<L> {
    #[inline(never)]
    fn eq_ct(&self, other: &Self) -> MaskCt {
        eq_ct!(self.0.iter(), other.0.iter())
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> LtCt for Signed<L> {
    #[inline(never)]
    fn lt_ct(&self, other: &Self) -> MaskCt {
        let lhs_sign = uops::sign_ct(&self.0);
        let rhs_sign = uops::sign_ct(&other.0);

        let cmp = cmp_ct!(self.0.iter(), other.0.iter());

        let sign_lt = lhs_sign.lt_ct(&rhs_sign);
        let sign_eq = lhs_sign.eq_ct(&rhs_sign);
        let cmp_lt = cmp.eq_ct(&-1);

        sign_lt | sign_eq & cmp_lt
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> GtCt for Signed<L> {
    #[inline(never)]
    fn gt_ct(&self, other: &Self) -> MaskCt {
        let lhs_sign = uops::sign_ct(&self.0);
        let rhs_sign = uops::sign_ct(&other.0);

        let cmp = cmp_ct!(self.0.iter(), other.0.iter());

        let sign_gt = lhs_sign.gt_ct(&rhs_sign);
        let sign_eq = lhs_sign.eq_ct(&rhs_sign);
        let cmp_gt = cmp.eq_ct(&1);

        sign_gt | sign_eq & cmp_gt
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> LtCt for Unsigned<L> {
    #[inline(never)]
    fn lt_ct(&self, other: &Self) -> MaskCt {
        let cmp = cmp_ct!(self.0.iter(), other.0.iter());

        cmp.eq_ct(&-1) & MaskCt::MAX
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> GtCt for Unsigned<L> {
    #[inline(never)]
    fn gt_ct(&self, other: &Self) -> MaskCt {
        let cmp = cmp_ct!(self.0.iter(), other.0.iter());

        cmp.eq_ct(&1) & MaskCt::MAX
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> SelectCt for Signed<L> {
    #[inline(never)]
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
        let lhs_mask = Self([Single::from_ne_bytes([mask; BYTES]); L]);
        let rhs_mask = Self([Single::from_ne_bytes([!mask; BYTES]); L]);

        lhs & lhs_mask | rhs & rhs_mask
    }
}

#[cfg(feature = "const-time")]
impl<const L: usize> SelectCt for Unsigned<L> {
    #[inline(never)]
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
        let lhs_mask = Self([Single::from_ne_bytes([mask; BYTES]); L]);
        let rhs_mask = Self([Single::from_ne_bytes([!mask; BYTES]); L]);

        lhs & lhs_mask | rhs & rhs_mask
    }
}

impl<'words, const L: usize, W: Word> ExactSizeIterator for DigitsIter<'words, L, W> {}
impl<'words, const L: usize, W: Word> Iterator for DigitsIter<'words, L, W> {
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
            self.acc |= (self.words[self.idx] as Double) << self.shl;
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

impl<const L: usize, W: Word> ExactSizeIterator for DigitsRadixIter<L, W> {}
impl<const L: usize, W: Word> Iterator for DigitsRadixIter<L, W> {
    type Item = W;

    fn next(&mut self) -> Option<Self::Item> {
        let radix = self.radix.as_double();

        let mut any = 0;
        let mut acc = 0;

        for word in self.words.iter_mut().rev() {
            any |= *word;
            acc = (acc << BITS) | *word as Double;

            *word = (acc / radix) as Single;

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

impl<const L: usize> BytesLen for Signed<L> {
    const BITS: usize = (L * BITS);
    const BYTES: usize = (L * BYTES);
}

impl<const L: usize> BytesLen for Unsigned<L> {
    const BITS: usize = (L * BITS);
    const BYTES: usize = (L * BYTES);
}

impl<const L: usize> BytesLen for Bytes<L> {
    const BITS: usize = (L * BITS);
    const BYTES: usize = (L * BYTES);
}

impl<const L: usize> BytesFn for Signed<L> {
    #[inline]
    fn read(&self, offset: Offset) -> Single {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        uops::read(&self.0, offset)
    }

    #[inline]
    fn write_bitor(&mut self, mask: Single, offset: Offset) -> &mut Self {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, |=);

        self
    }

    #[inline]
    fn write_bitand(&mut self, mask: Single, offset: Offset) -> &mut Self {
        use std::ops::Not;

        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, &=, .not());

        self
    }

    #[inline]
    fn write_bitxor(&mut self, mask: Single, offset: Offset) -> &mut Self {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, ^=);

        self
    }
}

impl<const L: usize> BytesFn for Unsigned<L> {
    #[inline]
    fn read(&self, offset: Offset) -> Single {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        uops::read(&self.0, offset)
    }

    #[inline]
    fn write_bitor(&mut self, mask: Single, offset: Offset) -> &mut Self {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, |=);

        self
    }

    #[inline]
    fn write_bitand(&mut self, mask: Single, offset: Offset) -> &mut Self {
        use std::ops::Not;

        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, &=, .not());

        self
    }

    #[inline]
    fn write_bitxor(&mut self, mask: Single, offset: Offset) -> &mut Self {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, ^=);

        self
    }
}

impl<const L: usize> BytesFn for Bytes<L> {
    #[inline]
    fn read(&self, offset: Offset) -> Single {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        uops::read(&self.0, offset)
    }

    #[inline]
    fn write_bitor(&mut self, mask: Single, offset: Offset) -> &mut Self {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, |=);

        self
    }

    #[inline]
    fn write_bitand(&mut self, mask: Single, offset: Offset) -> &mut Self {
        use std::ops::Not;

        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, &=, .not());

        self
    }

    #[inline]
    fn write_bitxor(&mut self, mask: Single, offset: Offset) -> &mut Self {
        let offset = match offset {
            Offset::Left(val) => val,
            Offset::Right(val) => (L * BITS).saturating_sub(val),
        };

        write_bitop_impl!(&mut self.0, mask, offset, ^=);

        self
    }
}

impl<const L: usize> AsBytesRef for Signed<L> {
    #[inline]
    fn as_bytes_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl<const L: usize> AsBytesMut for Signed<L> {
    #[inline]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }
}

impl<const L: usize> AsWordsRef for Signed<L> {
    #[inline]
    fn as_words_ref<W: Word>(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }
}

impl<const L: usize> AsWordsMut for Signed<L> {
    #[inline]
    fn as_words_mut<W: Word>(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }
}

impl<const L: usize> AsBytesRef for Unsigned<L> {
    #[inline]
    fn as_bytes_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl<const L: usize> AsBytesMut for Unsigned<L> {
    #[inline]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }
}

impl<const L: usize> AsWordsRef for Unsigned<L> {
    #[inline]
    fn as_words_ref<W: Word>(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }
}

impl<const L: usize> AsWordsMut for Unsigned<L> {
    #[inline]
    fn as_words_mut<W: Word>(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }
}

impl<const L: usize> AsBytesRef for Bytes<L> {
    #[inline]
    fn as_bytes_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl<const L: usize> AsBytesMut for Bytes<L> {
    #[inline]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }
}

impl<const L: usize> AsWordsRef for Bytes<L> {
    #[inline]
    fn as_words_ref<W: Word>(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }
}

impl<const L: usize> AsWordsMut for Bytes<L> {
    #[inline]
    fn as_words_mut<W: Word>(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }
}

impl<const L: usize> NumFn for Signed<L> {
    #[inline]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    #[inline]
    fn is_even(&self) -> bool {
        self.0[0] & 1 == 0
    }

    #[inline]
    fn write_odd(&mut self) -> &mut Self {
        self.0[0] |= 1;
        self
    }

    #[inline]
    fn write_even(&mut self) -> &mut Self {
        self.0[0] &= !1;
        self
    }

    #[inline]
    fn write_alt(&mut self) -> &mut Self {
        self.0[0] ^= 1;
        self
    }
}

impl<const L: usize> NumFn for Unsigned<L> {
    #[inline]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    #[inline]
    fn is_even(&self) -> bool {
        self.0[0] & 1 == 0
    }

    #[inline]
    fn write_odd(&mut self) -> &mut Self {
        self.0[0] |= 1;
        self
    }

    #[inline]
    fn write_even(&mut self) -> &mut Self {
        self.0[0] &= !1;
        self
    }

    #[inline]
    fn write_alt(&mut self) -> &mut Self {
        self.0[0] ^= 1;
        self
    }
}

impl<const L: usize> Num for Signed<L> {
    type Signed = Signed<L>;
    type Unsigned = Unsigned<L>;
}

impl<const L: usize> Num for Unsigned<L> {
    type Signed = Signed<L>;
    type Unsigned = Unsigned<L>;
}

impl<const L: usize> NumSigned for Signed<L> {}
impl<const L: usize> NumUnsigned for Unsigned<L> {
    #[inline]
    fn order(&self) -> usize {
        let len = length!(&self.0);

        match len {
            0 => 0,
            l => (l - 1) * BITS + self.0[l - 1].order(),
        }
    }

    #[inline]
    fn log(&self) -> Self {
        let len = length!(&self.0);

        match len {
            0 => Self::ZERO,
            l => Self::from((l - 1) * BITS + self.0[l - 1].order()),
        }
    }

    #[inline]
    fn sqrt(&self) -> Self {
        todo!()
    }
}

impl<const L: usize> NdRand for Signed<L> {}
impl<const L: usize> NdRand for Unsigned<L> {}

impl<const L: usize> NdPow for Signed<L> {}
impl<const L: usize> NdPow for Unsigned<L> {}

impl<const L: usize> NdGcd for Signed<L> {}
impl<const L: usize> NdGcd for Unsigned<L> {}

impl<const L: usize> Zero for Signed<L> {
    const ZERO: Self = Self([0; L]);
}

impl<const L: usize> Zero for Unsigned<L> {
    const ZERO: Self = Self([0; L]);
}

impl<const L: usize> One for Signed<L> {
    const ONE: Self = Self({
        let mut res = [MIN; L];

        res[0] = 1;
        res
    });
}

impl<const L: usize> One for Unsigned<L> {
    const ONE: Self = Self({
        let mut res = [MIN; L];

        res[0] = 1;
        res
    });
}

impl<const L: usize> Min for Signed<L> {
    const MIN: Self = Self({
        let mut res = [MIN; L];

        res[L - 1] = 1 << (BITS - 1);
        res
    });
}

impl<const L: usize> Min for Unsigned<L> {
    const MIN: Self = Self([MIN; L]);
}

impl<const L: usize> Max for Signed<L> {
    const MAX: Self = Self({
        let mut res = [MAX; L];

        res[L - 1] = MAX >> 1;
        res
    });
}

impl<const L: usize> Max for Unsigned<L> {
    const MAX: Self = Self([MAX; L]);
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

fn try_from_arr<const L: usize, const N: usize, W: Word>(
    arr: &[W; N],
    default: Single,
) -> Result<[Single; L], TryFromArrError> {
    match (N * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_arr(arr, default)),
        Ordering::Equal => Ok(from_arr(arr, default)),
        Ordering::Greater => Err(TryFromArrError::InvalidLength),
    }
}

fn try_from_slice<const L: usize, W: Word>(slice: &[W]) -> Result<[Single; L], TryFromSliceError> {
    match (slice.len() * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_slice(slice)),
        Ordering::Equal => Ok(from_slice(slice)),
        Ordering::Greater => Err(TryFromSliceError::InvalidLength),
    }
}

fn from_arr<const L: usize, const N: usize, W: Word>(arr: &[W; N], default: Single) -> [Single; L] {
    let len = N.min(L * BYTES / W::BYTES);

    let mut res = [default; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])[..len].copy_from_slice(&arr[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_slice<const L: usize, W: Word>(slice: &[W]) -> [Single; L] {
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

fn from_digits_validate<W: Word, Words>(digits: Words, radix: W) -> Result<(), FromDigitsError>
where
    Words: WordsIterator<Item = W>,
{
    let radix = radix.as_usize();

    if radix < 2 {
        return Err(FromDigitsError::InvalidRadix { radix });
    }

    if let Some(digit) = digits.map(|digit| digit.as_usize()).find(|&digit| digit >= radix) {
        return Err(FromDigitsError::InvalidDigit { digit, radix });
    }

    Ok(())
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
        return Err(FromStrError::InvalidSymbol { char: ch, radix });
    }

    Ok(())
}

fn to_digits_validate<W: Word>(exp: W) -> Result<(), ToDigitsError> {
    let exp = exp.as_usize();

    if exp == 0 || exp >= W::BITS {
        return Err(ToDigitsError::InvalidExponent { exp });
    }

    Ok(())
}

fn into_digits_validate<W: Word>(radix: W) -> Result<(), IntoDigitsError> {
    let radix = radix.as_usize();

    if radix < 2 {
        return Err(IntoDigitsError::InvalidRadix { radix });
    }

    Ok(())
}

fn from_digits_impl<const L: usize, W: Word, Words>(iter: Words, exp: usize) -> [Single; L]
where
    Words: WordsIterator<Item = W>,
{
    let bits = exp;
    let mask = (1 << BITS) - 1;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = [0; L];

    for digit in iter {
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
}

fn from_digits_radix_impl<const L: usize, W: Word, Words>(iter: Words, radix: W) -> [Single; L]
where
    Words: WordsIterator<Item = W>,
{
    let mut idx = 0;
    let mut res = [0; L];

    for digit in iter {
        let mut acc = digit.as_double();

        for ptr in res.iter_mut().take(idx + 1) {
            acc += *ptr as Double * radix.as_double();

            *ptr = acc as Single;

            acc >>= BITS;
        }

        if idx < L && res[idx] > 0 {
            idx += 1;
        }
    }

    res
}

fn from_digits<const L: usize, W: Word>(digits: &[W], exp: W) -> Result<[Single; L], FromDigitsError> {
    let exp = exp.as_usize();

    if exp == 0 || exp >= W::BITS {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate(digits.iter().copied(), W::from_single(1 << exp))?;

    let res = from_digits_impl(digits.iter().copied(), exp);

    Ok(res)
}

fn from_digits_iter<const L: usize, W: Word, Words>(digits: Words, exp: W) -> Result<[Single; L], FromDigitsError>
where
    Words: WordsIterator<Item = W>,
{
    let exp = exp.as_usize();

    if exp == 0 || exp >= W::BITS {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate(digits.clone(), W::from_single(1 << exp))?;

    let res = from_digits_impl(digits, exp);

    Ok(res)
}

fn from_str<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    from_str_validate(s, 1 << exp)?;

    let mut res = from_digits_impl(s.bytes().rev().filter_map(get_digit_from_byte), exp as usize);

    if sign == Sign::NEG {
        uops::neg(&mut res).eval();
    }

    Ok(res)
}

fn from_digits_radix<const L: usize, W: Word>(digits: &[W], radix: W) -> Result<[Single; L], FromDigitsError> {
    if radix.is_pow2() {
        return from_digits(digits, W::from_single(radix.order() as Single));
    }

    from_digits_validate(digits.iter().copied(), radix)?;

    let res = from_digits_radix_impl(digits.iter().copied().rev(), radix);

    Ok(res)
}

fn from_digits_radix_iter<const L: usize, W: Word, Words>(
    digits: Words,
    radix: W,
) -> Result<[Single; L], FromDigitsError>
where
    Words: WordsIterator<Item = W> + DoubleEndedIterator,
{
    if radix.is_pow2() {
        return from_digits_iter(digits, W::from_single(radix.order() as Single));
    }

    from_digits_validate(digits.clone(), radix)?;

    let res = from_digits_radix_impl(digits.rev(), radix);

    Ok(res)
}

fn from_str_radix<const L: usize>(s: &str, radix: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    if radix.is_pow2() {
        return from_str(s, radix.order() as u8, sign);
    }

    from_str_validate(s, radix)?;

    let mut res = from_digits_radix_impl(s.bytes().filter_map(get_digit_from_byte), radix);

    if sign == Sign::NEG {
        uops::neg(&mut res).eval();
    }

    Ok(res)
}

fn to_digits<const L: usize, W: Word>(words: &[Single; L], exp: W) -> Result<Vec<W>, ToDigitsError> {
    to_digits_validate(exp)?;

    let bits = exp.as_usize();
    let mask = (1 << bits) - 1;
    let len = (words.len() * BITS + bits - 1) / bits;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![W::ZERO; len + 1];

    for &digit in words {
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

    res.truncate(length!(&res, &W::ZERO));

    Ok(res)
}

fn to_digits_iter<const L: usize, W: Word>(words: &[Single; L], exp: W) -> Result<DigitsIter<'_, L, W>, ToDigitsError> {
    to_digits_validate(exp)?;

    let bits = exp.as_usize();
    let mask = (1 << bits) - 1;
    let cnt = length!(words);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsIter {
        words,
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

fn into_digits<const L: usize, W: Word>(mut words: [Single; L], radix: W) -> Result<Vec<W>, IntoDigitsError> {
    if radix.is_pow2() {
        return Ok(to_digits(&words, W::from_single(radix.order() as Single))?);
    }

    into_digits_validate(radix)?;

    let bits = radix.order();
    let len = (words.len() * BITS + bits - 1) / bits;

    let mut idx = 0;
    let mut res = vec![W::ZERO; len + 1];

    loop {
        let mut any = 0;
        let mut acc = 0;

        for digit in words.iter_mut().rev() {
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

    res.truncate(length!(&res, &W::ZERO));

    Ok(res)
}

fn into_digits_iter<const L: usize, W: Word>(
    words: [Single; L],
    radix: W,
) -> Result<DigitsRadixIter<L, W>, IntoDigitsError> {
    into_digits_validate(radix)?;

    let bits = radix.order();
    let cnt = length!(&words);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsRadixIter { words, radix, len })
}

#[inline]
fn write_dec(mut cursor: Cursor<&mut [u8]>, word: usize, width: usize) -> std::fmt::Result {
    match cursor.write_fmt(format_args!("{word:0width$}")) {
        Ok(()) => (),
        Err(_) => return Err(std::fmt::Error),
    }

    Ok(())
}

#[inline]
fn write_bin(cursor: Cursor<&mut [u8]>, mut word: usize, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    #[allow(clippy::unnecessary_cast)]
    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (word % 2) as u8;
        word /= 2;
    }

    Ok(())
}

#[inline]
fn write_oct(cursor: Cursor<&mut [u8]>, mut word: usize, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    #[allow(clippy::unnecessary_cast)]
    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (word % 8) as u8;
        word /= 8;
    }

    Ok(())
}

#[inline]
fn write_lhex(cursor: Cursor<&mut [u8]>, mut word: usize, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[word % 16];
        word /= 16;
    }

    Ok(())
}

#[inline]
fn write_uhex(cursor: Cursor<&mut [u8]>, mut word: usize, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D', b'E', b'F',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[word % 16];
        word /= 16;
    }

    Ok(())
}

fn write<const L: usize, F: Fn(Cursor<&mut [u8]>, usize, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    words: &[Single; L],
    radix: Radix,
    sign: Sign,
    func: F,
) -> std::fmt::Result {
    let prefix = if fmt.alternate() { radix.prefix } else { "" };
    let width = radix.width as usize;

    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let len = length!(words);

    let mut buf = vec![b'0'; len * width];

    for (i, &word) in words[..len].iter().enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), word.as_usize(), width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, prefix, str)
}

fn write_iter<W: Word, Words, F: Fn(Cursor<&mut [u8]>, usize, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    words: Words,
    radix: Radix,
    sign: Sign,
    func: F,
) -> std::fmt::Result
where
    Words: WordsIterator<Item = W> + ExactSizeIterator,
{
    let prefix = if fmt.alternate() { radix.prefix } else { "" };
    let width = radix.width as usize;

    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let len = words.len();

    let mut buf = vec![b'0'; len * width];

    for (i, word) in words.enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), word.as_usize(), width)?;
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
        return Ok((s, default));
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

fn get_sign<const L: usize, W: Word>(words: &[W; L], sign: Sign) -> Sign {
    if words != &[W::ZERO; L] { sign } else { Sign::ZERO }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat_n;

    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use super::*;
    use crate::long::alias::{S32, S64, U32, U64};
    #[cfg(feature = "const-time")]
    use crate::{AutoCt, CmpCt, GeCt, LeCt, MaxCt, MinCt};

    #[test]
    fn from_primitive() {
        #![allow(clippy::unnecessary_cast)]

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
            (S64::from     (val as  i64), S64 { 0: (val as  i64 as i64).to_le_bytes() }),
            (S64::from_i8  (val as   i8), S64 { 0: (val as   i8 as i64).to_le_bytes() }),
            (S64::from_i16 (val as  i16), S64 { 0: (val as  i16 as i64).to_le_bytes() }),
            (S64::from_i32 (val as  i32), S64 { 0: (val as  i32 as i64).to_le_bytes() }),
            (S64::from_i64 (val as  i64), S64 { 0: (val as  i64 as i64).to_le_bytes() }),
            (S64::from_i128(val as i128), S64 { 0: (val as i128 as i64).to_le_bytes() }),

            (S32::from     (val as  i64), S32 { 0: (val as  i64 as i32).to_le_bytes() }),
            (S32::from_i8  (val as   i8), S32 { 0: (val as   i8 as i32).to_le_bytes() }),
            (S32::from_i16 (val as  i16), S32 { 0: (val as  i16 as i32).to_le_bytes() }),
            (S32::from_i32 (val as  i32), S32 { 0: (val as  i32 as i32).to_le_bytes() }),
            (S32::from_i64 (val as  i64), S32 { 0: (val as  i64 as i32).to_le_bytes() }),
            (S32::from_i128(val as i128), S32 { 0: (val as i128 as i32).to_le_bytes() }),

            (S64::from     ((val as  i64).wrapping_neg()), S64 { 0: ((val as  i64).wrapping_neg() as i64).to_le_bytes() }),
            (S64::from_i8  ((val as   i8).wrapping_neg()), S64 { 0: ((val as   i8).wrapping_neg() as i64).to_le_bytes() }),
            (S64::from_i16 ((val as  i16).wrapping_neg()), S64 { 0: ((val as  i16).wrapping_neg() as i64).to_le_bytes() }),
            (S64::from_i32 ((val as  i32).wrapping_neg()), S64 { 0: ((val as  i32).wrapping_neg() as i64).to_le_bytes() }),
            (S64::from_i64 ((val as  i64).wrapping_neg()), S64 { 0: ((val as  i64).wrapping_neg() as i64).to_le_bytes() }),
            (S64::from_i128((val as i128).wrapping_neg()), S64 { 0: ((val as i128).wrapping_neg() as i64).to_le_bytes() }),

            (S32::from     ((val as  i64).wrapping_neg()), S32 { 0: ((val as  i64).wrapping_neg() as i32).to_le_bytes() }),
            (S32::from_i8  ((val as   i8).wrapping_neg()), S32 { 0: ((val as   i8).wrapping_neg() as i32).to_le_bytes() }),
            (S32::from_i16 ((val as  i16).wrapping_neg()), S32 { 0: ((val as  i16).wrapping_neg() as i32).to_le_bytes() }),
            (S32::from_i32 ((val as  i32).wrapping_neg()), S32 { 0: ((val as  i32).wrapping_neg() as i32).to_le_bytes() }),
            (S32::from_i64 ((val as  i64).wrapping_neg()), S32 { 0: ((val as  i64).wrapping_neg() as i32).to_le_bytes() }),
            (S32::from_i128((val as i128).wrapping_neg()), S32 { 0: ((val as i128).wrapping_neg() as i32).to_le_bytes() }),

            (U64::from     (val as  u64), U64 { 0: (val as  u64 as u64).to_le_bytes() }),
            (U64::from_u8  (val as   u8), U64 { 0: (val as   u8 as u64).to_le_bytes() }),
            (U64::from_u16 (val as  u16), U64 { 0: (val as  u16 as u64).to_le_bytes() }),
            (U64::from_u32 (val as  u32), U64 { 0: (val as  u32 as u64).to_le_bytes() }),
            (U64::from_u64 (val as  u64), U64 { 0: (val as  u64 as u64).to_le_bytes() }),
            (U64::from_u128(val as u128), U64 { 0: (val as u128 as u64).to_le_bytes() }),

            (U32::from     (val as  u64), U32 { 0: (val as  u64 as u32).to_le_bytes() }),
            (U32::from_u8  (val as   u8), U32 { 0: (val as   u8 as u32).to_le_bytes() }),
            (U32::from_u16 (val as  u16), U32 { 0: (val as  u16 as u32).to_le_bytes() }),
            (U32::from_u32 (val as  u32), U32 { 0: (val as  u32 as u32).to_le_bytes() }),
            (U32::from_u64 (val as  u64), U32 { 0: (val as  u64 as u32).to_le_bytes() }),
            (U32::from_u128(val as u128), U32 { 0: (val as u128 as u32).to_le_bytes() }),
        ] }
    }

    #[test]
    fn from_bytes() {
        #![allow(clippy::unnecessary_cast)]

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
            (S64::from_bytes(&(val as u64).to_le_bytes()), S64 { 0: (val as u64 as u64).to_le_bytes() }),
            (U64::from_bytes(&(val as u64).to_le_bytes()), U64 { 0: (val as u64 as u64).to_le_bytes() }),
            (S64::from_bytes(&(val as u32).to_le_bytes()), S64 { 0: (val as u32 as u64).to_le_bytes() }),
            (U64::from_bytes(&(val as u32).to_le_bytes()), U64 { 0: (val as u32 as u64).to_le_bytes() }),
            (S64::from_bytes(&(val as u16).to_le_bytes()), S64 { 0: (val as u16 as u64).to_le_bytes() }),
            (U64::from_bytes(&(val as u16).to_le_bytes()), U64 { 0: (val as u16 as u64).to_le_bytes() }),
            (S64::from_bytes(&(val as  u8).to_le_bytes()), S64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (U64::from_bytes(&(val as  u8).to_le_bytes()), U64 { 0: (val as  u8 as u64).to_le_bytes() }),

            (S32::from_bytes(&(val as u64).to_le_bytes()), S32 { 0: (val as u64 as u32).to_le_bytes() }),
            (U32::from_bytes(&(val as u64).to_le_bytes()), U32 { 0: (val as u64 as u32).to_le_bytes() }),
            (S32::from_bytes(&(val as u32).to_le_bytes()), S32 { 0: (val as u32 as u32).to_le_bytes() }),
            (U32::from_bytes(&(val as u32).to_le_bytes()), U32 { 0: (val as u32 as u32).to_le_bytes() }),
            (S32::from_bytes(&(val as u16).to_le_bytes()), S32 { 0: (val as u16 as u32).to_le_bytes() }),
            (U32::from_bytes(&(val as u16).to_le_bytes()), U32 { 0: (val as u16 as u32).to_le_bytes() }),
            (S32::from_bytes(&(val as  u8).to_le_bytes()), S32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (U32::from_bytes(&(val as  u8).to_le_bytes()), U32 { 0: (val as  u8 as u32).to_le_bytes() }),
        ] }
    }

    #[test]
    fn from_arr() {
        #![allow(clippy::unnecessary_cast)]

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
            (S64::nd_from(&(val as u64).to_le_bytes()), S64 { 0: (val as u64 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as u64).to_le_bytes()), U64 { 0: (val as u64 as u64).to_le_bytes() }),
            (S64::nd_from(&(val as u32).to_le_bytes()), S64 { 0: (val as u32 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as u32).to_le_bytes()), U64 { 0: (val as u32 as u64).to_le_bytes() }),
            (S64::nd_from(&(val as u16).to_le_bytes()), S64 { 0: (val as u16 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as u16).to_le_bytes()), U64 { 0: (val as u16 as u64).to_le_bytes() }),
            (S64::nd_from(&(val as  u8).to_le_bytes()), S64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as  u8).to_le_bytes()), U64 { 0: (val as  u8 as u64).to_le_bytes() }),

            (S32::nd_from(&(val as u64).to_le_bytes()), S32 { 0: (val as u64 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as u64).to_le_bytes()), U32 { 0: (val as u64 as u32).to_le_bytes() }),
            (S32::nd_from(&(val as u32).to_le_bytes()), S32 { 0: (val as u32 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as u32).to_le_bytes()), U32 { 0: (val as u32 as u32).to_le_bytes() }),
            (S32::nd_from(&(val as u16).to_le_bytes()), S32 { 0: (val as u16 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as u16).to_le_bytes()), U32 { 0: (val as u16 as u32).to_le_bytes() }),
            (S32::nd_from(&(val as  u8).to_le_bytes()), S32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as  u8).to_le_bytes()), U32 { 0: (val as  u8 as u32).to_le_bytes() }),

            (S64::nd_try_from(&(val as u64).to_le_bytes()), Ok(S64 { 0: (val as u64 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as u64).to_le_bytes()), Ok(U64 { 0: (val as u64 as u64).to_le_bytes() })),
            (S64::nd_try_from(&(val as u32).to_le_bytes()), Ok(S64 { 0: (val as u32 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as u32).to_le_bytes()), Ok(U64 { 0: (val as u32 as u64).to_le_bytes() })),
            (S64::nd_try_from(&(val as u16).to_le_bytes()), Ok(S64 { 0: (val as u16 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as u16).to_le_bytes()), Ok(U64 { 0: (val as u16 as u64).to_le_bytes() })),
            (S64::nd_try_from(&(val as  u8).to_le_bytes()), Ok(S64 { 0: (val as  u8 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as  u8).to_le_bytes()), Ok(U64 { 0: (val as  u8 as u64).to_le_bytes() })),

            (S32::nd_try_from(&(val as u64).to_le_bytes()), Err(TryFromArrError::InvalidLength)),
            (U32::nd_try_from(&(val as u64).to_le_bytes()), Err(TryFromArrError::InvalidLength)),
            (S32::nd_try_from(&(val as u32).to_le_bytes()), Ok(S32 { 0: (val as u32 as u32).to_le_bytes() })),
            (U32::nd_try_from(&(val as u32).to_le_bytes()), Ok(U32 { 0: (val as u32 as u32).to_le_bytes() })),
            (S32::nd_try_from(&(val as u16).to_le_bytes()), Ok(S32 { 0: (val as u16 as u32).to_le_bytes() })),
            (U32::nd_try_from(&(val as u16).to_le_bytes()), Ok(U32 { 0: (val as u16 as u32).to_le_bytes() })),
            (S32::nd_try_from(&(val as  u8).to_le_bytes()), Ok(S32 { 0: (val as  u8 as u32).to_le_bytes() })),
            (U32::nd_try_from(&(val as  u8).to_le_bytes()), Ok(U32 { 0: (val as  u8 as u32).to_le_bytes() })),
        ] }
    }

    #[test]
    fn from_slice() {
        #![allow(clippy::unnecessary_cast)]

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
            (S64::nd_from(&val.to_le_bytes()[..8]), S64 { 0: (val as u64 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..8]), U64 { 0: (val as u64 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..4]), S64 { 0: (val as u32 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..4]), U64 { 0: (val as u32 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..2]), S64 { 0: (val as u16 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..2]), U64 { 0: (val as u16 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..1]), S64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..1]), U64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..0]), S64 { 0:   (0 as  u8 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..0]), U64 { 0:   (0 as  u8 as u64).to_le_bytes() }),

            (S32::nd_from(&val.to_le_bytes()[..8]), S32 { 0: (val as u64 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..8]), U32 { 0: (val as u64 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..4]), S32 { 0: (val as u32 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..4]), U32 { 0: (val as u32 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..2]), S32 { 0: (val as u16 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..2]), U32 { 0: (val as u16 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..1]), S32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..1]), U32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..0]), S32 { 0:   (0 as  u8 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..0]), U32 { 0:   (0 as  u8 as u32).to_le_bytes() }),

            (S64::nd_try_from(&val.to_le_bytes()[..8]), Ok(S64 { 0: (val as u64 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..8]), Ok(U64 { 0: (val as u64 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..4]), Ok(S64 { 0: (val as u32 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..4]), Ok(U64 { 0: (val as u32 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..2]), Ok(S64 { 0: (val as u16 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..2]), Ok(U64 { 0: (val as u16 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..1]), Ok(S64 { 0: (val as  u8 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..1]), Ok(U64 { 0: (val as  u8 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..0]), Ok(S64 { 0:   (0 as  u8 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..0]), Ok(U64 { 0:   (0 as  u8 as u64).to_le_bytes() })),

            (S32::nd_try_from(&val.to_le_bytes()[..8]), Err(TryFromSliceError::InvalidLength)),
            (U32::nd_try_from(&val.to_le_bytes()[..8]), Err(TryFromSliceError::InvalidLength)),
            (S32::nd_try_from(&val.to_le_bytes()[..4]), Ok(S32 { 0: (val as u32 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..4]), Ok(U32 { 0: (val as u32 as u32).to_le_bytes() })),
            (S32::nd_try_from(&val.to_le_bytes()[..2]), Ok(S32 { 0: (val as u16 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..2]), Ok(U32 { 0: (val as u16 as u32).to_le_bytes() })),
            (S32::nd_try_from(&val.to_le_bytes()[..1]), Ok(S32 { 0: (val as  u8 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..1]), Ok(U32 { 0: (val as  u8 as u32).to_le_bytes() })),
            (S32::nd_try_from(&val.to_le_bytes()[..0]), Ok(S32 { 0:   (0 as  u8 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..0]), Ok(U32 { 0:   (0 as  u8 as u32).to_le_bytes() })),
        ] }
    }

    #[test]
    fn from_iter() {
        #![allow(clippy::unnecessary_cast)]

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
            (val.to_le_bytes().iter().copied().take(8).collect::<S64>(), S64 { 0: (val as u64 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(8).collect::<U64>(), U64 { 0: (val as u64 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(4).collect::<S64>(), S64 { 0: (val as u32 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(4).collect::<U64>(), U64 { 0: (val as u32 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(2).collect::<S64>(), S64 { 0: (val as u16 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(2).collect::<U64>(), U64 { 0: (val as u16 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(1).collect::<S64>(), S64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(1).collect::<U64>(), U64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(0).collect::<S64>(), S64 { 0:   (0 as  u8 as u64).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(0).collect::<U64>(), U64 { 0:   (0 as  u8 as u64).to_le_bytes() }),

            (val.to_le_bytes().iter().copied().take(8).collect::<S32>(), S32 { 0: (val as u64 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(8).collect::<U32>(), U32 { 0: (val as u64 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(4).collect::<S32>(), S32 { 0: (val as u32 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(4).collect::<U32>(), U32 { 0: (val as u32 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(2).collect::<S32>(), S32 { 0: (val as u16 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(2).collect::<U32>(), U32 { 0: (val as u16 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(1).collect::<S32>(), S32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(1).collect::<U32>(), U32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(0).collect::<S32>(), S32 { 0:   (0 as  u8 as u32).to_le_bytes() }),
            (val.to_le_bytes().iter().copied().take(0).collect::<U32>(), U32 { 0:   (0 as  u8 as u32).to_le_bytes() }),
        ] }
    }

    #[test]
    fn from_digits() {
        macro_rules! generate {
            ($long:ty, $primitive:ty, $rng:expr, $radix:expr) => {{
                const BYTES: usize = <$primitive>::BITS as usize / 8;

                let rng = $rng;
                let radix = $radix;

                let digits = (0..BYTES).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                let lhs = <$long>::from_digits(digits, RadixImpl { radix });
                let rhs = <$long>::nd_from(&bytes);

                (lhs, Ok(rhs))
            }};
        }

        let mut rng = ndassert::rand!(StdRng, 60);

        ndassert::check! { @eq (radix in (2..=u8::MAX).flat_map(|radix| repeat_n(radix, 1 << 8))) [
            generate!(S64, i64, &mut rng, radix),
            generate!(U64, u64, &mut rng, radix),
        ] }
    }

    #[test]
    fn from_digits_iter() {
        macro_rules! generate {
            ($long:ty, $primitive:ty, $rng:expr, $radix:expr) => {{
                const BYTES: usize = <$primitive>::BITS as usize / 8;

                let rng = $rng;
                let radix = $radix;

                let digits = (0..BYTES).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);
                let iter = digits.iter().copied();

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                let lhs = <$long>::from_digits_iter(iter, RadixImpl { radix });
                let rhs = <$long>::nd_from(&bytes);

                (lhs, Ok(rhs))
            }};
        }

        let mut rng = ndassert::rand!(StdRng, 60);

        ndassert::check! { @eq (radix in (2..=u8::MAX).flat_map(|radix| repeat_n(radix, 1 << 8))) [
            generate!(S64, i64, &mut rng, radix),
            generate!(U64, u64, &mut rng, radix),
        ] }
    }

    #[test]
    fn to_digits() {
        macro_rules! generate {
            ($long:ty, $primitive:ty, $rng:expr, $exp:expr) => {{
                const BYTES: usize = <$primitive>::BITS as usize / 8;

                let rng = $rng;
                let exp = $exp;

                let radix = 1u8 << exp;
                let digits = (0..BYTES).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

                let res = <$long>::from_digits(digits, ExpImpl { exp }).map(|long| {
                    long.to_digits(ExpImpl { exp })
                        .map(|digits| digits.iter().copied().collect_with([0; BYTES]))
                });

                (res, Ok(Ok(digits)))
            }};
        }

        let mut rng = ndassert::rand!(StdRng, 60);

        ndassert::check! { @eq (exp in (1..u8::BITS as u8).flat_map(|radix| repeat_n(radix, 1 << 16))) [
            generate!(S64, i64, &mut rng, exp),
            generate!(U64, u64, &mut rng, exp),
        ] }
    }

    #[test]
    fn to_digits_iter() {
        macro_rules! generate {
            ($long:ty, $primitive:ty, $rng:expr, $exp:expr) => {{
                const BYTES: usize = <$primitive>::BITS as usize / 8;

                let rng = $rng;
                let exp = $exp;

                let radix = 1u8 << exp;
                let digits = (0..BYTES).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

                let res = <$long>::from_digits(digits, ExpImpl { exp }).map(|long| {
                    long.to_digits_iter(ExpImpl { exp })
                        .map(|mut digits| digits.collect_with([0; BYTES]))
                });

                (res, Ok(Ok(digits)))
            }};
        }

        let mut rng = ndassert::rand!(StdRng, 60);

        ndassert::check! { @eq (exp in (1..u8::BITS as u8).flat_map(|radix| repeat_n(radix, 1 << 16))) [
            generate!(S64, i64, &mut rng, exp),
            generate!(U64, u64, &mut rng, exp),
        ] }
    }

    #[test]
    fn into_digits() {
        macro_rules! generate {
            ($long:ty, $primitive:ty, $rng:expr, $radix:expr) => {{
                const BYTES: usize = <$primitive>::BITS as usize / 8;

                let rng = $rng;
                let radix = $radix;

                let digits = (0..BYTES).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

                let res = <$long>::from_digits(digits, RadixImpl { radix }).map(|long| {
                    long.into_digits(RadixImpl { radix })
                        .map(|digits| digits.iter().copied().collect_with([0; BYTES]))
                });

                (res, Ok(Ok(digits)))
            }};
        }

        let mut rng = ndassert::rand!(StdRng, 60);

        ndassert::check! { @eq (radix in (2..=u8::MAX).flat_map(|radix| repeat_n(radix, 1 << 8))) [
            generate!(S64, i64, &mut rng, radix),
            generate!(U64, u64, &mut rng, radix),
        ] }
    }

    #[test]
    fn into_digits_iter() {
        macro_rules! generate {
            ($long:ty, $primitive:ty, $rng:expr, $radix:expr) => {{
                const BYTES: usize = <$primitive>::BITS as usize / 8;

                let rng = $rng;
                let radix = $radix;

                let digits = (0..BYTES).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

                let res = <$long>::from_digits(digits, RadixImpl { radix }).map(|long| {
                    long.into_digits_iter(RadixImpl { radix })
                        .map(|mut digits| digits.collect_with([0; BYTES]))
                });

                (res, Ok(Ok(digits)))
            }};
        }

        let mut rng = ndassert::rand!(StdRng, 60);

        ndassert::check! { @eq (radix in (2..=u8::MAX).flat_map(|radix| repeat_n(radix, 1 << 8))) [
            generate!(S64, i64, &mut rng, radix),
            generate!(U64, u64, &mut rng, radix),
        ] }
    }

    #[test]
    fn from_str() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 52)) [
            (format!("{:#}",  val).parse::<S64>(), Ok(S64::from(val))),
            (format!("{:#b}", val).parse::<S64>(), Ok(S64::from(val))),
            (format!("{:#o}", val).parse::<S64>(), Ok(S64::from(val))),
            (format!("{:#x}", val).parse::<S64>(), Ok(S64::from(val))),
            (format!("{:#X}", val).parse::<S64>(), Ok(S64::from(val))),

            (S64::nd_from_str(&format!("{:}",  val), Dec), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:b}", val), Bin), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:o}", val), Oct), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:x}", val), Hex), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:X}", val), Hex), Ok(S64::from(val))),

            (S64::nd_from_str(&format!("{:#}",  val), Dec), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:#b}", val), Bin), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:#o}", val), Oct), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:#x}", val), Hex), Ok(S64::from(val))),
            (S64::nd_from_str(&format!("{:#X}", val), Hex), Ok(S64::from(val))),

            (format!("{:#}",  val.wrapping_neg()).parse::<S64>(), Ok(S64::from(val.wrapping_neg()))),
            (format!("{:#b}", val.wrapping_neg()).parse::<S64>(), Ok(S64::from(val.wrapping_neg()))),
            (format!("{:#o}", val.wrapping_neg()).parse::<S64>(), Ok(S64::from(val.wrapping_neg()))),
            (format!("{:#x}", val.wrapping_neg()).parse::<S64>(), Ok(S64::from(val.wrapping_neg()))),
            (format!("{:#X}", val.wrapping_neg()).parse::<S64>(), Ok(S64::from(val.wrapping_neg()))),

            (S64::nd_from_str(&format!("{:}",  val.wrapping_neg()), Dec), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:b}", val.wrapping_neg()), Bin), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:o}", val.wrapping_neg()), Oct), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:x}", val.wrapping_neg()), Hex), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:X}", val.wrapping_neg()), Hex), Ok(S64::from(val.wrapping_neg()))),

            (S64::nd_from_str(&format!("{:#}",  val.wrapping_neg()), Dec), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:#b}", val.wrapping_neg()), Bin), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:#o}", val.wrapping_neg()), Oct), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:#x}", val.wrapping_neg()), Hex), Ok(S64::from(val.wrapping_neg()))),
            (S64::nd_from_str(&format!("{:#X}", val.wrapping_neg()), Hex), Ok(S64::from(val.wrapping_neg()))),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(u64, 52)) [
            (format!("{:#}",  val).parse::<U64>(), Ok(U64::from(val))),
            (format!("{:#b}", val).parse::<U64>(), Ok(U64::from(val))),
            (format!("{:#o}", val).parse::<U64>(), Ok(U64::from(val))),
            (format!("{:#x}", val).parse::<U64>(), Ok(U64::from(val))),
            (format!("{:#X}", val).parse::<U64>(), Ok(U64::from(val))),

            (U64::nd_from_str(&format!("{:}",  val), Dec), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:b}", val), Bin), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:o}", val), Oct), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:x}", val), Hex), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:X}", val), Hex), Ok(U64::from(val))),

            (U64::nd_from_str(&format!("{:#}",  val), Dec), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:#b}", val), Bin), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:#o}", val), Oct), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:#x}", val), Hex), Ok(U64::from(val))),
            (U64::nd_from_str(&format!("{:#X}", val), Hex), Ok(U64::from(val))),
        ] }
    }

    #[test]
    fn to_str() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 52)) [
            (format!("{:}",   S64::from(val)), format!("{:}",   val)),
            (format!("{:b}",  S64::from(val)), format!("{:b}",  val)),
            (format!("{:o}",  S64::from(val)), format!("{:o}",  val)),
            (format!("{:x}",  S64::from(val)), format!("{:x}",  val)),
            (format!("{:X}",  S64::from(val)), format!("{:X}",  val)),
            (format!("{:#}",  S64::from(val)), format!("{:#}",  val)),
            (format!("{:#b}", S64::from(val)), format!("{:#b}", val)),
            (format!("{:#o}", S64::from(val)), format!("{:#o}", val)),
            (format!("{:#x}", S64::from(val)), format!("{:#x}", val)),
            (format!("{:#X}", S64::from(val)), format!("{:#X}", val)),

            (format!("{:}",   S64::from(val.wrapping_neg())), format!("{:}",   val.wrapping_neg())),
            (format!("{:b}",  S64::from(val.wrapping_neg())), format!("{:b}",  val.wrapping_neg())),
            (format!("{:o}",  S64::from(val.wrapping_neg())), format!("{:o}",  val.wrapping_neg())),
            (format!("{:x}",  S64::from(val.wrapping_neg())), format!("{:x}",  val.wrapping_neg())),
            (format!("{:X}",  S64::from(val.wrapping_neg())), format!("{:X}",  val.wrapping_neg())),
            (format!("{:#}",  S64::from(val.wrapping_neg())), format!("{:#}",  val.wrapping_neg())),
            (format!("{:#b}", S64::from(val.wrapping_neg())), format!("{:#b}", val.wrapping_neg())),
            (format!("{:#o}", S64::from(val.wrapping_neg())), format!("{:#o}", val.wrapping_neg())),
            (format!("{:#x}", S64::from(val.wrapping_neg())), format!("{:#x}", val.wrapping_neg())),
            (format!("{:#X}", S64::from(val.wrapping_neg())), format!("{:#X}", val.wrapping_neg())),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(u64, 52)) [
            (format!("{:}",   U64::from(val)), format!("{:}",   val)),
            (format!("{:b}",  U64::from(val)), format!("{:b}",  val)),
            (format!("{:o}",  U64::from(val)), format!("{:o}",  val)),
            (format!("{:x}",  U64::from(val)), format!("{:x}",  val)),
            (format!("{:X}",  U64::from(val)), format!("{:X}",  val)),
            (format!("{:#}",  U64::from(val)), format!("{:#}",  val)),
            (format!("{:#b}", U64::from(val)), format!("{:#b}", val)),
            (format!("{:#o}", U64::from(val)), format!("{:#o}", val)),
            (format!("{:#x}", U64::from(val)), format!("{:#x}", val)),
            (format!("{:#X}", U64::from(val)), format!("{:#X}", val)),
        ] }
    }

    #[test]
    fn cmp() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (S64::from(lhs).eq (&S64::from(rhs)), lhs.eq (&rhs)),
            (S64::from(lhs).cmp(&S64::from(rhs)), lhs.cmp(&rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            (U64::from(lhs).eq (&U64::from(rhs)), lhs.eq (&rhs)),
            (U64::from(lhs).cmp(&U64::from(rhs)), lhs.cmp(&rhs)),
        ] }
    }

    #[cfg(feature = "const-time")]
    #[test]
    fn cmp_ct() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (AutoCt(S64::from(lhs)).eq_ct(&AutoCt(S64::from(rhs))), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (AutoCt(S64::from(lhs)).lt_ct(&AutoCt(S64::from(rhs))), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (AutoCt(S64::from(lhs)).gt_ct(&AutoCt(S64::from(rhs))), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (AutoCt(S64::from(lhs)).le_ct(&AutoCt(S64::from(rhs))), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (AutoCt(S64::from(lhs)).ge_ct(&AutoCt(S64::from(rhs))), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (AutoCt(S64::from(lhs)).cmp_ct(&AutoCt(S64::from(rhs))), lhs.cmp(&rhs) as RelCt),
            (AutoCt(S64::from(lhs)).min_ct(&AutoCt(S64::from(rhs))), AutoCt(S64::from(lhs.min(rhs)))),
            (AutoCt(S64::from(lhs)).max_ct(&AutoCt(S64::from(rhs))), AutoCt(S64::from(lhs.max(rhs)))),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            (AutoCt(U64::from(lhs)).eq_ct(&AutoCt(U64::from(rhs))), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (AutoCt(U64::from(lhs)).lt_ct(&AutoCt(U64::from(rhs))), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (AutoCt(U64::from(lhs)).gt_ct(&AutoCt(U64::from(rhs))), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (AutoCt(U64::from(lhs)).le_ct(&AutoCt(U64::from(rhs))), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (AutoCt(U64::from(lhs)).ge_ct(&AutoCt(U64::from(rhs))), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (AutoCt(U64::from(lhs)).cmp_ct(&AutoCt(U64::from(rhs))), lhs.cmp(&rhs) as RelCt),
            (AutoCt(U64::from(lhs)).min_ct(&AutoCt(U64::from(rhs))), AutoCt(U64::from(lhs.min(rhs)))),
            (AutoCt(U64::from(lhs)).max_ct(&AutoCt(U64::from(rhs))), AutoCt(U64::from(lhs.max(rhs)))),
        ] }
    }

    #[test]
    fn ops() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            rhs in ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
        ) [
            (S64::from(lhs) + S64::from(rhs), S64::from(lhs.wrapping_add(rhs))),
            (S64::from(lhs) - S64::from(rhs), S64::from(lhs.wrapping_sub(rhs))),
            (S64::from(lhs) * S64::from(rhs), S64::from(lhs.wrapping_mul(rhs))),

            ((rhs != 0).then_some(S64::from(lhs) / S64::from(rhs)), (rhs != 0).then(|| S64::from(lhs.wrapping_div(rhs)))),
            ((rhs != 0).then_some(S64::from(lhs) % S64::from(rhs)), (rhs != 0).then(|| S64::from(lhs.wrapping_rem(rhs)))),

            (S64::from(lhs) | S64::from(rhs), S64::from(lhs | rhs)),
            (S64::from(lhs) & S64::from(rhs), S64::from(lhs & rhs)),
            (S64::from(lhs) ^ S64::from(rhs), S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(u64, 56, 1).chain([0, 1]),
        ) [
            (U64::from(lhs) + U64::from(rhs), U64::from(lhs.wrapping_add(rhs))),
            (U64::from(lhs) - U64::from(rhs), U64::from(lhs.wrapping_sub(rhs))),
            (U64::from(lhs) * U64::from(rhs), U64::from(lhs.wrapping_mul(rhs))),

            ((rhs != 0).then_some(U64::from(lhs) / U64::from(rhs)), (rhs != 0).then(|| U64::from(lhs.wrapping_div(rhs)))),
            ((rhs != 0).then_some(U64::from(lhs) % U64::from(rhs)), (rhs != 0).then(|| U64::from(lhs.wrapping_rem(rhs)))),

            (U64::from(lhs) | U64::from(rhs), U64::from(lhs | rhs)),
            (U64::from(lhs) & U64::from(rhs), U64::from(lhs & rhs)),
            (U64::from(lhs) ^ U64::from(rhs), U64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            (S64::from(lhs) << rhs, S64::from(lhs.unbounded_shl(rhs as u32))),
            (S64::from(lhs) >> rhs, S64::from(lhs.unbounded_shr(rhs as u32))),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 52),
            rhs in 0..96,
        ) [
            (U64::from(lhs) << rhs, U64::from(lhs.unbounded_shl(rhs as u32))),
            (U64::from(lhs) >> rhs, U64::from(lhs.unbounded_shr(rhs as u32))),
        ] }
    }

    #[test]
    fn ops_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            rhs in ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
        ) [
            ({ let mut val = S64::from(lhs); val += S64::from(rhs); val }, S64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = S64::from(lhs); val -= S64::from(rhs); val }, S64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = S64::from(lhs); val *= S64::from(rhs); val }, S64::from(lhs.wrapping_mul(rhs))),

            ({ let mut val = S64::from(lhs); val /= S64::from(rhs); (rhs != 0).then_some(val) }, (rhs != 0).then(|| S64::from(lhs.wrapping_div(rhs)))),
            ({ let mut val = S64::from(lhs); val %= S64::from(rhs); (rhs != 0).then_some(val) }, (rhs != 0).then(|| S64::from(lhs.wrapping_rem(rhs)))),

            ({ let mut val = S64::from(lhs); val |= S64::from(rhs); val }, S64::from(lhs | rhs)),
            ({ let mut val = S64::from(lhs); val &= S64::from(rhs); val }, S64::from(lhs & rhs)),
            ({ let mut val = S64::from(lhs); val ^= S64::from(rhs); val }, S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(u64, 56, 1).chain([0, 1]),
        ) [
            ({ let mut val = U64::from(lhs); val += U64::from(rhs); val }, U64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = U64::from(lhs); val -= U64::from(rhs); val }, U64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = U64::from(lhs); val *= U64::from(rhs); val }, U64::from(lhs.wrapping_mul(rhs))),

            ({ let mut val = U64::from(lhs); val /= U64::from(rhs); (rhs != 0).then_some(val) }, (rhs != 0).then(|| U64::from(lhs.wrapping_div(rhs)))),
            ({ let mut val = U64::from(lhs); val %= U64::from(rhs); (rhs != 0).then_some(val) }, (rhs != 0).then(|| U64::from(lhs.wrapping_rem(rhs)))),

            ({ let mut val = U64::from(lhs); val |= U64::from(rhs); val }, U64::from(lhs | rhs)),
            ({ let mut val = U64::from(lhs); val &= U64::from(rhs); val }, U64::from(lhs & rhs)),
            ({ let mut val = U64::from(lhs); val ^= U64::from(rhs); val }, U64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 52),
            rhs in 0..96,
        ) [
            ({ let mut val = S64::from(lhs); val <<= rhs; val }, S64::from(lhs.unbounded_shl(rhs as u32))),
            ({ let mut val = S64::from(lhs); val >>= rhs; val }, S64::from(lhs.unbounded_shr(rhs as u32))),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 52),
            rhs in 0..96,
        ) [
            ({ let mut val = U64::from(lhs); val <<= rhs; val }, U64::from(lhs.unbounded_shl(rhs as u32))),
            ({ let mut val = U64::from(lhs); val >>= rhs; val }, U64::from(lhs.unbounded_shr(rhs as u32))),
        ] }
    }

    #[test]
    fn ops_primitive() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            rhs in ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
        ) [
            (S64::from(lhs) + rhs, S64::from(lhs.wrapping_add(rhs))),
            (S64::from(lhs) - rhs, S64::from(lhs.wrapping_sub(rhs))),
            (S64::from(lhs) * rhs, S64::from(lhs.wrapping_mul(rhs))),

            ((rhs != 0).then_some(S64::from(lhs) / rhs), (rhs != 0).then(|| S64::from(lhs.wrapping_div(rhs)))),
            ((rhs != 0).then_some(S64::from(lhs) % rhs), (rhs != 0).then(|| S64::from(lhs.wrapping_rem(rhs)))),

            (S64::from(lhs) | rhs, S64::from(lhs | rhs)),
            (S64::from(lhs) & rhs, S64::from(lhs & rhs)),
            (S64::from(lhs) ^ rhs, S64::from(lhs ^ rhs)),

            (rhs + S64::from(lhs), S64::from(lhs.wrapping_add(rhs))),
            (rhs * S64::from(lhs), S64::from(lhs.wrapping_mul(rhs))),
            (rhs | S64::from(lhs), S64::from(lhs | rhs)),
            (rhs & S64::from(lhs), S64::from(lhs & rhs)),
            (rhs ^ S64::from(lhs), S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(u64, 56, 1).chain([0, 1]),
        ) [
            (U64::from(lhs) + rhs, U64::from(lhs.wrapping_add(rhs))),
            (U64::from(lhs) - rhs, U64::from(lhs.wrapping_sub(rhs))),
            (U64::from(lhs) * rhs, U64::from(lhs.wrapping_mul(rhs))),

            ((rhs != 0).then_some(U64::from(lhs) / rhs), (rhs != 0).then(|| U64::from(lhs.wrapping_div(rhs)))),
            ((rhs != 0).then_some(U64::from(lhs) % rhs), (rhs != 0).then(|| U64::from(lhs.wrapping_rem(rhs)))),

            (U64::from(lhs) | rhs, U64::from(lhs | rhs)),
            (U64::from(lhs) & rhs, U64::from(lhs & rhs)),
            (U64::from(lhs) ^ rhs, U64::from(lhs ^ rhs)),

            (rhs + U64::from(lhs), U64::from(lhs.wrapping_add(rhs))),
            (rhs * U64::from(lhs), U64::from(lhs.wrapping_mul(rhs))),
            (rhs | U64::from(lhs), U64::from(lhs | rhs)),
            (rhs & U64::from(lhs), U64::from(lhs & rhs)),
            (rhs ^ U64::from(lhs), U64::from(lhs ^ rhs)),
        ] }
    }

    #[test]
    fn ops_primitive_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            rhs in ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
        ) [
            ({ let mut val = S64::from(lhs); val += rhs; val }, S64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = S64::from(lhs); val -= rhs; val }, S64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = S64::from(lhs); val *= rhs; val }, S64::from(lhs.wrapping_mul(rhs))),

            ({ let mut val = S64::from(lhs); val /= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| S64::from(lhs.wrapping_div(rhs)))),
            ({ let mut val = S64::from(lhs); val %= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| S64::from(lhs.wrapping_rem(rhs)))),

            ({ let mut val = S64::from(lhs); val |= rhs; val }, S64::from(lhs | rhs)),
            ({ let mut val = S64::from(lhs); val &= rhs; val }, S64::from(lhs & rhs)),
            ({ let mut val = S64::from(lhs); val ^= rhs; val }, S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0, 1]),
            rhs in ndassert::range!(u64, 56, 1).chain([0, 1]),
        ) [
            ({ let mut val = U64::from(lhs); val += rhs; val }, U64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = U64::from(lhs); val -= rhs; val }, U64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = U64::from(lhs); val *= rhs; val }, U64::from(lhs.wrapping_mul(rhs))),

            ({ let mut val = U64::from(lhs); val /= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| U64::from(lhs.wrapping_div(rhs)))),
            ({ let mut val = U64::from(lhs); val %= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| U64::from(lhs.wrapping_rem(rhs)))),

            ({ let mut val = U64::from(lhs); val |= rhs; val }, U64::from(lhs | rhs)),
            ({ let mut val = U64::from(lhs); val &= rhs; val }, U64::from(lhs & rhs)),
            ({ let mut val = U64::from(lhs); val ^= rhs; val }, U64::from(lhs ^ rhs)),
        ] }
    }

    #[test]
    fn ops_primitive_native() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56).chain([-1, 0, 1]),
            rhs in i8::MIN..i8::MAX,
        ) [
            (S64::from(lhs) + rhs, S64::from(lhs.wrapping_add(rhs as i64))),
            (S64::from(lhs) - rhs, S64::from(lhs.wrapping_sub(rhs as i64))),
            (S64::from(lhs) * rhs, S64::from(lhs.wrapping_mul(rhs as i64))),

            ((rhs != 0).then_some(S64::from(lhs) / rhs), (rhs != 0).then(|| S64::from(lhs.wrapping_div(rhs as i64)))),
            ((rhs != 0).then_some(S64::from(lhs) % rhs), (rhs != 0).then(|| S64::from(lhs.wrapping_rem(rhs as i64)))),

            (S64::from(lhs) | rhs, S64::from(lhs | rhs as i64)),
            (S64::from(lhs) & rhs, S64::from(lhs & rhs as i64)),
            (S64::from(lhs) ^ rhs, S64::from(lhs ^ rhs as i64)),

            (rhs + S64::from(lhs), S64::from(lhs.wrapping_add(rhs as i64))),
            (rhs * S64::from(lhs), S64::from(lhs.wrapping_mul(rhs as i64))),
            (rhs | S64::from(lhs), S64::from(lhs | rhs as i64)),
            (rhs & S64::from(lhs), S64::from(lhs & rhs as i64)),
            (rhs ^ S64::from(lhs), S64::from(lhs ^ rhs as i64)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56).chain([0, 1]),
            rhs in u8::MIN..u8::MAX,
        ) [
            (U64::from(lhs) + rhs, U64::from(lhs.wrapping_add(rhs as u64))),
            (U64::from(lhs) - rhs, U64::from(lhs.wrapping_sub(rhs as u64))),
            (U64::from(lhs) * rhs, U64::from(lhs.wrapping_mul(rhs as u64))),

            ((rhs != 0).then_some(U64::from(lhs) / rhs), (rhs != 0).then(|| U64::from(lhs.wrapping_div(rhs as u64)))),
            ((rhs != 0).then_some(U64::from(lhs) % rhs), (rhs != 0).then(|| U64::from(lhs.wrapping_rem(rhs as u64)))),

            (U64::from(lhs) | rhs, U64::from(lhs | rhs as u64)),
            (U64::from(lhs) & rhs, U64::from(lhs & rhs as u64)),
            (U64::from(lhs) ^ rhs, U64::from(lhs ^ rhs as u64)),

            (rhs + U64::from(lhs), U64::from(lhs.wrapping_add(rhs as u64))),
            (rhs * U64::from(lhs), U64::from(lhs.wrapping_mul(rhs as u64))),
            (rhs | U64::from(lhs), U64::from(lhs | rhs as u64)),
            (rhs & U64::from(lhs), U64::from(lhs & rhs as u64)),
            (rhs ^ U64::from(lhs), U64::from(lhs ^ rhs as u64)),
        ] }
    }

    #[test]
    fn ops_primitive_native_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56).chain([-1, 0, 1]),
            rhs in i8::MIN..i8::MAX,
        ) [
            ({ let mut val = S64::from(lhs); val += rhs; val }, S64::from(lhs.wrapping_add(rhs as i64))),
            ({ let mut val = S64::from(lhs); val -= rhs; val }, S64::from(lhs.wrapping_sub(rhs as i64))),
            ({ let mut val = S64::from(lhs); val *= rhs; val }, S64::from(lhs.wrapping_mul(rhs as i64))),

            ({ let mut val = S64::from(lhs); val /= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| S64::from(lhs.wrapping_div(rhs as i64)))),
            ({ let mut val = S64::from(lhs); val %= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| S64::from(lhs.wrapping_rem(rhs as i64)))),

            ({ let mut val = S64::from(lhs); val |= rhs; val }, S64::from(lhs | rhs as i64)),
            ({ let mut val = S64::from(lhs); val &= rhs; val }, S64::from(lhs & rhs as i64)),
            ({ let mut val = S64::from(lhs); val ^= rhs; val }, S64::from(lhs ^ rhs as i64)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56).chain([0, 1]),
            rhs in u8::MIN..u8::MAX,
        ) [
            ({ let mut val = U64::from(lhs); val += rhs; val }, U64::from(lhs.wrapping_add(rhs as u64))),
            ({ let mut val = U64::from(lhs); val -= rhs; val }, U64::from(lhs.wrapping_sub(rhs as u64))),
            ({ let mut val = U64::from(lhs); val *= rhs; val }, U64::from(lhs.wrapping_mul(rhs as u64))),

            ({ let mut val = U64::from(lhs); val /= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| U64::from(lhs.wrapping_div(rhs as u64)))),
            ({ let mut val = U64::from(lhs); val %= rhs; (rhs != 0).then_some(val) }, (rhs != 0).then(|| U64::from(lhs.wrapping_rem(rhs as u64)))),

            ({ let mut val = U64::from(lhs); val |= rhs; val }, U64::from(lhs | rhs as u64)),
            ({ let mut val = U64::from(lhs); val &= rhs; val }, U64::from(lhs & rhs as u64)),
            ({ let mut val = U64::from(lhs); val ^= rhs; val }, U64::from(lhs ^ rhs as u64)),
        ] }
    }

    #[test]
    fn uops() {
        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48),
            bytes as val.to_le_bytes(),
        ) [
            (uops::not(&bytes).eval(), (!val).to_le_bytes()),
            (uops::pos(&bytes).eval(), val.to_le_bytes()),
            (uops::neg(&bytes).eval(), val.wrapping_neg().to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56),
            rhs in ndassert::range!(u64, 56),
            lhs_bytes as lhs.to_le_bytes(),
            rhs_bytes as rhs.to_le_bytes(),
        ) [
            (uops::add(&lhs_bytes, &rhs_bytes).eval(), lhs.wrapping_add(rhs).to_le_bytes()),
            (uops::sub(&lhs_bytes, &rhs_bytes).eval(), lhs.wrapping_sub(rhs).to_le_bytes()),
            (uops::bitor(&lhs_bytes, &rhs_bytes).eval(), (lhs | rhs).to_le_bytes()),
            (uops::bitand(&lhs_bytes, &rhs_bytes).eval(), (lhs & rhs).to_le_bytes()),
            (uops::bitxor(&lhs_bytes, &rhs_bytes).eval(), (lhs ^ rhs).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56),
            rhs in u8::MIN..u8::MAX,
            bytes as lhs.to_le_bytes(),
        ) [
            (uops::add(&bytes, rhs).eval(), lhs.wrapping_add(rhs as u64).to_le_bytes()),
            (uops::sub(&bytes, rhs).eval(), lhs.wrapping_sub(rhs as u64).to_le_bytes()),
            (uops::bitor(&bytes, rhs).eval(), (lhs | rhs as u64).to_le_bytes()),
            (uops::bitand(&bytes, rhs).eval(), (lhs & rhs as u64).to_le_bytes()),
            (uops::bitxor(&bytes, rhs).eval(), (lhs ^ rhs as u64).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56),
            rhs in i8::MIN..i8::MAX,
            bytes as lhs.to_le_bytes(),
        ) [
            (uops::add(&bytes, rhs as <Single as Num>::Signed).eval(), lhs.wrapping_add(rhs as i64).to_le_bytes()),
            (uops::sub(&bytes, rhs as <Single as Num>::Signed).eval(), lhs.wrapping_sub(rhs as i64).to_le_bytes()),
            (uops::bitor(&bytes, rhs as <Single as Num>::Signed).eval(), (lhs | rhs as i64).to_le_bytes()),
            (uops::bitand(&bytes, rhs as <Single as Num>::Signed).eval(), (lhs & rhs as i64).to_le_bytes()),
            (uops::bitxor(&bytes, rhs as <Single as Num>::Signed).eval(), (lhs ^ rhs as i64).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            val in ndassert::range!(u64, 52),
            shift in 0..96,
            bytes as val.to_le_bytes(),
            shl_ext as u64::MAX.unbounded_shr(u64::BITS.saturating_sub(shift as u32)),
            shr_ext as u64::MAX.unbounded_shl(u64::BITS.saturating_sub(shift as u32)),
        ) [
            (uops::shl(&bytes, shift).eval(), val.unbounded_shl(shift as u32).to_le_bytes()),
            (uops::shr(&bytes, shift).eval(), val.unbounded_shr(shift as u32).to_le_bytes()),
            (uops::shl(&bytes, shift).default(MAX).eval(), (val.unbounded_shl(shift as u32) | shl_ext).to_le_bytes()),
            (uops::shr(&bytes, shift).default(MAX).eval(), (val.unbounded_shr(shift as u32) | shr_ext).to_le_bytes()),
        ] }
    }

    #[test]
    fn uops_mut() {
        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48),
            bytes as val.to_le_bytes(),
        ) [
            ({ let mut bytes = bytes; uops::not(&mut bytes).eval(); bytes }, (!val).to_le_bytes()),
            ({ let mut bytes = bytes; uops::pos(&mut bytes).eval(); bytes }, val.to_le_bytes()),
            ({ let mut bytes = bytes; uops::neg(&mut bytes).eval(); bytes }, val.wrapping_neg().to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56),
            rhs in ndassert::range!(u64, 56),
            lhs_bytes as lhs.to_le_bytes(),
            rhs_bytes as rhs.to_le_bytes(),
        ) [
            ({ let mut bytes = lhs_bytes; uops::add(&mut bytes, &rhs_bytes).eval(); bytes }, lhs.wrapping_add(rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::sub(&mut bytes, &rhs_bytes).eval(); bytes }, lhs.wrapping_sub(rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::bitor(&mut bytes, &rhs_bytes).eval(); bytes }, (lhs | rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::bitand(&mut bytes, &rhs_bytes).eval(); bytes }, (lhs & rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::bitxor(&mut bytes, &rhs_bytes).eval(); bytes }, (lhs ^ rhs).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56),
            rhs in u8::MIN..u8::MAX,
            bytes as lhs.to_le_bytes(),
        ) [
            ({ let mut bytes = bytes; uops::add(&mut bytes, rhs).eval(); bytes }, lhs.wrapping_add(rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::sub(&mut bytes, rhs).eval(); bytes }, lhs.wrapping_sub(rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitor(&mut bytes, rhs).eval(); bytes }, (lhs | rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitand(&mut bytes, rhs).eval(); bytes }, (lhs & rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitxor(&mut bytes, rhs).eval(); bytes }, (lhs ^ rhs as u64).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56),
            rhs in i8::MIN..i8::MAX,
            bytes as lhs.to_le_bytes(),
        ) [
            ({ let mut bytes = bytes; uops::add(&mut bytes, rhs as <Single as Num>::Signed).eval(); bytes }, lhs.wrapping_add(rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::sub(&mut bytes, rhs as <Single as Num>::Signed).eval(); bytes }, lhs.wrapping_sub(rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitor(&mut bytes, rhs as <Single as Num>::Signed).eval(); bytes }, (lhs | rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitand(&mut bytes, rhs as <Single as Num>::Signed).eval(); bytes }, (lhs & rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitxor(&mut bytes, rhs as <Single as Num>::Signed).eval(); bytes }, (lhs ^ rhs as i64).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            val in ndassert::range!(u64, 52),
            shift in 0..96,
            bytes as val.to_le_bytes(),
            shl_ext as u64::MAX.unbounded_shr(u64::BITS.saturating_sub(shift as u32)),
            shr_ext as u64::MAX.unbounded_shl(u64::BITS.saturating_sub(shift as u32)),
        ) [
            ({ let mut bytes = bytes; uops::shl(&mut bytes, shift).eval(); bytes }, val.unbounded_shl(shift as u32).to_le_bytes()),
            ({ let mut bytes = bytes; uops::shr(&mut bytes, shift).eval(); bytes }, val.unbounded_shr(shift as u32).to_le_bytes()),
            ({ let mut bytes = bytes; uops::shl(&mut bytes, shift).default(MAX).eval(); bytes }, (val.unbounded_shl(shift as u32) | shl_ext).to_le_bytes()),
            ({ let mut bytes = bytes; uops::shr(&mut bytes, shift).default(MAX).eval(); bytes }, (val.unbounded_shr(shift as u32) | shr_ext).to_le_bytes()),
        ] }
    }
}

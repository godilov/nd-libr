#![doc = include_str!("../docs/long.md")]
#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    io::{Cursor, Write},
    str::FromStr,
};

use ndext::{
    convert::{NdFrom, NdFromStr, NdTryFrom, NdxFrom},
    iter::IteratorExt,
    ops::*,
};
use thiserror::Error;
use zerocopy::{IntoBytes, transmute_mut, transmute_ref};

use crate::{
    CmpCt, Dir, EqCt, GeCt, GtCt, IsNegCt, IsOneCt, IsPosCt, IsZeroCt, LeCt, LtCt, MaskCt, Max, MaxCt, Min, MinCt,
    NdGcd, NdPow, NegxCt, Num, NumBinary, NumCt, NumExt, NumExtCt, NumFn, NumSigned, NumSignedCt, NumUnsigned,
    NumUnsignedCt, One, PosxCt, PowCt, RelCt, SelectCt, Sign, SignCt, Zero,
    arch::{
        AsWordsMut, AsWordsRef, Rand, codec,
        codec::{Codec, Decode, Decoded, Encode, Encoded},
        word::*,
    },
    long::{
        digits::*,
        radix::*,
        uops::{Expr, ExprMut},
    },
};

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
                let res = from_array(&bytes, [0, MAX][(value < 0) as usize]);

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
            + uops::add(&lhs.0, &Signed::from(rhs).0).signed().default(Signed),
            - uops::sub(&lhs.0, &Signed::from(rhs).0).signed().default(Signed),
            * algo::mul(&lhs.0, &Signed::from(rhs).0).signed().default(Signed),
            / algo::div(&lhs.0, &Signed::from(rhs).0).signed().default(Signed),
            % algo::rem(&lhs.0, &Signed::from(rhs).0).signed().default(Signed),

            | uops::bitor(&lhs.0, &Signed::from(rhs).0).eval(),
            & uops::bitand(&lhs.0, &Signed::from(rhs).0).eval(),
            ^ uops::bitxor(&lhs.0, &Signed::from(rhs).0).eval(),

            + @checked uops::add(&lhs.0, &Signed::from(rhs).0).signed().checked(Signed),
            - @checked uops::sub(&lhs.0, &Signed::from(rhs).0).signed().checked(Signed),
            * @checked algo::mul(&lhs.0, &Signed::from(rhs).0).signed().checked(Signed),
            / @checked algo::div(&lhs.0, &Signed::from(rhs).0).signed().checked(Signed),
            % @checked algo::rem(&lhs.0, &Signed::from(rhs).0).signed().checked(Signed),

            + @strict uops::add(&lhs.0, &Signed::from(rhs).0).signed().strict(Signed),
            - @strict uops::sub(&lhs.0, &Signed::from(rhs).0).signed().strict(Signed),
            * @strict algo::mul(&lhs.0, &Signed::from(rhs).0).signed().strict(Signed),
            / @strict algo::div(&lhs.0, &Signed::from(rhs).0).signed().strict(Signed),
            % @strict algo::rem(&lhs.0, &Signed::from(rhs).0).signed().strict(Signed),

            + @wrapping uops::add_iter(lhs.0.iter().copied(), uops::iter(rhs.as_unsigned().as_words(), [0, MAX][(rhs < 0) as usize], L)).with(Signed),
            - @wrapping uops::sub_iter(lhs.0.iter().copied(), uops::iter(rhs.as_unsigned().as_words(), [0, MAX][(rhs < 0) as usize], L)).with(Signed),

            * @wrapping algo::mul(&lhs.0, &Signed::from(rhs).0).signed().with(Signed),
            / @wrapping algo::div(&lhs.0, &Signed::from(rhs).0).signed().with(Signed),
            % @wrapping algo::rem(&lhs.0, &Signed::from(rhs).0).signed().with(Signed),

            + @saturating uops::add(&lhs.0, &Signed::from(rhs).0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() == Dir::POS) as usize]),
            - @saturating uops::sub(&lhs.0, &Signed::from(rhs).0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() == Dir::POS) as usize]),
            * @saturating algo::mul(&lhs.0, &Signed::from(rhs).0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() * Dir::from(rhs) == Dir::POS) as usize]),
            / @saturating algo::div(&lhs.0, &Signed::from(rhs).0).signed().saturating(Signed, &Signed::MAX),
            % @saturating algo::rem(&lhs.0, &Signed::from(rhs).0).signed().saturating(Signed, &Signed::ZERO),

            + @overflowing uops::add(&lhs.0, &Signed::from(rhs).0).signed().overflowing(Signed),
            - @overflowing uops::sub(&lhs.0, &Signed::from(rhs).0).signed().overflowing(Signed),
            * @overflowing algo::mul(&lhs.0, &Signed::from(rhs).0).signed().overflowing(Signed),
            / @overflowing algo::div(&lhs.0, &Signed::from(rhs).0).signed().overflowing(Signed),
            % @overflowing algo::rem(&lhs.0, &Signed::from(rhs).0).signed().overflowing(Signed),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Signed<L>) -> Signed<L> for [Signed<L>, $primitive], [
            + uops::add(&Signed::from(lhs).0, &rhs.0).signed().default(Signed),
            - uops::sub(&Signed::from(lhs).0, &rhs.0).signed().default(Signed),
            * algo::mul(&Signed::from(lhs).0, &rhs.0).signed().default(Signed),

            | uops::bitor(&Signed::from(lhs).0, &rhs.0).eval(),
            & uops::bitand(&Signed::from(lhs).0, &rhs.0).eval(),
            ^ uops::bitxor(&Signed::from(lhs).0, &rhs.0).eval(),

            + @checked uops::add(&Signed::from(lhs).0, &rhs.0).signed().checked(Signed),
            - @checked uops::sub(&Signed::from(lhs).0, &rhs.0).signed().checked(Signed),
            * @checked algo::mul(&Signed::from(lhs).0, &rhs.0).signed().checked(Signed),

            + @strict uops::add(&Signed::from(lhs).0, &rhs.0).signed().strict(Signed),
            - @strict uops::sub(&Signed::from(lhs).0, &rhs.0).signed().strict(Signed),
            * @strict algo::mul(&Signed::from(lhs).0, &rhs.0).signed().strict(Signed),

            + @wrapping uops::add_iter(uops::iter(lhs.as_unsigned().as_words(), [0, MAX][(lhs < 0) as usize], L), rhs.0.iter().copied()).with(Signed),
            - @wrapping uops::sub_iter(uops::iter(lhs.as_unsigned().as_words(), [0, MAX][(lhs < 0) as usize], L), rhs.0.iter().copied()).with(Signed),

            * @wrapping algo::mul(&Signed::from(lhs).0, &rhs.0).signed().with(Signed),

            + @saturating uops::add(&Signed::from(lhs).0, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(Dir::from(lhs) == Dir::POS) as usize]),
            - @saturating uops::sub(&Signed::from(lhs).0, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(Dir::from(lhs) == Dir::POS) as usize]),
            * @saturating algo::mul(&Signed::from(lhs).0, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(Dir::from(lhs) * rhs.dir() == Dir::POS) as usize]),

            + @overflowing uops::add(&Signed::from(lhs).0, &rhs.0).signed().overflowing(Signed),
            - @overflowing uops::sub(&Signed::from(lhs).0, &rhs.0).signed().overflowing(Signed),
            * @overflowing algo::mul(&Signed::from(lhs).0, &rhs.0).signed().overflowing(Signed),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, &rhs: &$primitive), [
            += uops::add(&mut lhs.0, &Signed::from(rhs).0).signed().default_mut(),
            -= uops::sub(&mut lhs.0, &Signed::from(rhs).0).signed().default_mut(),
            *= algo::mul(&mut lhs.0, &Signed::from(rhs).0).signed().default_mut(),
            /= algo::div(&mut lhs.0, &Signed::from(rhs).0).signed().default_mut(),
            %= algo::rem(&mut lhs.0, &Signed::from(rhs).0).signed().default_mut(),

            |= uops::bitor(&mut lhs.0, &Signed::from(rhs).0).eval_mut(),
            &= uops::bitand(&mut lhs.0, &Signed::from(rhs).0).eval_mut(),
            ^= uops::bitxor(&mut lhs.0, &Signed::from(rhs).0).eval_mut(),

            += @strict uops::add(&mut lhs.0, &Signed::from(rhs).0).signed().strict_mut(),
            -= @strict uops::sub(&mut lhs.0, &Signed::from(rhs).0).signed().strict_mut(),
            *= @strict algo::mul(&mut lhs.0, &Signed::from(rhs).0).signed().strict_mut(),
            /= @strict algo::div(&mut lhs.0, &Signed::from(rhs).0).signed().strict_mut(),
            %= @strict algo::rem(&mut lhs.0, &Signed::from(rhs).0).signed().strict_mut(),

            += @wrapping uops::add_iter(lhs.0.iter_mut(), uops::iter(rhs.as_unsigned().as_words(), [0, MAX][(rhs < 0) as usize], L)).with(|_| ()),
            -= @wrapping uops::sub_iter(lhs.0.iter_mut(), uops::iter(rhs.as_unsigned().as_words(), [0, MAX][(rhs < 0) as usize], L)).with(|_| ()),

            *= @wrapping algo::mul(&mut lhs.0, &Signed::from(rhs).0).signed().eval_mut(),
            /= @wrapping algo::div(&mut lhs.0, &Signed::from(rhs).0).signed().eval_mut(),
            %= @wrapping algo::rem(&mut lhs.0, &Signed::from(rhs).0).signed().eval_mut(),

            += @saturating {
                let dir = lhs.dir();

                uops::add(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
            },
            -= @saturating {
                let dir = lhs.dir();

                uops::sub(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
            },
            *= @saturating {
                let dir = lhs.dir() * Dir::from(rhs);

                algo::mul(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
            },

            /= @saturating algo::div(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut(&Signed::MAX.0),
            %= @saturating algo::rem(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut(&Signed::ZERO.0),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, &rhs: &$primitive) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add(&lhs.0, &Unsigned::from(rhs).0).default(Unsigned),
            - uops::sub(&lhs.0, &Unsigned::from(rhs).0).default(Unsigned),
            * algo::mul(&lhs.0, &Unsigned::from(rhs).0).default(Unsigned),
            / algo::div(&lhs.0, &Unsigned::from(rhs).0).default(Unsigned),
            % algo::rem(&lhs.0, &Unsigned::from(rhs).0).default(Unsigned),

            | uops::bitor(&lhs.0, &Unsigned::from(rhs).0).eval(),
            & uops::bitand(&lhs.0, &Unsigned::from(rhs).0).eval(),
            ^ uops::bitxor(&lhs.0, &Unsigned::from(rhs).0).eval(),

            + @checked uops::add(&lhs.0, &Unsigned::from(rhs).0).checked(Unsigned),
            - @checked uops::sub(&lhs.0, &Unsigned::from(rhs).0).checked(Unsigned),
            * @checked algo::mul(&lhs.0, &Unsigned::from(rhs).0).checked(Unsigned),
            / @checked algo::div(&lhs.0, &Unsigned::from(rhs).0).checked(Unsigned),
            % @checked algo::rem(&lhs.0, &Unsigned::from(rhs).0).checked(Unsigned),

            + @strict uops::add(&lhs.0, &Unsigned::from(rhs).0).strict(Unsigned),
            - @strict uops::sub(&lhs.0, &Unsigned::from(rhs).0).strict(Unsigned),
            * @strict algo::mul(&lhs.0, &Unsigned::from(rhs).0).strict(Unsigned),
            / @strict algo::div(&lhs.0, &Unsigned::from(rhs).0).strict(Unsigned),
            % @strict algo::rem(&lhs.0, &Unsigned::from(rhs).0).strict(Unsigned),

            + @wrapping uops::add_iter(lhs.0.iter().copied(), uops::iter(rhs.as_unsigned().as_words(), 0, L)).with(Unsigned),
            - @wrapping uops::sub_iter(lhs.0.iter().copied(), uops::iter(rhs.as_unsigned().as_words(), 0, L)).with(Unsigned),

            * @wrapping algo::mul(&lhs.0, &Unsigned::from(rhs).0).with(Unsigned),
            / @wrapping algo::div(&lhs.0, &Unsigned::from(rhs).0).with(Unsigned),
            % @wrapping algo::rem(&lhs.0, &Unsigned::from(rhs).0).with(Unsigned),

            + @saturating uops::add(&lhs.0, &Unsigned::from(rhs).0).saturating(Unsigned, &Unsigned::MAX),
            - @saturating uops::sub(&lhs.0, &Unsigned::from(rhs).0).saturating(Unsigned, &Unsigned::MIN),
            * @saturating algo::mul(&lhs.0, &Unsigned::from(rhs).0).saturating(Unsigned, &Unsigned::MAX),
            / @saturating algo::div(&lhs.0, &Unsigned::from(rhs).0).saturating(Unsigned, &Unsigned::MAX),
            % @saturating algo::rem(&lhs.0, &Unsigned::from(rhs).0).saturating(Unsigned, &Unsigned::MIN),

            + @overflowing uops::add(&lhs.0, &Unsigned::from(rhs).0).overflowing(Unsigned),
            - @overflowing uops::sub(&lhs.0, &Unsigned::from(rhs).0).overflowing(Unsigned),
            * @overflowing algo::mul(&lhs.0, &Unsigned::from(rhs).0).overflowing(Unsigned),
            / @overflowing algo::div(&lhs.0, &Unsigned::from(rhs).0).overflowing(Unsigned),
            % @overflowing algo::rem(&lhs.0, &Unsigned::from(rhs).0).overflowing(Unsigned),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Unsigned<L>) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add(&Unsigned::from(lhs).0, &rhs.0).default(Unsigned),
            - uops::sub(&Unsigned::from(lhs).0, &rhs.0).default(Unsigned),
            * algo::mul(&Unsigned::from(lhs).0, &rhs.0).default(Unsigned),

            | uops::bitor(&Unsigned::from(lhs).0, &rhs.0).eval(),
            & uops::bitand(&Unsigned::from(lhs).0, &rhs.0).eval(),
            ^ uops::bitxor(&Unsigned::from(lhs).0, &rhs.0).eval(),

            + @checked uops::add(&Unsigned::from(lhs).0, &rhs.0).checked(Unsigned),
            - @checked uops::sub(&Unsigned::from(lhs).0, &rhs.0).checked(Unsigned),
            * @checked algo::mul(&Unsigned::from(lhs).0, &rhs.0).checked(Unsigned),

            + @strict uops::add(&Unsigned::from(lhs).0, &rhs.0).strict(Unsigned),
            - @strict uops::sub(&Unsigned::from(lhs).0, &rhs.0).strict(Unsigned),
            * @strict algo::mul(&Unsigned::from(lhs).0, &rhs.0).strict(Unsigned),

            + @wrapping uops::add_iter(uops::iter(lhs.as_unsigned().as_words(), 0, L), rhs.0.iter().copied()).with(Unsigned),
            - @wrapping uops::sub_iter(uops::iter(lhs.as_unsigned().as_words(), 0, L), rhs.0.iter().copied()).with(Unsigned),

            * @wrapping algo::mul(&Unsigned::from(lhs).0, &rhs.0).with(Unsigned),

            + @saturating uops::add(&Unsigned::from(lhs).0, &rhs.0).saturating(Unsigned, &Unsigned::MAX),
            - @saturating uops::sub(&Unsigned::from(lhs).0, &rhs.0).saturating(Unsigned, &Unsigned::MIN),
            * @saturating algo::mul(&Unsigned::from(lhs).0, &rhs.0).saturating(Unsigned, &Unsigned::MAX),

            + @overflowing uops::add(&Unsigned::from(lhs).0, &rhs.0).overflowing(Unsigned),
            - @overflowing uops::sub(&Unsigned::from(lhs).0, &rhs.0).overflowing(Unsigned),
            * @overflowing algo::mul(&Unsigned::from(lhs).0, &rhs.0).overflowing(Unsigned),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, &rhs: &$primitive), [
            += uops::add(&mut lhs.0, &Unsigned::from(rhs).0).default_mut(),
            -= uops::sub(&mut lhs.0, &Unsigned::from(rhs).0).default_mut(),
            *= algo::mul(&mut lhs.0, &Unsigned::from(rhs).0).default_mut(),
            /= algo::div(&mut lhs.0, &Unsigned::from(rhs).0).default_mut(),
            %= algo::rem(&mut lhs.0, &Unsigned::from(rhs).0).default_mut(),

            |= uops::bitor(&mut lhs.0, &Unsigned::from(rhs).0).eval_mut(),
            &= uops::bitand(&mut lhs.0, &Unsigned::from(rhs).0).eval_mut(),
            ^= uops::bitxor(&mut lhs.0, &Unsigned::from(rhs).0).eval_mut(),

            += @strict uops::add(&mut lhs.0, &Unsigned::from(rhs).0).strict_mut(),
            -= @strict uops::sub(&mut lhs.0, &Unsigned::from(rhs).0).strict_mut(),
            *= @strict algo::mul(&mut lhs.0, &Unsigned::from(rhs).0).strict_mut(),
            /= @strict algo::div(&mut lhs.0, &Unsigned::from(rhs).0).strict_mut(),
            %= @strict algo::rem(&mut lhs.0, &Unsigned::from(rhs).0).strict_mut(),

            += @wrapping uops::add_iter(lhs.0.iter_mut(), uops::iter(rhs.as_unsigned().as_words(), 0, L)).eval(),
            -= @wrapping uops::sub_iter(lhs.0.iter_mut(), uops::iter(rhs.as_unsigned().as_words(), 0, L)).eval(),

            *= @wrapping algo::mul(&mut lhs.0, &Unsigned::from(rhs).0).eval_mut(),
            /= @wrapping algo::div(&mut lhs.0, &Unsigned::from(rhs).0).eval_mut(),
            %= @wrapping algo::rem(&mut lhs.0, &Unsigned::from(rhs).0).eval_mut(),

            += @saturating uops::add(&mut lhs.0, &Unsigned::from(rhs).0).saturating_mut(&Unsigned::MAX.0),
            -= @saturating uops::sub(&mut lhs.0, &Unsigned::from(rhs).0).saturating_mut(&Unsigned::MIN.0),
            *= @saturating algo::mul(&mut lhs.0, &Unsigned::from(rhs).0).saturating_mut(&Unsigned::MAX.0),
            /= @saturating algo::div(&mut lhs.0, &Unsigned::from(rhs).0).saturating_mut(&Unsigned::MAX.0),
            %= @saturating algo::rem(&mut lhs.0, &Unsigned::from(rhs).0).saturating_mut(&Unsigned::MIN.0),
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
            |= uops::bitor(&mut lhs.0, &Bytes::from(rhs).0).eval_mut(),
            &= uops::bitand(&mut lhs.0, &Bytes::from(rhs).0).eval_mut(),
            ^= uops::bitxor(&mut lhs.0, &Bytes::from(rhs).0).eval_mut(),
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
            + uops::add(&lhs.0, rhs as <Single as NumExt>::Signed).signed().default(Signed),
            - uops::sub(&lhs.0, rhs as <Single as NumExt>::Signed).signed().default(Signed),
            * algo::mul(&lhs.0, rhs as <Single as NumExt>::Signed).signed().default(Signed),
            / algo::div(&lhs.0, rhs as <Single as NumExt>::Signed).signed().default(Signed::from),
            % algo::rem(&lhs.0, rhs as <Single as NumExt>::Signed).signed().default(Signed::from),

            | uops::bitor(&lhs.0, rhs as <Single as NumExt>::Signed).eval(),
            & uops::bitand(&lhs.0, rhs as <Single as NumExt>::Signed).eval(),
            ^ uops::bitxor(&lhs.0, rhs as <Single as NumExt>::Signed).eval(),

            + @checked uops::add(&lhs.0, rhs as <Single as NumExt>::Signed).signed().checked(Signed),
            - @checked uops::sub(&lhs.0, rhs as <Single as NumExt>::Signed).signed().checked(Signed),
            * @checked algo::mul(&lhs.0, rhs as <Single as NumExt>::Signed).signed().checked(Signed),
            / @checked algo::div(&lhs.0, rhs as <Single as NumExt>::Signed).signed().checked(Signed::from),
            % @checked algo::rem(&lhs.0, rhs as <Single as NumExt>::Signed).signed().checked(Signed::from),

            + @strict uops::add(&lhs.0, rhs as <Single as NumExt>::Signed).signed().strict(Signed),
            - @strict uops::sub(&lhs.0, rhs as <Single as NumExt>::Signed).signed().strict(Signed),
            * @strict algo::mul(&lhs.0, rhs as <Single as NumExt>::Signed).signed().strict(Signed),
            / @strict algo::div(&lhs.0, rhs as <Single as NumExt>::Signed).signed().strict(Signed::from),
            % @strict algo::rem(&lhs.0, rhs as <Single as NumExt>::Signed).signed().strict(Signed::from),

            + @wrapping uops::add(&lhs.0, rhs as <Single as NumExt>::Signed).signed().with(Signed),
            - @wrapping uops::sub(&lhs.0, rhs as <Single as NumExt>::Signed).signed().with(Signed),
            * @wrapping algo::mul(&lhs.0, rhs as <Single as NumExt>::Signed).signed().with(Signed),
            / @wrapping algo::div(&lhs.0, rhs as <Single as NumExt>::Signed).signed().with(Signed::from),
            % @wrapping algo::rem(&lhs.0, rhs as <Single as NumExt>::Signed).signed().with(Signed::from),

            + @saturating uops::add(&lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() == Dir::POS) as usize]),
            - @saturating uops::sub(&lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() == Dir::POS) as usize]),
            * @saturating algo::mul(&lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() * Dir::from(rhs) == Dir::POS) as usize]),
            / @saturating algo::div(&lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating(Signed::from, &Signed::MAX),
            % @saturating algo::rem(&lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating(Signed::from, &Signed::ZERO),

            + @overflowing uops::add(&lhs.0, rhs as <Single as NumExt>::Signed).signed().overflowing(Signed),
            - @overflowing uops::sub(&lhs.0, rhs as <Single as NumExt>::Signed).signed().overflowing(Signed),
            * @overflowing algo::mul(&lhs.0, rhs as <Single as NumExt>::Signed).signed().overflowing(Signed),
            / @overflowing algo::div(&lhs.0, rhs as <Single as NumExt>::Signed).signed().overflowing(Signed::from),
            % @overflowing algo::rem(&lhs.0, rhs as <Single as NumExt>::Signed).signed().overflowing(Signed::from),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Signed<L>) -> Signed<L> for [Signed<L>, $primitive], [
            + uops::add(lhs as <Single as NumExt>::Signed, &rhs.0).signed().default(Signed),
            - uops::sub(lhs as <Single as NumExt>::Signed, &rhs.0).signed().default(Signed),
            * algo::mul(lhs as <Single as NumExt>::Signed, &rhs.0).signed().default(Signed),

            | uops::bitor(&rhs.0, lhs as <Single as NumExt>::Signed).eval(),
            & uops::bitand(&rhs.0, lhs as <Single as NumExt>::Signed).eval(),
            ^ uops::bitxor(&rhs.0, lhs as <Single as NumExt>::Signed).eval(),

            + @checked uops::add(lhs as <Single as NumExt>::Signed, &rhs.0).signed().checked(Signed),
            - @checked uops::sub(lhs as <Single as NumExt>::Signed, &rhs.0).signed().checked(Signed),
            * @checked algo::mul(lhs as <Single as NumExt>::Signed, &rhs.0).signed().checked(Signed),

            + @strict uops::add(lhs as <Single as NumExt>::Signed, &rhs.0).signed().strict(Signed),
            - @strict uops::sub(lhs as <Single as NumExt>::Signed, &rhs.0).signed().strict(Signed),
            * @strict algo::mul(lhs as <Single as NumExt>::Signed, &rhs.0).signed().strict(Signed),

            + @wrapping uops::add(lhs as <Single as NumExt>::Signed, &rhs.0).signed().with(Signed),
            - @wrapping uops::sub(lhs as <Single as NumExt>::Signed, &rhs.0).signed().with(Signed),
            * @wrapping algo::mul(lhs as <Single as NumExt>::Signed, &rhs.0).signed().with(Signed),

            + @saturating uops::add(lhs as <Single as NumExt>::Signed, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(Dir::from(lhs) == Dir::POS) as usize]),
            - @saturating uops::sub(lhs as <Single as NumExt>::Signed, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(Dir::from(lhs) == Dir::POS) as usize]),
            * @saturating algo::mul(lhs as <Single as NumExt>::Signed, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(Dir::from(lhs) * rhs.dir() == Dir::POS) as usize]),

            + @overflowing uops::add(lhs as <Single as NumExt>::Signed, &rhs.0).signed().overflowing(Signed),
            - @overflowing uops::sub(lhs as <Single as NumExt>::Signed, &rhs.0).signed().overflowing(Signed),
            * @overflowing algo::mul(lhs as <Single as NumExt>::Signed, &rhs.0).signed().overflowing(Signed),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, &rhs: &$primitive), [
            += uops::add(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().default_mut(),
            -= uops::sub(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().default_mut(),
            *= algo::mul(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().default_mut(),
            /= algo::div(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().default_mut(),
            %= algo::rem(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().default_mut(),

            |= uops::bitor(&mut lhs.0, rhs as <Single as NumExt>::Signed).eval_mut(),
            &= uops::bitand(&mut lhs.0, rhs as <Single as NumExt>::Signed).eval_mut(),
            ^= uops::bitxor(&mut lhs.0, rhs as <Single as NumExt>::Signed).eval_mut(),

            += @strict uops::add(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().strict_mut(),
            -= @strict uops::sub(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().strict_mut(),
            *= @strict algo::mul(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().strict_mut(),
            /= @strict algo::div(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().strict_mut(),
            %= @strict algo::rem(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().strict_mut(),

            += @wrapping uops::add(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().eval_mut(),
            -= @wrapping uops::sub(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().eval_mut(),
            *= @wrapping algo::mul(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().eval_mut(),
            /= @wrapping algo::div(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().eval_mut(),
            %= @wrapping algo::rem(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().eval_mut(),

            += @saturating {
                let dir = lhs.dir();

                uops::add(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
            },
            -= @saturating {
                let dir = lhs.dir();

                uops::sub(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
            },
            *= @saturating {
                let dir = lhs.dir() * Dir::from(rhs);

                algo::mul(&mut lhs.0, &Signed::from(rhs).0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
            },

            /= @saturating algo::div(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating_mut(&Signed::MAX.0),
            %= @saturating algo::rem(&mut lhs.0, rhs as <Single as NumExt>::Signed).signed().saturating_mut(&Signed::ZERO.0),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, &rhs: &$primitive) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add(&lhs.0, rhs as Single).default(Unsigned),
            - uops::sub(&lhs.0, rhs as Single).default(Unsigned),
            * algo::mul(&lhs.0, rhs as Single).default(Unsigned),
            / algo::div(&lhs.0, rhs as Single).default(Unsigned::from),
            % algo::rem(&lhs.0, rhs as Single).default(Unsigned::from),

            | uops::bitor(&lhs.0, rhs as Single).eval(),
            & uops::bitand(&lhs.0, rhs as Single).eval(),
            ^ uops::bitxor(&lhs.0, rhs as Single).eval(),

            + @checked uops::add(&lhs.0, rhs as Single).checked(Unsigned),
            - @checked uops::sub(&lhs.0, rhs as Single).checked(Unsigned),
            * @checked algo::mul(&lhs.0, rhs as Single).checked(Unsigned),
            / @checked algo::div(&lhs.0, rhs as Single).checked(Unsigned::from),
            % @checked algo::rem(&lhs.0, rhs as Single).checked(Unsigned::from),

            + @strict uops::add(&lhs.0, rhs as Single).strict(Unsigned),
            - @strict uops::sub(&lhs.0, rhs as Single).strict(Unsigned),
            * @strict algo::mul(&lhs.0, rhs as Single).strict(Unsigned),
            / @strict algo::div(&lhs.0, rhs as Single).strict(Unsigned::from),
            % @strict algo::rem(&lhs.0, rhs as Single).strict(Unsigned::from),

            + @wrapping uops::add(&lhs.0, rhs as Single).with(Unsigned),
            - @wrapping uops::sub(&lhs.0, rhs as Single).with(Unsigned),
            * @wrapping algo::mul(&lhs.0, rhs as Single).with(Unsigned),
            / @wrapping algo::div(&lhs.0, rhs as Single).with(Unsigned::from),
            % @wrapping algo::rem(&lhs.0, rhs as Single).with(Unsigned::from),

            + @saturating uops::add(&lhs.0, rhs as Single).saturating(Unsigned, &Unsigned::MAX),
            - @saturating uops::sub(&lhs.0, rhs as Single).saturating(Unsigned, &Unsigned::MIN),
            * @saturating algo::mul(&lhs.0, rhs as Single).saturating(Unsigned, &Unsigned::MAX),
            / @saturating algo::div(&lhs.0, rhs as Single).saturating(Unsigned::from, &Unsigned::MAX),
            % @saturating algo::rem(&lhs.0, rhs as Single).saturating(Unsigned::from, &Unsigned::MIN),

            + @overflowing uops::add(&lhs.0, rhs as Single).overflowing(Unsigned),
            - @overflowing uops::sub(&lhs.0, rhs as Single).overflowing(Unsigned),
            * @overflowing algo::mul(&lhs.0, rhs as Single).overflowing(Unsigned),
            / @overflowing algo::div(&lhs.0, rhs as Single).overflowing(Unsigned::from),
            % @overflowing algo::rem(&lhs.0, rhs as Single).overflowing(Unsigned::from),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Unsigned<L>) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + uops::add(lhs as Single, &rhs.0).default(Unsigned),
            - uops::sub(lhs as Single, &rhs.0).default(Unsigned),
            * algo::mul(lhs as Single, &rhs.0).default(Unsigned),

            | uops::bitor(&rhs.0, lhs as Single).eval(),
            & uops::bitand(&rhs.0, lhs as Single).eval(),
            ^ uops::bitxor(&rhs.0, lhs as Single).eval(),

            + @checked uops::add(lhs as Single, &rhs.0).checked(Unsigned),
            - @checked uops::sub(lhs as Single, &rhs.0).checked(Unsigned),
            * @checked algo::mul(lhs as Single, &rhs.0).checked(Unsigned),

            + @strict uops::add(lhs as Single, &rhs.0).strict(Unsigned),
            - @strict uops::sub(lhs as Single, &rhs.0).strict(Unsigned),
            * @strict algo::mul(lhs as Single, &rhs.0).strict(Unsigned),

            + @wrapping uops::add(lhs as Single, &rhs.0).with(Unsigned),
            - @wrapping uops::sub(lhs as Single, &rhs.0).with(Unsigned),
            * @wrapping algo::mul(lhs as Single, &rhs.0).with(Unsigned),

            + @saturating uops::add(lhs as Single, &rhs.0).saturating(Unsigned, &Unsigned::MAX),
            - @saturating uops::sub(lhs as Single, &rhs.0).saturating(Unsigned, &Unsigned::MIN),
            * @saturating algo::mul(lhs as Single, &rhs.0).saturating(Unsigned, &Unsigned::MAX),

            + @overflowing uops::add(lhs as Single, &rhs.0).overflowing(Unsigned),
            - @overflowing uops::sub(lhs as Single, &rhs.0).overflowing(Unsigned),
            * @overflowing algo::mul(lhs as Single, &rhs.0).overflowing(Unsigned),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, &rhs: &$primitive), [
            += uops::add(&mut lhs.0, rhs as Single).default_mut(),
            -= uops::sub(&mut lhs.0, rhs as Single).default_mut(),
            *= algo::mul(&mut lhs.0, rhs as Single).default_mut(),
            /= algo::div(&mut lhs.0, rhs as Single).default_mut(),
            %= algo::rem(&mut lhs.0, rhs as Single).default_mut(),

            |= uops::bitor(&mut lhs.0, rhs as Single).eval_mut(),
            &= uops::bitand(&mut lhs.0, rhs as Single).eval_mut(),
            ^= uops::bitxor(&mut lhs.0, rhs as Single).eval_mut(),

            += @strict uops::add(&mut lhs.0, rhs as Single).strict_mut(),
            -= @strict uops::sub(&mut lhs.0, rhs as Single).strict_mut(),
            *= @strict algo::mul(&mut lhs.0, rhs as Single).strict_mut(),
            /= @strict algo::div(&mut lhs.0, rhs as Single).strict_mut(),
            %= @strict algo::rem(&mut lhs.0, rhs as Single).strict_mut(),

            += @wrapping uops::add(&mut lhs.0, rhs as Single).eval_mut(),
            -= @wrapping uops::sub(&mut lhs.0, rhs as Single).eval_mut(),
            *= @wrapping algo::mul(&mut lhs.0, rhs as Single).eval_mut(),
            /= @wrapping algo::div(&mut lhs.0, rhs as Single).eval_mut(),
            %= @wrapping algo::rem(&mut lhs.0, rhs as Single).eval_mut(),

            += @saturating uops::add(&mut lhs.0, rhs as Single).saturating_mut(&Unsigned::MAX.0),
            -= @saturating uops::sub(&mut lhs.0, rhs as Single).saturating_mut(&Unsigned::MIN.0),
            *= @saturating algo::mul(&mut lhs.0, rhs as Single).saturating_mut(&Unsigned::MAX.0),
            /= @saturating algo::div(&mut lhs.0, rhs as Single).saturating_mut(&Unsigned::MAX.0),
            %= @saturating algo::rem(&mut lhs.0, rhs as Single).saturating_mut(&Unsigned::MIN.0),
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
            |= uops::bitor(&mut lhs.0, rhs as Single).eval_mut(),
            &= uops::bitand(&mut lhs.0, rhs as Single).eval_mut(),
            ^= uops::bitxor(&mut lhs.0, rhs as Single).eval_mut(),
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
            + <Signed<L> as NdAdd<$primitive, Signed<L>>>::nd_add(&lhs, &rhs),
            - <Signed<L> as NdSub<$primitive, Signed<L>>>::nd_sub(&lhs, &rhs),
            * <Signed<L> as NdMul<$primitive, Signed<L>>>::nd_mul(&lhs, &rhs),
            | <Signed<L> as NdBitOr<$primitive, Signed<L>>>::nd_bitor(&lhs, &rhs),
            & <Signed<L> as NdBitAnd<$primitive, Signed<L>>>::nd_bitand(&lhs, &rhs),
            ^ <Signed<L> as NdBitXor<$primitive, Signed<L>>>::nd_bitxor(&lhs, &rhs),
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
            + <Unsigned<L> as NdAdd<$primitive, Unsigned<L>>>::nd_add(&lhs, &rhs),
            - <Unsigned<L> as NdSub<$primitive, Unsigned<L>>>::nd_sub(&lhs, &rhs),
            * <Unsigned<L> as NdMul<$primitive, Unsigned<L>>>::nd_mul(&lhs, &rhs),
            | <Unsigned<L> as NdBitOr<$primitive, Unsigned<L>>>::nd_bitor(&lhs, &rhs),
            & <Unsigned<L> as NdBitAnd<$primitive, Unsigned<L>>>::nd_bitand(&lhs, &rhs),
            ^ <Unsigned<L> as NdBitXor<$primitive, Unsigned<L>>>::nd_bitxor(&lhs, &rhs),
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

pub mod uops {
    #![allow(clippy::type_complexity)]

    //! # Micro-ops
    //!
    //! **Long numbers/bytes uops**

    use super::*;

    /// Expression iterator for uops.
    ///
    /// Yields `lhs * mul + rhs + acc`.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ExprIter<
        Lhs: Iterator<Item = Single>,
        Rhs: Iterator<Item = Single>,
        Ctx: Copy,
        CtxFn: Copy + Fn(Single, Single, Single, Single, Ctx) -> Ctx,
    > {
        /// Lhs iterator.
        pub lhs: Lhs,

        /// Rhs iterator.
        pub rhs: Rhs,

        /// Multiplier.
        pub mul: Single,

        /// Accumulator.
        pub acc: Single,

        /// Context.
        pub ctx: Ctx,

        /// Context function.
        pub ctx_func: CtxFn,
    }

    /// Expression iterator mutable for uops.
    ///
    /// Yields `lhs * mul + rhs + acc` inplace.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ExprIterMut<
        'words,
        Lhs: Iterator<Item = &'words mut Single>,
        Rhs: Iterator<Item = Single>,
        Ctx: Copy,
        CtxFn: Copy + Fn(Single, Single, Single, Single, Ctx) -> Ctx,
    > {
        /// Lhs iterator.
        pub lhs: Lhs,

        /// Rhs iterator.
        pub rhs: Rhs,

        /// Multiplier.
        pub mul: Single,

        /// Accumulator.
        pub acc: Single,

        /// Context.
        pub ctx: Ctx,

        /// Context function.
        pub ctx_func: CtxFn,
    }

    /// Signed expression implementation marker.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SignedImpl;

    /// Unsigned expression implementation marker.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct UnsignedImpl;

    /// Not iterator expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct NotIter<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Direction iterator expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct DirvIter<Words> {
        /// Words of expression.
        pub words: Words,

        /// Direction of expression.
        pub dir: Dir,
    }

    /// Add iterators expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct AddIter<Lhs, Rhs> {
        /// Lhs in `lhs + rhs`, `lhs += rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs + rhs`, `lhs += rhs`.
        pub rhs: Rhs,
    }

    /// Sub iterators expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SubIter<Lhs, Rhs> {
        /// Lhs in `lhs - rhs`, `lhs -= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs - rhs`, `lhs -= rhs`.
        pub rhs: Rhs,
    }

    /// Bit-wise iterator expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct BitIter<Lhs, Rhs, F: Fn(Single, Single) -> Single> {
        /// Lhs in `lhs | rhs`, `lhs |= rhs`, `lhs & rhs`, `lhs &= rhs`, `lhs ^ rhs`, `lhs ^= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs | rhs`, `lhs |= rhs`, `lhs & rhs`, `lhs &= rhs`, `lhs ^ rhs`, `lhs ^= rhs`.
        pub rhs: Rhs,

        /// Bit-wise operation.
        pub func: F,
    }

    /// Not value expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Not<Words> {
        /// Words of expression.
        pub words: Words,
    }

    /// Direction value expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Dirv<Words> {
        /// Words of expression.
        pub words: Words,

        /// Direction of expression.
        pub dir: Dir,
    }

    /// Direction value (absolute) expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Dirx<Words> {
        /// Words of expression.
        pub words: Words,

        /// Direction of expression.
        pub dir: Dir,
    }

    /// Add expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Add<Lhs, Rhs, Impl> {
        /// Lhs in `lhs + rhs`, `lhs += rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs + rhs`, `lhs += rhs`.
        pub rhs: Rhs,

        /// Implementation: [`SignedImpl`], [`UnsignedImpl`].
        pub imp: Impl,
    }

    /// Sub expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Sub<Lhs, Rhs, Impl> {
        /// Lhs in `lhs - rhs`, `lhs -= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs - rhs`, `lhs -= rhs`.
        pub rhs: Rhs,

        /// Implementation: [`SignedImpl`], [`UnsignedImpl`].
        pub imp: Impl,
    }

    /// Mul expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Mul<Lhs, Rhs> {
        /// Lhs in `lhs * rhs`, `lhs *= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs * rhs`, `lhs *= rhs`.
        pub rhs: Rhs,
    }

    /// Bit-wise expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Bit<Lhs, Rhs, F: Fn(Single, Single) -> Single> {
        /// Lhs in `lhs | rhs`, `lhs |= rhs`, `lhs & rhs`, `lhs &= rhs`, `lhs ^ rhs`, `lhs ^= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs | rhs`, `lhs |= rhs`, `lhs & rhs`, `lhs &= rhs`, `lhs ^ rhs`, `lhs ^= rhs`.
        pub rhs: Rhs,

        /// Bit-wise operation.
        pub func: F,
    }

    /// Shl expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Shl<Words> {
        /// Lhs in `lhs << rhs`, `lhs <<= rhs`
        pub words: Words,

        /// Rhs in `lhs << rhs`, `lhs <<= rhs`
        pub shift: usize,

        /// Extension value.
        pub ext: Single,
    }

    /// Shr expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Shr<Words> {
        /// Lhs in `lhs >> rhs`, `lhs >>= rhs`
        pub words: Words,

        /// Rhs in `lhs >> rhs`, `lhs >>= rhs`
        pub shift: usize,

        /// Default value.
        pub default: Single,
    }

    /// Micro operations with standard implementation.
    ///
    /// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
    pub struct UopsStd;

    /// Micro operations with dynamic implementation.
    ///
    /// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
    pub struct UopsDyn;

    /// Micro operations with const-time implementation.
    ///
    /// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
    pub struct UopsCt;

    /// Micro operations.
    ///
    /// # Related
    ///
    /// - [`UopsStd`] - standard impl.
    /// - [`UopsDyn`] - dynamic impl.
    /// - [`UopsCt`] - const-time impl.
    ///
    /// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
    pub trait Uops {
        /// Flag in equality operations.
        type Flag;

        /// Order in comparison operations.
        type Order;
    }

    /// Expression.
    pub trait Expr<Words: Copy>: Sized {
        /// Evaluates expression as default.
        #[inline]
        fn default<Long: Copy, F: Fn(Words) -> Long>(self, func: F) -> Long {
            let (res, overflow) = self.eval_ext();

            debug_assert!(!overflow);

            func(res)
        }

        /// Evaluates expression as checked.
        #[inline]
        fn checked<Long: Copy, F: Fn(Words) -> Long>(self, func: F) -> Option<Long> {
            let (res, overflow) = self.eval_ext();

            match overflow {
                false => Some(func(res)),
                true => None,
            }
        }

        /// Evaluates expression as strict.
        #[inline]
        fn strict<Long: Copy, F: Fn(Words) -> Long>(self, func: F) -> Long {
            let (res, overflow) = self.eval_ext();

            assert!(!overflow);

            func(res)
        }

        /// Evaluates expression as saturating.
        #[inline]
        fn saturating<Long: Copy, F: Fn(Words) -> Long>(self, func: F, default: &Long) -> Long {
            let (res, overflow) = self.eval_ext();

            let res = func(res);

            *[&res, default][overflow as usize]
        }

        /// Evaluates expression as overflowing.
        #[inline]
        fn overflowing<Long: Copy, F: Fn(Words) -> Long>(self, func: F) -> (Long, bool) {
            let (res, overflow) = self.eval_ext();

            (func(res), overflow)
        }

        /// Evaluates expression with function.
        #[inline]
        fn with<Long: Copy, F: Fn(Words) -> Long>(self, func: F) -> Long {
            func(self.eval())
        }

        /// Evaluates expression.
        fn eval(self) -> Words;

        /// Evaluates expression with overflow.
        fn eval_ext(self) -> (Words, bool);
    }

    /// Expression mutable.
    pub trait ExprMut<'words, Words: 'words + Copy>: Sized {
        /// Evaluates expression as default.
        #[inline]
        fn default_mut(self) {
            let (_, overflow) = self.eval_ext_mut();

            debug_assert!(!overflow);
        }

        /// Evaluates expression as strict.
        #[inline]
        fn strict_mut(self) {
            let (_, overflow) = self.eval_ext_mut();

            assert!(!overflow);
        }

        /// Evaluates expression as saturating.
        #[inline]
        fn saturating_mut(self, default: &Words) {
            let (res, overflow) = self.eval_ext_mut();

            *res = *[res, default][overflow as usize];
        }

        /// Evaluates expression.
        fn eval_mut(self) -> &'words mut Words;

        /// Evaluates expression with overflow.
        fn eval_ext_mut(self) -> (&'words mut Words, bool);
    }

    /// Identity function.
    #[inline]
    pub fn id<T>(value: T) -> T {
        value
    }

    /// Identity context function.
    #[inline]
    pub fn id_ctx<Ctx>(_: Single, _: Single, _: Single, _: Single, ctx: Ctx) -> Ctx {
        ctx
    }

    impl<
        Lhs: Iterator<Item = Single>,
        Rhs: Iterator<Item = Single>,
        Ctx: Copy,
        CtxFn: Copy + Fn(Single, Single, Single, Single, Ctx) -> Ctx,
    > Iterator for ExprIter<Lhs, Rhs, Ctx, CtxFn>
    {
        type Item = Single;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let lhs = self.lhs.next()? as Double;
            let rhs = self.rhs.next()? as Double;
            let mul = self.mul as Double;
            let acc = self.acc as Double;
            let ctx = self.ctx;
            let func = &self.ctx_func;

            let val = lhs * mul + rhs + acc;
            let acc = (val / RADIX) as Single;

            self.acc = acc;
            self.ctx = func(lhs as Single, rhs as Single, acc, val as Single, ctx);

            Some(val as Single)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let lhs = self.lhs.size_hint();
            let rhs = self.lhs.size_hint();

            (lhs.0.min(rhs.0), lhs.1.and_then(|l| rhs.1.map(|r| l.min(r))))
        }
    }

    impl<
        'words,
        Lhs: Iterator<Item = &'words mut Single>,
        Rhs: Iterator<Item = Single>,
        Ctx: Copy,
        CtxFn: Copy + Fn(Single, Single, Single, Single, Ctx) -> Ctx,
    > Iterator for ExprIterMut<'words, Lhs, Rhs, Ctx, CtxFn>
    {
        type Item = Single;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let lhs = self.lhs.next()?;
            let rhs = self.rhs.next()? as Double;
            let mul = self.mul as Double;
            let acc = self.acc as Double;
            let elem = *lhs as Double;
            let ctx = self.ctx;
            let func = &self.ctx_func;

            let val = elem * mul + rhs + acc;
            let acc = (val / RADIX) as Single;

            self.acc = acc;
            self.ctx = func(*lhs, rhs as Single, acc, val as Single, ctx);

            *lhs = val as Single;

            Some(self.acc)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let lhs = self.lhs.size_hint();
            let rhs = self.lhs.size_hint();

            (lhs.0.min(rhs.0), lhs.1.and_then(|l| rhs.1.map(|r| l.min(r))))
        }
    }

    impl<
        Lhs: Iterator<Item = Single>,
        Rhs: Iterator<Item = Single>,
        Ctx: Copy,
        CtxFn: Copy + Fn(Single, Single, Single, Single, Ctx) -> Ctx,
    > ExprIter<Lhs, Rhs, Ctx, CtxFn>
    {
        /// Creates expression with acc.
        #[inline]
        pub fn acc(self, acc: Single) -> ExprIter<Lhs, Rhs, Ctx, CtxFn> {
            ExprIter {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: self.mul,
                acc,
                ctx: self.ctx,
                ctx_func: self.ctx_func,
            }
        }

        /// Creates expression with `Ctx`.
        #[inline]
        pub fn ctx<CtxNext: Copy, CtxFnNext: Copy + Fn(Single, Single, Single, Single, CtxNext) -> CtxNext>(
            self,
            ctx: CtxNext,
            ctx_func: CtxFnNext,
        ) -> ExprIter<Lhs, Rhs, CtxNext, CtxFnNext> {
            ExprIter {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: self.mul,
                acc: self.acc,
                ctx,
                ctx_func,
            }
        }

        /// Creates expression with `Ctx = ()`.
        #[inline]
        pub fn raw(self) -> ExprIter<Lhs, Rhs, (), impl Copy + Fn(Single, Single, Single, Single, ())> {
            ExprIter {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: self.mul,
                acc: self.acc,
                ctx: (),
                ctx_func: id_ctx,
            }
        }

        /// Evaluates expression.
        #[inline]
        pub fn eval<const L: usize>(mut self) -> [Single; L] {
            self.collect_with([0; L])
        }

        /// Evaluates expression with context.
        #[inline]
        pub fn eval_ext<const L: usize, F: Fn(Ctx) -> bool>(mut self, func: F) -> ([Single; L], bool) {
            let res = self.collect_with([0; L]);

            (res, func(self.ctx))
        }
    }

    impl<
        'words,
        Lhs: Iterator<Item = &'words mut Single>,
        Rhs: Iterator<Item = Single>,
        Ctx: Copy,
        CtxFn: Copy + Fn(Single, Single, Single, Single, Ctx) -> Ctx,
    > ExprIterMut<'words, Lhs, Rhs, Ctx, CtxFn>
    {
        /// Creates expression with acc.
        #[inline]
        pub fn acc(self, acc: Single) -> ExprIterMut<'words, Lhs, Rhs, Ctx, CtxFn> {
            ExprIterMut {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: self.mul,
                acc,
                ctx: self.ctx,
                ctx_func: self.ctx_func,
            }
        }

        /// Creates expression with `Ctx`.
        #[inline]
        pub fn ctx<CtxNext: Copy, CtxFnNext: Copy + Fn(Single, Single, Single, Single, CtxNext) -> CtxNext>(
            self,
            ctx: CtxNext,
            ctx_func: CtxFnNext,
        ) -> ExprIterMut<'words, Lhs, Rhs, CtxNext, CtxFnNext> {
            ExprIterMut {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: self.mul,
                acc: self.acc,
                ctx,
                ctx_func,
            }
        }

        /// Creates expression with `Ctx = ()`.
        #[inline]
        pub fn raw(self) -> ExprIterMut<'words, Lhs, Rhs, (), impl Copy + Fn(Single, Single, Single, Single, ())> {
            ExprIterMut {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: self.mul,
                acc: self.acc,
                ctx: (),
                ctx_func: id_ctx,
            }
        }

        /// Evaluates expression.
        #[inline]
        pub fn eval_mut(self) {
            self.for_each(|_| ());
        }

        /// Evaluates expression with context.
        #[inline]
        pub fn eval_ext_mut<F: Fn(Ctx) -> bool>(mut self, func: F) -> ((), bool) {
            (&mut self).for_each(|_| ());

            ((), func(self.ctx))
        }
    }

    impl<Lhs, Rhs, Impl> Add<Lhs, Rhs, Impl> {
        /// Add expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Add<Lhs, Rhs, SignedImpl> {
            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
        }
    }

    impl<Lhs, Rhs, Impl> Sub<Lhs, Rhs, Impl> {
        /// Sub expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Sub<Lhs, Rhs, SignedImpl> {
            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
        }
    }

    impl<Words: Iterator<Item = Single>> NotIter<Words> {
        /// Iterator for [`NotIter`] expression.
        #[inline]
        pub fn iter(self) -> impl Iterator<Item = Single> {
            self.words.map(|word| !word)
        }
    }

    impl<'words, Words: Iterator<Item = &'words mut Single>> NotIter<Words> {
        /// Iterator for [`NotIter`] expression.
        #[inline]
        pub fn iter_mut(self) -> impl Iterator<Item = &'words mut Single> {
            self.words.map(|word| {
                *word = !*word;
                word
            })
        }
    }

    impl<Words: Iterator<Item = Single>> DirvIter<Words> {
        /// Iterator for [`DirvIter`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            let (xor, acc) = match self.dir {
                Dir::POS => (0, 0),
                Dir::NEG => (MAX, 1),
            };

            ExprIter {
                lhs: self.words.map(move |word| word ^ xor),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<'words, Words: Iterator<Item = &'words mut Single>> DirvIter<Words> {
        /// Iterator for [`DirvIter`] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<
            'words,
            impl Iterator<Item = &'words mut Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            let (xor, acc) = match self.dir {
                Dir::POS => (0, 0),
                Dir::NEG => (MAX, 1),
            };

            ExprIterMut {
                lhs: self.words.map(move |word| {
                    *word ^= xor;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> AddIter<Lhs, Rhs> {
        /// Iterator for [`AddIter`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            ExprIter {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: 1,
                acc: 0,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> AddIter<Lhs, Rhs> {
        /// Iterator for [`AddIter`] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<
            'words,
            impl Iterator<Item = &'words mut Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            ExprIterMut {
                lhs: self.lhs,
                rhs: self.rhs,
                mul: 1,
                acc: 0,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> SubIter<Lhs, Rhs> {
        /// Iterator for [`SubIter`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            ExprIter {
                lhs: self.lhs,
                rhs: self.rhs.map(|word| !word),
                mul: 1,
                acc: 1,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> SubIter<Lhs, Rhs> {
        /// Iterator for [`SubIter`] expression.
        #[inline]
        pub fn iter_mut(
            self,
        ) -> ExprIterMut<
            'words,
            impl Iterator<Item = &'words mut Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            ExprIterMut {
                lhs: self.lhs,
                rhs: self.rhs.map(|word| !word),
                mul: 1,
                acc: 1,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>, F: 'static + Fn(Single, Single) -> Single + Copy>
        BitIter<Lhs, Rhs, F>
    {
        /// Iterator for [`BitIter`] expression.
        #[inline]
        pub fn iter(self) -> impl Iterator<Item = Single> {
            let lhs = self.lhs;
            let rhs = self.rhs;
            let func = self.func;

            lhs.zip(rhs).map(move |(lhs, rhs)| func(lhs, rhs))
        }
    }

    impl<
        'words,
        Lhs: Iterator<Item = &'words mut Single>,
        Rhs: Iterator<Item = Single>,
        F: 'static + Fn(Single, Single) -> Single + Copy,
    > BitIter<Lhs, Rhs, F>
    {
        /// Iterator for [`BitIter`] expression.
        #[inline]
        pub fn iter_mut(self) -> impl Iterator<Item = &'words mut Single> {
            let lhs = self.lhs;
            let rhs = self.rhs;
            let func = self.func;

            lhs.zip(rhs).map(move |(ptr, val)| {
                *ptr = func(*ptr, val);
                ptr
            })
        }
    }

    impl<const L: usize> Not<&[Single; L]> {
        /// Iterator for [`Not`] expression.
        #[inline]
        pub fn iter(self) -> impl Iterator<Item = Single> {
            let words = self.words.iter().copied();

            NotIter { words }.iter()
        }
    }

    impl<const L: usize> Not<&mut [Single; L]> {
        /// Iterator for [`Not`] expression.
        #[inline]
        pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Single> {
            let words = self.words.iter_mut();

            NotIter { words }.iter_mut()
        }
    }

    impl<const L: usize> Dirv<&[Single; L]> {
        /// Iterator for [`Dirv`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (usize, bool),
            impl Copy + Fn(Single, Single, Single, Single, (usize, bool)) -> (usize, bool),
        > {
            let words = self.words.iter().copied();
            let dir = self.dir;
            let xor = match self.dir {
                Dir::POS => 0,
                Dir::NEG => MAX,
            };

            DirvIter { words, dir }
                .iter()
                .ctx((0, true), move |word, _, _, _, (idx, flag)| {
                    (
                        idx + 1,
                        flag && [0, 1 << (BITS - 1)][(idx == L - 1) as usize] == word ^ xor && dir == Dir::NEG,
                    )
                })
        }
    }

    impl<const L: usize> Dirv<&mut [Single; L]> {
        /// Iterator for [`Dirv`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            (usize, bool),
            impl Copy + Fn(Single, Single, Single, Single, (usize, bool)) -> (usize, bool),
        > {
            let words = self.words.iter_mut();
            let dir = self.dir;
            let xor = match self.dir {
                Dir::POS => 0,
                Dir::NEG => MAX,
            };

            DirvIter { words, dir }
                .iter_mut()
                .ctx((0, true), move |word, _, _, _, (idx, flag)| {
                    (
                        idx + 1,
                        flag && [0, 1 << (BITS - 1)][(idx == L - 1) as usize] == word ^ xor && dir == Dir::NEG,
                    )
                })
        }
    }

    impl<const L: usize> Dirx<&[Single; L]> {
        /// Iterator for [`Dirx`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (usize, bool),
            impl Copy + Fn(Single, Single, Single, Single, (usize, bool)) -> (usize, bool),
        > {
            let dirx = self.dir;
            let (xor, acc) = match dir(self.words) == self.dir {
                true => (0, 0),
                false => (MAX, 1),
            };

            ExprIter {
                lhs: self.words.iter().copied().map(move |word| word ^ xor),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
                ctx: (0, true),
                ctx_func: move |word, _, _, _, (idx, flag)| {
                    (
                        idx + 1,
                        flag && [0, 1 << (BITS - 1)][(idx == L - 1) as usize] == word ^ xor && dirx == Dir::POS,
                    )
                },
            }
        }
    }

    impl<const L: usize> Dirx<&mut [Single; L]> {
        /// Iterator for [`Dirx`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            (usize, bool),
            impl Copy + Fn(Single, Single, Single, Single, (usize, bool)) -> (usize, bool),
        > {
            let dirx = self.dir;
            let (xor, acc) = match dir(self.words) == self.dir {
                true => (0, 0),
                false => (MAX, 1),
            };

            ExprIterMut {
                lhs: self.words.iter_mut().map(move |word| {
                    *word ^= xor;
                    word
                }),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc,
                ctx: (0, true),
                ctx_func: move |word, _, _, _, (idx, flag)| {
                    (
                        idx + 1,
                        flag && [0, 1 << (BITS - 1)][(idx == L - 1) as usize] == word ^ xor && dirx == Dir::POS,
                    )
                },
            }
        }
    }

    impl<const L: usize, Impl> Add<&[Single; L], &[Single; L], Impl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            AddIter {
                lhs: self.lhs.iter().copied(),
                rhs: self.rhs.iter().copied(),
            }
            .iter()
        }
    }

    impl<const L: usize, Impl> Add<&mut [Single; L], &[Single; L], Impl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            AddIter {
                lhs: self.lhs.iter_mut(),
                rhs: self.rhs.iter().copied(),
            }
            .iter_mut()
        }
    }

    impl<const L: usize> Add<&[Single; L], Single, UnsignedImpl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            ExprIter {
                lhs: self.lhs.iter().copied(),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: self.rhs,
                ctx: false,
                ctx_func: |_, _, acc, _, _| acc > 0,
            }
        }
    }

    impl<const L: usize> Add<Single, &[Single; L], UnsignedImpl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            Add {
                lhs: self.rhs,
                rhs: self.lhs,
                imp: self.imp,
            }
            .iter()
        }
    }

    impl<const L: usize> Add<&mut [Single; L], Single, UnsignedImpl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            ExprIterMut {
                lhs: self.lhs.iter_mut(),
                rhs: std::iter::repeat(0),
                mul: 1,
                acc: self.rhs,
                ctx: false,
                ctx_func: |_, _, acc, _, _| acc > 0,
            }
        }
    }

    impl<const L: usize> Add<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let rhs = self.rhs as Single;

            let ext = ext(&[rhs]);
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(&[rhs]);

            ExprIter {
                lhs: self.lhs.iter().copied(),
                rhs: (0..L).map(move |idx| [rhs, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
                ctx: false,
                ctx_func: move |_, _, _, word, _| eq && dirx != dir(&[word]),
            }
        }
    }

    impl<const L: usize> Add<<Single as NumExt>::Signed, &[Single; L], SignedImpl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            Add {
                lhs: self.rhs,
                rhs: self.lhs,
                imp: self.imp,
            }
            .iter()
        }
    }

    impl<const L: usize> Add<&mut [Single; L], <Single as NumExt>::Signed, SignedImpl> {
        /// Iterator for [`Add`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let rhs = self.rhs as Single;

            let ext = ext(&[rhs]);
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(&[rhs]);

            ExprIterMut {
                lhs: self.lhs.iter_mut(),
                rhs: (0..L).map(move |idx| [rhs, ext][(idx > 0) as usize]),
                mul: 1,
                acc: 0,
                ctx: false,
                ctx_func: move |_, _, _, word, _| eq && dirx != dir(&[word]),
            }
        }
    }

    impl<const L: usize, Impl> Sub<&[Single; L], &[Single; L], Impl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            SubIter {
                lhs: self.lhs.iter().copied(),
                rhs: self.rhs.iter().copied(),
            }
            .iter()
        }
    }

    impl<const L: usize, Impl> Sub<&mut [Single; L], &[Single; L], Impl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            SubIter {
                lhs: self.lhs.iter_mut(),
                rhs: self.rhs.iter().copied(),
            }
            .iter_mut()
        }
    }

    impl<const L: usize> Sub<&[Single; L], Single, UnsignedImpl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let rhs = self.rhs as Single;

            ExprIter {
                lhs: self.lhs.iter().copied(),
                rhs: (0..L).map(move |idx| [!rhs, !0][(idx > 0) as usize]),
                mul: 1,
                acc: 1,
                ctx: false,
                ctx_func: |lhs, rhs, _, _, flag| lhs < !rhs || lhs == !rhs && flag,
            }
        }
    }

    impl<const L: usize> Sub<Single, &[Single; L], UnsignedImpl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let lhs = self.lhs as Single;

            ExprIter {
                lhs: (0..L).map(move |idx| [lhs, 0][(idx > 0) as usize]),
                rhs: self.rhs.iter().copied().map(|word| !word),
                mul: 1,
                acc: 1,
                ctx: false,
                ctx_func: |lhs, rhs, _, _, flag| lhs < !rhs || lhs == !rhs && flag,
            }
        }
    }

    impl<const L: usize> Sub<&mut [Single; L], Single, UnsignedImpl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let rhs = self.rhs as Single;

            ExprIterMut {
                lhs: self.lhs.iter_mut(),
                rhs: (0..L).map(move |idx| [!rhs, !0][(idx > 0) as usize]),
                mul: 1,
                acc: 1,
                ctx: false,
                ctx_func: |lhs, rhs, _, _, flag| lhs < !rhs || lhs == !rhs && flag,
            }
        }
    }

    impl<const L: usize> Sub<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let rhs = self.rhs as Single;

            let ext = ext(&[rhs]);
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(&[rhs]);

            ExprIter {
                lhs: self.lhs.iter().copied(),
                rhs: (0..L).map(move |idx| [!rhs, !ext][(idx > 0) as usize]),
                mul: 1,
                acc: 1,
                ctx: false,
                ctx_func: move |_, _, _, word, _| !eq && dirx != dir(&[word]),
            }
        }
    }

    impl<const L: usize> Sub<<Single as NumExt>::Signed, &[Single; L], SignedImpl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let lhs = self.lhs as Single;

            let ext = ext(&[lhs]);
            let dirx = dir(&[lhs]);
            let eq = dir(&[lhs]) == dir(self.rhs);

            ExprIter {
                lhs: (0..L).map(move |idx| [lhs, ext][(idx > 0) as usize]),
                rhs: self.rhs.iter().copied().map(|word| !word),
                mul: 1,
                acc: 1,
                ctx: false,
                ctx_func: move |_, _, _, word, _| !eq && dirx != dir(&[word]),
            }
        }
    }

    impl<const L: usize> Sub<&mut [Single; L], <Single as NumExt>::Signed, SignedImpl> {
        /// Iterator for [`Sub`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            bool,
            impl Copy + Fn(Single, Single, Single, Single, bool) -> bool,
        > {
            let rhs = self.rhs as Single;

            let ext = ext(&[rhs]);
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(&[rhs]);

            ExprIterMut {
                lhs: self.lhs.iter_mut(),
                rhs: (0..L).map(move |idx| [!rhs, !ext][(idx > 0) as usize]),
                mul: 1,
                acc: 1,
                ctx: false,
                ctx_func: move |_, _, _, word, _| !eq && dirx != dir(&[word]),
            }
        }
    }

    impl<const L: usize> Mul<&[Single; L], Single> {
        /// Iterator for [`Mul`] expression.
        #[inline]
        pub fn iter(
            self,
        ) -> ExprIter<
            impl Iterator<Item = Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            ExprIter {
                lhs: self.lhs.iter().copied(),
                rhs: std::iter::repeat(0),
                mul: self.rhs,
                acc: 0,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<const L: usize> Mul<&mut [Single; L], Single> {
        /// Iterator for [`Mul`] expression.
        #[inline]
        pub fn iter_mut(
            &mut self,
        ) -> ExprIterMut<
            '_,
            impl Iterator<Item = &mut Single>,
            impl Iterator<Item = Single>,
            (),
            impl Copy + Fn(Single, Single, Single, Single, ()),
        > {
            ExprIterMut {
                lhs: self.lhs.iter_mut(),
                rhs: std::iter::repeat(0),
                mul: self.rhs,
                acc: 0,
                ctx: (),
                ctx_func: id_ctx,
            }
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Bit<&[Single; L], &[Single; L], F> {
        /// Iterator for [`Bit`] expression.
        #[inline]
        pub fn iter(self) -> impl Iterator<Item = Single> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs.iter().copied();
            let func = self.func;

            BitIter { lhs, rhs, func }.iter()
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Bit<&mut [Single; L], &[Single; L], F> {
        /// Iterator for [`Bit`] expression.
        #[inline]
        pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Single> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs.iter().copied();
            let func = self.func;

            BitIter { lhs, rhs, func }.iter_mut()
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Bit<&[Single; L], Single, F> {
        /// Iterator for [`Bit`] expression.
        #[inline]
        pub fn iter(self) -> impl Iterator<Item = Single> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs;
            let func = self.func;

            BitIter {
                lhs,
                rhs: (0..L).map(move |idx| [rhs, 0][(idx > 0) as usize]),
                func,
            }
            .iter()
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Bit<&mut [Single; L], Single, F> {
        /// Iterator for [`Bit`] expression.
        #[inline]
        pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Single> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs;
            let func = self.func;

            BitIter {
                lhs,
                rhs: (0..L).map(move |idx| [rhs, 0][(idx > 0) as usize]),
                func,
            }
            .iter_mut()
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy>
        Bit<&[Single; L], <Single as NumExt>::Signed, F>
    {
        /// Iterator for [`Bit`] expression.
        #[inline]
        pub fn iter(self) -> impl Iterator<Item = Single> {
            let lhs = self.lhs.iter().copied();
            let rhs = self.rhs as Single;
            let func = self.func;

            let ext = ext(&[rhs]);

            BitIter {
                lhs,
                rhs: (0..L).map(move |idx| [rhs, ext][(idx > 0) as usize]),
                func,
            }
            .iter()
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy>
        Bit<&mut [Single; L], <Single as NumExt>::Signed, F>
    {
        /// Iterator for [`Bit`] expression.
        #[inline]
        pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Single> {
            let lhs = self.lhs.iter_mut();
            let rhs = self.rhs as Single;
            let func = self.func;

            let ext = ext(&[rhs]);

            BitIter {
                lhs,
                rhs: (0..L).map(move |idx| [rhs, ext][(idx > 0) as usize]),
                func,
            }
            .iter_mut()
        }
    }

    impl<const L: usize> Shl<&[Single; L]> {
        /// Shl expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            self
        }

        /// Shl expression with extension value.
        #[inline]
        pub fn ext(mut self, ext: Single) -> Self {
            self.ext = ext;
            self
        }
    }

    impl<const L: usize> Shl<&mut [Single; L]> {
        /// Shl expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            self
        }

        /// Shl expression with extension value.
        #[inline]
        pub fn ext(mut self, ext: Single) -> Self {
            self.ext = ext;
            self
        }
    }

    impl<const L: usize> Shr<&[Single; L]> {
        /// Shr expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            let dir = dir(self.words);

            Self {
                words: self.words,
                shift: self.shift,
                default: [0, MAX][(dir == Dir::NEG) as usize],
            }
        }

        /// Shr expression with extension value.
        #[inline]
        pub fn ext(mut self, ext: Single) -> Self {
            self.default = ext;
            self
        }
    }

    impl<const L: usize> Shr<&mut [Single; L]> {
        /// Shr expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Self {
            let dir = dir(self.words);

            Self {
                words: self.words,
                shift: self.shift,
                default: [0, MAX][(dir == Dir::NEG) as usize],
            }
        }

        /// Shr expression with extension value.
        #[inline]
        pub fn ext(mut self, ext: Single) -> Self {
            self.default = ext;
            self
        }
    }

    impl<const L: usize, Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> Expr<[Single; L]>
        for AddIter<Lhs, Rhs>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(|_| false)
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> Expr<()> for AddIter<Lhs, Rhs> {
        #[inline]
        fn eval(self) {
            self.iter_mut().raw().eval_mut()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext_mut(|_| false)
        }
    }

    impl<const L: usize, Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>> Expr<[Single; L]>
        for SubIter<Lhs, Rhs>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(|_| false)
        }
    }

    impl<'words, Lhs: Iterator<Item = &'words mut Single>, Rhs: Iterator<Item = Single>> Expr<()> for SubIter<Lhs, Rhs> {
        #[inline]
        fn eval(self) {
            self.iter_mut().raw().eval_mut()
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            self.iter_mut().eval_ext_mut(|_| false)
        }
    }

    impl<
        const L: usize,
        Lhs: Iterator<Item = Single>,
        Rhs: Iterator<Item = Single>,
        F: 'static + Fn(Single, Single) -> Single + Copy,
    > Expr<[Single; L]> for BitIter<Lhs, Rhs, F>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().collect_with([0; L])
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.iter().collect_with([0; L]), false)
        }
    }

    impl<
        'words,
        Lhs: Iterator<Item = &'words mut Single>,
        Rhs: Iterator<Item = Single>,
        F: 'static + Fn(Single, Single) -> Single + Copy,
    > Expr<()> for BitIter<Lhs, Rhs, F>
    {
        #[inline]
        fn eval(self) {
            self.iter_mut().for_each(|_| ())
        }

        #[inline]
        fn eval_ext(self) -> ((), bool) {
            (self.iter_mut().for_each(|_| ()), false)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Not<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().collect_with([0; L])
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.iter().collect_with([0; L]), false)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Not<&'words mut [Single; L]> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().for_each(|_| ());

            self.words
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            self.iter_mut().for_each(|_| ());

            (self.words, false)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Dirv<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(|(_, flag)| flag)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Dirv<&'words mut [Single; L]> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.words
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self.iter_mut().eval_ext_mut(|(_, flag)| flag);

            (self.words, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Dirx<&[Single; L]> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(|(_, flag)| flag)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Dirx<&'words mut [Single; L]> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.words
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self.iter_mut().eval_ext_mut(|(_, flag)| flag);

            (self.words, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().ctx(false, move |_, _, acc, _, _| acc > 0).eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Add<&'words mut [Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self.iter_mut().ctx(false, move |_, _, acc, _, _| acc > 0).eval_ext_mut(id);

            (self.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(id)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<Single, &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Add<&'words mut [Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self.iter_mut().eval_ext_mut(id);

            (self.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .raw()
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(self.rhs);

            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .ctx(false, move |_, _, _, word, _| eq && dirx != dir(&[word]))
            .eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Add<&'words mut [Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let mut expr = Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            expr.iter_mut().raw().eval_mut();

            expr.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(self.rhs);

            let mut expr = Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            let (_, overflow) = expr
                .iter_mut()
                .ctx(false, move |_, _, _, word, _| eq && dirx != dir(&[word]))
                .eval_ext_mut(id);

            (expr.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .raw()
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .eval_ext(id)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Add<<Single as NumExt>::Signed, &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .raw()
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]>
        for Add<&'words mut [Single; L], <Single as NumExt>::Signed, SignedImpl>
    {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let mut expr = Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            expr.iter_mut().raw().eval_mut();

            expr.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let mut expr = Add {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            let (_, overflow) = expr.iter_mut().eval_ext_mut(id);

            (expr.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter()
                .ctx(false, |lhs, rhs, _, _, flag| lhs < !rhs || lhs == !rhs && flag)
                .eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Sub<&'words mut [Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self
                .iter_mut()
                .ctx(false, |lhs, rhs, _, _, flag| lhs < !rhs || lhs == !rhs && flag)
                .eval_ext_mut(id);

            (self.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(id)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<Single, &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Sub<&'words mut [Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self.iter_mut().eval_ext_mut(id);

            (self.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .raw()
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(self.rhs);

            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .ctx(false, move |_, _, _, word, _| !eq && dirx != dir(&[word]))
            .eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Sub<&'words mut [Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let mut expr = Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            expr.iter_mut().raw().eval_mut();

            expr.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let dirx = dir(self.lhs);
            let eq = dir(self.lhs) == dir(self.rhs);

            let mut expr = Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            let (_, overflow) = expr
                .iter_mut()
                .ctx(false, move |_, _, _, word, _| !eq && dirx != dir(&[word]))
                .eval_ext_mut(id);

            (expr.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .raw()
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .eval_ext(id)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Sub<<Single as NumExt>::Signed, &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .raw()
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .iter()
            .eval_ext(id)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]>
        for Sub<&'words mut [Single; L], <Single as NumExt>::Signed, SignedImpl>
    {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let mut expr = Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            expr.iter_mut().raw().eval_mut();

            expr.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let mut expr = Sub {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            };

            let (_, overflow) = expr.iter_mut().eval_ext_mut(id);

            (expr.lhs, overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], Single> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            self.iter().eval_ext(|_| false)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Mul<&'words mut [Single; L], Single> {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().raw().eval_mut();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            let (_, overflow) = self.iter_mut().eval_ext_mut(|_| false);

            (self.lhs, overflow)
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Expr<[Single; L]>
        for Bit<&[Single; L], &[Single; L], F>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().collect_with([0; L])
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.iter().collect_with([0; L]), false)
        }
    }

    impl<'words, const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> ExprMut<'words, [Single; L]>
        for Bit<&'words mut [Single; L], &[Single; L], F>
    {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().for_each(|_| ());

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            self.iter_mut().for_each(|_| ());

            (self.lhs, false)
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Expr<[Single; L]>
        for Bit<&[Single; L], Single, F>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().collect_with([0; L])
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.iter().collect_with([0; L]), false)
        }
    }

    impl<'words, const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> ExprMut<'words, [Single; L]>
        for Bit<&'words mut [Single; L], Single, F>
    {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().for_each(|_| ());

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            self.iter_mut().for_each(|_| ());

            (self.lhs, false)
        }
    }

    impl<const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> Expr<[Single; L]>
        for Bit<&[Single; L], <Single as NumExt>::Signed, F>
    {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.iter().collect_with([0; L])
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            (self.iter().collect_with([0; L]), false)
        }
    }

    impl<'words, const L: usize, F: 'static + Fn(Single, Single) -> Single + Copy> ExprMut<'words, [Single; L]>
        for Bit<&'words mut [Single; L], <Single as NumExt>::Signed, F>
    {
        #[inline]
        fn eval_mut(mut self) -> &'words mut [Single; L] {
            self.iter_mut().for_each(|_| ());

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(mut self) -> (&'words mut [Single; L], bool) {
            self.iter_mut().for_each(|_| ());

            (self.lhs, false)
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
            let default = self.ext;

            let offset = (shift / BITS).min(L);
            let shl = shift % BITS;
            let shr = BITS - shl;

            let mut acc = default;
            let mut res = repeat_n(default, offset)
                .chain(words[..L - offset].iter().copied())
                .collect_with([0; L]);

            for ptr in res[offset..].iter_mut() {
                let val = *ptr;

                let val_h = ptr.unbounded_shl(shl as u32);
                let val_l = acc.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            (res, shift >= BITS * L)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Shl<&'words mut [Single; L]> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            self.eval_ext_mut().0
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            use std::iter::repeat_n;

            let shift = self.shift;
            let default = self.ext;

            let offset = (shift / BITS).min(L);
            let shl = shift % BITS;
            let shr = BITS - shl;

            let mut acc = default;

            *self.words = repeat_n(default, offset)
                .chain(self.words[..L - offset].iter().copied())
                .collect_with([0; L]);

            for ptr in self.words[offset..].iter_mut() {
                let val = *ptr;

                let val_h = ptr.unbounded_shl(shl as u32);
                let val_l = acc.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            (self.words, shift >= BITS * L)
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
            let mut res = words[offset..]
                .iter()
                .copied()
                .chain(repeat_n(default, offset))
                .collect_with([0; L]);

            for ptr in res[..L - offset].iter_mut().rev() {
                let val = *ptr;

                let val_h = acc.unbounded_shl(shl as u32);
                let val_l = ptr.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            (res, shift >= BITS * L)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Shr<&'words mut [Single; L]> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            self.eval_ext_mut().0
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            use std::iter::repeat_n;

            let shift = self.shift;
            let default = self.default;

            let offset = (shift / BITS).min(L);
            let shr = shift % BITS;
            let shl = BITS - shr;

            let mut acc = default;

            *self.words = self.words[offset..]
                .iter()
                .copied()
                .chain(repeat_n(default, offset))
                .collect_with([0; L]);

            for ptr in self.words[..L - offset].iter_mut().rev() {
                let val = *ptr;

                let val_h = acc.unbounded_shl(shl as u32);
                let val_l = ptr.unbounded_shr(shr as u32);

                acc = val;
                *ptr = val_h | val_l;
            }

            (self.words, shift >= BITS * L)
        }
    }

    /// Not iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn not_iter<Words>(words: Words) -> NotIter<Words> {
        NotIter { words }
    }

    /// Positive iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn pos_iter<Words>(words: Words) -> DirvIter<Words> {
        DirvIter { words, dir: Dir::POS }
    }

    /// Negative iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn neg_iter<Words>(words: Words) -> DirvIter<Words> {
        DirvIter { words, dir: Dir::NEG }
    }

    /// Direction iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn dirv_iter<Words>(words: Words, dir: Dir) -> DirvIter<Words> {
        DirvIter { words, dir }
    }

    /// Add iterators expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn add_iter<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> AddIter<Lhs, Rhs> {
        AddIter { lhs, rhs }
    }

    /// Sub iterators expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn sub_iter<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> SubIter<Lhs, Rhs> {
        SubIter { lhs, rhs }
    }

    /// BitOr iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn bitor_iter<Lhs, Rhs>(
        lhs: Lhs,
        rhs: Rhs,
    ) -> BitIter<Lhs, Rhs, impl 'static + Fn(Single, Single) -> Single + Copy> {
        BitIter {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs | rhs,
        }
    }

    /// BitAnd iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn bitand_iter<Lhs, Rhs>(
        lhs: Lhs,
        rhs: Rhs,
    ) -> BitIter<Lhs, Rhs, impl 'static + Fn(Single, Single) -> Single + Copy> {
        BitIter {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs & rhs,
        }
    }

    /// BitXor iterator expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn bitxor_iter<Lhs, Rhs>(
        lhs: Lhs,
        rhs: Rhs,
    ) -> BitIter<Lhs, Rhs, impl 'static + Fn(Single, Single) -> Single + Copy> {
        BitIter {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs ^ rhs,
        }
    }

    /// Not value expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn not<Words>(words: Words) -> Not<Words> {
        Not { words }
    }

    /// Positive value expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn pos<Words>(words: Words) -> Dirv<Words> {
        Dirv { words, dir: Dir::POS }
    }

    /// Negative value expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn neg<Words>(words: Words) -> Dirv<Words> {
        Dirv { words, dir: Dir::NEG }
    }

    /// Direction value expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn dirv<Words>(words: Words, dir: Dir) -> Dirv<Words> {
        Dirv { words, dir }
    }

    /// Direction value (absolute) expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn dirx<Words>(words: Words, dir: Dir) -> Dirx<Words> {
        Dirx { words, dir }
    }

    /// Add expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn add<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Add<Lhs, Rhs, UnsignedImpl> {
        Add { lhs, rhs, imp: UnsignedImpl }
    }

    /// Sub expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn sub<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Sub<Lhs, Rhs, UnsignedImpl> {
        Sub { lhs, rhs, imp: UnsignedImpl }
    }

    /// Mul expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn mul<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Mul<Lhs, Rhs> {
        Mul { lhs, rhs }
    }

    /// BitOr expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn bitor<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Bit<Lhs, Rhs, impl 'static + Fn(Single, Single) -> Single + Copy> {
        Bit {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs | rhs,
        }
    }

    /// BitAnd expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn bitand<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Bit<Lhs, Rhs, impl 'static + Fn(Single, Single) -> Single + Copy> {
        Bit {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs & rhs,
        }
    }

    /// BitXor expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn bitxor<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Bit<Lhs, Rhs, impl 'static + Fn(Single, Single) -> Single + Copy> {
        Bit {
            lhs,
            rhs,
            func: |lhs: Single, rhs: Single| lhs ^ rhs,
        }
    }

    /// Shl expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn shl<Words>(words: Words, shift: usize) -> Shl<Words> {
        Shl { words, shift, ext: 0 }
    }

    /// Shr expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn shr<Words>(words: Words, shift: usize) -> Shr<Words> {
        Shr { words, shift, default: 0 }
    }

    /// Iterates words.
    #[inline]
    pub fn iter<W: Word>(words: &[W], ext: W, len: usize) -> impl Iterator<Item = W> {
        (0..len).map(move |idx| match idx < words.len() {
            true => words[idx],
            false => ext,
        })
    }

    /// Reads extension.
    #[inline]
    pub fn ext<const L: usize>(words: &[Single; L]) -> Single {
        match words[L - 1] >> (BITS - 1) {
            0 => 0,
            _ => MAX,
        }
    }

    /// Reads direction.
    #[inline]
    pub fn dir<const L: usize>(words: &[Single; L]) -> Dir {
        match words[L - 1] >> (BITS - 1) {
            0 => Dir::POS,
            _ => Dir::NEG,
        }
    }

    /// Reads sign.
    #[inline]
    pub fn sign<const L: usize>(words: &[Single; L]) -> Sign {
        match words == &[0; L] {
            false => match words[L - 1] >> (BITS - 1) {
                0 => Sign::POS,
                _ => Sign::NEG,
            },
            true => Sign::ZERO,
        }
    }

    #[inline]
    pub(crate) fn ext_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        crate::pos_ct((words[L - 1] >> (BITS - 1)) as MaskCt)
    }

    #[inline]
    pub(crate) fn eq_ct<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>>(lhs: Lhs, rhs: Rhs) -> MaskCt {
        crate::eq_ct(&lhs.zip(rhs).map(|(a, b)| a ^ b).fold(0, |acc, cmp| acc | cmp), &0)
    }

    #[inline]
    pub(crate) fn cmp_ct<Lhs: Iterator<Item = Single>, Rhs: Iterator<Item = Single>>(
        lhs: Lhs,
        rhs: Rhs,
        lhs_ext: MaskCt,
        rhs_ext: MaskCt,
    ) -> (MaskCt, MaskCt) {
        let (lt, gt) = lhs
            .zip(rhs)
            .map(|(a, b)| crate::cmp_ct(&a, &b))
            .fold((0, 0), |(lt_, gt_), (lt, gt)| {
                let eq = !lt & !gt;
                let lt = lt_ & eq | lt;
                let gt = gt_ & eq | gt;

                (lt, gt)
            });

        let xor_ext = lhs_ext ^ rhs_ext;
        let lt_res = xor_ext & lhs_ext | !xor_ext & lt;
        let gt_res = xor_ext & rhs_ext | !xor_ext & gt;

        (lt_res, gt_res)
    }

    #[inline]
    pub(crate) fn words_ct<const L: usize>(
        words: &[Single; L],
        mask: MaskCt,
    ) -> BitIter<
        impl Iterator<Item = Single>,
        impl Iterator<Item = Single>,
        impl 'static + Fn(Single, Single) -> Single + Copy,
    > {
        let mask = Single::from_ne_bytes([mask; BYTES]);

        uops::bitand_iter(words.iter().copied(), (0..L).map(move |_| mask))
    }
}

pub mod algo {
    //! # Algorithms
    //!
    //! **Long numbers/bytes algorithms**

    use super::uops::{Expr, ExprMut, SignedImpl, UnsignedImpl};
    use super::*;

    /// Mul expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Mul<Lhs, Rhs, Impl> {
        /// Lhs in `lhs * rhs`, `lhs *= rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs * rhs`, `lhs *= rhs`.
        pub rhs: Rhs,

        /// Implementation: [`SignedImpl`], [`UnsignedImpl`].
        pub imp: Impl,
    }

    /// Div expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Div<Lhs, Rhs, Impl> {
        /// Lhs in `lhs / rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs / rhs`.
        pub rhs: Rhs,

        /// Implementation: [`SignedImpl`], [`UnsignedImpl`].
        pub imp: Impl,
    }

    /// Rem expression.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Rem<Lhs, Rhs, Impl> {
        /// Lhs in `lhs % rhs`.
        pub lhs: Lhs,

        /// Rhs in `lhs % rhs`.
        pub rhs: Rhs,

        /// Implementation: [`SignedImpl`], [`UnsignedImpl`].
        pub imp: Impl,
    }

    #[inline]
    fn search<N: Num, F: Fn(N) -> bool>(l: N, r: N, func: F) -> N {
        let mut idx = N::ZERO;
        let mut len = N::nd_sub(&r, &l);

        while len > N::ZERO {
            let half = N::nd_shr(&len, 1);
            let index = N::nd_add(&idx, &half);
            let step = N::nd_sub(&len, &half);

            let diff = [N::ZERO, step][func(index) as usize];

            idx = N::nd_add(&idx, &diff);
            len = half;
        }

        idx
    }

    impl<Lhs, Rhs, Impl> Mul<Lhs, Rhs, Impl> {
        /// Mul expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Mul<Lhs, Rhs, SignedImpl> {
            Mul {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
        }
    }

    impl<Lhs, Rhs, Impl> Div<Lhs, Rhs, Impl> {
        /// Div expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Div<Lhs, Rhs, SignedImpl> {
            Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
        }
    }

    impl<Lhs, Rhs, Impl> Rem<Lhs, Rhs, Impl> {
        /// Rem expression for signed numbers.
        #[inline]
        pub fn signed(self) -> Rem<Lhs, Rhs, SignedImpl> {
            Rem {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
        }
    }

    impl<const L: usize> Div<&[Single; L], &[Single; L], UnsignedImpl> {
        /// Checks overflow.
        #[inline]
        pub fn overflows(&self) -> bool {
            self.rhs == &[0; L]
        }
    }

    impl<const L: usize> Div<&[Single; L], Single, UnsignedImpl> {
        /// Checks overflow.
        #[inline]
        pub fn overflows(&self) -> bool {
            self.rhs == 0
        }
    }

    impl<const L: usize> Div<&[Single; L], &[Single; L], SignedImpl> {
        /// Checks overflow.
        #[inline]
        pub fn overflows(&self) -> bool {
            self.rhs == &[0; L] || self.lhs == &Signed::MIN.0 && self.rhs == &[MAX; L]
        }
    }

    impl<const L: usize> Div<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        /// Checks overflow.
        #[inline]
        pub fn overflows(&self) -> bool {
            self.rhs == 0 || self.lhs == &Signed::MIN.0 && self.rhs == -1
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut res = [0; L];

            for (idx, val) in rhs.iter().copied().enumerate() {
                uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval_mut();
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

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            uops::mul(self.lhs, self.rhs).iter().raw().eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            uops::mul(self.lhs, self.rhs)
                .iter()
                .ctx(false, |_, _, acc, _, _| acc > 0)
                .eval_ext(uops::id)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<Single, &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Mul {
                lhs: self.rhs,
                rhs: self.lhs,
                imp: self.imp,
            }
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            Mul {
                lhs: self.rhs,
                rhs: self.lhs,
                imp: self.imp,
            }
            .eval_ext()
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut res = [0; L];

            for (idx, val) in rhs.iter().copied().enumerate() {
                uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval_mut();
            }

            res
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let ext = uops::ext(rhs);

            let mut res = [[0; L]; 2];

            for (idx, val) in rhs.iter().copied().enumerate() {
                let mut iter = uops::mul(lhs, val).iter();

                let acc = uops::add_iter(res[0][idx..].iter_mut(), &mut iter)
                    .iter_mut()
                    .last()
                    .unwrap_or(0);

                let acc = uops::add_iter(res[1][..idx].iter_mut(), &mut iter)
                    .iter_mut()
                    .acc(acc)
                    .last()
                    .unwrap_or(0);

                let mut iter = uops::mul([&[0; L], &[MAX; L]][(uops::dir(lhs) == Dir::NEG) as usize], val)
                    .iter()
                    .acc(iter.acc);

                uops::add_iter(res[1][idx..].iter_mut(), &mut iter)
                    .iter_mut()
                    .acc(acc)
                    .eval_mut();
            }

            for (idx, val) in (0..L).map(|_| ext).enumerate() {
                uops::add_iter(res[1][idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval_mut();
            }

            let dir = uops::dir(&res[0]);

            (res[0], &res[1] != [&[0; L], &[MAX; L]][(dir == Dir::NEG) as usize])
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = self.lhs;
            let rhs = self.rhs as Single;

            let ext = uops::ext(&[rhs]);

            let mut res = [0; L];

            for (idx, val) in (0..L).map(|idx| [rhs, ext][(idx > 0) as usize]).enumerate() {
                uops::add_iter(res[idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval_mut();
            }

            res
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let lhs = self.lhs;
            let rhs = self.rhs as Single;

            let ext = uops::ext(&[rhs]);

            let mut res = [[0; L]; 2];

            for (idx, val) in (0..L).map(|idx| [rhs, ext][(idx > 0) as usize]).enumerate() {
                let mut iter = uops::mul(lhs, val).iter();

                let acc = uops::add_iter(res[0][idx..].iter_mut(), &mut iter)
                    .iter_mut()
                    .last()
                    .unwrap_or(0);

                let acc = uops::add_iter(res[1][..idx].iter_mut(), &mut iter)
                    .iter_mut()
                    .acc(acc)
                    .last()
                    .unwrap_or(0);

                let mut iter = uops::mul([&[0; L], &[MAX; L]][(uops::dir(lhs) == Dir::NEG) as usize], val)
                    .iter()
                    .acc(iter.acc);

                uops::add_iter(res[1][idx..].iter_mut(), &mut iter)
                    .iter_mut()
                    .acc(acc)
                    .eval_mut();
            }

            for (idx, val) in (0..L).map(|_| ext).enumerate() {
                uops::add_iter(res[1][idx..].iter_mut(), uops::mul(lhs, val).iter())
                    .iter_mut()
                    .eval_mut();
            }

            let dir = uops::dir(&res[0]);

            (res[0], &res[1] != [&[0; L], &[MAX; L]][(dir == Dir::NEG) as usize])
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Mul<<Single as NumExt>::Signed, &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Mul {
                lhs: self.rhs,
                rhs: self.lhs,
                imp: self.imp,
            }
            .eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            Mul {
                lhs: self.rhs,
                rhs: self.lhs,
                imp: self.imp,
            }
            .eval_ext()
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Mul<&'words mut [Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Mul {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let (res, overflow) = Mul {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval_ext();

            *self.lhs = res;

            (self.lhs, overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Mul<&'words mut [Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let mut expr = uops::mul(self.lhs, self.rhs);

            expr.iter_mut().raw().eval_mut();

            expr.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let mut expr = uops::mul(self.lhs, self.rhs);

            let (_, overflow) = expr.iter_mut().ctx(false, |_, _, acc, _, _| acc > 0).eval_ext_mut(uops::id);

            (expr.lhs, overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Mul<&'words mut [Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Mul {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let (res, overflow) = Mul {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: SignedImpl,
            }
            .eval_ext();

            *self.lhs = res;

            (self.lhs, overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]>
        for Mul<&'words mut [Single; L], <Single as NumExt>::Signed, SignedImpl>
    {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Mul {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let (res, overflow) = Mul {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval_ext();

            *self.lhs = res;

            (self.lhs, overflow)
        }
    }

    impl<'words, const L: usize> Div<&'words [Single; L], &'words [Single; L], UnsignedImpl> {
        /// Evaluates div + rem.
        #[inline]
        pub fn evalx(self) -> ([Single; L], [Single; L]) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut div = [0; L];
            let mut rem = [0; L];

            for (ptr, val) in div.iter_mut().zip(lhs.iter().copied()).rev() {
                for idx in (1..rem.len()).rev() {
                    rem[idx] = rem[idx - 1];
                }

                rem[0] = val;

                *ptr = search(0, RADIX, |m: Double| {
                    let mut iter = uops::mul(rhs, m as Single).iter();

                    let cmp = (&mut iter).zip(rem.iter().copied()).fold(Ordering::Equal, |acc, (lhs, rhs)| {
                        match lhs.cmp(&rhs) {
                            Ordering::Less => Ordering::Less,
                            Ordering::Equal => acc,
                            Ordering::Greater => Ordering::Greater,
                        }
                    });

                    [Ordering::Less, Ordering::Equal].contains(&cmp) && iter.acc == 0
                })
                .saturating_sub(1) as Single;

                uops::sub_iter(rem.iter_mut(), uops::mul(rhs, *ptr).iter()).eval();
            }

            (div, rem)
        }
    }

    impl<const L: usize> Div<&[Single; L], Single, UnsignedImpl> {
        /// Evaluates div + rem.
        #[inline]
        pub fn evalx(self) -> ([Single; L], Single) {
            let lhs = self.lhs;
            let rhs = self.rhs;

            let mut div = [0; L];
            let mut rem = 0 as Double;

            for (ptr, val) in div.iter_mut().zip(lhs.iter().copied()).rev() {
                rem <<= BITS;
                rem |= val as Double;

                *ptr = search(0, RADIX, |m: Double| m * rhs as Double <= rem).saturating_sub(1) as Single;

                rem -= *ptr as Double * rhs as Double;
            }

            (div, rem as Single)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Div<&[Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.evalx().0
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let overflow = self.overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Div<&[Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            self.evalx().0
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let overflow = self.overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Rem<&[Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .evalx()
            .1
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let overflow = Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<Single> for Rem<&[Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval(self) -> Single {
            Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .evalx()
            .1
        }

        #[inline]
        fn eval_ext(self) -> (Single, bool) {
            let overflow = Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Div<&[Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = uops::dirx(self.lhs, Dir::POS).eval();
            let rhs = uops::dirx(self.rhs, Dir::POS).eval();
            let lhs_dir = uops::dir(self.lhs);
            let rhs_dir = uops::dir(self.rhs);

            let res = Div {
                lhs: &lhs,
                rhs: &rhs,
                imp: UnsignedImpl,
            }
            .eval();

            uops::dirx(&res, lhs_dir * rhs_dir).eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let overflow = self.overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Div<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = uops::dirx(self.lhs, Dir::POS).eval();
            let lhs_dir = uops::dir(self.lhs);

            let rhs = self.rhs.unsigned_abs();
            let rhs_dir = Dir::from(self.rhs);

            let res = Div {
                lhs: &lhs,
                rhs,
                imp: UnsignedImpl,
            }
            .eval();

            uops::dirx(&res, lhs_dir * rhs_dir).eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let overflow = self.overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<[Single; L]> for Rem<&[Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval(self) -> [Single; L] {
            let lhs = uops::dirx(self.lhs, Dir::POS).eval();
            let rhs = uops::dirx(self.rhs, Dir::POS).eval();
            let lhs_dir = uops::dir(self.lhs);

            let res = Rem {
                lhs: &lhs,
                rhs: &rhs,
                imp: UnsignedImpl,
            }
            .eval();

            uops::dirx(&res, lhs_dir).eval()
        }

        #[inline]
        fn eval_ext(self) -> ([Single; L], bool) {
            let overflow = Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval(), overflow)
        }
    }

    impl<const L: usize> Expr<<Single as NumExt>::Signed> for Rem<&[Single; L], <Single as NumExt>::Signed, SignedImpl> {
        #[inline]
        fn eval(self) -> <Single as NumExt>::Signed {
            let lhs = uops::dirx(self.lhs, Dir::POS).eval();
            let lhs_dir = uops::dir(self.lhs);

            let rhs = self.rhs.unsigned_abs();

            let res = Rem {
                lhs: &lhs,
                rhs,
                imp: UnsignedImpl,
            }
            .eval() as <Single as NumExt>::Signed;

            [res, res.wrapping_neg()][(lhs_dir == Dir::NEG) as usize]
        }

        #[inline]
        fn eval_ext(self) -> (<Single as NumExt>::Signed, bool) {
            let overflow = Div {
                lhs: self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Div<&'words mut [Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Div<&'words mut [Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Rem<&'words mut [Single; L], &[Single; L], UnsignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Rem {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Rem<&'words mut [Single; L], Single, UnsignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let res = Rem {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs[0] = res;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = 0);
            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Div<&'words mut [Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]>
        for Div<&'words mut [Single; L], <Single as NumExt>::Signed, SignedImpl>
    {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]> for Rem<&'words mut [Single; L], &[Single; L], SignedImpl> {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            *self.lhs = Rem {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval();

            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    impl<'words, const L: usize> ExprMut<'words, [Single; L]>
        for Rem<&'words mut [Single; L], <Single as NumExt>::Signed, SignedImpl>
    {
        #[inline]
        fn eval_mut(self) -> &'words mut [Single; L] {
            let val = Rem {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .eval() as Single;

            let ext = uops::ext(&[val]);

            self.lhs[0] = val;
            self.lhs[1..].iter_mut().for_each(|ptr| *ptr = ext);
            self.lhs
        }

        #[inline]
        fn eval_ext_mut(self) -> (&'words mut [Single; L], bool) {
            let overflow = Div {
                lhs: &*self.lhs,
                rhs: self.rhs,
                imp: self.imp,
            }
            .overflows();

            (self.eval_mut(), overflow)
        }
    }

    /// Mul expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn mul<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Mul<Lhs, Rhs, UnsignedImpl> {
        Mul { lhs, rhs, imp: UnsignedImpl }
    }

    /// Div expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn div<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Div<Lhs, Rhs, UnsignedImpl> {
        Div { lhs, rhs, imp: UnsignedImpl }
    }

    /// Rem expression.
    ///
    /// Evaluated via [`Expr`] methods.
    #[inline]
    pub fn rem<Lhs, Rhs>(lhs: Lhs, rhs: Rhs) -> Rem<Lhs, Rhs, UnsignedImpl> {
        Rem { lhs, rhs, imp: UnsignedImpl }
    }
}

pub mod radix {
    //! # Radix
    //!
    //! **Radix related definitions**

    use super::*;

    /// Dec radix.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Dec;

    /// Bin radix.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Bin;

    /// Oct radix.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Oct;

    /// Hex radix.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Hex;

    /// X64 radix.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct X64;

    /// Radix.
    pub enum Radix<'str> {
        /// Dec radix.
        Dec(Dir, &'str str, codec::Dec),

        /// Bin radix.
        Bin(Dir, &'str str, codec::Bin),

        /// Oct radix.
        Oct(Dir, &'str str, codec::Oct),

        /// Hex radix.
        Hex(Dir, &'str str, codec::Hex),

        /// X64 radix.
        X64(Dir, &'str str, codec::X64),
    }

    /// Error.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
    pub enum Error {
        /// Found invalid direction.
        #[error("Found invalid direction")]
        InvalidDir,
        /// Found invalid payload.
        #[error("Found invalid payload")]
        InvalidPayload,
    }

    impl<'str> TryFrom<&'str str> for Radix<'str> {
        type Error = Error;

        #[inline]
        fn try_from(str: &'str str) -> Result<Self, Self::Error> {
            let (str, dir) = match &str[..1] {
                "" => Err(Error::InvalidDir),
                "+" => Ok((&str[1..], Dir::POS)),
                "-" => Ok((&str[1..], Dir::NEG)),
                _ => Ok((str, Dir::POS)),
            }?;

            match &str[..2] {
                "0x" | "0X" if !str[2..].is_empty() => Ok(Self::Hex(dir, &str[2..], codec::Hex)),
                "0o" | "0O" if !str[2..].is_empty() => Ok(Self::Oct(dir, &str[2..], codec::Oct)),
                "0b" | "0B" if !str[2..].is_empty() => Ok(Self::Bin(dir, &str[2..], codec::Bin)),
                "0x" | "0X" | "0o" | "0O" | "0b" | "0B" | "" => Err(Error::InvalidPayload),
                _ => Ok(Self::Dec(dir, str, codec::Dec)),
            }
        }
    }

    impl Radix<'_> {
        /// Parse into words.
        #[inline]
        pub fn parse<W: Word, Words: AsWordsMut<W>>(&self, words: Words) -> Words {
            match self {
                Radix::Dec(_, _, _) => words,
                Radix::Bin(_, str, _) => codec::Bin::decode(words, str.bytes().rev()),
                Radix::Oct(_, str, _) => codec::Oct::decode(words, str.bytes().rev()),
                Radix::Hex(_, str, _) => codec::Hex::decode(words, str.bytes().rev()),
                Radix::X64(_, str, _) => codec::X64::decode(words, str.bytes().rev()),
            }
        }

        /// Parse into words (checked).
        #[inline]
        #[rustfmt::skip]
        pub fn try_parse<W: Word, Words: AsWordsMut<W>>(&self, words: Words) -> Result<Words, Error> {
            match self {
                Radix::Dec(_, _, _) => Ok(words),
                Radix::Bin(_, str, _) => codec::Bin::try_decode(words, str.bytes().rev()).map_err(|_| Error::InvalidPayload),
                Radix::Oct(_, str, _) => codec::Oct::try_decode(words, str.bytes().rev()).map_err(|_| Error::InvalidPayload),
                Radix::Hex(_, str, _) => codec::Hex::try_decode(words, str.bytes().rev()).map_err(|_| Error::InvalidPayload),
                Radix::X64(_, str, _) => codec::X64::try_decode(words, str.bytes().rev()).map_err(|_| Error::InvalidPayload),
            }
        }
    }

    #[inline]
    pub(crate) fn write<Ascii: ExactSizeIterator<Item = u8> + DoubleEndedIterator>(
        fmt: &mut Formatter<'_>,
        ascii_len: Ascii,
        ascii_fmt: Ascii,
        prefix: &'static str,
    ) -> std::fmt::Result {
        if fmt.alternate() {
            fmt.write_str(prefix)?;
        }

        let len = ascii_len.length(b'0').max(1);

        codec::write(fmt, ascii_fmt.take(len).rev())
    }

    #[inline]
    pub(crate) fn write_dec<W: Word, Words: Iterator<Item = W> + ExactSizeIterator>(
        fmt: &mut Formatter<'_>,
        words: Words,
        dir: Dir,
        digits: usize,
    ) -> std::fmt::Result {
        let len = words.len();
        let sign = match dir {
            Dir::NEG => "-",
            Dir::POS => "",
        };

        let mut buf = vec![b'0'; len * digits];

        for (idx, word) in words.enumerate() {
            let offset = (len - idx - 1) * digits;

            Cursor::new(&mut buf[offset..])
                .write_fmt(format_args!("{word:0digits$}"))
                .map_err(|_| std::fmt::Error)?;
        }

        let offset = buf.len() - buf.iter().copied().rev().length(b'0');

        if offset == buf.len() {
            return fmt.write_str("0");
        }

        let str = match str::from_utf8(&buf[offset..]) {
            Ok(val) => val,
            Err(_) => return Err(std::fmt::Error),
        };

        write!(fmt, "{}{}", sign, str)
    }
}

pub mod digits {
    //! # Digits
    //!
    //! **Digits related definitions**

    use super::*;

    /// `From`/`To`/`Into` digits conversion by `exp`.
    ///
    /// For more info, see [`ToDigits`] documentation.
    pub struct ExpImpl<W: Word> {
        /// Exponent used in conversions.
        ///
        /// Radix is `1 << exp`.
        pub exp: W,
    }

    /// `From`/`To`/`Into` digits conversion by `radix`.
    ///
    /// For more info, see [`IntoDigits`] documentation.
    pub struct RadixImpl<W: Word> {
        /// Radix used in conversions.
        ///
        /// Radix is arbitrary.
        pub radix: W,
    }

    /// Digits iterator.
    ///
    /// For more info, see [`IntoDigits`] documentation.
    #[derive(Debug, Clone)]
    pub struct DigitsIter<Words: AsWordsMut<Single>> {
        /// Words.
        pub words: Words,

        /// Radix.
        pub radix: Single,

        /// Index.
        pub idx: usize,

        /// Length.
        pub len: usize,
    }

    /// Error type for failable long conversion from digits.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
    pub enum DigitsError {
        /// Found invalid payload.
        #[error("Found invalid payload")]
        InvalidPayload,
    }

    /// Error type for failable conversion to digits.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
    pub enum ExpError {
        /// Found invalid exp.
        #[error("Found invalid exp '{exp}'")]
        InvalidExponent {
            /// Exponent value.
            exp: usize,
        },
    }

    /// Error type for failable conversion into digits.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
    pub enum RadixError {
        /// Found invalid radix.
        #[error("Found invalid radix '{radix}'")]
        InvalidRadix {
            /// Radix value.
            radix: usize,
        },
    }

    /// Conversion to arbitrary digits iterator represented by [`Word`] with `exp`.
    ///
    /// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
    pub trait ToDigits: Sized {
        /// Conversion function.
        fn to_digits<W: Word>(&self, ctx: ExpImpl<W>) -> impl ExactSizeIterator<Item = W>;
    }

    /// Conversion into arbitrary digits iterator represented by [`Word`] with `radix`.
    ///
    /// For more info, see [module-level](crate::long) and [crate-level](crate) documentation.
    pub trait IntoDigits: Sized {
        /// Conversion function.
        fn into_digits(self, ctx: RadixImpl<Single>) -> impl ExactSizeIterator<Item = Single>;
    }

    impl<W: Word> ExpImpl<W> {
        /// [`ExpImpl`] from word.
        pub fn from(exp: W) -> ExpImpl<W> {
            ExpImpl { exp }
        }

        /// [`ExpImpl`] from word (checked).
        pub fn try_from(exp: W) -> Result<ExpImpl<W>, ExpError> {
            let value = exp.as_usize();

            match value == 0 || value >= W::BITS {
                false => Ok(ExpImpl { exp }),
                true => Err(ExpError::InvalidExponent { exp: value }),
            }
        }
    }

    impl<W: Word> RadixImpl<W> {
        /// [`RadixImpl`] from word.
        pub fn from(radix: W) -> RadixImpl<W> {
            RadixImpl { radix }
        }

        /// [`RadixImpl`] from word (checked).
        pub fn try_from(radix: W) -> Result<RadixImpl<W>, RadixError> {
            let value = radix.as_usize();

            match value < 2 {
                false => Ok(RadixImpl { radix }),
                true => Err(RadixError::InvalidRadix { radix: value }),
            }
        }
    }

    impl<Words: AsWordsMut<Single>> ExactSizeIterator for DigitsIter<Words> {}
    impl<Words: AsWordsMut<Single>> Iterator for DigitsIter<Words> {
        type Item = Single;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let radix = self.radix.as_double();

            let mut any = 0;
            let mut acc = 0;

            for word in self.words.as_words_mut().iter_mut().rev() {
                any |= *word;
                acc = (acc << BITS) | *word as Double;

                *word = (acc / radix) as Single;

                acc %= radix;
            }

            if any == 0 {
                return None;
            }

            self.idx += 1;

            Some(acc as Single)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.len - self.idx;

            (len, Some(len))
        }
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
pub struct SignedRef<'words, const L: usize>(pub &'words [Single; L]);

/// Signed long represented with `[Word; L]` by mutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, PartialEq, Eq)]
pub struct SignedMut<'words, const L: usize>(pub &'words mut [Single; L]);

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
pub struct UnsignedRef<'words, const L: usize>(pub &'words [Single; L]);

/// Unsigned long represented with `[Word; L]` by mutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, PartialEq, Eq)]
pub struct UnsignedMut<'words, const L: usize>(pub &'words mut [Single; L]);

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
pub struct BytesRef<'words, const L: usize>(pub &'words [Single; L]);

/// Bytes long represented with `[Word; L]` by mutable reference, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, PartialEq, Eq)]
pub struct BytesMut<'words, const L: usize>(pub &'words mut [Single; L]);

/// Error type for failable conversions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum InitError {
    /// Found invalid length during initializing.
    ///
    /// Data doesn't fit long by type (without leading-zeroes check).
    #[error("Found invalid length during initializing")]
    InvalidLength,
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

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N], ()> for Signed<L> {
    #[inline]
    fn nd_from(value: &[W; N], _: ()) -> Self {
        Self(from_array(value, 0))
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N], ()> for Unsigned<L> {
    #[inline]
    fn nd_from(value: &[W; N], _: ()) -> Self {
        Self(from_array(value, 0))
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N], ()> for Bytes<L> {
    #[inline]
    fn nd_from(value: &[W; N], _: ()) -> Self {
        Self(from_array(value, 0))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W], ()> for Signed<L> {
    #[inline]
    fn nd_from(value: &[W], _: ()) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W], ()> for Unsigned<L> {
    #[inline]
    fn nd_from(value: &[W], _: ()) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W], ()> for Bytes<L> {
    #[inline]
    fn nd_from(value: &[W], _: ()) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N], ()> for Signed<L> {
    type Error = InitError;

    #[inline]
    fn nd_try_from(value: &[W; N], _: ()) -> Result<Self, Self::Error> {
        try_from_array(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N], ()> for Unsigned<L> {
    type Error = InitError;

    #[inline]
    fn nd_try_from(value: &[W; N], _: ()) -> Result<Self, Self::Error> {
        try_from_array(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N], ()> for Bytes<L> {
    type Error = InitError;

    #[inline]
    fn nd_try_from(value: &[W; N], _: ()) -> Result<Self, Self::Error> {
        try_from_array(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W], ()> for Signed<L> {
    type Error = InitError;

    #[inline]
    fn nd_try_from(value: &[W], _: ()) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W], ()> for Unsigned<L> {
    type Error = InitError;

    #[inline]
    fn nd_try_from(value: &[W], _: ()) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W], ()> for Bytes<L> {
    type Error = InitError;

    #[inline]
    fn nd_try_from(value: &[W], _: ()) -> Result<Self, Self::Error> {
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

impl<const L: usize, W: Word, Words: Clone + ExactSizeIterator<Item = W> + DoubleEndedIterator>
    NdTryFrom<Words, ExpImpl<W>> for Signed<L>
{
    type Error = DigitsError;

    #[inline]
    fn nd_try_from(words: Words, ctx: ExpImpl<W>) -> Result<Self, Self::Error> {
        Decoded::try_write(Self([0; L]), ctx.exp.as_usize(), words).map_err(|_| DigitsError::InvalidPayload)
    }
}

impl<const L: usize, W: Word, Words: Clone + ExactSizeIterator<Item = W> + DoubleEndedIterator>
    NdTryFrom<Words, ExpImpl<W>> for Unsigned<L>
{
    type Error = DigitsError;

    #[inline]
    fn nd_try_from(words: Words, ctx: ExpImpl<W>) -> Result<Self, Self::Error> {
        Decoded::try_write(Self([0; L]), ctx.exp.as_usize(), words).map_err(|_| DigitsError::InvalidPayload)
    }
}

impl<const L: usize, W: Word, Words: Clone + ExactSizeIterator<Item = W> + DoubleEndedIterator>
    NdTryFrom<Words, RadixImpl<W>> for Signed<L>
{
    type Error = DigitsError;

    #[inline]
    fn nd_try_from(_words: Words, _ctx: RadixImpl<W>) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl<const L: usize, W: Word, Words: Clone + ExactSizeIterator<Item = W> + DoubleEndedIterator>
    NdTryFrom<Words, RadixImpl<W>> for Unsigned<L>
{
    type Error = DigitsError;

    #[inline]
    fn nd_try_from(_words: Words, _ctx: RadixImpl<W>) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl<const L: usize> NdxFrom<Signed<L>, ()> for Signed<L> {
    fn ndx_from(value: Signed<L>, _: ()) -> Self {
        value
    }
}

impl<const L: usize> NdxFrom<Unsigned<L>, ()> for Unsigned<L> {
    fn ndx_from(value: Unsigned<L>, _: ()) -> Self {
        value
    }
}

impl<const L: usize> NdxFrom<Bytes<L>, ()> for Bytes<L> {
    fn ndx_from(value: Bytes<L>, _: ()) -> Self {
        value
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = radix::Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Radix::try_from(s)?.try_parse::<u8, Self>(Self::default())
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = radix::Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Radix::try_from(s)?.try_parse::<u8, Self>(Self::default())
    }
}

impl<const L: usize> FromStr for Bytes<L> {
    type Err = radix::Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Radix::try_from(s)?.try_parse::<u8, Self>(Self::default())
    }
}

impl<const L: usize> NdFromStr<Dec> for Signed<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(_s: &str, _: Dec) -> Result<Self, Self::Err> {
        todo!()
    }
}

impl<const L: usize> NdFromStr<Dec> for Unsigned<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(_s: &str, _: Dec) -> Result<Self, Self::Err> {
        todo!()
    }
}

impl<const L: usize> NdFromStr<Bin> for Signed<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Bin) -> Result<Self, Self::Err> {
        codec::Bin::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Bin> for Unsigned<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Bin) -> Result<Self, Self::Err> {
        codec::Bin::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Bin> for Bytes<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Bin) -> Result<Self, Self::Err> {
        codec::Bin::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Oct> for Signed<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Oct) -> Result<Self, Self::Err> {
        codec::Oct::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Oct> for Unsigned<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Oct) -> Result<Self, Self::Err> {
        codec::Oct::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Oct> for Bytes<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Oct) -> Result<Self, Self::Err> {
        codec::Oct::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Hex> for Signed<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Hex) -> Result<Self, Self::Err> {
        codec::Hex::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Hex> for Unsigned<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Hex) -> Result<Self, Self::Err> {
        codec::Hex::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
    }
}

impl<const L: usize> NdFromStr<Hex> for Bytes<L> {
    type Err = radix::Error;

    #[inline]
    fn nd_from_str(s: &str, _: Hex) -> Result<Self, Self::Err> {
        codec::Hex::try_decode::<u8, Self>(Self::default(), s.bytes().rev()).map_err(|_| Error::InvalidPayload)
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
        let lhs_dir = uops::dir(&self.0);
        let rhs_dir = uops::dir(&other.0);

        let (lt, gt) = match (lhs_dir, rhs_dir) {
            (Dir::POS, Dir::POS) => (-1, 1),
            (Dir::POS, Dir::NEG) => (1, 1),
            (Dir::NEG, Dir::POS) => (-1, -1),
            (Dir::NEG, Dir::NEG) => (1, -1),
        };

        let lhs = uops::dirx(&self.0, Dir::POS).iter();
        let rhs = uops::dirx(&other.0, Dir::POS).iter();

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
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let radix = RadixImpl {
            radix: codec::Dec::RADIX as Single,
        };

        let iter = uops::dirx(&self.0, Dir::POS).with(Signed).into_digits(radix);

        write_dec(fmt, iter, self.dir(), codec::Dec::DIGITS)
    }
}

impl<const L: usize> Display for Unsigned<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        let radix = RadixImpl {
            radix: codec::Dec::RADIX as Single,
        };

        let iter = self.into_digits(radix);

        write_dec(fmt, iter, Dir::POS, codec::Dec::DIGITS)
    }
}

impl<const L: usize> Display for Bytes<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Hex>(self),
            Encode::<u8>::encoded::<codec::Hex>(self),
            codec::Hex::PREFIX,
        )
    }
}

impl<const L: usize> Binary for Signed<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Bin>(self),
            Encode::<u8>::encoded::<codec::Bin>(self),
            codec::Bin::PREFIX,
        )
    }
}

impl<const L: usize> Binary for Unsigned<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Bin>(self),
            Encode::<u8>::encoded::<codec::Bin>(self),
            codec::Bin::PREFIX,
        )
    }
}

impl<const L: usize> Binary for Bytes<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Bin>(self),
            Encode::<u8>::encoded::<codec::Bin>(self),
            codec::Bin::PREFIX,
        )
    }
}

impl<const L: usize> Octal for Signed<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Oct>(self),
            Encode::<u8>::encoded::<codec::Oct>(self),
            codec::Oct::PREFIX,
        )
    }
}

impl<const L: usize> Octal for Unsigned<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Oct>(self),
            Encode::<u8>::encoded::<codec::Oct>(self),
            codec::Oct::PREFIX,
        )
    }
}

impl<const L: usize> Octal for Bytes<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Oct>(self),
            Encode::<u8>::encoded::<codec::Oct>(self),
            codec::Oct::PREFIX,
        )
    }
}

impl<const L: usize> LowerHex for Signed<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            codec::lowercase(Encode::<u8>::encoded::<codec::Hex>(self)),
            codec::lowercase(Encode::<u8>::encoded::<codec::Hex>(self)),
            codec::Hex::PREFIX,
        )
    }
}

impl<const L: usize> LowerHex for Unsigned<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            codec::lowercase(Encode::<u8>::encoded::<codec::Hex>(self)),
            codec::lowercase(Encode::<u8>::encoded::<codec::Hex>(self)),
            codec::Hex::PREFIX,
        )
    }
}

impl<const L: usize> LowerHex for Bytes<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            codec::lowercase(Encode::<u8>::encoded::<codec::Hex>(self)),
            codec::lowercase(Encode::<u8>::encoded::<codec::Hex>(self)),
            codec::Hex::PREFIX,
        )
    }
}

impl<const L: usize> UpperHex for Signed<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Hex>(self),
            Encode::<u8>::encoded::<codec::Hex>(self),
            codec::Hex::PREFIX,
        )
    }
}

impl<const L: usize> UpperHex for Unsigned<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Hex>(self),
            Encode::<u8>::encoded::<codec::Hex>(self),
            codec::Hex::PREFIX,
        )
    }
}

impl<const L: usize> UpperHex for Bytes<L> {
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        write(
            fmt,
            Encode::<u8>::encoded::<codec::Hex>(self),
            Encode::<u8>::encoded::<codec::Hex>(self),
            codec::Hex::PREFIX,
        )
    }
}

ndops::def! { @ndun <const L: usize> (value: &Signed<L>) -> Signed<L>, [
    ! uops::not(&value.0).with(Signed),

    - uops::neg(&value.0).default(Signed),
    - @checked uops::neg(&value.0).checked(Signed),
    - @strict uops::neg(&value.0).strict(Signed),
    - @wrapping uops::neg(&value.0).with(Signed),
    - @saturating uops::neg(&value.0).saturating(Signed, &Signed::MAX),
    - @overflowing uops::neg(&value.0).overflowing(Signed),

    posx uops::dirx(&value.0, Dir::POS).default(Signed),
    posx @checked uops::dirx(&value.0, Dir::POS).checked(Signed),
    posx @strict uops::dirx(&value.0, Dir::POS).strict(Signed),
    posx @wrapping uops::dirx(&value.0, Dir::POS).with(Signed),
    posx @saturating uops::dirx(&value.0, Dir::POS).saturating(Signed, &Signed::MAX),
    posx @overflowing uops::dirx(&value.0, Dir::POS).overflowing(Signed),

    negx uops::dirx(&value.0, Dir::NEG).default(Signed),
    negx @checked uops::dirx(&value.0, Dir::NEG).checked(Signed),
    negx @strict uops::dirx(&value.0, Dir::NEG).strict(Signed),
    negx @wrapping uops::dirx(&value.0, Dir::NEG).with(Signed),
    negx @saturating uops::dirx(&value.0, Dir::NEG).saturating(Signed, &Signed::MIN),
    negx @overflowing uops::dirx(&value.0, Dir::NEG).overflowing(Signed),
] }

ndops::def! { @ndun <const L: usize> (value: &Unsigned<L>) -> Unsigned<L>, [
    ! uops::not(&value.0).with(Unsigned),
] }

ndops::def! { @ndun <const L: usize> (value: &Bytes<L>) -> Bytes<L>, [
    ! uops::not(&value.0).with(Bytes),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, rhs: &Signed<L>) -> Signed<L>, [
    + uops::add(&lhs.0, &rhs.0).signed().default(Signed),
    - uops::sub(&lhs.0, &rhs.0).signed().default(Signed),
    * algo::mul(&lhs.0, &rhs.0).signed().default(Signed),
    / algo::div(&lhs.0, &rhs.0).signed().default(Signed),
    % algo::rem(&lhs.0, &rhs.0).signed().default(Signed),

    | uops::bitor(&lhs.0, &rhs.0).eval(),
    & uops::bitand(&lhs.0, &rhs.0).eval(),
    ^ uops::bitxor(&lhs.0, &rhs.0).eval(),

    + @checked uops::add(&lhs.0, &rhs.0).signed().checked(Signed),
    - @checked uops::sub(&lhs.0, &rhs.0).signed().checked(Signed),
    * @checked algo::mul(&lhs.0, &rhs.0).signed().checked(Signed),
    / @checked algo::div(&lhs.0, &rhs.0).signed().checked(Signed),
    % @checked algo::rem(&lhs.0, &rhs.0).signed().checked(Signed),

    + @strict uops::add(&lhs.0, &rhs.0).signed().strict(Signed),
    - @strict uops::sub(&lhs.0, &rhs.0).signed().strict(Signed),
    * @strict algo::mul(&lhs.0, &rhs.0).signed().strict(Signed),
    / @strict algo::div(&lhs.0, &rhs.0).signed().strict(Signed),
    % @strict algo::rem(&lhs.0, &rhs.0).signed().strict(Signed),

    + @wrapping uops::add(&lhs.0, &rhs.0).signed().with(Signed),
    - @wrapping uops::sub(&lhs.0, &rhs.0).signed().with(Signed),
    * @wrapping algo::mul(&lhs.0, &rhs.0).signed().with(Signed),
    / @wrapping algo::div(&lhs.0, &rhs.0).signed().with(Signed),
    % @wrapping algo::rem(&lhs.0, &rhs.0).signed().with(Signed),

    + @saturating uops::add(&lhs.0, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() == Dir::POS) as usize]),
    - @saturating uops::sub(&lhs.0, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() == Dir::POS) as usize]),
    * @saturating algo::mul(&lhs.0, &rhs.0).signed().saturating(Signed, [&Signed::MIN, &Signed::MAX][(lhs.dir() * rhs.dir() == Dir::POS) as usize]),
    / @saturating algo::div(&lhs.0, &rhs.0).signed().saturating(Signed, &Signed::MAX),
    % @saturating algo::rem(&lhs.0, &rhs.0).signed().saturating(Signed, &Signed::ZERO),

    + @overflowing uops::add(&lhs.0, &rhs.0).signed().overflowing(Signed),
    - @overflowing uops::sub(&lhs.0, &rhs.0).signed().overflowing(Signed),
    * @overflowing algo::mul(&lhs.0, &rhs.0).signed().overflowing(Signed),
    / @overflowing algo::div(&lhs.0, &rhs.0).signed().overflowing(Signed),
    % @overflowing algo::rem(&lhs.0, &rhs.0).signed().overflowing(Signed),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, rhs: usize) -> Signed<L> for Signed<L>, [
    << uops::shl(&lhs.0, rhs).signed().default(Signed),
    >> uops::shr(&lhs.0, rhs).signed().default(Signed),

    << @checked uops::shl(&lhs.0, rhs).signed().checked(Signed),
    >> @checked uops::shr(&lhs.0, rhs).signed().checked(Signed),

    << @strict uops::shl(&lhs.0, rhs).signed().strict(Signed),
    >> @strict uops::shr(&lhs.0, rhs).signed().strict(Signed),

    << @unbounded uops::shl(&lhs.0, rhs).signed().with(Signed),
    >> @unbounded uops::shr(&lhs.0, rhs).signed().with(Signed),

    << @overflowing (uops::shl(&lhs.0, rhs % (BITS * L)).signed().with(Signed), rhs >= BITS * L),
    >> @overflowing (uops::shr(&lhs.0, rhs % (BITS * L)).signed().with(Signed), rhs >= BITS * L),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, rhs: &Unsigned<L>) -> Unsigned<L>, [
    + uops::add(&lhs.0, &rhs.0).default(Unsigned),
    - uops::sub(&lhs.0, &rhs.0).default(Unsigned),
    * algo::mul(&lhs.0, &rhs.0).default(Unsigned),
    / algo::div(&lhs.0, &rhs.0).default(Unsigned),
    % algo::rem(&lhs.0, &rhs.0).default(Unsigned),

    | uops::bitor(&lhs.0, &rhs.0).eval(),
    & uops::bitand(&lhs.0, &rhs.0).eval(),
    ^ uops::bitxor(&lhs.0, &rhs.0).eval(),

    + @checked uops::add(&lhs.0, &rhs.0).checked(Unsigned),
    - @checked uops::sub(&lhs.0, &rhs.0).checked(Unsigned),
    * @checked algo::mul(&lhs.0, &rhs.0).checked(Unsigned),
    / @checked algo::div(&lhs.0, &rhs.0).checked(Unsigned),
    % @checked algo::rem(&lhs.0, &rhs.0).checked(Unsigned),

    + @strict uops::add(&lhs.0, &rhs.0).strict(Unsigned),
    - @strict uops::sub(&lhs.0, &rhs.0).strict(Unsigned),
    * @strict algo::mul(&lhs.0, &rhs.0).strict(Unsigned),
    / @strict algo::div(&lhs.0, &rhs.0).strict(Unsigned),
    % @strict algo::rem(&lhs.0, &rhs.0).strict(Unsigned),

    + @wrapping uops::add(&lhs.0, &rhs.0).with(Unsigned),
    - @wrapping uops::sub(&lhs.0, &rhs.0).with(Unsigned),
    * @wrapping algo::mul(&lhs.0, &rhs.0).with(Unsigned),
    / @wrapping algo::div(&lhs.0, &rhs.0).with(Unsigned),
    % @wrapping algo::rem(&lhs.0, &rhs.0).with(Unsigned),

    + @saturating uops::add(&lhs.0, &rhs.0).saturating(Unsigned, &Unsigned::MAX),
    - @saturating uops::sub(&lhs.0, &rhs.0).saturating(Unsigned, &Unsigned::MIN),
    * @saturating algo::mul(&lhs.0, &rhs.0).saturating(Unsigned, &Unsigned::MAX),
    / @saturating algo::div(&lhs.0, &rhs.0).saturating(Unsigned, &Unsigned::MAX),
    % @saturating algo::rem(&lhs.0, &rhs.0).saturating(Unsigned, &Unsigned::MIN),

    + @overflowing uops::add(&lhs.0, &rhs.0).overflowing(Unsigned),
    - @overflowing uops::sub(&lhs.0, &rhs.0).overflowing(Unsigned),
    * @overflowing algo::mul(&lhs.0, &rhs.0).overflowing(Unsigned),
    / @overflowing algo::div(&lhs.0, &rhs.0).overflowing(Unsigned),
    % @overflowing algo::rem(&lhs.0, &rhs.0).overflowing(Unsigned),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, rhs: usize) -> Unsigned<L> for Unsigned<L>, [
    << uops::shl(&lhs.0, rhs).default(Unsigned),
    >> uops::shr(&lhs.0, rhs).default(Unsigned),

    << @checked uops::shl(&lhs.0, rhs).checked(Unsigned),
    >> @checked uops::shr(&lhs.0, rhs).checked(Unsigned),

    << @strict uops::shl(&lhs.0, rhs).strict(Unsigned),
    >> @strict uops::shr(&lhs.0, rhs).strict(Unsigned),

    << @unbounded uops::shl(&lhs.0, rhs).with(Unsigned),
    >> @unbounded uops::shr(&lhs.0, rhs).with(Unsigned),

    << @overflowing (uops::shl(&lhs.0, rhs % (BITS * L)).with(Unsigned), rhs >= BITS * L),
    >> @overflowing (uops::shr(&lhs.0, rhs % (BITS * L)).with(Unsigned), rhs >= BITS * L),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, rhs: &Bytes<L>) -> Bytes<L>, [
    | uops::bitor(&lhs.0, &rhs.0).eval(),
    & uops::bitand(&lhs.0, &rhs.0).eval(),
    ^ uops::bitxor(&lhs.0, &rhs.0).eval(),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, rhs: usize) -> Bytes<L> for Bytes<L>, [
    << uops::shl(&lhs.0, rhs).default(Bytes),
    >> uops::shr(&lhs.0, rhs).default(Bytes),

    << @checked uops::shl(&lhs.0, rhs).checked(Bytes),
    >> @checked uops::shr(&lhs.0, rhs).checked(Bytes),

    << @strict uops::shl(&lhs.0, rhs).strict(Bytes),
    >> @strict uops::shr(&lhs.0, rhs).strict(Bytes),

    << @unbounded uops::shl(&lhs.0, rhs).with(Bytes),
    >> @unbounded uops::shr(&lhs.0, rhs).with(Bytes),

    << @overflowing (uops::shl(&lhs.0, rhs % (BITS * L)).with(Bytes), rhs >= BITS * L),
    >> @overflowing (uops::shr(&lhs.0, rhs % (BITS * L)).with(Bytes), rhs >= BITS * L),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, rhs: &Signed<L>), [
    += uops::add(&mut lhs.0, &rhs.0).signed().default_mut(),
    -= uops::sub(&mut lhs.0, &rhs.0).signed().default_mut(),
    *= algo::mul(&mut lhs.0, &rhs.0).signed().default_mut(),
    /= algo::div(&mut lhs.0, &rhs.0).signed().default_mut(),
    %= algo::rem(&mut lhs.0, &rhs.0).signed().default_mut(),

    |= uops::bitor(&mut lhs.0, &rhs.0).eval_mut(),
    &= uops::bitand(&mut lhs.0, &rhs.0).eval_mut(),
    ^= uops::bitxor(&mut lhs.0, &rhs.0).eval_mut(),

    += @strict uops::add(&mut lhs.0, &rhs.0).signed().strict_mut(),
    -= @strict uops::sub(&mut lhs.0, &rhs.0).signed().strict_mut(),
    *= @strict algo::mul(&mut lhs.0, &rhs.0).signed().strict_mut(),
    /= @strict algo::div(&mut lhs.0, &rhs.0).signed().strict_mut(),
    %= @strict algo::rem(&mut lhs.0, &rhs.0).signed().strict_mut(),

    += @wrapping uops::add(&mut lhs.0, &rhs.0).signed().eval_mut(),
    -= @wrapping uops::sub(&mut lhs.0, &rhs.0).signed().eval_mut(),
    *= @wrapping algo::mul(&mut lhs.0, &rhs.0).signed().eval_mut(),
    /= @wrapping algo::div(&mut lhs.0, &rhs.0).signed().eval_mut(),
    %= @wrapping algo::rem(&mut lhs.0, &rhs.0).signed().eval_mut(),

    += @saturating {
        let dir = lhs.dir();

        uops::add(&mut lhs.0, &rhs.0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
    },
    -= @saturating {
        let dir = lhs.dir();

        uops::sub(&mut lhs.0, &rhs.0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
    },
    *= @saturating {
        let dir = lhs.dir() * rhs.dir();

        algo::mul(&mut lhs.0, &rhs.0).signed().saturating_mut([&Signed::MIN.0, &Signed::MAX.0][(dir == Dir::POS) as usize])
    },
    /= @saturating algo::div(&mut lhs.0, &rhs.0).signed().saturating_mut(&Signed::MAX.0),
    %= @saturating algo::rem(&mut lhs.0, &rhs.0).signed().saturating_mut(&Signed::ZERO.0),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, rhs: usize) for Signed<L>, [
    <<= uops::shl(&mut lhs.0, rhs).signed().default_mut(),
    >>= uops::shr(&mut lhs.0, rhs).signed().default_mut(),

    <<= @strict uops::shl(&mut lhs.0, rhs).signed().strict_mut(),
    >>= @strict uops::shr(&mut lhs.0, rhs).signed().strict_mut(),

    <<= @unbounded uops::shl(&mut lhs.0, rhs).signed().eval_mut(),
    >>= @unbounded uops::shr(&mut lhs.0, rhs).signed().eval_mut(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: &Unsigned<L>), [
    += uops::add(&mut lhs.0, &rhs.0).default_mut(),
    -= uops::sub(&mut lhs.0, &rhs.0).default_mut(),
    *= algo::mul(&mut lhs.0, &rhs.0).default_mut(),
    /= algo::div(&mut lhs.0, &rhs.0).default_mut(),
    %= algo::rem(&mut lhs.0, &rhs.0).default_mut(),

    |= uops::bitor(&mut lhs.0, &rhs.0).eval_mut(),
    &= uops::bitand(&mut lhs.0, &rhs.0).eval_mut(),
    ^= uops::bitxor(&mut lhs.0, &rhs.0).eval_mut(),

    += @strict uops::add(&mut lhs.0, &rhs.0).strict_mut(),
    -= @strict uops::sub(&mut lhs.0, &rhs.0).strict_mut(),
    *= @strict algo::mul(&mut lhs.0, &rhs.0).strict_mut(),
    /= @strict algo::div(&mut lhs.0, &rhs.0).strict_mut(),
    %= @strict algo::rem(&mut lhs.0, &rhs.0).strict_mut(),

    += @wrapping uops::add(&mut lhs.0, &rhs.0).eval_mut(),
    -= @wrapping uops::sub(&mut lhs.0, &rhs.0).eval_mut(),
    *= @wrapping algo::mul(&mut lhs.0, &rhs.0).eval_mut(),
    /= @wrapping algo::div(&mut lhs.0, &rhs.0).eval_mut(),
    %= @wrapping algo::rem(&mut lhs.0, &rhs.0).eval_mut(),

    += @saturating uops::add(&mut lhs.0, &rhs.0).saturating_mut(&Unsigned::MAX.0),
    -= @saturating uops::sub(&mut lhs.0, &rhs.0).saturating_mut(&Unsigned::MIN.0),
    *= @saturating algo::mul(&mut lhs.0, &rhs.0).saturating_mut(&Unsigned::MAX.0),
    /= @saturating algo::div(&mut lhs.0, &rhs.0).saturating_mut(&Unsigned::MAX.0),
    %= @saturating algo::rem(&mut lhs.0, &rhs.0).saturating_mut(&Unsigned::MIN.0),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: usize) for Unsigned<L>, [
    <<= uops::shl(&mut lhs.0, rhs).default_mut(),
    >>= uops::shr(&mut lhs.0, rhs).default_mut(),

    <<= @strict uops::shl(&mut lhs.0, rhs).strict_mut(),
    >>= @strict uops::shr(&mut lhs.0, rhs).strict_mut(),

    <<= @unbounded uops::shl(&mut lhs.0, rhs).eval_mut(),
    >>= @unbounded uops::shr(&mut lhs.0, rhs).eval_mut(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, rhs: &Bytes<L>), [
    |= uops::bitor(&mut lhs.0, &rhs.0).eval_mut(),
    &= uops::bitand(&mut lhs.0, &rhs.0).eval_mut(),
    ^= uops::bitxor(&mut lhs.0, &rhs.0).eval_mut(),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, rhs: usize) for Bytes<L>, [
    <<= uops::shl(&mut lhs.0, rhs).default_mut(),
    >>= uops::shr(&mut lhs.0, rhs).default_mut(),

    <<= @strict uops::shl(&mut lhs.0, rhs).strict_mut(),
    >>= @strict uops::shr(&mut lhs.0, rhs).strict_mut(),

    <<= @unbounded uops::shl(&mut lhs.0, rhs).eval_mut(),
    >>= @unbounded uops::shr(&mut lhs.0, rhs).eval_mut(),
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
    const _CHECK: () = assert!(0 < L);

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
        uops::sign(&self.0)
    }

    /// Long number dir.
    #[inline]
    pub fn dir(&self) -> Dir {
        uops::dir(&self.0)
    }

    /// Creates signed with specified direction.
    #[inline]
    pub fn signed(&self, dir: Dir) -> Self {
        uops::dirx(&self.0, dir).with(Self)
    }

    /// Creates unsigned from raw `self.0`.
    #[inline]
    pub fn unsigned(self) -> Unsigned<L> {
        Unsigned(self.0)
    }
}

impl<const L: usize> Unsigned<L> {
    const _CHECK: () = assert!(0 < L);

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
        match self.0.eq(&[0; L]) {
            false => Sign::POS,
            true => Sign::ZERO,
        }
    }

    /// Creates signed with specified direction.
    #[inline]
    pub fn signed(&self, dir: Dir) -> Signed<L> {
        uops::dirx(&self.0, dir).with(Signed)
    }

    /// Creates unsigned from raw `self.0`.
    #[inline]
    pub fn unsigned(self) -> Self {
        Self(self.0)
    }
}

impl<const L: usize> Bytes<L> {
    const _CHECK: () = assert!(0 < L);

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

impl<const L: usize> ToDigits for Signed<L> {
    #[inline]
    fn to_digits<W: Word>(&self, ctx: ExpImpl<W>) -> impl ExactSizeIterator<Item = W> {
        Encoded::read(self, ctx.exp.as_usize())
    }
}

impl<const L: usize> ToDigits for Unsigned<L> {
    #[inline]
    fn to_digits<W: Word>(&self, ctx: ExpImpl<W>) -> impl ExactSizeIterator<Item = W> {
        Encoded::read(self, ctx.exp.as_usize())
    }
}

impl<const L: usize> IntoDigits for Signed<L> {
    #[inline]
    fn into_digits(self, ctx: RadixImpl<Single>) -> impl ExactSizeIterator<Item = Single> {
        let bits = ctx.radix.order();
        let len = self.0.iter().copied().length(0);

        DigitsIter {
            words: self,
            radix: ctx.radix,
            idx: 0,
            len: (len * BITS + bits - 1) / bits,
        }
    }
}

impl<const L: usize> IntoDigits for Unsigned<L> {
    #[inline]
    fn into_digits(self, ctx: RadixImpl<Single>) -> impl ExactSizeIterator<Item = Single> {
        let bits = ctx.radix.order();
        let len = self.0.iter().copied().length(0);

        DigitsIter {
            words: self,
            radix: ctx.radix,
            idx: 0,
            len: (len * BITS + bits - 1) / bits,
        }
    }
}

impl<const L: usize, W: Word> AsWordsRef<W> for Signed<L> {
    #[inline]
    fn as_words_ref(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }
}

impl<const L: usize, W: Word> AsWordsRef<W> for Unsigned<L> {
    #[inline]
    fn as_words_ref(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }
}

impl<const L: usize, W: Word> AsWordsRef<W> for Bytes<L> {
    #[inline]
    fn as_words_ref(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }
}

impl<const L: usize, W: Word> AsWordsMut<W> for Signed<L> {
    fn as_words_mut(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }
}

impl<const L: usize, W: Word> AsWordsMut<W> for Unsigned<L> {
    fn as_words_mut(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }
}

impl<const L: usize, W: Word> AsWordsMut<W> for Bytes<L> {
    fn as_words_mut(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }
}

impl<const L: usize> Rand for Signed<L> {}
impl<const L: usize> Rand for Unsigned<L> {}
impl<const L: usize> Rand for Bytes<L> {}

impl<const L: usize, W: Word> Encode<W> for Signed<L> {}
impl<const L: usize, W: Word> Encode<W> for Unsigned<L> {}
impl<const L: usize, W: Word> Encode<W> for Bytes<L> {}

impl<const L: usize, W: Word> Decode<W> for Signed<L> {}
impl<const L: usize, W: Word> Decode<W> for Unsigned<L> {}
impl<const L: usize, W: Word> Decode<W> for Bytes<L> {}

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

impl<const L: usize> Num for Signed<L> {}
impl<const L: usize> Num for Unsigned<L> {}

impl<const L: usize> NumExt for Signed<L> {
    type Signed = Signed<L>;
    type Unsigned = Unsigned<L>;

    #[inline]
    fn as_signed(&self) -> Self::Signed {
        Signed(self.0)
    }

    #[inline]
    fn as_unsigned(&self) -> Self::Unsigned {
        Unsigned(self.0)
    }
}

impl<const L: usize> NumExt for Unsigned<L> {
    type Signed = Signed<L>;
    type Unsigned = Unsigned<L>;

    #[inline]
    fn as_signed(&self) -> Self::Signed {
        Signed(self.0)
    }

    #[inline]
    fn as_unsigned(&self) -> Self::Unsigned {
        Unsigned(self.0)
    }
}

impl<const L: usize> NumSigned for Signed<L> {}
impl<const L: usize> NumUnsigned for Unsigned<L> {
    #[inline]
    fn order(&self) -> usize {
        let len = self.0.iter().copied().length(0);

        match len {
            0 => 0,
            l => (l - 1) * BITS + self.0[l - 1].order(),
        }
    }

    #[inline]
    fn log(&self) -> Self {
        let len = self.0.iter().copied().length(0);

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

impl<const L: usize> NumBinary for Signed<L> {
    const BITS: usize = (BITS * L);
    const BYTES: usize = (BYTES * L);
}

impl<const L: usize> NumBinary for Unsigned<L> {
    const BITS: usize = (BITS * L);
    const BYTES: usize = (BYTES * L);
}

impl<const L: usize> NumCt for Signed<L> {
    const SIGNED: MaskCt = MaskCt::MAX;
    const UNSIGNED: MaskCt = MaskCt::MIN;

    #[inline]
    fn with_mask_ct(&self, mask: MaskCt) -> Self {
        uops::words_ct(&self.0, mask).with(Self)
    }
}

impl<const L: usize> NumCt for Unsigned<L> {
    const SIGNED: MaskCt = MaskCt::MIN;
    const UNSIGNED: MaskCt = MaskCt::MAX;

    #[inline]
    fn with_mask_ct(&self, mask: MaskCt) -> Self {
        uops::words_ct(&self.0, mask).with(Self)
    }
}

impl<const L: usize> NumExtCt for Signed<L> {}
impl<const L: usize> NumExtCt for Unsigned<L> {}

impl<const L: usize> NumSignedCt for Signed<L> {
    #[inline]
    fn as_rel_ct(&self) -> RelCt {
        self.0[0] as RelCt
    }
}

impl<const L: usize> NumUnsignedCt for Unsigned<L> {
    #[inline]
    fn as_mask_ct(&self) -> MaskCt {
        self.0[0] as MaskCt
    }
}

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

impl<const L: usize> EqCt for Signed<L> {
    #[inline(never)]
    fn eq_ct(&self, other: &Self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), other.0.iter().copied())
    }
}

impl<const L: usize> EqCt for Unsigned<L> {
    #[inline(never)]
    fn eq_ct(&self, other: &Self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), other.0.iter().copied())
    }
}

impl<const L: usize> EqCt for Bytes<L> {
    #[inline(never)]
    fn eq_ct(&self, other: &Self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), other.0.iter().copied())
    }
}

impl<const L: usize> CmpCt for Signed<L> {
    #[inline(never)]
    fn cmp_ct(&self, other: &Self) -> RelCt {
        crate::rel_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ))
    }
}

impl<const L: usize> CmpCt for Unsigned<L> {
    #[inline(never)]
    fn cmp_ct(&self, other: &Self) -> RelCt {
        crate::rel_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> SignCt for Signed<L> {
    #[inline(never)]
    fn sign_ct(&self) -> RelCt {
        crate::rel_ct(uops::cmp_ct(
            self.0.iter().copied(),
            (0..L).map(|_| 0),
            uops::ext_ct(&self.0),
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> SignCt for Unsigned<L> {
    #[inline(never)]
    fn sign_ct(&self) -> RelCt {
        crate::rel_ct(uops::cmp_ct(
            self.0.iter().copied(),
            (0..L).map(|_| 0),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> IsZeroCt for Signed<L> {
    #[inline(never)]
    fn is_zero_ct(&self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), (0..L).map(|_| 0))
    }
}

impl<const L: usize> IsZeroCt for Unsigned<L> {
    #[inline(never)]
    fn is_zero_ct(&self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), (0..L).map(|_| 0))
    }
}

impl<const L: usize> IsOneCt for Signed<L> {
    #[inline(never)]
    fn is_one_ct(&self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), (0..L).map(|idx| [1, 0][(idx > 0) as usize]))
    }
}

impl<const L: usize> IsOneCt for Unsigned<L> {
    #[inline(never)]
    fn is_one_ct(&self) -> MaskCt {
        uops::eq_ct(self.0.iter().copied(), (0..L).map(|idx| [1, 0][(idx > 0) as usize]))
    }
}

impl<const L: usize> IsPosCt for Signed<L> {
    #[inline(never)]
    fn is_pos_ct(&self) -> MaskCt {
        crate::gt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            (0..L).map(|_| 0),
            uops::ext_ct(&self.0),
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> IsPosCt for Unsigned<L> {
    #[inline(never)]
    fn is_pos_ct(&self) -> MaskCt {
        crate::gt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            (0..L).map(|_| 0),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> IsNegCt for Signed<L> {
    #[inline(never)]
    fn is_neg_ct(&self) -> MaskCt {
        crate::lt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            (0..L).map(|_| 0),
            uops::ext_ct(&self.0),
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> IsNegCt for Unsigned<L> {
    #[inline(never)]
    fn is_neg_ct(&self) -> MaskCt {
        crate::lt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            (0..L).map(|_| 0),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> LtCt for Signed<L> {
    #[inline(never)]
    fn lt_ct(&self, other: &Self) -> MaskCt {
        crate::lt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ))
    }
}

impl<const L: usize> LtCt for Unsigned<L> {
    #[inline(never)]
    fn lt_ct(&self, other: &Self) -> MaskCt {
        crate::lt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> GtCt for Signed<L> {
    #[inline(never)]
    fn gt_ct(&self, other: &Self) -> MaskCt {
        crate::gt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ))
    }
}

impl<const L: usize> GtCt for Unsigned<L> {
    #[inline(never)]
    fn gt_ct(&self, other: &Self) -> MaskCt {
        crate::gt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> LeCt for Signed<L> {
    #[inline(never)]
    fn le_ct(&self, other: &Self) -> MaskCt {
        crate::le_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ))
    }
}

impl<const L: usize> LeCt for Unsigned<L> {
    #[inline(never)]
    fn le_ct(&self, other: &Self) -> MaskCt {
        crate::le_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> GeCt for Signed<L> {
    #[inline(never)]
    fn ge_ct(&self, other: &Self) -> MaskCt {
        crate::ge_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ))
    }
}

impl<const L: usize> GeCt for Unsigned<L> {
    #[inline(never)]
    fn ge_ct(&self, other: &Self) -> MaskCt {
        crate::ge_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ))
    }
}

impl<const L: usize> MinCt for Signed<L> {
    #[inline(never)]
    fn min_ct(&self, other: &Self) -> Self {
        let mask = crate::lt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ));

        let lhs = uops::words_ct(&self.0, mask).iter();
        let rhs = uops::words_ct(&other.0, !mask).iter();

        uops::bitor_iter(lhs, rhs).with(Self)
    }
}

impl<const L: usize> MinCt for Unsigned<L> {
    #[inline(never)]
    fn min_ct(&self, other: &Self) -> Self {
        let mask = crate::lt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ));

        let lhs = uops::words_ct(&self.0, mask).iter();
        let rhs = uops::words_ct(&other.0, !mask).iter();

        uops::bitor_iter(lhs, rhs).with(Self)
    }
}

impl<const L: usize> MaxCt for Signed<L> {
    #[inline(never)]
    fn max_ct(&self, other: &Self) -> Self {
        let mask = crate::gt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            uops::ext_ct(&self.0),
            uops::ext_ct(&other.0),
        ));

        let lhs = uops::words_ct(&self.0, mask).iter();
        let rhs = uops::words_ct(&other.0, !mask).iter();

        uops::bitor_iter(lhs, rhs).with(Self)
    }
}

impl<const L: usize> MaxCt for Unsigned<L> {
    #[inline(never)]
    fn max_ct(&self, other: &Self) -> Self {
        let mask = crate::gt_ct(uops::cmp_ct(
            self.0.iter().copied(),
            other.0.iter().copied(),
            MaskCt::MIN,
            MaskCt::MIN,
        ));

        let lhs = uops::words_ct(&self.0, mask).iter();
        let rhs = uops::words_ct(&other.0, !mask).iter();

        uops::bitor_iter(lhs, rhs).with(Self)
    }
}

impl<const L: usize> PosxCt for Signed<L> {
    #[inline(never)]
    fn posx_ct(&self) -> Self {
        uops::dirx(&self.0, Dir::POS).with(Self)
    }
}

impl<const L: usize> NegxCt for Signed<L> {
    #[inline(never)]
    fn negx_ct(&self) -> Self {
        uops::dirx(&self.0, Dir::NEG).with(Self)
    }
}

impl<const L: usize> SelectCt for Signed<L> {
    #[inline(never)]
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
        let lhs = uops::words_ct(&lhs.0, mask).iter();
        let rhs = uops::words_ct(&rhs.0, !mask).iter();

        uops::bitor_iter(lhs, rhs).with(Self)
    }
}

impl<const L: usize> SelectCt for Unsigned<L> {
    #[inline(never)]
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
        let lhs = uops::words_ct(&lhs.0, mask).iter();
        let rhs = uops::words_ct(&rhs.0, !mask).iter();

        uops::bitor_iter(lhs, rhs).with(Self)
    }
}

impl<const L: usize> PowCt for Signed<L> {}
impl<const L: usize> PowCt for Unsigned<L> {}

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

fn try_from_array<const L: usize, const N: usize, W: Word>(
    arr: &[W; N],
    default: Single,
) -> Result<[Single; L], InitError> {
    match (N * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_array(arr, default)),
        Ordering::Equal => Ok(from_array(arr, default)),
        Ordering::Greater => Err(InitError::InvalidLength),
    }
}

fn try_from_slice<const L: usize, W: Word>(slice: &[W]) -> Result<[Single; L], InitError> {
    match (slice.len() * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_slice(slice)),
        Ordering::Equal => Ok(from_slice(slice)),
        Ordering::Greater => Err(InitError::InvalidLength),
    }
}

fn from_array<const L: usize, const N: usize, W: Word>(arr: &[W; N], default: Single) -> [Single; L] {
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

#[cfg(test)]
mod tests {
    use std::{iter::repeat_n, ops::*, panic::RefUnwindSafe};

    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use super::*;

    use crate::{
        CmpCt, GeCt, LeCt, MaxCt, MinCt, Saturating, Strict, Unbounded, Wrapping,
        long::alias::{S32, S64, U32, U64},
    };

    fn ops_impl<
        Lhs: Zero + Num + Debug + RefUnwindSafe,
        Rhs: Zero + Num + Debug + RefUnwindSafe,
        LhsLong: Num
            + Debug
            + RefUnwindSafe
            + Ops<RhsLong, usize, Type = LhsLong>
            + OpsAssign<RhsLong, usize>
            + NdOpsChecked<LhsLong, RhsLong, usize, All = LhsLong>
            + NdOpsOverflowing<LhsLong, RhsLong, usize, All = LhsLong>,
        RhsLong: Num
            + Debug
            + RefUnwindSafe
            + Add<LhsLong, Output = LhsLong>
            + Sub<LhsLong, Output = LhsLong>
            + Mul<LhsLong, Output = LhsLong>
            + BitOr<LhsLong, Output = LhsLong>
            + BitAnd<LhsLong, Output = LhsLong>
            + BitXor<LhsLong, Output = LhsLong>,
        LhsAlt: Num
            + Debug
            + RefUnwindSafe
            + Ops<RhsAlt, usize, Type = LhsAlt>
            + OpsAssign<RhsAlt, usize>
            + NdOpsChecked<LhsAlt, RhsAlt, usize, All = LhsAlt>
            + NdOpsOverflowing<LhsAlt, RhsAlt, usize, All = LhsAlt>,
        RhsAlt: Num
            + Debug
            + RefUnwindSafe
            + Add<LhsAlt, Output = LhsAlt>
            + Sub<LhsAlt, Output = LhsAlt>
            + Mul<LhsAlt, Output = LhsAlt>
            + BitOr<LhsAlt, Output = LhsAlt>
            + BitAnd<LhsAlt, Output = LhsAlt>
            + BitXor<LhsAlt, Output = LhsAlt>,
    >(
        lhs_iter: impl Iterator<Item = Lhs> + Clone,
        rhs_iter: impl Iterator<Item = Rhs> + Clone,
        lhs_long_fn: impl Fn(Lhs) -> LhsLong,
        rhs_long_fn: impl Fn(Rhs) -> RhsLong,
        lhs_alt_fn: impl Fn(Lhs) -> LhsAlt,
        rhs_alt_fn: impl Fn(Rhs) -> RhsAlt,
        func: impl Copy + Fn(LhsAlt) -> LhsLong + RefUnwindSafe,
    ) {
        ndassert::check! { @eq (
            lhs in lhs_iter.clone(),
            rhs in rhs_iter.clone(),
            lhs_long as lhs_long_fn(lhs),
            rhs_long as rhs_long_fn(rhs),
            lhs_alt as lhs_alt_fn(lhs),
            rhs_alt as rhs_alt_fn(rhs),
        ) [
            ndassert::catch!(lhs_long + rhs_long, func(lhs_alt + rhs_alt)),
            ndassert::catch!(lhs_long - rhs_long, func(lhs_alt - rhs_alt)),
            ndassert::catch!(lhs_long * rhs_long, func(lhs_alt * rhs_alt)),

            ndassert::catch!(rhs_long + lhs_long, func(rhs_alt + lhs_alt)),
            ndassert::catch!(rhs_long - lhs_long, func(rhs_alt - lhs_alt)),
            ndassert::catch!(rhs_long * lhs_long, func(rhs_alt * lhs_alt)),

            ndassert::catch!((rhs != Rhs::ZERO).then(|| lhs_long / rhs_long), (rhs != Rhs::ZERO).then(|| func(lhs_alt / rhs_alt))),
            ndassert::catch!((rhs != Rhs::ZERO).then(|| lhs_long % rhs_long), (rhs != Rhs::ZERO).then(|| func(lhs_alt % rhs_alt))),

            ndassert::catch!({ let mut val = lhs_long; val += rhs_long; val }, func(lhs_alt + rhs_alt)),
            ndassert::catch!({ let mut val = lhs_long; val -= rhs_long; val }, func(lhs_alt - rhs_alt)),
            ndassert::catch!({ let mut val = lhs_long; val *= rhs_long; val }, func(lhs_alt * rhs_alt)),

            ndassert::catch!({ let mut val = lhs_long; (rhs != Rhs::ZERO).then(|| { val /= rhs_long; val }) }, (rhs != Rhs::ZERO).then(|| func(lhs_alt / rhs_alt))),
            ndassert::catch!({ let mut val = lhs_long; (rhs != Rhs::ZERO).then(|| { val %= rhs_long; val }) }, (rhs != Rhs::ZERO).then(|| func(lhs_alt % rhs_alt))),

            (LhsLong::nd_add_checked(&lhs_long, &rhs_long), LhsAlt::nd_add_checked(&lhs_alt, &rhs_alt).map(func)),
            (LhsLong::nd_sub_checked(&lhs_long, &rhs_long), LhsAlt::nd_sub_checked(&lhs_alt, &rhs_alt).map(func)),
            (LhsLong::nd_mul_checked(&lhs_long, &rhs_long), LhsAlt::nd_mul_checked(&lhs_alt, &rhs_alt).map(func)),
            (LhsLong::nd_div_checked(&lhs_long, &rhs_long), LhsAlt::nd_div_checked(&lhs_alt, &rhs_alt).map(func)),
            (LhsLong::nd_rem_checked(&lhs_long, &rhs_long), LhsAlt::nd_rem_checked(&lhs_alt, &rhs_alt).map(func)),

            (LhsLong::nd_add_overflowing(&lhs_long, &rhs_long), { let (val, flag) = LhsAlt::nd_add_overflowing(&lhs_alt, &rhs_alt); (func(val), flag) }),
            (LhsLong::nd_sub_overflowing(&lhs_long, &rhs_long), { let (val, flag) = LhsAlt::nd_sub_overflowing(&lhs_alt, &rhs_alt); (func(val), flag) }),
            (LhsLong::nd_mul_overflowing(&lhs_long, &rhs_long), { let (val, flag) = LhsAlt::nd_mul_overflowing(&lhs_alt, &rhs_alt); (func(val), flag) }),

            ((rhs != Rhs::ZERO).then(|| LhsLong::nd_div_overflowing(&lhs_long, &rhs_long)), (rhs != Rhs::ZERO).then(|| { let (val, flag) = LhsAlt::nd_div_overflowing(&lhs_alt, &rhs_alt); (func(val), flag) })),
            ((rhs != Rhs::ZERO).then(|| LhsLong::nd_rem_overflowing(&lhs_long, &rhs_long)), (rhs != Rhs::ZERO).then(|| { let (val, flag) = LhsAlt::nd_rem_overflowing(&lhs_alt, &rhs_alt); (func(val), flag) })),

            (lhs_long | rhs_long, func(lhs_alt | rhs_alt)),
            (lhs_long & rhs_long, func(lhs_alt & rhs_alt)),
            (lhs_long ^ rhs_long, func(lhs_alt ^ rhs_alt)),

            (rhs_long | lhs_long, func(rhs_alt | lhs_alt)),
            (rhs_long & lhs_long, func(rhs_alt & lhs_alt)),
            (rhs_long ^ lhs_long, func(rhs_alt ^ lhs_alt)),

            ({ let mut val = lhs_long; val |= rhs_long; val }, func(lhs_alt | rhs_alt)),
            ({ let mut val = lhs_long; val &= rhs_long; val }, func(lhs_alt & rhs_alt)),
            ({ let mut val = lhs_long; val ^= rhs_long; val }, func(lhs_alt ^ rhs_alt)),
        ] }
    }

    fn ops_shift_impl<
        Value: Num + Debug + RefUnwindSafe,
        ValueLong: Num
            + Debug
            + RefUnwindSafe
            + Ops<ValueLong, usize, Type = ValueLong>
            + OpsAssign<ValueLong, usize>
            + NdOpsChecked<ValueLong, ValueLong, usize, All = ValueLong>
            + NdOpsOverflowing<ValueLong, ValueLong, usize, All = ValueLong>,
        ValueAlt: Num
            + Debug
            + RefUnwindSafe
            + Ops<ValueAlt, usize, Type = ValueAlt>
            + OpsAssign<ValueAlt, usize>
            + NdOpsChecked<ValueAlt, ValueAlt, usize, All = ValueAlt>
            + NdOpsOverflowing<ValueAlt, ValueAlt, usize, All = ValueAlt>,
    >(
        value_iter: impl Iterator<Item = Value> + Clone,
        shift_iter: impl Iterator<Item = usize> + Clone,
        long_fn: impl Fn(Value) -> ValueLong,
        alt_fn: impl Fn(Value) -> ValueAlt,
        func: impl Copy + Fn(ValueAlt) -> ValueLong + RefUnwindSafe,
    ) {
        ndassert::check! { @eq (
            value in value_iter.clone(),
            shift in shift_iter.clone(),
            long as long_fn(value),
            alt as alt_fn(value),
        ) [
            ndassert::catch!(long << shift, func(alt << shift)),
            ndassert::catch!(long >> shift, func(alt >> shift)),

            ndassert::catch!({ let mut val = long; val <<= shift; val }, func(alt << shift)),
            ndassert::catch!({ let mut val = long; val >>= shift; val }, func(alt >> shift)),

            (ValueLong::nd_shl_checked(&long, shift), ValueAlt::nd_shl_checked(&alt, shift).map(func)),
            (ValueLong::nd_shr_checked(&long, shift), ValueAlt::nd_shr_checked(&alt, shift).map(func)),

            (ValueLong::nd_shl_overflowing(&long, shift), { let (val, flag) = ValueAlt::nd_shl_overflowing(&alt, shift); (func(val), flag) }),
            (ValueLong::nd_shr_overflowing(&long, shift), { let (val, flag) = ValueAlt::nd_shr_overflowing(&alt, shift); (func(val), flag) }),
        ] }
    }

    fn ops_unary_impl<
        Value: Num + Debug + RefUnwindSafe,
        ValueLong: Num
            + Debug
            + RefUnwindSafe
            + Not<Output = ValueLong>
            + Neg<Output = ValueLong>
            + NdPosx<Type = ValueLong>
            + NdNegx<Type = ValueLong>,
        ValueAlt: Num
            + Debug
            + RefUnwindSafe
            + Not<Output = ValueAlt>
            + Neg<Output = ValueAlt>
            + NdPosx<Type = ValueAlt>
            + NdNegx<Type = ValueAlt>,
    >(
        value_iter: impl Iterator<Item = Value> + Clone,
        long_fn: impl Fn(Value) -> ValueLong,
        alt_fn: impl Fn(Value) -> ValueAlt,
        func: impl Copy + Fn(ValueAlt) -> ValueLong + RefUnwindSafe,
    ) {
        ndassert::check! { @eq (
            value in value_iter.clone(),
            long as long_fn(value),
            alt as alt_fn(value),
        ) [
            (!long, func(!alt)),

            ndassert::catch!(-long, func(-alt)),
            ndassert::catch!(ValueLong::nd_posx(&long), func(ValueAlt::nd_posx(&alt))),
            ndassert::catch!(ValueLong::nd_negx(&long), func(ValueAlt::nd_negx(&alt))),
        ] }
    }

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
            (S64::nd_from(&(val as u64).to_le_bytes(), ()), S64 { 0: (val as u64 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as u64).to_le_bytes(), ()), U64 { 0: (val as u64 as u64).to_le_bytes() }),
            (S64::nd_from(&(val as u32).to_le_bytes(), ()), S64 { 0: (val as u32 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as u32).to_le_bytes(), ()), U64 { 0: (val as u32 as u64).to_le_bytes() }),
            (S64::nd_from(&(val as u16).to_le_bytes(), ()), S64 { 0: (val as u16 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as u16).to_le_bytes(), ()), U64 { 0: (val as u16 as u64).to_le_bytes() }),
            (S64::nd_from(&(val as  u8).to_le_bytes(), ()), S64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (U64::nd_from(&(val as  u8).to_le_bytes(), ()), U64 { 0: (val as  u8 as u64).to_le_bytes() }),

            (S32::nd_from(&(val as u64).to_le_bytes(), ()), S32 { 0: (val as u64 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as u64).to_le_bytes(), ()), U32 { 0: (val as u64 as u32).to_le_bytes() }),
            (S32::nd_from(&(val as u32).to_le_bytes(), ()), S32 { 0: (val as u32 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as u32).to_le_bytes(), ()), U32 { 0: (val as u32 as u32).to_le_bytes() }),
            (S32::nd_from(&(val as u16).to_le_bytes(), ()), S32 { 0: (val as u16 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as u16).to_le_bytes(), ()), U32 { 0: (val as u16 as u32).to_le_bytes() }),
            (S32::nd_from(&(val as  u8).to_le_bytes(), ()), S32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (U32::nd_from(&(val as  u8).to_le_bytes(), ()), U32 { 0: (val as  u8 as u32).to_le_bytes() }),

            (S64::nd_try_from(&(val as u64).to_le_bytes(), ()), Ok(S64 { 0: (val as u64 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as u64).to_le_bytes(), ()), Ok(U64 { 0: (val as u64 as u64).to_le_bytes() })),
            (S64::nd_try_from(&(val as u32).to_le_bytes(), ()), Ok(S64 { 0: (val as u32 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as u32).to_le_bytes(), ()), Ok(U64 { 0: (val as u32 as u64).to_le_bytes() })),
            (S64::nd_try_from(&(val as u16).to_le_bytes(), ()), Ok(S64 { 0: (val as u16 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as u16).to_le_bytes(), ()), Ok(U64 { 0: (val as u16 as u64).to_le_bytes() })),
            (S64::nd_try_from(&(val as  u8).to_le_bytes(), ()), Ok(S64 { 0: (val as  u8 as u64).to_le_bytes() })),
            (U64::nd_try_from(&(val as  u8).to_le_bytes(), ()), Ok(U64 { 0: (val as  u8 as u64).to_le_bytes() })),

            (S32::nd_try_from(&(val as u64).to_le_bytes(), ()), Err(InitError::InvalidLength)),
            (U32::nd_try_from(&(val as u64).to_le_bytes(), ()), Err(InitError::InvalidLength)),
            (S32::nd_try_from(&(val as u32).to_le_bytes(), ()), Ok(S32 { 0: (val as u32 as u32).to_le_bytes() })),
            (U32::nd_try_from(&(val as u32).to_le_bytes(), ()), Ok(U32 { 0: (val as u32 as u32).to_le_bytes() })),
            (S32::nd_try_from(&(val as u16).to_le_bytes(), ()), Ok(S32 { 0: (val as u16 as u32).to_le_bytes() })),
            (U32::nd_try_from(&(val as u16).to_le_bytes(), ()), Ok(U32 { 0: (val as u16 as u32).to_le_bytes() })),
            (S32::nd_try_from(&(val as  u8).to_le_bytes(), ()), Ok(S32 { 0: (val as  u8 as u32).to_le_bytes() })),
            (U32::nd_try_from(&(val as  u8).to_le_bytes(), ()), Ok(U32 { 0: (val as  u8 as u32).to_le_bytes() })),
        ] }
    }

    #[test]
    fn from_slice() {
        #![allow(clippy::unnecessary_cast)]

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
            (S64::nd_from(&val.to_le_bytes()[..8], ()), S64 { 0: (val as u64 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..8], ()), U64 { 0: (val as u64 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..4], ()), S64 { 0: (val as u32 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..4], ()), U64 { 0: (val as u32 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..2], ()), S64 { 0: (val as u16 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..2], ()), U64 { 0: (val as u16 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..1], ()), S64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..1], ()), U64 { 0: (val as  u8 as u64).to_le_bytes() }),
            (S64::nd_from(&val.to_le_bytes()[..0], ()), S64 { 0:   (0 as  u8 as u64).to_le_bytes() }),
            (U64::nd_from(&val.to_le_bytes()[..0], ()), U64 { 0:   (0 as  u8 as u64).to_le_bytes() }),

            (S32::nd_from(&val.to_le_bytes()[..8], ()), S32 { 0: (val as u64 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..8], ()), U32 { 0: (val as u64 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..4], ()), S32 { 0: (val as u32 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..4], ()), U32 { 0: (val as u32 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..2], ()), S32 { 0: (val as u16 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..2], ()), U32 { 0: (val as u16 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..1], ()), S32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..1], ()), U32 { 0: (val as  u8 as u32).to_le_bytes() }),
            (S32::nd_from(&val.to_le_bytes()[..0], ()), S32 { 0:   (0 as  u8 as u32).to_le_bytes() }),
            (U32::nd_from(&val.to_le_bytes()[..0], ()), U32 { 0:   (0 as  u8 as u32).to_le_bytes() }),

            (S64::nd_try_from(&val.to_le_bytes()[..8], ()), Ok(S64 { 0: (val as u64 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..8], ()), Ok(U64 { 0: (val as u64 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..4], ()), Ok(S64 { 0: (val as u32 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..4], ()), Ok(U64 { 0: (val as u32 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..2], ()), Ok(S64 { 0: (val as u16 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..2], ()), Ok(U64 { 0: (val as u16 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..1], ()), Ok(S64 { 0: (val as  u8 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..1], ()), Ok(U64 { 0: (val as  u8 as u64).to_le_bytes() })),
            (S64::nd_try_from(&val.to_le_bytes()[..0], ()), Ok(S64 { 0:   (0 as  u8 as u64).to_le_bytes() })),
            (U64::nd_try_from(&val.to_le_bytes()[..0], ()), Ok(U64 { 0:   (0 as  u8 as u64).to_le_bytes() })),

            (S32::nd_try_from(&val.to_le_bytes()[..8], ()), Err(InitError::InvalidLength)),
            (U32::nd_try_from(&val.to_le_bytes()[..8], ()), Err(InitError::InvalidLength)),
            (S32::nd_try_from(&val.to_le_bytes()[..4], ()), Ok(S32 { 0: (val as u32 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..4], ()), Ok(U32 { 0: (val as u32 as u32).to_le_bytes() })),
            (S32::nd_try_from(&val.to_le_bytes()[..2], ()), Ok(S32 { 0: (val as u16 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..2], ()), Ok(U32 { 0: (val as u16 as u32).to_le_bytes() })),
            (S32::nd_try_from(&val.to_le_bytes()[..1], ()), Ok(S32 { 0: (val as  u8 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..1], ()), Ok(U32 { 0: (val as  u8 as u32).to_le_bytes() })),
            (S32::nd_try_from(&val.to_le_bytes()[..0], ()), Ok(S32 { 0:   (0 as  u8 as u32).to_le_bytes() })),
            (U32::nd_try_from(&val.to_le_bytes()[..0], ()), Ok(U32 { 0:   (0 as  u8 as u32).to_le_bytes() })),
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
                let iter = digits.iter().copied();

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                let lhs = <$long>::nd_try_from(iter, RadixImpl { radix });
                let rhs = <$long>::nd_from(&bytes, ());

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
                let iter = digits.iter().copied();

                let res = <$long>::nd_try_from(iter, ExpImpl { exp })
                    .map(|long| long.to_digits(ExpImpl { exp }).collect_with([0; BYTES]));

                (res, Ok(digits))
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
                let iter = digits.iter().copied();

                let res = <$long>::nd_try_from(iter, RadixImpl { radix })
                    .map(|long| long.into_digits(RadixImpl { radix }).collect_with([0; BYTES]));

                (res, Ok(digits))
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
        ndassert::check! { @eq (val in ndassert::range!(i64, 48)) [
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

        ndassert::check! { @eq (val in ndassert::range!(u64, 48)) [
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
        ndassert::check! { @eq (
            val in ndassert::range!(i64, 48),
            pos as S64::from(val),
            neg as S64::from(val.wrapping_neg()),
        ) [
            (format!("{:}",   pos), format!("{:}",   val)),
            (format!("{:b}",  pos), format!("{:b}",  val)),
            (format!("{:o}",  pos), format!("{:o}",  val)),
            (format!("{:x}",  pos), format!("{:x}",  val)),
            (format!("{:X}",  pos), format!("{:X}",  val)),
            (format!("{:#}",  pos), format!("{:#}",  val)),
            (format!("{:#b}", pos), format!("{:#b}", val)),
            (format!("{:#o}", pos), format!("{:#o}", val)),
            (format!("{:#x}", pos), format!("{:#x}", val)),
            (format!("{:#X}", pos), format!("{:#X}", val)),

            (format!("{:}",   neg), format!("{:}",   val.wrapping_neg())),
            (format!("{:b}",  neg), format!("{:b}",  val.wrapping_neg())),
            (format!("{:o}",  neg), format!("{:o}",  val.wrapping_neg())),
            (format!("{:x}",  neg), format!("{:x}",  val.wrapping_neg())),
            (format!("{:X}",  neg), format!("{:X}",  val.wrapping_neg())),
            (format!("{:#}",  neg), format!("{:#}",  val.wrapping_neg())),
            (format!("{:#b}", neg), format!("{:#b}", val.wrapping_neg())),
            (format!("{:#o}", neg), format!("{:#o}", val.wrapping_neg())),
            (format!("{:#x}", neg), format!("{:#x}", val.wrapping_neg())),
            (format!("{:#X}", neg), format!("{:#X}", val.wrapping_neg())),
        ] }

        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48),
            long as U64::from(val),
        ) [
            (format!("{:}",   long), format!("{:}",   val)),
            (format!("{:b}",  long), format!("{:b}",  val)),
            (format!("{:o}",  long), format!("{:o}",  val)),
            (format!("{:x}",  long), format!("{:x}",  val)),
            (format!("{:X}",  long), format!("{:X}",  val)),
            (format!("{:#}",  long), format!("{:#}",  val)),
            (format!("{:#b}", long), format!("{:#b}", val)),
            (format!("{:#o}", long), format!("{:#o}", val)),
            (format!("{:#x}", long), format!("{:#x}", val)),
            (format!("{:#X}", long), format!("{:#X}", val)),
        ] }
    }

    #[test]
    fn cmp() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
            lhs_long as S64::from(lhs),
            rhs_long as S64::from(rhs),
        ) [
            (lhs_long.eq (&rhs_long), lhs.eq (&rhs)),
            (lhs_long.cmp(&rhs_long), lhs.cmp(&rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1),
            lhs_long as U64::from(lhs),
            rhs_long as U64::from(rhs),
        ) [
            (lhs_long.eq (&rhs_long), lhs.eq (&rhs)),
            (lhs_long.cmp(&rhs_long), lhs.cmp(&rhs)),
        ] }
    }

    #[test]
    fn cmp_ct() {
        #![allow(clippy::absurd_extreme_comparisons)]
        #![allow(unused_comparisons)]

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
            lhs_long as S64::from(lhs),
            rhs_long as S64::from(rhs),
        ) [
            (lhs_long.eq_ct(&rhs_long),  MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs_long.cmp_ct(&rhs_long), lhs.cmp(&rhs) as RelCt),
            (lhs_long.sign_ct(),         lhs.cmp(&0)   as RelCt),

            (lhs_long.is_zero_ct(),      MaskCt::MAX * (lhs == 0)   as MaskCt),
            (lhs_long.is_one_ct(),       MaskCt::MAX * (lhs == 1)   as MaskCt),
            (lhs_long.is_pos_ct(),       MaskCt::MAX * (lhs >  0)   as MaskCt),
            (lhs_long.is_neg_ct(),       MaskCt::MAX * (lhs <  0)   as MaskCt),
            (lhs_long.lt_ct(&rhs_long),  MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs_long.gt_ct(&rhs_long),  MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs_long.le_ct(&rhs_long),  MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs_long.ge_ct(&rhs_long),  MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs_long.min_ct(&rhs_long), S64::from(lhs.min(rhs))),
            (lhs_long.max_ct(&rhs_long), S64::from(lhs.max(rhs))),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1),
            lhs_long as U64::from(lhs),
            rhs_long as U64::from(rhs),
        ) [
            (lhs_long.eq_ct(&rhs_long),  MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs_long.cmp_ct(&rhs_long), lhs.cmp(&rhs) as RelCt),
            (lhs_long.sign_ct(),         lhs.cmp(&0)   as RelCt),

            (lhs_long.is_zero_ct(),      MaskCt::MAX * (lhs == 0)   as MaskCt),
            (lhs_long.is_one_ct(),       MaskCt::MAX * (lhs == 1)   as MaskCt),
            (lhs_long.is_pos_ct(),       MaskCt::MAX * (lhs >  0)   as MaskCt),
            (lhs_long.is_neg_ct(),       MaskCt::MAX * (lhs <  0)   as MaskCt),
            (lhs_long.lt_ct(&rhs_long),  MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs_long.gt_ct(&rhs_long),  MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs_long.le_ct(&rhs_long),  MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs_long.ge_ct(&rhs_long),  MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs_long.min_ct(&rhs_long), U64::from(lhs.min(rhs))),
            (lhs_long.max_ct(&rhs_long), U64::from(lhs.max(rhs))),
        ] }
    }

    #[test]
    fn ops_signed() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| S64::from(val),
            |val: i64| S64::from(val),
            |val: i64| val,
            |val: i64| val,
            |val: i64| S64::from(val),
        );

        ops_shift_impl(
            ndassert::range!(i64, 52),
            0..96,
            |val: i64| S64::from(val),
            |val: i64| val,
            |val: i64| S64::from(val),
        );

        ops_unary_impl(
            ndassert::range!(i64, 52),
            |val: i64| S64::from(val),
            |val: i64| val,
            |val: i64| S64::from(val),
        );
    }

    #[test]
    fn ops_unsigned() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| U64::from(val),
            |val: u64| U64::from(val),
            |val: u64| val,
            |val: u64| val,
            |val: u64| U64::from(val),
        );

        ops_shift_impl(
            ndassert::range!(u64, 52),
            0..96,
            |val: u64| U64::from(val),
            |val: u64| val,
            |val: u64| U64::from(val),
        );
    }

    #[test]
    fn ops_signed_primitive() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| S64::from(val),
            |val: i64| val,
            |val: i64| val,
            |val: i64| val,
            |val: i64| S64::from(val),
        );
    }

    #[test]
    fn ops_unsigned_primitive() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| U64::from(val),
            |val: u64| val,
            |val: u64| val,
            |val: u64| val,
            |val: u64| U64::from(val),
        );
    }

    #[test]
    fn ops_signed_primitive_native() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            i8::MIN..i8::MAX,
            |val: i64| S64::from(val),
            |val: i8| val,
            |val: i64| val,
            |val: i8| val as i64,
            |val: i64| S64::from(val),
        );
    }

    #[test]
    fn ops_unsigned_primitive_native() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            u8::MIN..u8::MAX,
            |val: u64| U64::from(val),
            |val: u8| val,
            |val: u64| val,
            |val: u8| val as u64,
            |val: u64| U64::from(val),
        );
    }

    #[test]
    fn ops_signed_strict() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Strict(S64::from(val)),
            |val: i64| Strict(S64::from(val)),
            |val: i64| Strict(val),
            |val: i64| Strict(val),
            |val: Strict<i64>| Strict(S64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(i64, 52),
            0..96,
            |val: i64| Strict(S64::from(val)),
            |val: i64| Strict(val),
            |val: Strict<i64>| Strict(S64::from(val.0)),
        );

        ops_unary_impl(
            ndassert::range!(i64, 52),
            |val: i64| Strict(S64::from(val)),
            |val: i64| Strict(val),
            |val: Strict<i64>| Strict(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_strict() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Strict(U64::from(val)),
            |val: u64| Strict(U64::from(val)),
            |val: u64| Strict(val),
            |val: u64| Strict(val),
            |val: Strict<u64>| Strict(U64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(u64, 52),
            0..96,
            |val: u64| Strict(U64::from(val)),
            |val: u64| Strict(val),
            |val: Strict<u64>| Strict(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_strict() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Strict(S64::from(val)),
            |val: i64| Strict(val),
            |val: i64| Strict(val),
            |val: i64| Strict(val),
            |val: Strict<i64>| Strict(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_strict() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Strict(U64::from(val)),
            |val: u64| Strict(val),
            |val: u64| Strict(val),
            |val: u64| Strict(val),
            |val: Strict<u64>| Strict(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_native_strict() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            i8::MIN..i8::MAX,
            |val: i64| Strict(S64::from(val)),
            |val: i8| Strict(val),
            |val: i64| Strict(val),
            |val: i8| Strict(val as i64),
            |val: Strict<i64>| Strict(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_native_strict() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            u8::MIN..u8::MAX,
            |val: u64| Strict(U64::from(val)),
            |val: u8| Strict(val),
            |val: u64| Strict(val),
            |val: u8| Strict(val as u64),
            |val: Strict<u64>| Strict(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_wrapping() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Wrapping(S64::from(val)),
            |val: i64| Wrapping(S64::from(val)),
            |val: i64| Wrapping(val),
            |val: i64| Wrapping(val),
            |val: Wrapping<i64>| Wrapping(S64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(i64, 52),
            0..96,
            |val: i64| Wrapping(S64::from(val)),
            |val: i64| Wrapping(val),
            |val: Wrapping<i64>| Wrapping(S64::from(val.0)),
        );

        ops_unary_impl(
            ndassert::range!(i64, 52),
            |val: i64| Wrapping(S64::from(val)),
            |val: i64| Wrapping(val),
            |val: Wrapping<i64>| Wrapping(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_wrapping() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Wrapping(U64::from(val)),
            |val: u64| Wrapping(U64::from(val)),
            |val: u64| Wrapping(val),
            |val: u64| Wrapping(val),
            |val: Wrapping<u64>| Wrapping(U64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(u64, 52),
            0..96,
            |val: u64| Wrapping(U64::from(val)),
            |val: u64| Wrapping(val),
            |val: Wrapping<u64>| Wrapping(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_wrapping() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Wrapping(S64::from(val)),
            |val: i64| Wrapping(val),
            |val: i64| Wrapping(val),
            |val: i64| Wrapping(val),
            |val: Wrapping<i64>| Wrapping(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_wrapping() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Wrapping(U64::from(val)),
            |val: u64| Wrapping(val),
            |val: u64| Wrapping(val),
            |val: u64| Wrapping(val),
            |val: Wrapping<u64>| Wrapping(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_native_wrapping() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            i8::MIN..i8::MAX,
            |val: i64| Wrapping(S64::from(val)),
            |val: i8| Wrapping(val),
            |val: i64| Wrapping(val),
            |val: i8| Wrapping(val as i64),
            |val: Wrapping<i64>| Wrapping(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_native_wrapping() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            u8::MIN..u8::MAX,
            |val: u64| Wrapping(U64::from(val)),
            |val: u8| Wrapping(val),
            |val: u64| Wrapping(val),
            |val: u8| Wrapping(val as u64),
            |val: Wrapping<u64>| Wrapping(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_saturating() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Saturating(S64::from(val)),
            |val: i64| Saturating(S64::from(val)),
            |val: i64| Saturating(val),
            |val: i64| Saturating(val),
            |val: Saturating<i64>| Saturating(S64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(i64, 52),
            0..96,
            |val: i64| Saturating(S64::from(val)),
            |val: i64| Saturating(val),
            |val: Saturating<i64>| Saturating(S64::from(val.0)),
        );

        ops_unary_impl(
            ndassert::range!(i64, 52),
            |val: i64| Saturating(S64::from(val)),
            |val: i64| Saturating(val),
            |val: Saturating<i64>| Saturating(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_saturating() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Saturating(U64::from(val)),
            |val: u64| Saturating(U64::from(val)),
            |val: u64| Saturating(val),
            |val: u64| Saturating(val),
            |val: Saturating<u64>| Saturating(U64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(u64, 52),
            0..96,
            |val: u64| Saturating(U64::from(val)),
            |val: u64| Saturating(val),
            |val: Saturating<u64>| Saturating(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_saturating() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Saturating(S64::from(val)),
            |val: i64| Saturating(val),
            |val: i64| Saturating(val),
            |val: i64| Saturating(val),
            |val: Saturating<i64>| Saturating(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_saturating() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Saturating(U64::from(val)),
            |val: u64| Saturating(val),
            |val: u64| Saturating(val),
            |val: u64| Saturating(val),
            |val: Saturating<u64>| Saturating(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_native_saturating() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            i8::MIN..i8::MAX,
            |val: i64| Saturating(S64::from(val)),
            |val: i8| Saturating(val),
            |val: i64| Saturating(val),
            |val: i8| Saturating(val as i64),
            |val: Saturating<i64>| Saturating(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_native_saturating() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            u8::MIN..u8::MAX,
            |val: u64| Saturating(U64::from(val)),
            |val: u8| Saturating(val),
            |val: u64| Saturating(val),
            |val: u8| Saturating(val as u64),
            |val: Saturating<u64>| Saturating(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_unbounded() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Unbounded(S64::from(val)),
            |val: i64| Unbounded(S64::from(val)),
            |val: i64| Unbounded(val),
            |val: i64| Unbounded(val),
            |val: Unbounded<i64>| Unbounded(S64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(i64, 52),
            0..96,
            |val: i64| Unbounded(S64::from(val)),
            |val: i64| Unbounded(val),
            |val: Unbounded<i64>| Unbounded(S64::from(val.0)),
        );

        ops_unary_impl(
            ndassert::range!(i64, 52),
            |val: i64| Unbounded(S64::from(val)),
            |val: i64| Unbounded(val),
            |val: Unbounded<i64>| Unbounded(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_unbounded() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Unbounded(U64::from(val)),
            |val: u64| Unbounded(U64::from(val)),
            |val: u64| Unbounded(val),
            |val: u64| Unbounded(val),
            |val: Unbounded<u64>| Unbounded(U64::from(val.0)),
        );

        ops_shift_impl(
            ndassert::range!(u64, 52),
            0..96,
            |val: u64| Unbounded(U64::from(val)),
            |val: u64| Unbounded(val),
            |val: Unbounded<u64>| Unbounded(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_unbounded() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            ndassert::range!(i64, 56, 1).chain([-1, 0, 1]),
            |val: i64| Unbounded(S64::from(val)),
            |val: i64| Unbounded(val),
            |val: i64| Unbounded(val),
            |val: i64| Unbounded(val),
            |val: Unbounded<i64>| Unbounded(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_unbounded() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            ndassert::range!(u64, 56, 1).chain([0, 1]),
            |val: u64| Unbounded(U64::from(val)),
            |val: u64| Unbounded(val),
            |val: u64| Unbounded(val),
            |val: u64| Unbounded(val),
            |val: Unbounded<u64>| Unbounded(U64::from(val.0)),
        );
    }

    #[test]
    fn ops_signed_primitive_native_unbounded() {
        ops_impl(
            ndassert::range!(i64, 56, 0).chain([-1, 0, 1]),
            i8::MIN..i8::MAX,
            |val: i64| Unbounded(S64::from(val)),
            |val: i8| Unbounded(val),
            |val: i64| Unbounded(val),
            |val: i8| Unbounded(val as i64),
            |val: Unbounded<i64>| Unbounded(S64::from(val.0)),
        );
    }

    #[test]
    fn ops_unsigned_primitive_native_unbounded() {
        ops_impl(
            ndassert::range!(u64, 56, 0).chain([0, 1]),
            u8::MIN..u8::MAX,
            |val: u64| Unbounded(U64::from(val)),
            |val: u8| Unbounded(val),
            |val: u64| Unbounded(val),
            |val: u8| Unbounded(val as u64),
            |val: Unbounded<u64>| Unbounded(U64::from(val.0)),
        );
    }

    #[test]
    fn uops() {
        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48),
            pos as (val as i64),
            neg as (val as i64).wrapping_neg(),
            bytes as val.to_le_bytes(),
        ) [
            (uops::not(&bytes).eval(), (!val).to_le_bytes()),
            (uops::pos(&bytes).eval(), pos.to_le_bytes()),
            (uops::neg(&bytes).eval(), neg.to_le_bytes()),

            (uops::dirv(&bytes, Dir::POS).eval(), pos.to_le_bytes()),
            (uops::dirv(&bytes, Dir::NEG).eval(), neg.to_le_bytes()),
            (uops::dirx(&bytes, Dir::POS).eval(), [pos, neg][(neg > 0) as usize].to_le_bytes()),
            (uops::dirx(&bytes, Dir::NEG).eval(), [pos, neg][(pos > 0) as usize].to_le_bytes()),
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
            (uops::add(&bytes, rhs).signed().eval(), lhs.wrapping_add(rhs as i64).to_le_bytes()),
            (uops::sub(&bytes, rhs).signed().eval(), lhs.wrapping_sub(rhs as i64).to_le_bytes()),
            (uops::bitor(&bytes, rhs).eval(), (lhs | rhs as i64).to_le_bytes()),
            (uops::bitand(&bytes, rhs).eval(), (lhs & rhs as i64).to_le_bytes()),
            (uops::bitxor(&bytes, rhs).eval(), (lhs ^ rhs as i64).to_le_bytes()),
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
            (uops::shl(&bytes, shift).ext(MAX).eval(), (val.unbounded_shl(shift as u32) | shl_ext).to_le_bytes()),
            (uops::shr(&bytes, shift).ext(MAX).eval(), (val.unbounded_shr(shift as u32) | shr_ext).to_le_bytes()),
        ] }
    }

    #[test]
    fn uops_mut() {
        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48),
            pos as (val as i64),
            neg as (val as i64).wrapping_neg(),
            bytes as val.to_le_bytes(),
        ) [
            ({ let mut bytes = bytes; uops::not(&mut bytes).eval_mut(); bytes }, (!val).to_le_bytes()),
            ({ let mut bytes = bytes; uops::pos(&mut bytes).eval_mut(); bytes }, pos.to_le_bytes()),
            ({ let mut bytes = bytes; uops::neg(&mut bytes).eval_mut(); bytes }, neg.to_le_bytes()),

            ({ let mut bytes = bytes; uops::dirv(&mut bytes, Dir::POS).eval_mut(); bytes }, pos.to_le_bytes()),
            ({ let mut bytes = bytes; uops::dirv(&mut bytes, Dir::NEG).eval_mut(); bytes }, neg.to_le_bytes()),
            ({ let mut bytes = bytes; uops::dirx(&mut bytes, Dir::POS).eval_mut(); bytes }, [pos, neg][(neg > 0) as usize].to_le_bytes()),
            ({ let mut bytes = bytes; uops::dirx(&mut bytes, Dir::NEG).eval_mut(); bytes }, [pos, neg][(pos > 0) as usize].to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56),
            rhs in ndassert::range!(u64, 56),
            lhs_bytes as lhs.to_le_bytes(),
            rhs_bytes as rhs.to_le_bytes(),
        ) [
            ({ let mut bytes = lhs_bytes; uops::add(&mut bytes, &rhs_bytes).eval_mut(); bytes }, lhs.wrapping_add(rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::sub(&mut bytes, &rhs_bytes).eval_mut(); bytes }, lhs.wrapping_sub(rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::bitor(&mut bytes, &rhs_bytes).eval_mut(); bytes }, (lhs | rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::bitand(&mut bytes, &rhs_bytes).eval_mut(); bytes }, (lhs & rhs).to_le_bytes()),
            ({ let mut bytes = lhs_bytes; uops::bitxor(&mut bytes, &rhs_bytes).eval_mut(); bytes }, (lhs ^ rhs).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56),
            rhs in u8::MIN..u8::MAX,
            bytes as lhs.to_le_bytes(),
        ) [
            ({ let mut bytes = bytes; uops::add(&mut bytes, rhs).eval_mut(); bytes }, lhs.wrapping_add(rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::sub(&mut bytes, rhs).eval_mut(); bytes }, lhs.wrapping_sub(rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitor(&mut bytes, rhs).eval_mut(); bytes }, (lhs | rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitand(&mut bytes, rhs).eval_mut(); bytes }, (lhs & rhs as u64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitxor(&mut bytes, rhs).eval_mut(); bytes }, (lhs ^ rhs as u64).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56),
            rhs in i8::MIN..i8::MAX,
            bytes as lhs.to_le_bytes(),
        ) [
            ({ let mut bytes = bytes; uops::add(&mut bytes, rhs).signed().eval_mut(); bytes }, lhs.wrapping_add(rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::sub(&mut bytes, rhs).signed().eval_mut(); bytes }, lhs.wrapping_sub(rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitor(&mut bytes, rhs).eval_mut(); bytes }, (lhs | rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitand(&mut bytes, rhs).eval_mut(); bytes }, (lhs & rhs as i64).to_le_bytes()),
            ({ let mut bytes = bytes; uops::bitxor(&mut bytes, rhs).eval_mut(); bytes }, (lhs ^ rhs as i64).to_le_bytes()),
        ] }

        ndassert::check! { @eq (
            val in ndassert::range!(u64, 52),
            shift in 0..96,
            bytes as val.to_le_bytes(),
            shl_ext as u64::MAX.unbounded_shr(u64::BITS.saturating_sub(shift as u32)),
            shr_ext as u64::MAX.unbounded_shl(u64::BITS.saturating_sub(shift as u32)),
        ) [
            ({ let mut bytes = bytes; uops::shl(&mut bytes, shift).eval_mut(); bytes }, val.unbounded_shl(shift as u32).to_le_bytes()),
            ({ let mut bytes = bytes; uops::shr(&mut bytes, shift).eval_mut(); bytes }, val.unbounded_shr(shift as u32).to_le_bytes()),
            ({ let mut bytes = bytes; uops::shl(&mut bytes, shift).ext(MAX).eval_mut(); bytes }, (val.unbounded_shl(shift as u32) | shl_ext).to_le_bytes()),
            ({ let mut bytes = bytes; uops::shr(&mut bytes, shift).ext(MAX).eval_mut(); bytes }, (val.unbounded_shr(shift as u32) | shr_ext).to_le_bytes()),
        ] }
    }
}

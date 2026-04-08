#![doc = include_str!("../docs/long.md")]
#![allow(clippy::manual_div_ceil)]

use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    io::{Cursor, Write},
    iter::{once, repeat},
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
    BytesFn, Max, Min, Num, NumFn, NumSigned, NumUnsigned, One, Sign, Zero,
    arch::{BytesLen, Offset, word::*},
    long::{radix::*, uops::*},
};
#[cfg(feature = "const-time")]
use crate::{EqCt, GtCt, LtCt, MaskCt, SelectCt, SignCt};

#[cfg(feature = "asm")]
const LENS: [usize; 3] = [(1 << 8) / BITS, (1 << 12) / BITS, (1 << 16) / BITS];

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
        let diff = $lhs.rev().zip($rhs.rev()).map(|(a, b)| a ^ b).fold(0, |acc, cmp| acc | cmp);

        std::hint::black_box(diff.eq_ct(&0)) as MaskCt
    }};
}

#[cfg(feature = "const-time")]
macro_rules! cmp_ct {
    ($lhs:expr, $rhs:expr) => {{
        let (lt, gt) = $lhs.rev().zip($rhs.rev()).map(|(a, b)| ((a < b) as i8, (a > b) as i8)).fold(
            (0i8, 0i8),
            |(lt_, gt_), (lt, gt)| {
                let ltr = lt_ | (lt & (gt_ == 0) as i8);
                let gtr = gt_ | (gt & (lt_ == 0) as i8);

                (ltr, gtr)
            },
        );

        std::hint::black_box(gt - lt) as SignCt
    }};
}

macro_rules! from_primitive {
    ($long:ident [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!($long, $primitive);)+
    };
    ($long:ident, $primitive:ty $(,)?) => {
        impl<const L: usize> From<$primitive> for $long<L> {
            #[inline]
            #[allow(unused_comparisons)]
            fn from(value: $primitive) -> Self {
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
        #[allow(unused_comparisons)]
        pub const fn $fn(value: $primitive) -> Self {
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

macro_rules! from_digits_radix_impl {
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

macro_rules! from_str_impl {
    (@radix $str:expr, $radix:ty) => {{
        let (s, sign) = get_sign_from_str($str)?;
        let (s, radix) = get_radix_from_str(s, <$radix>::VALUE)?;

        if radix != <$radix>::VALUE {
            return Err(FromStrError::InvalidRadix { radix: radix as usize });
        }

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, sign)
        } else {
            from_str_radix(s, radix, sign)
        }
    }};
    (@long $str:expr) => {{
        let (s, sign) = get_sign_from_str($str)?;
        let (s, radix) = get_radix_from_str(s, 10)?;

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, sign)
        } else {
            from_str_radix(s, radix, sign)
        }
    }};
    (@bytes $str:expr) => {{
        let (s, radix) = get_radix_from_str($str, 16)?;

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, Sign::POS)
        } else {
            Err(FromStrError::InvalidRadix { radix: radix as usize })
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
            + Signed::<L>(add_long(&lhs.0, &Signed::<L>::from(rhs).0)),
            - Signed::<L>(sub_long(&lhs.0, &Signed::<L>::from(rhs).0)),
            * Signed::<L>(mul_long(&lhs.0, &Signed::<L>::from(rhs).0)),
            / Signed::<L>(div_long(&lhs.abs().0, &Signed::<L>::from(rhs.checked_abs().unwrap_or(<$primitive>::MIN)).0).0).signed(lhs.sign() * Sign::from(rhs)),
            % Signed::<L>(div_long(&lhs.abs().0, &Signed::<L>::from(rhs.checked_abs().unwrap_or(<$primitive>::MIN)).0).1).signed(lhs.sign()),
            | Signed::<L>(bit_long(&lhs.0, &Signed::<L>::from(rhs).0, |lop, rop| lop | rop)),
            & Signed::<L>(bit_long(&lhs.0, &Signed::<L>::from(rhs).0, |lop, rop| lop & rop)),
            ^ Signed::<L>(bit_long(&lhs.0, &Signed::<L>::from(rhs).0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Signed<L>) -> Signed<L> for [Signed<L>, $primitive], [
            + Signed::<L>(add_long(&Signed::<L>::from(lhs).0, &rhs.0)),
            * Signed::<L>(mul_long(&Signed::<L>::from(lhs).0, &rhs.0)),
            | Signed::<L>(bit_long(&Signed::<L>::from(lhs).0, &rhs.0, |lop, rop| lop | rop)),
            & Signed::<L>(bit_long(&Signed::<L>::from(lhs).0, &rhs.0, |lop, rop| lop & rop)),
            ^ Signed::<L>(bit_long(&Signed::<L>::from(lhs).0, &rhs.0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, &rhs: &$primitive), [
            += add_long_mut(&mut lhs.0, &Signed::<L>::from(rhs).0),
            -= sub_long_mut(&mut lhs.0, &Signed::<L>::from(rhs).0),
            *= mul_long_mut(&mut lhs.0, &Signed::<L>::from(rhs).0),
            /= { *lhs = Signed::<L>(div_long(&lhs.abs().0, &Signed::<L>::from(rhs.checked_abs().unwrap_or(<$primitive>::MIN)).0).0).signed(lhs.sign() * Sign::from(rhs)); },
            %= { *lhs = Signed::<L>(div_long(&lhs.abs().0, &Signed::<L>::from(rhs.checked_abs().unwrap_or(<$primitive>::MIN)).0).1).signed(lhs.sign()); },
            |= bit_long_mut(&mut lhs.0, &Signed::<L>::from(rhs).0, |lop, rop| lop | rop),
            &= bit_long_mut(&mut lhs.0, &Signed::<L>::from(rhs).0, |lop, rop| lop & rop),
            ^= bit_long_mut(&mut lhs.0, &Signed::<L>::from(rhs).0, |lop, rop| lop ^ rop),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, &rhs: &$primitive) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + Unsigned::<L>(add_long(&lhs.0, &Unsigned::<L>::from(rhs).0)),
            - Unsigned::<L>(sub_long(&lhs.0, &Unsigned::<L>::from(rhs).0)),
            * Unsigned::<L>(mul_long(&lhs.0, &Unsigned::<L>::from(rhs).0)),
            / Unsigned::<L>(div_long(&lhs.0, &Unsigned::<L>::from(rhs).0).0),
            % Unsigned::<L>(div_long(&lhs.0, &Unsigned::<L>::from(rhs).0).1),
            | Unsigned::<L>(bit_long(&lhs.0, &Unsigned::<L>::from(rhs).0, |lop, rop| lop | rop)),
            & Unsigned::<L>(bit_long(&lhs.0, &Unsigned::<L>::from(rhs).0, |lop, rop| lop & rop)),
            ^ Unsigned::<L>(bit_long(&lhs.0, &Unsigned::<L>::from(rhs).0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Unsigned<L>) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + Unsigned::<L>(add_long(&Unsigned::<L>::from(lhs).0, &rhs.0)),
            * Unsigned::<L>(mul_long(&Unsigned::<L>::from(lhs).0, &rhs.0)),
            | Unsigned::<L>(bit_long(&Unsigned::<L>::from(lhs).0, &rhs.0, |lop, rop| lop | rop)),
            & Unsigned::<L>(bit_long(&Unsigned::<L>::from(lhs).0, &rhs.0, |lop, rop| lop & rop)),
            ^ Unsigned::<L>(bit_long(&Unsigned::<L>::from(lhs).0, &rhs.0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, &rhs: &$primitive), [
            += add_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0),
            -= sub_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0),
            *= mul_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0),
            /= div_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0),
            %= rem_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0),
            |= bit_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0, |lop, rop| lop | rop),
            &= bit_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0, |lop, rop| lop & rop),
            ^= bit_long_mut(&mut lhs.0, &Unsigned::<L>::from(rhs).0, |lop, rop| lop ^ rop),
        ] }
    };
    (@bytes $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, &rhs: &$primitive) -> Bytes<L> for [Bytes<L>, $primitive], [
            | Bytes::<L>(bit_long(&lhs.0, &Bytes::<L>::from(rhs).0, |lop, rop| lop | rop)),
            & Bytes::<L>(bit_long(&lhs.0, &Bytes::<L>::from(rhs).0, |lop, rop| lop & rop)),
            ^ Bytes::<L>(bit_long(&lhs.0, &Bytes::<L>::from(rhs).0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Bytes<L>) -> Bytes<L> for [Bytes<L>, $primitive], [
            | Bytes::<L>(bit_long(&Bytes::<L>::from(lhs).0, &rhs.0, |lop, rop| lop | rop)),
            & Bytes::<L>(bit_long(&Bytes::<L>::from(lhs).0, &rhs.0, |lop, rop| lop & rop)),
            ^ Bytes::<L>(bit_long(&Bytes::<L>::from(lhs).0, &rhs.0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, &rhs: &$primitive), [
            |= bit_long_mut(&mut lhs.0, &Bytes::<L>::from(rhs).0, |lop, rop| lop | rop),
            &= bit_long_mut(&mut lhs.0, &Bytes::<L>::from(rhs).0, |lop, rop| lop & rop),
            ^= bit_long_mut(&mut lhs.0, &Bytes::<L>::from(rhs).0, |lop, rop| lop ^ rop),
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
            + Signed::<L>(add_signed(&lhs.0, (rhs.unsigned_abs() as Single, Sign::from(rhs)))),
            - Signed::<L>(sub_signed(&lhs.0, (rhs.unsigned_abs() as Single, Sign::from(rhs)))),
            * Signed::<L>(mul_signed(&lhs.0, (rhs.unsigned_abs() as Single, Sign::from(rhs)))),
            / Signed::<L>(div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).0).signed(lhs.sign() * Sign::from(rhs)),
            % Signed::<L>(div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).1).signed(lhs.sign()),
            | Signed::<L>(bit_single(&lhs.0, rhs as Single, if rhs >= 0 { 0 } else { MAX }, |lop, rop| lop | rop)),
            & Signed::<L>(bit_single(&lhs.0, rhs as Single, if rhs >= 0 { 0 } else { MAX }, |lop, rop| lop & rop)),
            ^ Signed::<L>(bit_single(&lhs.0, rhs as Single, if rhs >= 0 { 0 } else { MAX }, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Signed<L>) -> Signed<L> for [Signed<L>, $primitive], [
            + Signed::<L>(add_signed(&rhs.0, (lhs.unsigned_abs() as Single, Sign::from(lhs)))),
            * Signed::<L>(mul_signed(&rhs.0, (lhs.unsigned_abs() as Single, Sign::from(lhs)))),
            | Signed::<L>(bit_single(&rhs.0, lhs as Single, if lhs >= 0 { 0 } else { MAX }, |lop, rop| lop | rop)),
            & Signed::<L>(bit_single(&rhs.0, lhs as Single, if lhs >= 0 { 0 } else { MAX }, |lop, rop| lop & rop)),
            ^ Signed::<L>(bit_single(&rhs.0, lhs as Single, if lhs >= 0 { 0 } else { MAX }, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, &rhs: &$primitive), [
            += add_signed_mut(&mut lhs.0, (rhs.unsigned_abs() as Single, Sign::from(rhs))),
            -= sub_signed_mut(&mut lhs.0, (rhs.unsigned_abs() as Single, Sign::from(rhs))),
            *= mul_signed_mut(&mut lhs.0, (rhs.unsigned_abs() as Single, Sign::from(rhs))),
            /= { *lhs = Signed::<L>(div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).0).signed(lhs.sign() * Sign::from(rhs)); },
            %= { *lhs = Signed::<L>(div_single(&lhs.abs().0, rhs.unsigned_abs() as Single).1).signed(lhs.sign()); },
            |= bit_single_mut(&mut lhs.0, rhs as Single, if rhs >= 0 { 0 } else { MAX }, |lop, rop| lop | rop),
            &= bit_single_mut(&mut lhs.0, rhs as Single, if rhs >= 0 { 0 } else { MAX }, |lop, rop| lop & rop),
            ^= bit_single_mut(&mut lhs.0, rhs as Single, if rhs >= 0 { 0 } else { MAX }, |lop, rop| lop ^ rop),
        ] }
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, &rhs: &$primitive) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + Unsigned::<L>(add_single(&lhs.0, rhs as Single)),
            - Unsigned::<L>(sub_single(&lhs.0, rhs as Single)),
            * Unsigned::<L>(mul_single(&lhs.0, rhs as Single)),
            / Unsigned::<L>(div_single(&lhs.0, rhs as Single).0),
            % Unsigned::<L>(div_single(&lhs.0, rhs as Single).1),
            | Unsigned::<L>(bit_single(&lhs.0, rhs as Single, 0, |lop, rop| lop | rop)),
            & Unsigned::<L>(bit_single(&lhs.0, rhs as Single, 0, |lop, rop| lop & rop)),
            ^ Unsigned::<L>(bit_single(&lhs.0, rhs as Single, 0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Unsigned<L>) -> Unsigned<L> for [Unsigned<L>, $primitive], [
            + Unsigned::<L>(add_single(&rhs.0, lhs as Single)),
            * Unsigned::<L>(mul_single(&rhs.0, lhs as Single)),
            | Unsigned::<L>(bit_single(&rhs.0, lhs as Single, 0, |lop, rop| lop | rop)),
            & Unsigned::<L>(bit_single(&rhs.0, lhs as Single, 0, |lop, rop| lop & rop)),
            ^ Unsigned::<L>(bit_single(&rhs.0, lhs as Single, 0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, &rhs: &$primitive), [
            += add_single_mut(&mut lhs.0, rhs as Single),
            -= sub_single_mut(&mut lhs.0, rhs as Single),
            *= mul_single_mut(&mut lhs.0, rhs as Single),
            /= div_single_mut(&mut lhs.0, rhs as Single),
            %= rem_single_mut(&mut lhs.0, rhs as Single),
            |= bit_single_mut(&mut lhs.0, rhs as Single, 0, |lop, rop| lop | rop),
            &= bit_single_mut(&mut lhs.0, rhs as Single, 0, |lop, rop| lop & rop),
            ^= bit_single_mut(&mut lhs.0, rhs as Single, 0, |lop, rop| lop ^ rop),
        ] }
    };
    (@bytes $primitive:ty $(,)?) => {
        ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, &rhs: &$primitive) -> Bytes<L> for [Bytes<L>, $primitive], [
            | Bytes::<L>(bit_single(&lhs.0, rhs as Single, 0, |lop, rop| lop | rop)),
            & Bytes::<L>(bit_single(&lhs.0, rhs as Single, 0, |lop, rop| lop & rop)),
            ^ Bytes::<L>(bit_single(&lhs.0, rhs as Single, 0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndbin <const L: usize> (&lhs: &$primitive, rhs: &Bytes<L>) -> Bytes<L> for [Bytes<L>, $primitive], [
            | Bytes::<L>(bit_single(&rhs.0, lhs as Single, 0, |lop, rop| lop | rop)),
            & Bytes::<L>(bit_single(&rhs.0, lhs as Single, 0, |lop, rop| lop & rop)),
            ^ Bytes::<L>(bit_single(&rhs.0, lhs as Single, 0, |lop, rop| lop ^ rop)),
        ] }

        ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, &rhs: &$primitive), [
            |= bit_single_mut(&mut lhs.0, rhs as Single, 0, |lop, rop| lop | rop),
            &= bit_single_mut(&mut lhs.0, rhs as Single, 0, |lop, rop| lop & rop),
            ^= bit_single_mut(&mut lhs.0, rhs as Single, 0, |lop, rop| lop ^ rop),
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

macro_rules! add_long_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.zip($rhs).scan(0, |acc, (a, b)| {
            let val = a as Double + b as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
}

macro_rules! sub_long_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.zip($rhs).scan(0, |acc, (a, b)| {
            let val = RADIX + a as Double - b as Double - *acc;

            *acc = (val < RADIX) as Double;

            Some(val as Single)
        })
    };
}

macro_rules! add_single_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.scan($rhs as Double, |acc, a| {
            let val = a as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
    (@overflow $lhs:expr, $rhs:expr, $acc:expr) => {
        $lhs.scan($rhs as Double, |_, a| {
            let val = a as Double + $acc;

            $acc = val / RADIX;

            Some(val as Single)
        })
    };
}

macro_rules! sub_single_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.scan($rhs as Double, |acc, a| {
            let val = RADIX + a as Double - *acc;

            *acc = (val < RADIX) as Double;

            Some(val as Single)
        })
    };
}

macro_rules! mul_single_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.scan(0, |acc, a| {
            let val = a as Double * $rhs as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
    (@overflow $lhs:expr, $rhs:expr, $acc:expr) => {{
        $lhs.scan(0, |_, a| {
            let val = a as Double * $rhs as Double + $acc;

            $acc = val / RADIX;

            Some(val as Single)
        })
    }};
}

macro_rules! add_long_mut_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.zip($rhs).fold(0, |acc, (ptr, val)| {
            let v = *ptr as Double + val as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! sub_long_mut_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.zip($rhs).fold(0, |acc, (ptr, val)| {
            let v = RADIX + *ptr as Double - val as Double - acc;

            *ptr = v as Single;

            (v < RADIX) as Double
        });
    };
}

macro_rules! add_single_mut_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.fold($rhs as Double, |acc, ptr| {
            let v = *ptr as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! sub_single_mut_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.fold($rhs as Double, |acc, ptr| {
            let v = RADIX + *ptr as Double - acc;

            *ptr = v as Single;

            (v < RADIX) as Double
        });
    };
}

macro_rules! mul_single_mut_impl {
    ($lhs:expr, $rhs:expr) => {
        $lhs.fold(0, |acc, ptr| {
            let v = *ptr as Double * $rhs as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! div_long_impl {
    ($lhs:expr, $rhs:expr) => {{
        #[allow(unused_mut)]
        let mut div = $lhs;
        let mut rem = [0; L];

        for val in div.iter_mut().rev() {
            cycle!(rem, *val);

            let digit = search!(@upper 0, RADIX, |m: Double| {
                let mut acc = 0;

                let mul = mul_single_impl!(@overflow $rhs, m, acc).collect_with([0; L]);

                if acc > 0 {
                    return Ordering::Greater;
                }

                mul.iter().rev().cmp(rem.iter().rev())
            });

            let digit = digit.saturating_sub(1) as Single;

            *val = digit;

            if digit > 0 {
                let rem_iter = rem.iter_mut();
                let mul_iter = mul_single_impl!($rhs, digit);

                sub_long_mut_impl!(rem_iter, mul_iter);
            }
        }

        (div, rem)
    }};
}

macro_rules! div_single_impl {
    ($lhs:expr, $rhs:expr) => {{
        #[allow(unused_mut)]
        let mut div = $lhs;
        let mut rem = 0 as Double;

        for val in div.iter_mut().rev() {
            rem <<= BITS;
            rem |= *val as Double;

            let digit = search!(@upper 0, RADIX, |m: Double| { (m * $rhs as Double).cmp(&rem) });
            let digit = digit.saturating_sub(1) as Single;

            *val = digit;
            rem -= digit as Double * $rhs as Double;
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

#[allow(unused)]
mod uops {
    use super::*;

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn pos<const L: usize>(words: &[Single; L]) -> [Single; L] {
        let mut words = *words;

        pos_mut(&mut words);

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn pos_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn neg<const L: usize>(words: &[Single; L]) -> [Single; L] {
        let mut words = *words;

        not_mut(&mut words);
        inc_mut(&mut words);

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn neg_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(words);
        inc_mut(words);

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn not<const L: usize>(words: &[Single; L]) -> [Single; L] {
        let mut words = *words;

        not_mut(&mut words);

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn not_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        words.iter_mut().for_each(|word| *word = !*word);
        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn inc<const L: usize>(words: &[Single; L]) -> [Single; L] {
        let mut words = *words;

        inc_mut(&mut words);

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn dec<const L: usize>(words: &[Single; L]) -> [Single; L] {
        let mut words = *words;

        dec_mut(&mut words);

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn inc_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        let mut acc = 1;

        for ptr in words.iter_mut() {
            let word = *ptr as Double + acc as Double;

            *ptr = word as Single;

            acc = word / RADIX;

            if acc == 0 {
                break;
            }
        }

        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn dec_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        let mut acc = 1;

        for ptr in words.iter_mut() {
            let word = RADIX + *ptr as Double - acc as Double;

            *ptr = word as Single;

            acc = (word < RADIX) as Double;

            if acc == 0 {
                break;
            }
        }

        words
    }

    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shl<const L: usize>(words: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        let mut words = *words;

        shl_mut(&mut words, shift, default);

        words
    }

    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shr<const L: usize>(words: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        let mut words = *words;

        shr_mut(&mut words, shift, default);

        words
    }

    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shl_mut<const L: usize>(words: &mut [Single; L], shift: usize, default: Single) -> &mut [Single; L] {
        let offset = (shift / BITS).min(L);
        let shl = shift % BITS;
        let shr = BITS - shl;

        for idx in ((offset + 1).min(L)..L).rev() {
            let idx_h = idx - offset;
            let idx_l = idx - offset - 1;

            let val_h = words[idx_h].unbounded_shl(shl as u32);
            let val_l = words[idx_l].unbounded_shr(shr as u32);

            words[idx] = val_h | val_l;
        }

        let val_h = words[0].unbounded_shl(shl as u32);
        let val_l = default.unbounded_shr(shr as u32);

        if offset < L {
            words[offset] = val_h | val_l;
        }

        words[..offset].iter_mut().for_each(|ptr| *ptr = default);
        words
    }

    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shr_mut<const L: usize>(words: &mut [Single; L], shift: usize, default: Single) -> &mut [Single; L] {
        let offset = (shift / BITS).min(L);
        let shr = shift % BITS;
        let shl = BITS - shr;

        for idx in 0..(L - offset).saturating_sub(1) {
            let idx_h = idx + offset + 1;
            let idx_l = idx + offset;

            let val_h = words[idx_h].unbounded_shl(shl as u32);
            let val_l = words[idx_l].unbounded_shr(shr as u32);

            words[idx] = val_h | val_l;
        }

        let val_h = default.unbounded_shl(shl as u32);
        let val_l = words[L - 1].unbounded_shr(shr as u32);

        if offset < L {
            words[L - offset - 1] = val_h | val_l;
        }

        words[L - offset..].iter_mut().for_each(|ptr| *ptr = default);
        words
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shl_signed<const L: usize>(words: &[Single; L], shift: usize) -> [Single; L] {
        shl(words, shift, 0)
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shr_signed<const L: usize>(words: &[Single; L], shift: usize) -> [Single; L] {
        let default = match sign(words, Sign::POS, Sign::NEG) {
            Sign::ZERO => 0,
            Sign::NEG => MAX,
            Sign::POS => 0,
        };

        shr(words, shift, default)
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shl_signed_mut<const L: usize>(words: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        shl_mut(words, shift, 0)
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn shr_signed_mut<const L: usize>(words: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        let default = match sign(words, Sign::POS, Sign::NEG) {
            Sign::ZERO => 0,
            Sign::NEG => MAX,
            Sign::POS => 0,
        };

        shr_mut(words, shift, default)
    }

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn read<const L: usize>(words: &[Single; L], offset: usize) -> Single {
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

    #[inline]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn sign<const L: usize>(words: &[Single; L], pos: Sign, neg: Sign) -> Sign {
        if words == &[0; L] {
            return Sign::ZERO;
        }

        match words[L - 1] >> (BITS - 1) {
            0 => pos,
            _ => neg,
        }
    }

    #[cfg(feature = "const-time")]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn sign_ct<const L: usize>(words: &[Single; L]) -> SignCt {
        let zero = zero_ct(words);
        let neg = neg_ct(words);
        let pos = !zero & !neg & 1;

        neg as SignCt | pos as SignCt
    }

    #[cfg(feature = "const-time")]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn pos_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        let zero = zero_ct(words);
        let neg = neg_ct(words);

        !zero & !neg
    }

    #[cfg(feature = "const-time")]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn neg_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        let neg = (words[L - 1] >> (BITS - 1)) as MaskCt;

        <MaskCt as Zero>::ZERO.wrapping_sub(neg)
    }

    #[cfg(feature = "const-time")]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
    #[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
    pub(super) fn zero_ct<const L: usize>(words: &[Single; L]) -> MaskCt {
        eq_ct!(words.iter(), std::hint::black_box(repeat(0)))
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

/// Unsigned long represented with `[Word; L]`, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and arithmetic/bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unsigned<const L: usize>(pub [Single; L]);

/// Bytes long represented with `[Word; L]`, where `Word` is unsigned CPU-word.
///
/// Implements all standard Rust traits and bitwise/shift operations of `Std-kind` and `Nd-kind`.
///
/// For more info, see [crate-level](crate) documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bytes<const L: usize>(pub [Single; L]);

/// Signed long dynamic number. (**WIP**)
#[cfg(feature = "dyn")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedDyn(Vec<Single>, Sign);

/// Unsigned long dynamic number. (**WIP**)
#[cfg(feature = "dyn")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsignedDyn(Vec<Single>);

/// Bytes long dynamic number. (**WIP**)
#[cfg(feature = "dyn")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BytesDyn(Vec<Single>);

/// Signed SIMD-optimized long. (**WIP**)
#[cfg(feature = "simd")]
#[derive(Debug, Clone, Copy)]
pub struct SignedSimd<const L: usize>(pub [Single; L]);

/// Unsigned SIMD-optimized long. (**WIP**)
#[cfg(feature = "simd")]
#[derive(Debug, Clone, Copy)]
pub struct UnsignedSimd<const L: usize>(pub [Single; L]);

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
        self.as_words()
    }
}

impl<const L: usize, W: Word> AsRef<[W]> for Unsigned<L> {
    #[inline]
    fn as_ref(&self) -> &[W] {
        self.as_words()
    }
}

impl<const L: usize, W: Word> AsRef<[W]> for Bytes<L> {
    #[inline]
    fn as_ref(&self) -> &[W] {
        self.as_words()
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
        let x = self.sign();
        let y = other.sign();

        match x.cmp(&y) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => match x {
                Sign::ZERO => Ordering::Equal,
                Sign::NEG => self.abs().unsigned().cmp(&other.abs().unsigned()).reverse(),
                Sign::POS => self.abs().unsigned().cmp(&other.abs().unsigned()),
            },
            Ordering::Greater => Ordering::Greater,
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
        let iter = match self
            .signed(Sign::POS)
            .into_digits_iter(RadixImpl { radix: Dec::RADIX as Single })
        {
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
    ! Signed::<L>(not(&value.0)),
    - Signed::<L>(neg(&value.0)),
] }

ndops::def! { @ndun <const L: usize> (value: &Unsigned<L>) -> Unsigned<L>, [
    ! Unsigned::<L>(not(&value.0)),
] }

ndops::def! { @ndun <const L: usize> (value: &Bytes<L>) -> Bytes<L>, [
    ! Bytes::<L>(not(&value.0)),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, rhs: &Signed<L>) -> Signed<L>, [
    + Signed::<L>(add_long(&lhs.0, &rhs.0)),
    - Signed::<L>(sub_long(&lhs.0, &rhs.0)),
    * Signed::<L>(mul_long(&lhs.0, &rhs.0)),
    / Signed::<L>(div_long(&lhs.abs().0, &rhs.abs().0).0).signed(lhs.sign() * rhs.sign()),
    % Signed::<L>(div_long(&lhs.abs().0, &rhs.abs().0).1).signed(lhs.sign()),
    | Signed::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop | rop)),
    & Signed::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop & rop)),
    ^ Signed::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop ^ rop)),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Signed<L>, rhs: usize) -> Signed<L> for [Signed<L>, usize], [
    << Signed::<L>(shl_signed(&lhs.0, rhs)),
    >> Signed::<L>(shr_signed(&lhs.0, rhs)),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, rhs: &Unsigned<L>) -> Unsigned<L>, [
    + Unsigned::<L>(add_long(&lhs.0, &rhs.0)),
    - Unsigned::<L>(sub_long(&lhs.0, &rhs.0)),
    * Unsigned::<L>(mul_long(&lhs.0, &rhs.0)),
    / Unsigned::<L>(div_long(&lhs.0, &rhs.0).0),
    % Unsigned::<L>(div_long(&lhs.0, &rhs.0).1),
    | Unsigned::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop | rop)),
    & Unsigned::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop & rop)),
    ^ Unsigned::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop ^ rop)),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Unsigned<L>, rhs: usize) -> Unsigned<L> for [Unsigned<L>, usize], [
    << Unsigned::<L>(shl(&lhs.0, rhs, 0)),
    >> Unsigned::<L>(shr(&lhs.0, rhs, 0)),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, rhs: &Bytes<L>) -> Bytes<L>, [
    | Bytes::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop | rop)),
    & Bytes::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop & rop)),
    ^ Bytes::<L>(bit_long(&lhs.0, &rhs.0, |lop, rop| lop ^ rop)),
] }

ndops::def! { @ndbin <const L: usize> (lhs: &Bytes<L>, rhs: usize) -> Bytes<L> for [Bytes<L>, usize], [
    << Bytes::<L>(shl(&lhs.0, rhs, 0)),
    >> Bytes::<L>(shr(&lhs.0, rhs, 0)),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, rhs: &Signed<L>), [
    += add_long_mut(&mut lhs.0, &rhs.0),
    -= sub_long_mut(&mut lhs.0, &rhs.0),
    *= mul_long_mut(&mut lhs.0, &rhs.0),
    /= { *lhs = Signed::<L>(div_long(&lhs.abs().0, &rhs.abs().0).0).signed(lhs.sign() * rhs.sign()); },
    %= { *lhs = Signed::<L>(div_long(&lhs.abs().0, &rhs.abs().0).1).signed(lhs.sign()); },
    |= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop | rop),
    &= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop & rop),
    ^= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop ^ rop),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Signed<L>, rhs: usize) for [Signed<L>, usize], [
    <<= { shl_signed_mut(&mut lhs.0, rhs); },
    >>= { shr_signed_mut(&mut lhs.0, rhs); },
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: &Unsigned<L>), [
    += add_long_mut(&mut lhs.0, &rhs.0),
    -= sub_long_mut(&mut lhs.0, &rhs.0),
    *= mul_long_mut(&mut lhs.0, &rhs.0),
    /= div_long_mut(&mut lhs.0, &rhs.0),
    %= rem_long_mut(&mut lhs.0, &rhs.0),
    |= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop | rop),
    &= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop & rop),
    ^= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop ^ rop),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Unsigned<L>, rhs: usize) for [Unsigned<L>, usize], [
    <<= { shl_mut(&mut lhs.0, rhs, 0); },
    >>= { shr_mut(&mut lhs.0, rhs, 0); },
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, rhs: &Bytes<L>), [
    |= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop | rop),
    &= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop & rop),
    ^= bit_long_mut(&mut lhs.0, &rhs.0, |lop, rop| lop ^ rop),
] }

ndops::def! { @ndmut <const L: usize> (lhs: &mut Bytes<L>, rhs: usize) for [Bytes<L>, usize], [
    <<= { shl_mut(&mut lhs.0, rhs, 0); },
    >>= { shr_mut(&mut lhs.0, rhs, 0); },
] }

ndops::def! { @stdun <const L: usize> (mut value: Signed<L>) -> Signed<L>, [
    ! { not_mut(&mut value.0); value },
    - { neg_mut(&mut value.0); value },
] }

ndops::def! { @stdun <const L: usize> (mut value: Unsigned<L>) -> Unsigned<L>, [
    ! { not_mut(&mut value.0); value },
] }

ndops::def! { @stdun <const L: usize> (mut value: Bytes<L>) -> Bytes<L>, [
    ! { not_mut(&mut value.0); value },
] }

ndops::def! { @stdun <const L: usize> (value: &Signed<L>) -> Signed<L>, [
    ! <Signed<L> as NdNot>::nd_not(value),
    - <Signed<L> as NdNeg>::nd_neg(value),
] }

ndops::def! { @stdun <const L: usize> (value: &Unsigned<L>) -> Unsigned<L>, [
    ! <Unsigned<L> as NdNot>::nd_not(value),
] }

ndops::def! { @stdun <const L: usize> (value: &Bytes<L>) -> Bytes<L>, [
    ! <Bytes<L> as NdNot>::nd_not(value),
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

    /// `self.0` as raw bytes ref.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// `self.0` as raw bytes mut.
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    /// `self.0` as raw [`Words`](Word) ref.
    #[inline]
    pub fn as_words<W: Word>(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }

    /// `self.0` as raw [`Words`](Word) mut.
    #[inline]
    pub fn as_words_mut<W: Word>(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }

    /// Long number sign.
    #[inline]
    pub fn sign(&self) -> Sign {
        sign(&self.0, Sign::POS, Sign::NEG)
    }

    /// Absolute value.
    #[inline]
    pub fn abs(&self) -> Signed<L> {
        match self.sign() {
            Sign::ZERO => Signed::<L>(self.0),
            Sign::NEG => Signed::<L>(neg(&self.0)),
            Sign::POS => Signed::<L>(self.0),
        }
    }

    /// Creates new signed with specified sign from raw `self.0`.
    #[inline]
    pub fn signed(mut self, sign: Sign) -> Self {
        match self.sign() * sign {
            Sign::ZERO => return Self::default(),
            Sign::NEG => neg_mut(&mut self.0),
            Sign::POS => pos_mut(&mut self.0),
        };

        self
    }

    /// Creates new unsigned from raw `self.0`.
    #[inline]
    pub fn unsigned(self) -> Unsigned<L> {
        Unsigned::<L>(self.0)
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

    /// `self.0` as raw bytes ref.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// `self.0` as raw bytes mut.
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    /// `self.0` as raw [`Words`](Word) ref.
    #[inline]
    pub fn as_words<W: Word>(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }

    /// `self.0` as raw [`Words`](Word) mut.
    #[inline]
    pub fn as_words_mut<W: Word>(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
    }

    /// Long number sign.
    #[inline]
    pub fn sign(&self) -> Sign {
        sign(&self.0, Sign::POS, Sign::POS)
    }

    /// Creates new signed with specified sign from raw `self.0`.
    #[inline]
    pub fn signed(mut self, sign: Sign) -> Signed<L> {
        match self.sign() * sign {
            Sign::ZERO => return Signed::<L>::default(),
            Sign::NEG => neg_mut(&mut self.0),
            Sign::POS => pos_mut(&mut self.0),
        };

        Signed::<L>(self.0)
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

    /// `self.0` as raw bytes ref.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// `self.0` as raw bytes mut.
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    /// `self.0` as raw [`Words`](Word) ref.
    #[inline]
    pub fn as_words<W: Word>(&self) -> &[W] {
        transmute_ref!(&self.0[..]) as &[W]
    }

    /// `self.0` as raw [`Words`](Word) mut.
    #[inline]
    pub fn as_words_mut<W: Word>(&mut self) -> &mut [W] {
        transmute_mut!(&mut self.0[..]) as &mut [W]
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
        let lhs_sign = sign_ct(&self.0);
        let rhs_sign = sign_ct(&other.0);

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
        let lhs_sign = sign_ct(&self.0);
        let rhs_sign = sign_ct(&other.0);

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
    fn as_bytes_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }

    #[inline]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

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
    fn as_bytes_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }

    #[inline]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

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
    fn as_bytes_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }

    #[inline]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

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

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type W = Single)]
fn from_digits<const L: usize, W: Word>(digits: &[W], exp: W) -> Result<[Single; L], FromDigitsError> {
    let exp = exp.as_usize();

    if exp == 0 || exp >= W::BITS {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate(digits.iter().copied(), W::from_single(1 << exp))?;

    let res = from_digits_impl!(digits, digits.len(), exp);

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

    let res = from_digits_impl!(digits, digits.len(), exp);

    Ok(res)
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn from_str<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    from_str_validate(s, 1 << exp)?;

    let mut res = from_digits_impl!(s.bytes().rev().filter_map(get_digit_from_byte), s.len(), exp);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type W = Single)]
fn from_digits_radix<const L: usize, W: Word>(digits: &[W], radix: W) -> Result<[Single; L], FromDigitsError> {
    if radix.is_pow2() {
        return from_digits(digits, W::from_single(radix.order() as Single));
    }

    from_digits_validate(digits.iter().copied(), radix)?;

    let res = from_digits_radix_impl!(digits.iter().rev(), radix);

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

    let res = from_digits_radix_impl!(digits.rev(), radix);

    Ok(res)
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn from_str_radix<const L: usize>(s: &str, radix: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    if radix.is_pow2() {
        return from_str(s, radix.order() as u8, sign);
    }

    from_str_validate(s, radix)?;

    let mut res = from_digits_radix_impl!(s.bytes().filter_map(get_digit_from_byte), radix);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type W = Single)]
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

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type W = Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type W = Single)]
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
    Words: WordsIterator<Item = W>,
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

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn add_long<const L: usize>(lhs: &[Single; L], rhs: &[Single; L]) -> [Single; L] {
    add_long_impl!(lhs.iter().copied(), rhs.iter().copied()).collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn sub_long<const L: usize>(lhs: &[Single; L], rhs: &[Single; L]) -> [Single; L] {
    sub_long_impl!(lhs.iter().copied(), rhs.iter().copied()).collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn mul_long<const L: usize>(lhs: &[Single; L], rhs: &[Single; L]) -> [Single; L] {
    let mut res = [0; L];

    for (idx, x) in rhs.iter().enumerate() {
        let res_iter = res.iter_mut().skip(idx);
        let mul_iter = mul_single_impl!(lhs.iter().copied(), *x);

        add_long_mut_impl!(res_iter, mul_iter);
    }

    res
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn div_long<const L: usize>(lhs: &[Single; L], rhs: &[Single; L]) -> ([Single; L], [Single; L]) {
    div_long_impl!(*lhs, rhs.iter().copied())
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type F = fn(Single, Single) -> Single)]
fn bit_long<const L: usize, F>(lhs: &[Single; L], rhs: &[Single; L], f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    lhs.iter()
        .copied()
        .zip(rhs.iter().copied())
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn add_single<const L: usize>(lhs: &[Single; L], rhs: Single) -> [Single; L] {
    add_single_impl!(lhs.iter().copied(), rhs).collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn sub_single<const L: usize>(lhs: &[Single; L], rhs: Single) -> [Single; L] {
    sub_single_impl!(lhs.iter().copied(), rhs).collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn mul_single<const L: usize>(lhs: &[Single; L], rhs: Single) -> [Single; L] {
    mul_single_impl!(lhs.iter().copied(), rhs).collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn div_single<const L: usize>(lhs: &[Single; L], rhs: Single) -> ([Single; L], [Single; L]) {
    let (div, rem) = div_single_impl!(*lhs, rhs);

    (div, from_arr(&rem.to_le_bytes(), 0))
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type F = fn(Single, Single) -> Single)]
fn bit_single<const L: usize, F>(lhs: &[Single; L], rhs: Single, default: Single, f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    lhs.iter()
        .copied()
        .zip(once(rhs).chain(repeat(default)))
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn add_signed<const L: usize>(lhs: &[Single; L], (rhs, sign): (Single, Sign)) -> [Single; L] {
    match sign {
        Sign::ZERO => sub_single(lhs, rhs),
        Sign::NEG => sub_single(lhs, rhs),
        Sign::POS => add_single(lhs, rhs),
    }
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn sub_signed<const L: usize>(lhs: &[Single; L], (rhs, sign): (Single, Sign)) -> [Single; L] {
    match sign {
        Sign::ZERO => add_single(lhs, rhs),
        Sign::NEG => add_single(lhs, rhs),
        Sign::POS => sub_single(lhs, rhs),
    }
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn mul_signed<const L: usize>(lhs: &[Single; L], (rhs, sign): (Single, Sign)) -> [Single; L] {
    let mut mul = mul_single(lhs, rhs);

    if sign == Sign::NEG {
        neg_mut(&mut mul);
    }

    mul
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn add_long_mut<const L: usize>(lhs: &mut [Single; L], rhs: &[Single; L]) {
    add_long_mut_impl!(lhs.iter_mut(), rhs.iter().copied());
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn sub_long_mut<const L: usize>(lhs: &mut [Single; L], rhs: &[Single; L]) {
    sub_long_mut_impl!(lhs.iter_mut(), rhs.iter().copied());
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn mul_long_mut<const L: usize>(lhs: &mut [Single; L], rhs: &[Single; L]) {
    *lhs = mul_long(lhs, rhs);
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn div_long_mut<const L: usize>(lhs: &mut [Single; L], rhs: &[Single; L]) {
    div_long_impl!(lhs, rhs.iter().copied());
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn rem_long_mut<const L: usize>(lhs: &mut [Single; L], rhs: &[Single; L]) {
    let (_, rem) = div_long_impl!(*lhs, rhs.iter().copied());

    *lhs = rem;
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type F = fn(Single, Single) -> Single)]
fn bit_long_mut<const L: usize, F>(lhs: &mut [Single; L], rhs: &[Single; L], f: F)
where
    F: Fn(Single, Single) -> Single,
{
    lhs.iter_mut()
        .zip(rhs.iter().copied())
        .for_each(|(ptr, val)| *ptr = f(*ptr, val));
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn add_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) {
    add_single_mut_impl!(lhs.iter_mut(), rhs);
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn sub_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) {
    sub_single_mut_impl!(lhs.iter_mut(), rhs);
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn mul_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) {
    mul_single_mut_impl!(lhs.iter_mut(), rhs);
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn div_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) {
    div_single_impl!(lhs, rhs);
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn rem_single_mut<const L: usize>(lhs: &mut [Single; L], rhs: Single) {
    let (_, rem) = div_single_impl!(*lhs, rhs);

    *lhs = from_arr(&rem.to_le_bytes(), 0);
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1], type F = fn(Single, Single) -> Single)]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2], type F = fn(Single, Single) -> Single)]
fn bit_single_mut<const L: usize, F>(lhs: &mut [Single; L], rhs: Single, default: Single, f: F)
where
    F: Fn(Single, Single) -> Single,
{
    lhs.iter_mut()
        .zip(once(rhs).chain(repeat(default)))
        .for_each(|(ptr, val)| *ptr = f(*ptr, val));
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn add_signed_mut<const L: usize>(lhs: &mut [Single; L], (rhs, sign): (Single, Sign)) {
    match sign {
        Sign::ZERO => sub_single_mut(lhs, rhs),
        Sign::NEG => sub_single_mut(lhs, rhs),
        Sign::POS => add_single_mut(lhs, rhs),
    }
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn sub_signed_mut<const L: usize>(lhs: &mut [Single; L], (rhs, sign): (Single, Sign)) {
    match sign {
        Sign::ZERO => add_single_mut(lhs, rhs),
        Sign::NEG => add_single_mut(lhs, rhs),
        Sign::POS => sub_single_mut(lhs, rhs),
    }
}

#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[0])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[1])]
#[ndasm::emit_if([feature = "asm"] const L: usize = LENS[2])]
fn mul_signed_mut<const L: usize>(lhs: &mut [Single; L], (rhs, sign): (Single, Sign)) {
    mul_single_mut(lhs, rhs);

    if sign == Sign::NEG {
        neg_mut(lhs);
    }
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
    use crate::{CmpCt, GeCt, LeCt, MaxCt, MinCt};

    fn sdiv_default(_: i64, _: i64) -> i64 {
        0
    }

    fn srem_default(lhs: i64, _: i64) -> i64 {
        lhs
    }

    fn udiv_default(_: u64, _: u64) -> u64 {
        u64::MAX
    }

    fn urem_default(lhs: u64, _: u64) -> u64 {
        lhs
    }

    fn sdiv_native_default(_: i64, rhs: i8) -> i64 {
        i64::MIN * (rhs < 0) as i64
    }

    fn srem_native_default(lhs: i64, _: i8) -> i64 {
        let abs = lhs.checked_abs().unwrap_or(i64::MIN);

        if lhs < 0 {
            return -(abs & Double::MAX as i64);
        }

        abs & Double::MAX as i64
    }

    fn udiv_native_default(_: u64, _: u8) -> u64 {
        u64::MAX
    }

    fn urem_native_default(lhs: u64, _: u8) -> u64 {
        lhs & Double::MAX as u64
    }

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn from_primitive() {
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
    #[allow(clippy::unnecessary_cast)]
    fn from_bytes() {
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
    #[allow(clippy::unnecessary_cast)]
    fn from_arr() {
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
    #[allow(clippy::unnecessary_cast)]
    fn from_slice() {
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
    #[allow(clippy::unnecessary_cast)]
    fn from_iter() {
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
    #[rustfmt::skip]
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
    #[rustfmt::skip]
    fn cmp_ct() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (S64::from(lhs).eq_ct(&S64::from(rhs)), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (S64::from(lhs).lt_ct(&S64::from(rhs)), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (S64::from(lhs).gt_ct(&S64::from(rhs)), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (S64::from(lhs).le_ct(&S64::from(rhs)), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (S64::from(lhs).ge_ct(&S64::from(rhs)), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (S64::from(lhs).cmp_ct(&S64::from(rhs)), lhs.cmp(&rhs) as SignCt),
            (S64::from(lhs).min_ct(&S64::from(rhs)), S64::from(lhs.min(rhs))),
            (S64::from(lhs).max_ct(&S64::from(rhs)), S64::from(lhs.max(rhs))),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            (U64::from(lhs).eq_ct(&U64::from(rhs)), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (U64::from(lhs).lt_ct(&U64::from(rhs)), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (U64::from(lhs).gt_ct(&U64::from(rhs)), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (U64::from(lhs).le_ct(&U64::from(rhs)), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (U64::from(lhs).ge_ct(&U64::from(rhs)), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (U64::from(lhs).cmp_ct(&U64::from(rhs)), lhs.cmp(&rhs) as SignCt),
            (U64::from(lhs).min_ct(&U64::from(rhs)), U64::from(lhs.min(rhs))),
            (U64::from(lhs).max_ct(&U64::from(rhs)), U64::from(lhs.max(rhs))),
        ] }
    }

    #[test]
    fn ops() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([0]),
            rhs in ndassert::range!(i64, 56, 1).chain([0]),
        ) [
            (S64::from(lhs) + S64::from(rhs), S64::from(lhs.wrapping_add(rhs))),
            (S64::from(lhs) - S64::from(rhs), S64::from(lhs.wrapping_sub(rhs))),
            (S64::from(lhs) * S64::from(rhs), S64::from(lhs.wrapping_mul(rhs))),
            (S64::from(lhs) / S64::from(rhs), S64::from(lhs.checked_div(rhs).unwrap_or(sdiv_default(lhs, rhs)))),
            (S64::from(lhs) % S64::from(rhs), S64::from(lhs.checked_rem(rhs).unwrap_or(srem_default(lhs, rhs)))),
            (S64::from(lhs) | S64::from(rhs), S64::from(lhs | rhs)),
            (S64::from(lhs) & S64::from(rhs), S64::from(lhs & rhs)),
            (S64::from(lhs) ^ S64::from(rhs), S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0]),
            rhs in ndassert::range!(u64, 56, 1).chain([0]),
        ) [
            (U64::from(lhs) + U64::from(rhs), U64::from(lhs.wrapping_add(rhs))),
            (U64::from(lhs) - U64::from(rhs), U64::from(lhs.wrapping_sub(rhs))),
            (U64::from(lhs) * U64::from(rhs), U64::from(lhs.wrapping_mul(rhs))),
            (U64::from(lhs) / U64::from(rhs), U64::from(lhs.checked_div(rhs).unwrap_or(udiv_default(lhs, rhs)))),
            (U64::from(lhs) % U64::from(rhs), U64::from(lhs.checked_rem(rhs).unwrap_or(urem_default(lhs, rhs)))),
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
    fn ops_primitive() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([0]),
            rhs in ndassert::range!(i64, 56, 1).chain([0]),
        ) [
            (S64::from(lhs) + rhs, S64::from(lhs.wrapping_add(rhs))),
            (S64::from(lhs) - rhs, S64::from(lhs.wrapping_sub(rhs))),
            (S64::from(lhs) * rhs, S64::from(lhs.wrapping_mul(rhs))),
            (S64::from(lhs) / rhs, S64::from(lhs.checked_div(rhs).unwrap_or(sdiv_default(lhs, rhs)))),
            (S64::from(lhs) % rhs, S64::from(lhs.checked_rem(rhs).unwrap_or(srem_default(lhs, rhs)))),
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
            lhs in ndassert::range!(u64, 56, 0).chain([0]),
            rhs in ndassert::range!(u64, 56, 1).chain([0]),
        ) [
            (U64::from(lhs) + rhs, U64::from(lhs.wrapping_add(rhs))),
            (U64::from(lhs) - rhs, U64::from(lhs.wrapping_sub(rhs))),
            (U64::from(lhs) * rhs, U64::from(lhs.wrapping_mul(rhs))),
            (U64::from(lhs) / rhs, U64::from(lhs.checked_div(rhs).unwrap_or(udiv_default(lhs, rhs)))),
            (U64::from(lhs) % rhs, U64::from(lhs.checked_rem(rhs).unwrap_or(urem_default(lhs, rhs)))),
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
    fn ops_primitive_native() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56).chain([0]),
            rhs in i8::MIN..i8::MAX,
        ) [
            (S64::from(lhs) + rhs, S64::from(lhs.wrapping_add(rhs as i64))),
            (S64::from(lhs) - rhs, S64::from(lhs.wrapping_sub(rhs as i64))),
            (S64::from(lhs) * rhs, S64::from(lhs.wrapping_mul(rhs as i64))),
            (S64::from(lhs) / rhs, S64::from(lhs.checked_div(rhs as i64).unwrap_or(sdiv_native_default(lhs, rhs)))),
            (S64::from(lhs) % rhs, S64::from(lhs.checked_rem(rhs as i64).unwrap_or(srem_native_default(lhs, rhs)))),
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
            lhs in ndassert::range!(u64, 56).chain([0]),
            rhs in u8::MIN..u8::MAX,
        ) [
            (U64::from(lhs) + rhs, U64::from(lhs.wrapping_add(rhs as u64))),
            (U64::from(lhs) - rhs, U64::from(lhs.wrapping_sub(rhs as u64))),
            (U64::from(lhs) * rhs, U64::from(lhs.wrapping_mul(rhs as u64))),
            (U64::from(lhs) / rhs, U64::from(lhs.checked_div(rhs as u64).unwrap_or(udiv_native_default(lhs, rhs)))),
            (U64::from(lhs) % rhs, U64::from(lhs.checked_rem(rhs as u64).unwrap_or(urem_native_default(lhs, rhs)))),
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
    #[rustfmt::skip]
    fn ops_assign() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([0]),
            rhs in ndassert::range!(i64, 56, 1).chain([0]),
        ) [
            ({let mut val = S64::from(lhs); val += S64::from(rhs); val }, S64::from(lhs.wrapping_add(rhs))),
            ({let mut val = S64::from(lhs); val -= S64::from(rhs); val }, S64::from(lhs.wrapping_sub(rhs))),
            ({let mut val = S64::from(lhs); val *= S64::from(rhs); val }, S64::from(lhs.wrapping_mul(rhs))),
            ({let mut val = S64::from(lhs); val /= S64::from(rhs); val }, S64::from(lhs.checked_div(rhs).unwrap_or(sdiv_default(lhs, rhs)))),
            ({let mut val = S64::from(lhs); val %= S64::from(rhs); val }, S64::from(lhs.checked_rem(rhs).unwrap_or(srem_default(lhs, rhs)))),
            ({let mut val = S64::from(lhs); val |= S64::from(rhs); val }, S64::from(lhs | rhs)),
            ({let mut val = S64::from(lhs); val &= S64::from(rhs); val }, S64::from(lhs & rhs)),
            ({let mut val = S64::from(lhs); val ^= S64::from(rhs); val }, S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0]),
            rhs in ndassert::range!(u64, 56, 1).chain([0]),
        ) [
            ({ let mut val = U64::from(lhs); val += U64::from(rhs); val }, U64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = U64::from(lhs); val -= U64::from(rhs); val }, U64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = U64::from(lhs); val *= U64::from(rhs); val }, U64::from(lhs.wrapping_mul(rhs))),
            ({ let mut val = U64::from(lhs); val /= U64::from(rhs); val }, U64::from(lhs.checked_div(rhs).unwrap_or(udiv_default(lhs, rhs)))),
            ({ let mut val = U64::from(lhs); val %= U64::from(rhs); val }, U64::from(lhs.checked_rem(rhs).unwrap_or(urem_default(lhs, rhs)))),
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
    #[rustfmt::skip]
    fn ops_primitive_assign() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).chain([0]),
            rhs in ndassert::range!(i64, 56, 1).chain([0]),
        ) [
            ({ let mut val = S64::from(lhs); val += rhs; val }, S64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = S64::from(lhs); val -= rhs; val }, S64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = S64::from(lhs); val *= rhs; val }, S64::from(lhs.wrapping_mul(rhs))),
            ({ let mut val = S64::from(lhs); val /= rhs; val }, S64::from(lhs.checked_div(rhs).unwrap_or(sdiv_default(lhs, rhs)))),
            ({ let mut val = S64::from(lhs); val %= rhs; val }, S64::from(lhs.checked_rem(rhs).unwrap_or(srem_default(lhs, rhs)))),
            ({ let mut val = S64::from(lhs); val |= rhs; val }, S64::from(lhs | rhs)),
            ({ let mut val = S64::from(lhs); val &= rhs; val }, S64::from(lhs & rhs)),
            ({ let mut val = S64::from(lhs); val ^= rhs; val }, S64::from(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).chain([0]),
            rhs in ndassert::range!(u64, 56, 1).chain([0]),
        ) [
            ({ let mut val = U64::from(lhs); val += rhs; val }, U64::from(lhs.wrapping_add(rhs))),
            ({ let mut val = U64::from(lhs); val -= rhs; val }, U64::from(lhs.wrapping_sub(rhs))),
            ({ let mut val = U64::from(lhs); val *= rhs; val }, U64::from(lhs.wrapping_mul(rhs))),
            ({ let mut val = U64::from(lhs); val /= rhs; val }, U64::from(lhs.checked_div(rhs).unwrap_or(udiv_default(lhs, rhs)))),
            ({ let mut val = U64::from(lhs); val %= rhs; val }, U64::from(lhs.checked_rem(rhs).unwrap_or(urem_default(lhs, rhs)))),
            ({ let mut val = U64::from(lhs); val |= rhs; val }, U64::from(lhs | rhs)),
            ({ let mut val = U64::from(lhs); val &= rhs; val }, U64::from(lhs & rhs)),
            ({ let mut val = U64::from(lhs); val ^= rhs; val }, U64::from(lhs ^ rhs)),
        ] }
    }

    #[test]
    #[rustfmt::skip]
    fn ops_primitive_native_assign() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56).chain([0]),
            rhs in i8::MIN..i8::MAX,
        ) [
            ({ let mut val = S64::from(lhs); val += rhs; val }, S64::from(lhs.wrapping_add(rhs as i64))),
            ({ let mut val = S64::from(lhs); val -= rhs; val }, S64::from(lhs.wrapping_sub(rhs as i64))),
            ({ let mut val = S64::from(lhs); val *= rhs; val }, S64::from(lhs.wrapping_mul(rhs as i64))),
            ({ let mut val = S64::from(lhs); val /= rhs; val }, S64::from(lhs.checked_div(rhs as i64).unwrap_or(sdiv_native_default(lhs, rhs)))),
            ({ let mut val = S64::from(lhs); val %= rhs; val }, S64::from(lhs.checked_rem(rhs as i64).unwrap_or(srem_native_default(lhs, rhs)))),
            ({ let mut val = S64::from(lhs); val |= rhs; val }, S64::from(lhs | rhs as i64)),
            ({ let mut val = S64::from(lhs); val &= rhs; val }, S64::from(lhs & rhs as i64)),
            ({ let mut val = S64::from(lhs); val ^= rhs; val }, S64::from(lhs ^ rhs as i64)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56).chain([0]),
            rhs in u8::MIN..u8::MAX,
        ) [
            ({ let mut val = U64::from(lhs); val += rhs; val }, U64::from(lhs.wrapping_add(rhs as u64))),
            ({ let mut val = U64::from(lhs); val -= rhs; val }, U64::from(lhs.wrapping_sub(rhs as u64))),
            ({ let mut val = U64::from(lhs); val *= rhs; val }, U64::from(lhs.wrapping_mul(rhs as u64))),
            ({ let mut val = U64::from(lhs); val /= rhs; val }, U64::from(lhs.checked_div(rhs as u64).unwrap_or(udiv_native_default(lhs, rhs)))),
            ({ let mut val = U64::from(lhs); val %= rhs; val }, U64::from(lhs.checked_rem(rhs as u64).unwrap_or(urem_native_default(lhs, rhs)))),
            ({ let mut val = U64::from(lhs); val |= rhs; val }, U64::from(lhs | rhs as u64)),
            ({ let mut val = U64::from(lhs); val &= rhs; val }, U64::from(lhs & rhs as u64)),
            ({ let mut val = U64::from(lhs); val ^= rhs; val }, U64::from(lhs ^ rhs as u64)),
        ] }
    }
}

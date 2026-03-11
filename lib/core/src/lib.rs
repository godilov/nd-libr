#![doc = include_str!("../README.md")]

use std::{
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
    str::FromStr,
};

pub mod iter {
    /// Extends standard Iterator.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait IteratorExt: Iterator {
        /// Collects iterator with pre-allocated collection by value.
        ///
        /// ```rust
        /// # use ndcore::iter::IteratorExt;
        ///
        /// // Collects 4096 at max
        /// let arr = (0..=4096).into_iter().collect_with([0; 4096]);
        /// ```
        ///
        /// For more information and examples, see [crate-level](crate) documentation.
        fn collect_with<Dst>(&mut self, mut dst: Dst) -> Dst
        where
            for<'value> &'value mut Dst: IntoIterator<Item = &'value mut Self::Item>,
        {
            dst.into_iter().zip(self).for_each(|(dst, src)| *dst = src);
            dst
        }

        /// Collects iterator with pre-allocated collection by mutable reference.
        ///
        /// ```rust
        /// # use ndcore::iter::IteratorExt;
        ///
        /// let mut arr = [0; 4096];
        ///
        /// // Collects 4096 at max
        /// let arr_mut = (0..=4096).into_iter().collect_with_mut(&mut arr);
        /// ```
        ///
        /// For more information and examples, see [crate-level](crate) documentation.
        fn collect_with_mut<'dst, Dst>(&mut self, dst: &'dst mut Dst) -> &'dst mut Dst
        where
            for<'value> &'value mut Dst: IntoIterator<Item = &'value mut Self::Item>,
        {
            dst.into_iter().zip(self).for_each(|(dst, src)| *dst = src);
            dst
        }
    }

    impl<Iter: Iterator> IteratorExt for Iter {}
}

pub mod convert {
    use super::*;

    /// `Nd` alternative to [`From`] for describing non-failable conversions.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdFrom<T>: Sized {
        /// Convert from `T` into `Self` in non-failable way.
        fn nd_from(value: T) -> Self;
    }

    /// `Nd` alternative to [`TryFrom`] for describing failable conversions.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdTryFrom<T>: Sized {
        type Error;

        /// Convert from `T` into `Self` in failable way.
        fn nd_try_from(value: T) -> Result<Self, Self::Error>;
    }

    /// `Nd` alternative to [`std::str::FromStr`] for describing interpreted conversions.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdFromStr<Ctx>: Sized {
        type Err;

        /// Convert from `&str` into `Self` in interpreted way.
        fn nd_from_str(s: &str, ctx: Ctx) -> Result<Self, Self::Err>;
    }

    impl<U, V: From<U>> NdFrom<U> for V {
        fn nd_from(value: U) -> Self {
            V::from(value)
        }
    }

    impl<U, V: TryFrom<U>> NdTryFrom<U> for V {
        type Error = V::Error;

        fn nd_try_from(value: U) -> Result<Self, Self::Error> {
            V::try_from(value)
        }
    }

    impl<T: FromStr> NdFromStr<()> for T {
        type Err = T::Err;

        fn nd_from_str(s: &str, _: ()) -> Result<Self, Self::Err> {
            T::from_str(s)
        }
    }
}

pub mod ops {
    use super::*;

    macro_rules! nd_ops_impl {
        (@signed [$($primitive:ty),+ $(,)?]) => {
            $(nd_ops_impl!(@signed $primitive);)+
        };
        (@unsigned [$($primitive:ty),+ $(,)?]) => {
            $(nd_ops_impl!(@unsigned $primitive);)+
        };
        (@signed $primitive:ty $(,)?) => {
            ndops::def! { @ndun crate (value: &$primitive) -> $primitive, [
                ! !value,
                - -value,
                - @checked value.checked_neg(),
                - @strict value.strict_neg(),
                - @wrapping value.wrapping_neg(),
                - @saturating value.saturating_neg(),
                - @overflowing value.overflowing_neg(),
            ] }

            nd_ops_impl!(@impl $primitive);
        };
        (@unsigned $primitive:ty $(,)?) => {
            ndops::def! { @ndun crate (value: &$primitive) -> $primitive, [
                ! !value,
            ] }

            nd_ops_impl!(@impl $primitive);
        };
        (@impl $primitive:ty $(,)?) => {
            ndops::def! { @ndbin crate (lhs: &$primitive, rhs: &$primitive) -> $primitive, [
                + lhs.add(rhs),
                - lhs.sub(rhs),
                * lhs.mul(rhs),
                / lhs.div(rhs),
                % lhs.rem(rhs),
                | lhs.bitor(rhs),
                & lhs.bitand(rhs),
                ^ lhs.bitxor(rhs),
                + @checked lhs.checked_add(*rhs),
                - @checked lhs.checked_sub(*rhs),
                * @checked lhs.checked_mul(*rhs),
                / @checked lhs.checked_div(*rhs),
                % @checked lhs.checked_rem(*rhs),
                + @strict lhs.strict_add(*rhs),
                - @strict lhs.strict_sub(*rhs),
                * @strict lhs.strict_mul(*rhs),
                / @strict lhs.strict_div(*rhs),
                % @strict lhs.strict_rem(*rhs),
                + @wrapping lhs.wrapping_add(*rhs),
                - @wrapping lhs.wrapping_sub(*rhs),
                * @wrapping lhs.wrapping_mul(*rhs),
                / @wrapping lhs.wrapping_div(*rhs),
                % @wrapping lhs.wrapping_rem(*rhs),
                + @saturating lhs.saturating_add(*rhs),
                - @saturating lhs.saturating_sub(*rhs),
                * @saturating lhs.saturating_mul(*rhs),
                / @saturating lhs.saturating_div(*rhs),
                % @saturating lhs.wrapping_rem(*rhs),
                + @overflowing lhs.overflowing_add(*rhs),
                - @overflowing lhs.overflowing_sub(*rhs),
                * @overflowing lhs.overflowing_mul(*rhs),
                / @overflowing lhs.overflowing_div(*rhs),
                % @overflowing lhs.overflowing_rem(*rhs),
            ] }

            ndops::def! { @ndbin crate (lhs: &$primitive, rhs: usize) -> $primitive, [
                << lhs.shl(rhs),
                >> lhs.shr(rhs),
                << @checked lhs.checked_shl(rhs as u32),
                >> @checked lhs.checked_shr(rhs as u32),
                << @overflowing lhs.overflowing_shl(rhs as u32),
                >> @overflowing lhs.overflowing_shr(rhs as u32),
                << @unbounded lhs.unbounded_shl(rhs as u32),
                >> @unbounded lhs.unbounded_shr(rhs as u32),
            ] }

            ndops::def! { @ndmut crate (lhs: &mut $primitive, rhs: &$primitive), [
                += lhs.add_assign(rhs),
                -= lhs.sub_assign(rhs),
                *= lhs.mul_assign(rhs),
                /= lhs.div_assign(rhs),
                %= lhs.rem_assign(rhs),
                |= lhs.bitor_assign(rhs),
                &= lhs.bitand_assign(rhs),
                ^= lhs.bitxor_assign(rhs),
                += @strict *lhs = lhs.strict_add(*rhs),
                -= @strict *lhs = lhs.strict_sub(*rhs),
                *= @strict *lhs = lhs.strict_mul(*rhs),
                /= @strict *lhs = lhs.strict_div(*rhs),
                %= @strict *lhs = lhs.strict_rem(*rhs),
                += @wrapping *lhs = lhs.wrapping_add(*rhs),
                -= @wrapping *lhs = lhs.wrapping_sub(*rhs),
                *= @wrapping *lhs = lhs.wrapping_mul(*rhs),
                /= @wrapping *lhs = lhs.wrapping_div(*rhs),
                %= @wrapping *lhs = lhs.wrapping_rem(*rhs),
                += @saturating *lhs = lhs.saturating_add(*rhs),
                -= @saturating *lhs = lhs.saturating_sub(*rhs),
                *= @saturating *lhs = lhs.saturating_mul(*rhs),
                /= @saturating *lhs = lhs.saturating_div(*rhs),
                %= @saturating *lhs = lhs.wrapping_rem(*rhs),
            ] }

            ndops::def! { @ndmut crate (lhs: &mut $primitive, rhs: usize), [
                <<= lhs.shl_assign(rhs),
                >>= lhs.shr_assign(rhs),
                <<= @unbounded *lhs = lhs.unbounded_shl(rhs as u32),
                >>= @unbounded *lhs = lhs.unbounded_shr(rhs as u32),
            ] }
        };
    }

    /// `Nd` alternative to [`std::ops::Not`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNot<Value = Self> {
        type Type;

        fn nd_not(value: &Value) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Neg`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNeg<Value = Self> {
        type Type;

        fn nd_neg(value: &Value) -> Self::Type;
    }

    /// `Nd` variant for describing checked neg operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNegChecked<Value = Self> {
        type Type;

        fn nd_neg_checked(value: &Value) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing strict neg operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNegStrict<Value = Self> {
        type Type;

        fn nd_neg_strict(value: &Value) -> Self::Type;
    }

    /// `Nd` variant for describing wrapping neg operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNegWrapping<Value = Self> {
        type Type;

        fn nd_neg_wrapping(value: &Value) -> Self::Type;
    }

    /// `Nd` variant for describing saturating neg operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNegSaturating<Value = Self> {
        type Type;

        fn nd_neg_saturating(value: &Value) -> Self::Type;
    }

    /// `Nd` variant for describing overflowing neg operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNegOverflowing<Value = Self> {
        type Type;

        fn nd_neg_overflowing(value: &Value) -> (Self::Type, bool);
    }

    /// `Nd` alternative to [`std::ops::Add`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAdd<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_add(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Sub`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSub<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_sub(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Mul`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMul<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_mul(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Div`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDiv<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_div(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Rem`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRem<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_rem(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::BitOr`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitOr<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_bitor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::BitAnd`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitAnd<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_bitand(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::BitXor`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitXor<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_bitxor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Shl`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShl<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shl(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Shr`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShr<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shr(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing checked add operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_add_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing checked sub operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_sub_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing checked mul operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_mul_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing checked div operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_div_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing checked rem operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_rem_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing checked shl operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlChecked<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shl_checked(lhs: &Lhs, rhs: Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing checked shr operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrChecked<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shr_checked(lhs: &Lhs, rhs: Rhs) -> Option<Self::Type>;
    }

    /// `Nd` variant for describing strict add operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddStrict<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_add_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing strict sub operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubStrict<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_sub_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing strict mul operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulStrict<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_mul_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing strict div operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivStrict<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_div_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing strict rem operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemStrict<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_rem_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing strict shl operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlStrict<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shl_strict(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing strict shr operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrStrict<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shr_strict(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing wrapping add operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_add_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing wrapping sub operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_sub_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing wrapping mul operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_mul_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing wrapping div operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_div_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing wrapping rem operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_rem_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing saturating add operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_add_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing saturating sub operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_sub_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing saturating mul operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_mul_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing saturating div operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_div_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing saturating rem operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_rem_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing overflowing add operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_add_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing overflowing sub operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_sub_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing overflowing mul operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_mul_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing overflowing div operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_div_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing overflowing rem operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_rem_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing overflowing shl operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlOverflowing<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shl_overflowing(lhs: &Lhs, rhs: Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing overflowing shr operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrOverflowing<Lhs = Self, Rhs = usize> {
        type Type;

        fn nd_shr_overflowing(lhs: &Lhs, rhs: Rhs) -> (Self::Type, bool);
    }

    /// `Nd` variant for describing unbounded shl operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlUnbounded<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_shl_unbounded(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` variant for describing unbounded shr operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrUnbounded<Lhs = Self, Rhs = Self> {
        type Type;

        fn nd_shr_unbounded(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::AddAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddAssign<Lhs = Self, Rhs = Self> {
        fn nd_add_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::SubAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubAssign<Lhs = Self, Rhs = Self> {
        fn nd_sub_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::MulAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulAssign<Lhs = Self, Rhs = Self> {
        fn nd_mul_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::DivAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivAssign<Lhs = Self, Rhs = Self> {
        fn nd_div_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::RemAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemAssign<Lhs = Self, Rhs = Self> {
        fn nd_rem_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::BitOrAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitOrAssign<Lhs = Self, Rhs = Self> {
        fn nd_bitor_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::BitAndAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitAndAssign<Lhs = Self, Rhs = Self> {
        fn nd_bitand_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::BitXorAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitXorAssign<Lhs = Self, Rhs = Self> {
        fn nd_bitxor_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::ShlAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlAssign<Lhs = Self, Rhs = usize> {
        fn nd_shl_assign(lhs: &mut Lhs, rhs: Rhs);
    }

    /// `Nd` alternative to [`std::ops::ShrAssign`] for describing operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrAssign<Lhs = Self, Rhs = usize> {
        fn nd_shr_assign(lhs: &mut Lhs, rhs: Rhs);
    }

    /// `Nd` variant for describing strict add assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddAssignStrict<Lhs = Self, Rhs = Self> {
        fn nd_add_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing strict sub assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubAssignStrict<Lhs = Self, Rhs = Self> {
        fn nd_sub_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing strict mul assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulAssignStrict<Lhs = Self, Rhs = Self> {
        fn nd_mul_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing strict div assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivAssignStrict<Lhs = Self, Rhs = Self> {
        fn nd_div_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing strict rem assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemAssignStrict<Lhs = Self, Rhs = Self> {
        fn nd_rem_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing strict shl assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlAssignStrict<Lhs = Self, Rhs = usize> {
        fn nd_shl_assign_strict(lhs: &mut Lhs, rhs: Rhs);
    }

    /// `Nd` variant for describing strict shr assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrAssignStrict<Lhs = Self, Rhs = usize> {
        fn nd_shr_assign_strict(lhs: &mut Lhs, rhs: Rhs);
    }

    /// `Nd` variant for describing wrapping add assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddAssignWrapping<Lhs = Self, Rhs = Self> {
        fn nd_add_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing wrapping sub assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubAssignWrapping<Lhs = Self, Rhs = Self> {
        fn nd_sub_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing wrapping mul assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulAssignWrapping<Lhs = Self, Rhs = Self> {
        fn nd_mul_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing wrapping div assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivAssignWrapping<Lhs = Self, Rhs = Self> {
        fn nd_div_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing wrapping rem assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemAssignWrapping<Lhs = Self, Rhs = Self> {
        fn nd_rem_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing saturating add assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddAssignSaturating<Lhs = Self, Rhs = Self> {
        fn nd_add_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing saturating sub assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubAssignSaturating<Lhs = Self, Rhs = Self> {
        fn nd_sub_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing saturating mul assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulAssignSaturating<Lhs = Self, Rhs = Self> {
        fn nd_mul_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing saturating div assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivAssignSaturating<Lhs = Self, Rhs = Self> {
        fn nd_div_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing saturating rem assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemAssignSaturating<Lhs = Self, Rhs = Self> {
        fn nd_rem_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` variant for describing unbounded shl assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlAssignUnbounded<Lhs = Self, Rhs = usize> {
        fn nd_shl_assign_unbounded(lhs: &mut Lhs, rhs: Rhs);
    }

    /// `Nd` variant for describing unbounded shr assign operations.
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrAssignUnbounded<Lhs = Self, Rhs = usize> {
        fn nd_shr_assign_unbounded(lhs: &mut Lhs, rhs: Rhs);
    }

    /// Aggregate trait for describing types that support all standard Rust binary operations of `Std-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait Ops<Rhs = Self, ShiftRhs = usize>:
        Sized
        + Copy
        + Add<Rhs, Output = Self::Type>
        + Sub<Rhs, Output = Self::Type>
        + Mul<Rhs, Output = Self::Type>
        + Div<Rhs, Output = Self::Type>
        + Rem<Rhs, Output = Self::Type>
        + BitOr<Rhs, Output = Self::Type>
        + BitAnd<Rhs, Output = Self::Type>
        + BitXor<Rhs, Output = Self::Type>
        + Shl<ShiftRhs, Output = Self::Type>
        + Shr<ShiftRhs, Output = Self::Type>
    {
        type Type;
    }

    /// Aggregate trait for describing types that support all standard Rust assign operations of `Std-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait OpsAssign<Rhs = Self, ShiftRhs = usize>:
        Copy
        + AddAssign<Rhs>
        + SubAssign<Rhs>
        + MulAssign<Rhs>
        + DivAssign<Rhs>
        + RemAssign<Rhs>
        + BitOrAssign<Rhs>
        + BitAndAssign<Rhs>
        + BitXorAssign<Rhs>
        + ShlAssign<ShiftRhs>
        + ShrAssign<ShiftRhs>
    {
    }

    /// Aggregate trait for describing types that support all standard Rust binary operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOps<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAdd<Lhs, Rhs, Type = Self::All>
        + NdSub<Lhs, Rhs, Type = Self::All>
        + NdMul<Lhs, Rhs, Type = Self::All>
        + NdDiv<Lhs, Rhs, Type = Self::All>
        + NdRem<Lhs, Rhs, Type = Self::All>
        + NdBitOr<Lhs, Rhs, Type = Self::All>
        + NdBitAnd<Lhs, Rhs, Type = Self::All>
        + NdBitXor<Lhs, Rhs, Type = Self::All>
        + NdShl<Lhs, ShiftRhs, Type = Self::All>
        + NdShr<Lhs, ShiftRhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all checked operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsChecked<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddChecked<Lhs, Rhs, Type = Self::All>
        + NdSubChecked<Lhs, Rhs, Type = Self::All>
        + NdMulChecked<Lhs, Rhs, Type = Self::All>
        + NdDivChecked<Lhs, Rhs, Type = Self::All>
        + NdRemChecked<Lhs, Rhs, Type = Self::All>
        + NdShlChecked<Lhs, ShiftRhs, Type = Self::All>
        + NdShrChecked<Lhs, ShiftRhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all strict operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsStrict<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddStrict<Lhs, Rhs, Type = Self::All>
        + NdSubStrict<Lhs, Rhs, Type = Self::All>
        + NdMulStrict<Lhs, Rhs, Type = Self::All>
        + NdDivStrict<Lhs, Rhs, Type = Self::All>
        + NdRemStrict<Lhs, Rhs, Type = Self::All>
        + NdShlStrict<Lhs, ShiftRhs, Type = Self::All>
        + NdShrStrict<Lhs, ShiftRhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all wrapping operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsWrapping<Lhs = Self, Rhs = Self>:
        NdAddWrapping<Lhs, Rhs, Type = Self::All>
        + NdSubWrapping<Lhs, Rhs, Type = Self::All>
        + NdMulWrapping<Lhs, Rhs, Type = Self::All>
        + NdDivWrapping<Lhs, Rhs, Type = Self::All>
        + NdRemWrapping<Lhs, Rhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all saturating operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsSaturating<Lhs = Self, Rhs = Self>:
        NdAddSaturating<Lhs, Rhs, Type = Self::All>
        + NdSubSaturating<Lhs, Rhs, Type = Self::All>
        + NdMulSaturating<Lhs, Rhs, Type = Self::All>
        + NdDivSaturating<Lhs, Rhs, Type = Self::All>
        + NdRemSaturating<Lhs, Rhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all overflowing operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsOverflowing<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddOverflowing<Lhs, Rhs, Type = Self::All>
        + NdSubOverflowing<Lhs, Rhs, Type = Self::All>
        + NdMulOverflowing<Lhs, Rhs, Type = Self::All>
        + NdDivOverflowing<Lhs, Rhs, Type = Self::All>
        + NdRemOverflowing<Lhs, Rhs, Type = Self::All>
        + NdShlOverflowing<Lhs, ShiftRhs, Type = Self::All>
        + NdShrOverflowing<Lhs, ShiftRhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all unbounded operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsUnbounded<Lhs = Self, Rhs = Self>:
        NdShlUnbounded<Lhs, Rhs, Type = Self::All> + NdShrUnbounded<Lhs, Rhs, Type = Self::All>
    {
        type All;
    }

    /// Aggregate trait for describing types that support all standard Rust assign operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsAssign<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddAssign<Lhs, Rhs>
        + NdSubAssign<Lhs, Rhs>
        + NdMulAssign<Lhs, Rhs>
        + NdDivAssign<Lhs, Rhs>
        + NdRemAssign<Lhs, Rhs>
        + NdBitOrAssign<Lhs, Rhs>
        + NdBitAndAssign<Lhs, Rhs>
        + NdBitXorAssign<Lhs, Rhs>
        + NdShlAssign<Lhs, ShiftRhs>
        + NdShrAssign<Lhs, ShiftRhs>
    {
    }

    /// Aggregate trait for describing types that support all strict assign operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsAssignStrict<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddAssignStrict<Lhs, Rhs>
        + NdSubAssignStrict<Lhs, Rhs>
        + NdMulAssignStrict<Lhs, Rhs>
        + NdDivAssignStrict<Lhs, Rhs>
        + NdRemAssignStrict<Lhs, Rhs>
        + NdShlAssignStrict<Lhs, Rhs>
        + NdShrAssignStrict<Lhs, Rhs>
    {
    }

    /// Aggregate trait for describing types that support all wrapping assign operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsAssignWrapping<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddAssignWrapping<Lhs, Rhs>
        + NdSubAssignWrapping<Lhs, Rhs>
        + NdMulAssignWrapping<Lhs, Rhs>
        + NdDivAssignWrapping<Lhs, Rhs>
        + NdRemAssignWrapping<Lhs, Rhs>
    {
    }

    /// Aggregate trait for describing types that support all saturating assign operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsAssignSaturating<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdAddAssignSaturating<Lhs, Rhs>
        + NdSubAssignSaturating<Lhs, Rhs>
        + NdMulAssignSaturating<Lhs, Rhs>
        + NdDivAssignSaturating<Lhs, Rhs>
        + NdRemAssignSaturating<Lhs, Rhs>
    {
    }

    /// Aggregate trait for describing types that support all unbounded assign operations of `Nd-kind`
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdOpsAssignUnbounded<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
        NdShlAssignUnbounded<Lhs, Rhs> + NdShrAssignUnbounded<Lhs, Rhs>
    {
    }

    impl<Lhs, Rhs, ShiftRhs, Type> Ops<Rhs, ShiftRhs> for Lhs
    where
        Self: Sized
            + Clone
            + Copy
            + Add<Rhs, Output = Type>
            + Sub<Rhs, Output = Type>
            + Mul<Rhs, Output = Type>
            + Div<Rhs, Output = Type>
            + Rem<Rhs, Output = Type>
            + BitOr<Rhs, Output = Type>
            + BitAnd<Rhs, Output = Type>
            + BitXor<Rhs, Output = Type>
            + Shl<ShiftRhs, Output = Type>
            + Shr<ShiftRhs, Output = Type>,
    {
        type Type = Type;
    }

    impl<Lhs, Rhs, ShiftRhs> OpsAssign<Rhs, ShiftRhs> for Lhs where
        Self: Copy
            + AddAssign<Rhs>
            + SubAssign<Rhs>
            + MulAssign<Rhs>
            + DivAssign<Rhs>
            + RemAssign<Rhs>
            + BitOrAssign<Rhs>
            + BitAndAssign<Rhs>
            + BitXorAssign<Rhs>
            + ShlAssign<ShiftRhs>
            + ShrAssign<ShiftRhs>
    {
    }

    impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOps<Lhs, Rhs, ShiftRhs> for Any
    where
        Any: NdAdd<Lhs, Rhs, Type = Type>
            + NdSub<Lhs, Rhs, Type = Type>
            + NdMul<Lhs, Rhs, Type = Type>
            + NdDiv<Lhs, Rhs, Type = Type>
            + NdRem<Lhs, Rhs, Type = Type>
            + NdBitOr<Lhs, Rhs, Type = Type>
            + NdBitAnd<Lhs, Rhs, Type = Type>
            + NdBitXor<Lhs, Rhs, Type = Type>
            + NdShl<Lhs, ShiftRhs, Type = Type>
            + NdShr<Lhs, ShiftRhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOpsChecked<Lhs, Rhs, ShiftRhs> for Any
    where
        Any: NdAddChecked<Lhs, Rhs, Type = Type>
            + NdSubChecked<Lhs, Rhs, Type = Type>
            + NdMulChecked<Lhs, Rhs, Type = Type>
            + NdDivChecked<Lhs, Rhs, Type = Type>
            + NdRemChecked<Lhs, Rhs, Type = Type>
            + NdShlChecked<Lhs, ShiftRhs, Type = Type>
            + NdShrChecked<Lhs, ShiftRhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOpsStrict<Lhs, Rhs, ShiftRhs> for Any
    where
        Any: NdAddStrict<Lhs, Rhs, Type = Type>
            + NdSubStrict<Lhs, Rhs, Type = Type>
            + NdMulStrict<Lhs, Rhs, Type = Type>
            + NdDivStrict<Lhs, Rhs, Type = Type>
            + NdRemStrict<Lhs, Rhs, Type = Type>
            + NdShlStrict<Lhs, ShiftRhs, Type = Type>
            + NdShrStrict<Lhs, ShiftRhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, Type> NdOpsWrapping<Lhs, Rhs> for Any
    where
        Any: NdAddWrapping<Lhs, Rhs, Type = Type>
            + NdSubWrapping<Lhs, Rhs, Type = Type>
            + NdMulWrapping<Lhs, Rhs, Type = Type>
            + NdDivWrapping<Lhs, Rhs, Type = Type>
            + NdRemWrapping<Lhs, Rhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, Type> NdOpsSaturating<Lhs, Rhs> for Any
    where
        Any: NdAddSaturating<Lhs, Rhs, Type = Type>
            + NdSubSaturating<Lhs, Rhs, Type = Type>
            + NdMulSaturating<Lhs, Rhs, Type = Type>
            + NdDivSaturating<Lhs, Rhs, Type = Type>
            + NdRemSaturating<Lhs, Rhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOpsOverflowing<Lhs, Rhs, ShiftRhs> for Any
    where
        Any: NdAddOverflowing<Lhs, Rhs, Type = Type>
            + NdSubOverflowing<Lhs, Rhs, Type = Type>
            + NdMulOverflowing<Lhs, Rhs, Type = Type>
            + NdDivOverflowing<Lhs, Rhs, Type = Type>
            + NdRemOverflowing<Lhs, Rhs, Type = Type>
            + NdShlOverflowing<Lhs, ShiftRhs, Type = Type>
            + NdShrOverflowing<Lhs, ShiftRhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, Type> NdOpsUnbounded<Lhs, Rhs> for Any
    where
        Any: NdShlUnbounded<Lhs, Rhs, Type = Type> + NdShrUnbounded<Lhs, Rhs, Type = Type>,
    {
        type All = Type;
    }

    impl<Any, Lhs, Rhs, ShiftRhs> NdOpsAssign<Lhs, Rhs, ShiftRhs> for Any where
        Any: NdAddAssign<Lhs, Rhs>
            + NdSubAssign<Lhs, Rhs>
            + NdMulAssign<Lhs, Rhs>
            + NdDivAssign<Lhs, Rhs>
            + NdRemAssign<Lhs, Rhs>
            + NdBitOrAssign<Lhs, Rhs>
            + NdBitAndAssign<Lhs, Rhs>
            + NdBitXorAssign<Lhs, Rhs>
            + NdShlAssign<Lhs, ShiftRhs>
            + NdShrAssign<Lhs, ShiftRhs>
    {
    }

    impl<Any, Lhs, Rhs> NdOpsAssignStrict<Lhs, Rhs> for Any where
        Any: NdAddAssignStrict<Lhs, Rhs>
            + NdSubAssignStrict<Lhs, Rhs>
            + NdMulAssignStrict<Lhs, Rhs>
            + NdDivAssignStrict<Lhs, Rhs>
            + NdRemAssignStrict<Lhs, Rhs>
            + NdShlAssignStrict<Lhs, Rhs>
            + NdShrAssignStrict<Lhs, Rhs>
    {
    }

    impl<Any, Lhs, Rhs> NdOpsAssignWrapping<Lhs, Rhs> for Any where
        Any: NdAddAssignWrapping<Lhs, Rhs>
            + NdSubAssignWrapping<Lhs, Rhs>
            + NdMulAssignWrapping<Lhs, Rhs>
            + NdDivAssignWrapping<Lhs, Rhs>
            + NdRemAssignWrapping<Lhs, Rhs>
    {
    }

    impl<Any, Lhs, Rhs> NdOpsAssignSaturating<Lhs, Rhs> for Any where
        Any: NdAddAssignSaturating<Lhs, Rhs>
            + NdSubAssignSaturating<Lhs, Rhs>
            + NdMulAssignSaturating<Lhs, Rhs>
            + NdDivAssignSaturating<Lhs, Rhs>
            + NdRemAssignSaturating<Lhs, Rhs>
    {
    }

    impl<Any, Lhs, Rhs> NdOpsAssignUnbounded<Lhs, Rhs> for Any where
        Any: NdShlAssignUnbounded<Lhs, Rhs> + NdShrAssignUnbounded<Lhs, Rhs>
    {
    }

    nd_ops_impl!(@signed [i8, i16, i32, i64, i128, isize]);
    nd_ops_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);
}

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
            ndops::all_auto! { @ndun crate (&value: &$primitive) -> $primitive, (value) [-, !] }

            ndops::all_auto! { @ndbin crate (&lhs: &$primitive, &rhs: &$primitive) -> $primitive, (lhs) (rhs) [+, -, *, /, %, |, &, ^] }
            ndops::all_auto! { @ndmut crate (lhs: &mut $primitive, &rhs: &$primitive), (*lhs) (rhs) [+=, -=, *=, /=, %=, |=, &=, ^=] }

            ndops::all_auto! { @ndbin crate (&lhs: &$primitive, rhs: usize) -> $primitive, (lhs) (rhs) [<<, >>] }
            ndops::all_auto! { @ndmut crate (lhs: &mut $primitive, rhs: usize), (*lhs) (rhs) [<<=, >>=] }
        };
        (@unsigned $primitive:ty $(,)?) => {
            ndops::all_auto! { @ndun crate (&value: &$primitive) -> $primitive, (value) [!] }

            ndops::all_auto! { @ndbin crate (&lhs: &$primitive, &rhs: &$primitive) -> $primitive, (lhs) (rhs) [+, -, *, /, %, |, &, ^] }
            ndops::all_auto! { @ndmut crate (lhs: &mut $primitive, &rhs: &$primitive), (*lhs) (rhs) [+=, -=, *=, /=, %=, |=, &=, ^=] }

            ndops::all_auto! { @ndbin crate (&lhs: &$primitive, rhs: usize) -> $primitive, (lhs) (rhs) [<<, >>] }
            ndops::all_auto! { @ndmut crate (lhs: &mut $primitive, rhs: usize), (*lhs) (rhs) [<<=, >>=] }
        };
    }

    /// `Nd` alternative to [`std::ops::Neg`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNeg<Value = Self> {
        type Type;

        fn neg(value: &Value) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Not`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdNot<Value = Self> {
        type Type;

        fn not(value: &Value) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Add`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAdd<Lhs = Self, Rhs = Self> {
        type Type;

        fn add(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Sub`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSub<Lhs = Self, Rhs = Self> {
        type Type;

        fn sub(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Mul`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMul<Lhs = Self, Rhs = Self> {
        type Type;

        fn mul(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Div`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDiv<Lhs = Self, Rhs = Self> {
        type Type;

        fn div(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Rem`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRem<Lhs = Self, Rhs = Self> {
        type Type;

        fn rem(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::BitOr`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitOr<Lhs = Self, Rhs = Self> {
        type Type;

        fn bitor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::BitAnd`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitAnd<Lhs = Self, Rhs = Self> {
        type Type;

        fn bitand(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::BitXor`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitXor<Lhs = Self, Rhs = Self> {
        type Type;

        fn bitxor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Shl`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShl<Lhs = Self, Rhs = usize> {
        type Type;

        fn shl(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::Shr`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShr<Lhs = Self, Rhs = usize> {
        type Type;

        fn shr(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    /// `Nd` alternative to [`std::ops::AddAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdAddAssign<Lhs = Self, Rhs = Self> {
        fn add_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::SubAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdSubAssign<Lhs = Self, Rhs = Self> {
        fn sub_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::MulAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdMulAssign<Lhs = Self, Rhs = Self> {
        fn mul_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::DivAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdDivAssign<Lhs = Self, Rhs = Self> {
        fn div_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::RemAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdRemAssign<Lhs = Self, Rhs = Self> {
        fn rem_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::BitOrAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitOrAssign<Lhs = Self, Rhs = Self> {
        fn bitor_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::BitAndAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitAndAssign<Lhs = Self, Rhs = Self> {
        fn bitand_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::BitXorAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdBitXorAssign<Lhs = Self, Rhs = Self> {
        fn bitxor_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    /// `Nd` alternative to [`std::ops::ShlAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShlAssign<Lhs = Self, Rhs = usize> {
        fn shl_assign(lhs: &mut Lhs, rhs: Rhs);
    }

    /// `Nd` alternative to [`std::ops::ShrAssign`] for describing operations
    ///
    /// For more information and examples, see [crate-level](crate) documentation.
    pub trait NdShrAssign<Lhs = Self, Rhs = usize> {
        fn shr_assign(lhs: &mut Lhs, rhs: Rhs);
    }

    pub trait NdAddChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn add_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    pub trait NdSubChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn sub_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    pub trait NdMulChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn mul_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    pub trait NdDivChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn div_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    pub trait NdRemChecked<Lhs = Self, Rhs = Self> {
        type Type;

        fn rem_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
    }

    pub trait NdAddWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn add_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdSubWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn sub_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdMulWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn mul_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdDivWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn div_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdRemWrapping<Lhs = Self, Rhs = Self> {
        type Type;

        fn rem_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdAddSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn add_saturing(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdSubSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn sub_saturing(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdMulSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn mul_saturing(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdDivSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn div_saturing(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdRemSaturating<Lhs = Self, Rhs = Self> {
        type Type;

        fn rem_saturing(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdAddOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn add_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    pub trait NdSubOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn sub_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    pub trait NdMulOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn mul_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    pub trait NdDivOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn div_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    pub trait NdRemOverflowing<Lhs = Self, Rhs = Self> {
        type Type;

        fn rem_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
    }

    pub trait NdShlChecked<Lhs = Self, Rhs = usize> {
        type Type;

        fn shl_checked(lhs: &Lhs, rhs: Rhs) -> Option<Self::Type>;
    }

    pub trait NdShrChecked<Lhs = Self, Rhs = usize> {
        type Type;

        fn shr_checked(lhs: &Lhs, rhs: Rhs) -> Option<Self::Type>;
    }

    pub trait NdShlUnbounded<Lhs = Self, Rhs = Self> {
        type Type;

        fn shl_unbounded(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    pub trait NdShrUnbounded<Lhs = Self, Rhs = Self> {
        type Type;

        fn shr_unbounded(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    pub trait NdAddAssignWrapping<Lhs = Self, Rhs = Self> {
        fn add_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdSubAssignWrapping<Lhs = Self, Rhs = Self> {
        fn sub_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdMulAssignWrapping<Lhs = Self, Rhs = Self> {
        fn mul_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdDivAssignWrapping<Lhs = Self, Rhs = Self> {
        fn div_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdRemAssignWrapping<Lhs = Self, Rhs = Self> {
        fn rem_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdAddAssignSaturating<Lhs = Self, Rhs = Self> {
        fn add_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdSubAssignSaturating<Lhs = Self, Rhs = Self> {
        fn sub_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdMulAssignSaturating<Lhs = Self, Rhs = Self> {
        fn mul_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdDivAssignSaturating<Lhs = Self, Rhs = Self> {
        fn div_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdRemAssignSaturating<Lhs = Self, Rhs = Self> {
        fn rem_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdShlAssignUnbounded<Lhs = Self, Rhs = usize> {
        fn shl_assign_unbounded(lhs: &mut Lhs, rhs: Rhs);
    }

    pub trait NdShrAssignUnbounded<Lhs = Self, Rhs = usize> {
        fn shr_assign_unbounded(lhs: &mut Lhs, rhs: Rhs);
    }

    /// Convenience trait for describing types that support all standard Rust binary operations of `Nd-kind`
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

    /// Convenience trait for describing types that support all standard Rust assign operations of `Nd-kind`
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

    /// Convenience trait for describing types that support all standard Rust binary operations of `Std-kind`
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

    /// Convenience trait for describing types that support all standard Rust assign operations of `Std-kind`
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

    nd_ops_impl!(@signed [i8, i16, i32, i64, i128, isize]);
    nd_ops_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);
}

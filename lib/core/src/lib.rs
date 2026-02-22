#![doc = include_str!("../README.md")]

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

pub mod iter {
    pub trait IteratorExt: Iterator {
        fn collect_with<Dst>(&mut self, mut dst: Dst) -> Dst
        where
            for<'value> &'value mut Dst: IntoIterator<Item = &'value mut Self::Item>,
        {
            dst.into_iter().zip(self).for_each(|(dst, src)| *dst = src);
            dst
        }

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
    pub trait NdFrom<T>: Sized {
        fn nd_from(value: T) -> Self;
    }

    pub trait NdTryFrom<T>: Sized {
        type Error;

        fn nd_try_from(value: T) -> Result<Self, Self::Error>;
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

    pub trait NdNeg<Value = Self> {
        type Type;

        fn neg(value: &Value) -> Self::Type;
    }

    pub trait NdNot<Value = Self> {
        type Type;

        fn not(value: &Value) -> Self::Type;
    }

    pub trait NdAdd<Lhs = Self, Rhs = Self> {
        type Type;

        fn add(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdSub<Lhs = Self, Rhs = Self> {
        type Type;

        fn sub(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdMul<Lhs = Self, Rhs = Self> {
        type Type;

        fn mul(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdDiv<Lhs = Self, Rhs = Self> {
        type Type;

        fn div(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdRem<Lhs = Self, Rhs = Self> {
        type Type;

        fn rem(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdBitOr<Lhs = Self, Rhs = Self> {
        type Type;

        fn bitor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdBitAnd<Lhs = Self, Rhs = Self> {
        type Type;

        fn bitand(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdBitXor<Lhs = Self, Rhs = Self> {
        type Type;

        fn bitxor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
    }

    pub trait NdShl<Lhs = Self, Rhs = usize> {
        type Type;

        fn shl(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    pub trait NdShr<Lhs = Self, Rhs = usize> {
        type Type;

        fn shr(lhs: &Lhs, rhs: Rhs) -> Self::Type;
    }

    pub trait NdAddAssign<Lhs = Self, Rhs = Self> {
        fn add_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdSubAssign<Lhs = Self, Rhs = Self> {
        fn sub_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdMulAssign<Lhs = Self, Rhs = Self> {
        fn mul_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdDivAssign<Lhs = Self, Rhs = Self> {
        fn div_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdRemAssign<Lhs = Self, Rhs = Self> {
        fn rem_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdBitOrAssign<Lhs = Self, Rhs = Self> {
        fn bitor_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdBitAndAssign<Lhs = Self, Rhs = Self> {
        fn bitand_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdBitXorAssign<Lhs = Self, Rhs = Self> {
        fn bitxor_assign(lhs: &mut Lhs, rhs: &Rhs);
    }

    pub trait NdShlAssign<Lhs = Self, Rhs = usize> {
        fn shl_assign(lhs: &mut Lhs, rhs: Rhs);
    }

    pub trait NdShrAssign<Lhs = Self, Rhs = usize> {
        fn shr_assign(lhs: &mut Lhs, rhs: Rhs);
    }

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

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use ndproc::ops_impl_auto;

macro_rules! nd_ops_impl {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_impl!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
        ops_impl_auto!(@ndun crate for $primitive (&value: &$primitive) -> $primitive, (value) [-, !]);

        ops_impl_auto!(@ndbin crate for $primitive (&lhs: &$primitive, &rhs: &$primitive) -> $primitive, (lhs) (rhs) [+, -, *, /, %, |, &, ^]);
        ops_impl_auto!(@ndmut crate for $primitive (lhs: &mut $primitive, &rhs: &$primitive), (*lhs) (rhs) [+=, -=, *=, /=, %=, |=, &=, ^=]);

        ops_impl_auto!(@ndbin crate for $primitive (&lhs: &$primitive, rhs: usize) -> $primitive, (lhs) (rhs) [<<, >>]);
        ops_impl_auto!(@ndmut crate for $primitive (lhs: &mut $primitive, rhs: usize), (*lhs) (rhs) [<<=, >>=]);
    };
    (@unsigned $primitive:ty $(,)?) => {
        ops_impl_auto!(@ndun crate for $primitive (&value: &$primitive) -> $primitive, (value) [!]);

        ops_impl_auto!(@ndbin crate for $primitive (&lhs: &$primitive, &rhs: &$primitive) -> $primitive, (lhs) (rhs) [+, -, *, /, %, |, &, ^]);
        ops_impl_auto!(@ndmut crate for $primitive (lhs: &mut $primitive, &rhs: &$primitive), (*lhs) (rhs) [+=, -=, *=, /=, %=, |=, &=, ^=]);

        ops_impl_auto!(@ndbin crate for $primitive (&lhs: &$primitive, rhs: usize) -> $primitive, (lhs) (rhs) [<<, >>]);
        ops_impl_auto!(@ndmut crate for $primitive (lhs: &mut $primitive, rhs: usize), (*lhs) (rhs) [<<=, >>=]);
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
    AddAssign<Rhs>
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
    Self: AddAssign<Rhs>
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

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use std::ops::{Neg, Not};

    use ndproc::ops_impl_auto;

    use super::*;

    macro_rules! ops_struct_def {
        ($([$($gen:tt)+][$($generics:tt)+] $(where [$($where:tt)+])?)? $type1:ident, $type2:ident, $type:ty $(,)?) => {
            #[derive(Debug, PartialEq, Eq)]
            struct $type1 $(<$($generics)+> $(where $($where)+)?)? ($type);

            #[derive(Debug, PartialEq, Eq)]
            struct $type2 $(<$($generics)+> $(where $($where)+)?)? ($type);

            impl $(<$($generics)+>)? From<$type> for $type1<$($($gen)+)?> $($(where $($where)+)?)? {
                fn from(value: $type) -> Self {
                    Self(value)
                }
            }

            impl $(<$($generics)+>)? From<$type> for $type2<$($($gen)+)?> $($(where $($where)+)?)? {
                fn from(value: $type) -> Self {
                    Self(value)
                }
            }
        };
    }

    macro_rules! assert_ops {
        ($arg1:expr, $arg2:expr, $fn:ident, $val1:expr, $val2:expr) => {
            assert_eq!($arg1 + $arg2, $fn($val1 + $val2));
            assert_eq!($arg1 - $arg2, $fn($val1 - $val2));
            assert_eq!($arg1 * $arg2, $fn($val1 * $val2));
            assert_eq!($arg1 / $arg2, $fn($val1 / $val2));
            assert_eq!($arg1 % $arg2, $fn($val1 % $val2));
            assert_eq!($arg1 | $arg2, $fn($val1 | $val2));
            assert_eq!($arg1 & $arg2, $fn($val1 & $val2));
            assert_eq!($arg1 ^ $arg2, $fn($val1 ^ $val2));
            assert_eq!($arg1 << $arg2, $fn($val1 << $val2));
            assert_eq!($arg1 >> $arg2, $fn($val1 >> $val2));
        };
    }

    macro_rules! assert_ops_assign {
        ($arg1:expr, $arg2:expr, $fn:ident, $val1:expr, $val2:expr) => {
            assert_ops_assign!(@impl += $arg1, $arg2, $fn($val1 + $val2));
            assert_ops_assign!(@impl -= $arg1, $arg2, $fn($val1 - $val2));
            assert_ops_assign!(@impl *= $arg1, $arg2, $fn($val1 * $val2));
            assert_ops_assign!(@impl /= $arg1, $arg2, $fn($val1 / $val2));
            assert_ops_assign!(@impl %= $arg1, $arg2, $fn($val1 % $val2));
            assert_ops_assign!(@impl |= $arg1, $arg2, $fn($val1 | $val2));
            assert_ops_assign!(@impl &= $arg1, $arg2, $fn($val1 & $val2));
            assert_ops_assign!(@impl ^= $arg1, $arg2, $fn($val1 ^ $val2));
            assert_ops_assign!(@impl <<= $arg1, $arg2, $fn($val1 << $val2));
            assert_ops_assign!(@impl >>= $arg1, $arg2, $fn($val1 >> $val2));
        };
        (@impl $op:tt $arg1:expr, $arg2:expr, $val:expr) => {{
            let mut val = $arg1;

            val $op $arg2;

            assert_eq!(val, $val);
        }};
    }

    ops_struct_def!(A0, B0, i64);
    ops_struct_def!(A1, B1, i64);
    ops_struct_def!(A2, B2, i64);
    ops_struct_def!(A3, B3, i64);

    ops_struct_def!([N][N: Sized + Copy] X0, Y0, N);
    ops_struct_def!([N][N: Sized + Copy] X1, Y1, N);
    ops_struct_def!([N][N: Sized + Copy] X2, Y2, N);
    ops_struct_def!([N][N: Sized + Copy] X3, Y3, N);

    ops_impl_auto!(@stdmut (lhs: &mut A0, *rhs: &B0), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut (lhs: &mut A0, *rhs: &A0), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut (lhs: &mut A1, *rhs:  B1), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut (lhs: &mut A1, *rhs:  A1), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);

    ops_impl_auto!(@stdbin (*lhs: &A0, *rhs: &B0) -> A0, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs: &A0, *rhs: &A0) -> A0, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs: &A1, *rhs:  B1) -> A1, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs: &A1, *rhs:  A1) -> A1, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs:  A2, *rhs: &B2) -> A2, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs:  A2, *rhs: &A2) -> A2, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs:  A3, *rhs:  B3) -> A3, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*lhs:  A3, *rhs:  A3) -> A3, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);

    ops_impl_auto!(@stdun (*value: &A0) -> A0, (value.0) [-, !]);
    ops_impl_auto!(@stdun (*value:  A1) -> A1, (value.0) [-, !]);

    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (lhs: &mut X0<N>, *rhs: &Y0<N>), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (lhs: &mut X0<N>, *rhs: &X0<N>), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (lhs: &mut X1<N>, *rhs:  Y1<N>), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (lhs: &mut X1<N>, *rhs:  X1<N>), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);

    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs: &X0<N>, *rhs: &Y0<N>) -> X0<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs: &X0<N>, *rhs: &X0<N>) -> X0<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs: &X1<N>, *rhs:  Y1<N>) -> X1<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs: &X1<N>, *rhs:  X1<N>) -> X1<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs:  X2<N>, *rhs: &Y2<N>) -> X2<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs:  X2<N>, *rhs: &X2<N>) -> X2<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs:  X3<N>, *rhs:  Y3<N>) -> X3<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*lhs:  X3<N>, *rhs:  X3<N>) -> X3<N>, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>]);

    ops_impl_auto!(@stdun <N: Sized + Copy + Neg<Output = N> + Not<Output = N>> (*value: &X0<N>) -> X0<N>, (value.0) [-, !]);
    ops_impl_auto!(@stdun <N: Sized + Copy + Neg<Output = N> + Not<Output = N>> (*value:  X1<N>) -> X1<N>, (value.0) [-, !]);

    #[test]
    fn ops() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops!(&A0(val1), &A0(val2), A0, val1, val2);
        assert_ops!(&A0(val1), &B0(val2), A0, val1, val2);

        assert_ops!(&A0(val1), A0(val2), A0, val1, val2);
        assert_ops!(&A0(val1), B0(val2), A0, val1, val2);

        assert_ops!(A0(val1), &A0(val2), A0, val1, val2);
        assert_ops!(A0(val1), &B0(val2), A0, val1, val2);

        assert_ops!(A0(val1), A0(val2), A0, val1, val2);
        assert_ops!(A0(val1), B0(val2), A0, val1, val2);

        assert_eq!(-&A0(val1), A0(-val1));
        assert_eq!(!&A0(val1), A0(!val1));

        assert_eq!(-A0(val1), A0(-val1));
        assert_eq!(!A0(val1), A0(!val1));
    }

    #[test]
    fn ops_gen() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops!(&X0(val1), &X0(val2), X0, val1, val2);
        assert_ops!(&X0(val1), &Y0(val2), X0, val1, val2);

        assert_ops!(&X0(val1), X0(val2), X0, val1, val2);
        assert_ops!(&X0(val1), Y0(val2), X0, val1, val2);

        assert_ops!(X0(val1), &X0(val2), X0, val1, val2);
        assert_ops!(X0(val1), &Y0(val2), X0, val1, val2);

        assert_ops!(X0(val1), X0(val2), X0, val1, val2);
        assert_ops!(X0(val1), Y0(val2), X0, val1, val2);

        assert_eq!(-&X0(val1), X0(-val1));
        assert_eq!(!&X0(val1), X0(!val1));

        assert_eq!(-X0(val1), X0(-val1));
        assert_eq!(!X0(val1), X0(!val1));
    }

    #[test]
    fn ops_assign() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_assign!(A0(val1), &A0(val2), A0, val1, val2);
        assert_ops_assign!(A0(val1), &B0(val2), A0, val1, val2);
        assert_ops_assign!(A0(val1), A0(val2), A0, val1, val2);
        assert_ops_assign!(A0(val1), B0(val2), A0, val1, val2);
    }

    #[test]
    fn ops_gen_assign() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_assign!(X0(val1), &X0(val2), X0, val1, val2);
        assert_ops_assign!(X0(val1), &Y0(val2), X0, val1, val2);
        assert_ops_assign!(X0(val1), X0(val2), X0, val1, val2);
        assert_ops_assign!(X0(val1), Y0(val2), X0, val1, val2);
    }
}

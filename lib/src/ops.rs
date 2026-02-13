use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

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

#[rustfmt::skip]
pub trait NdOps<Lhs = Self, Rhs = Self>:
    NdAdd<Lhs, Rhs, Type = Self::All>
    + NdSub<Lhs, Rhs, Type = Self::All>
    + NdMul<Lhs, Rhs, Type = Self::All>
    + NdDiv<Lhs, Rhs, Type = Self::All>
    + NdRem<Lhs, Rhs, Type = Self::All>
{
    type All;
}

#[rustfmt::skip]
pub trait NdOpsBitwise<Lhs = Self, Rhs = Self>:
    NdBitOr<Lhs, Rhs, Type = Self::All>
    + NdBitAnd<Lhs, Rhs, Type = Self::All>
    + NdBitXor<Lhs, Rhs, Type = Self::All>
{
    type All;
}

#[rustfmt::skip]
pub trait NdOpsShift<Lhs = Self, Rhs = usize>:
    NdShl<Lhs, Rhs, Type = Self::All>
    + NdShr<Lhs, Rhs, Type = Self::All>
{
    type All;
}

pub trait Ops<Rhs = Self, ShiftRhs = usize>:
    Sized
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

    ops_impl_auto!(@stdmut (a: &mut A0, *b: &B0), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut (a: &mut A0, *b: &A0), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut (a: &mut A1, *b:  B1), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut (a: &mut A1, *b:  A1), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);

    ops_impl_auto!(@stdbin (*a: &A0, *b: &B0) -> A0, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a: &A0, *b: &A0) -> A0, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a: &A1, *b:  B1) -> A1, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a: &A1, *b:  A1) -> A1, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a:  A2, *b: &B2) -> A2, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a:  A2, *b: &A2) -> A2, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a:  A3, *b:  B3) -> A3, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin (*a:  A3, *b:  A3) -> A3, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);

    ops_impl_auto!(@stdun (*a: &A0) -> A0, (a.0) [-, !]);
    ops_impl_auto!(@stdun (*a:  A1) -> A1, (a.0) [-, !]);

    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (a: &mut X0<N>, *b: &Y0<N>), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (a: &mut X0<N>, *b: &X0<N>), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (a: &mut X1<N>, *b:  Y1<N>), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);
    ops_impl_auto!(@stdmut <N: Sized + Copy + OpsAssign<N, N>> (a: &mut X1<N>, *b:  X1<N>), (a.0) (b.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=]);

    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a: &X0<N>, *b: &Y0<N>) -> X0::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a: &X0<N>, *b: &X0<N>) -> X0::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a: &X1<N>, *b:  Y1<N>) -> X1::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a: &X1<N>, *b:  X1<N>) -> X1::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a:  X2<N>, *b: &Y2<N>) -> X2::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a:  X2<N>, *b: &X2<N>) -> X2::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a:  X3<N>, *b:  Y3<N>) -> X3::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);
    ops_impl_auto!(@stdbin <N: Sized + Copy + Ops<N, N, Type = N>> (*a:  X3<N>, *b:  X3<N>) -> X3::<N>, (a.0) (b.0) [+, -, *, /, %, |, &, ^, <<, >>]);

    ops_impl_auto!(@stdun <N: Sized + Copy + Neg<Output = N> + Not<Output = N>> (*a: &X0<N>) -> X0<N>, (a.0) [-, !]);
    ops_impl_auto!(@stdun <N: Sized + Copy + Neg<Output = N> + Not<Output = N>> (*a:  X1<N>) -> X1<N>, (a.0) [-, !]);

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

use std::ops::*;

macro_rules! ops_struct_def {
    ($([$($gen:tt)+][$($generics:tt)+])? ($type1:ident, $type2:ident, $type3:ident), $type:ty $(,)?) => {
        #[allow(unused)]
        #[derive(Debug, PartialEq, Eq)]
        struct $type1 $(<$($generics)+>)? ($type);

        #[allow(unused)]
        #[derive(Debug, PartialEq, Eq)]
        struct $type2 $(<$($generics)+>)? ($type);

        #[allow(unused)]
        #[derive(Debug, PartialEq, Eq)]
        struct $type3 $(<$($generics)+>)? ($type);

        impl $(<$($generics)+>)? From<$type> for $type1<$($($gen)+)?> {
            fn from(value: $type) -> Self {
                Self(value)
            }
        }

        impl $(<$($generics)+>)? From<$type> for $type2<$($($gen)+)?> {
            fn from(value: $type) -> Self {
                Self(value)
            }
        }

        impl $(<$($generics)+>)? From<$type> for $type3<$($($gen)+)?> {
            fn from(value: $type) -> Self {
                Self(value)
            }
        }
    };
}

macro_rules! assert_ops {
    ($lhs:expr, $rhs:expr, $fn:ident, $lval:expr, $rval:expr) => {
        assert_ops!(@impl +  $lhs, $rhs, $fn($lval +  $rval));
        assert_ops!(@impl -  $lhs, $rhs, $fn($lval -  $rval));
        assert_ops!(@impl *  $lhs, $rhs, $fn($lval *  $rval));
        assert_ops!(@impl /  $lhs, $rhs, $fn($lval /  $rval));
        assert_ops!(@impl %  $lhs, $rhs, $fn($lval %  $rval));
        assert_ops!(@impl |  $lhs, $rhs, $fn($lval |  $rval));
        assert_ops!(@impl &  $lhs, $rhs, $fn($lval &  $rval));
        assert_ops!(@impl ^  $lhs, $rhs, $fn($lval ^  $rval));
        assert_ops!(@impl << $lhs, $rhs, $fn($lval << $rval));
        assert_ops!(@impl >> $lhs, $rhs, $fn($lval >> $rval));
    };
    (@impl $op:tt $lhs:expr, $rhs:expr, $val:expr) => {{
        assert_eq!($lhs $op $rhs, $val);
    }};
}

macro_rules! assert_ops_assign {
    ($lhs:expr, $rhs:expr, $fn:ident, $lval:expr, $rval:expr) => {
        assert_ops_assign!(@impl +=  $lhs, $rhs, $fn($lval +  $rval));
        assert_ops_assign!(@impl -=  $lhs, $rhs, $fn($lval -  $rval));
        assert_ops_assign!(@impl *=  $lhs, $rhs, $fn($lval *  $rval));
        assert_ops_assign!(@impl /=  $lhs, $rhs, $fn($lval /  $rval));
        assert_ops_assign!(@impl %=  $lhs, $rhs, $fn($lval %  $rval));
        assert_ops_assign!(@impl |=  $lhs, $rhs, $fn($lval |  $rval));
        assert_ops_assign!(@impl &=  $lhs, $rhs, $fn($lval &  $rval));
        assert_ops_assign!(@impl ^=  $lhs, $rhs, $fn($lval ^  $rval));
        assert_ops_assign!(@impl <<= $lhs, $rhs, $fn($lval << $rval));
        assert_ops_assign!(@impl >>= $lhs, $rhs, $fn($lval >> $rval));
    };
    (@impl $op:tt $lhs:expr, $rhs:expr, $val:expr) => {{
        assert_eq!({
            let mut lhs = $lhs;

            lhs $op $rhs;
            lhs
        }, $val);
    }};
}

ops_struct_def!((A0, B0, C0), i64);
ops_struct_def!((A1, B1, C1), i64);
ops_struct_def!((A2, B2, C2), i64);
ops_struct_def!((A3, B3, C3), i64);

ops_struct_def!([N][N: Sized + Copy] (X0, Y0, Z0), N);
ops_struct_def!([N][N: Sized + Copy] (X1, Y1, Z1), N);
ops_struct_def!([N][N: Sized + Copy] (X2, Y2, Z2), N);
ops_struct_def!([N][N: Sized + Copy] (X3, Y3, Z3), N);

ndops::all_auto! { @stdmut (lhs: &mut A0, *rhs: &B0), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=] }
ndops::all_auto! { @stdmut (lhs: &mut A0, *rhs: &A0), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=] }
ndops::all_auto! { @stdmut (lhs: &mut A1, *rhs:  B1), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=] }
ndops::all_auto! { @stdmut (lhs: &mut A1, *rhs:  A1), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=] }

ndops::all_auto! { @stdbin (*lhs: &A0, *rhs: &B0) -> C0, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs: &A0, *rhs: &A0) -> C0, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs: &A1, *rhs:  B1) -> C1, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs: &A1, *rhs:  A1) -> C1, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs:  A2, *rhs: &B2) -> C2, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs:  A2, *rhs: &A2) -> C2, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs:  A3, *rhs:  B3) -> C3, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }
ndops::all_auto! { @stdbin (*lhs:  A3, *rhs:  A3) -> C3, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^, <<, >>] }

ndops::all_auto! { @stdun (*value: &A0) -> C0, (value.0) [-, !] }
ndops::all_auto! { @stdun (*value:  A1) -> C1, (value.0) [-, !] }

ndops::all_auto! { @stdmut <N: Sized + Copy> (lhs: &mut X0<N>, *rhs: &Y0<N>), (lhs.0) (rhs.0) [
    +=  where [N: AddAssign<N>],
    -=  where [N: SubAssign<N>],
    *=  where [N: MulAssign<N>],
    /=  where [N: DivAssign<N>],
    %=  where [N: RemAssign<N>],
    |=  where [N: BitOrAssign<N>],
    &=  where [N: BitAndAssign<N>],
    ^=  where [N: BitXorAssign<N>],
    <<= where [N: ShlAssign<N>],
    >>= where [N: ShrAssign<N>],
] }

ndops::all_auto! { @stdmut <N: Sized + Copy> (lhs: &mut X0<N>, *rhs: &X0<N>), (lhs.0) (rhs.0) [
    +=  where [N: AddAssign<N>],
    -=  where [N: SubAssign<N>],
    *=  where [N: MulAssign<N>],
    /=  where [N: DivAssign<N>],
    %=  where [N: RemAssign<N>],
    |=  where [N: BitOrAssign<N>],
    &=  where [N: BitAndAssign<N>],
    ^=  where [N: BitXorAssign<N>],
    <<= where [N: ShlAssign<N>],
    >>= where [N: ShrAssign<N>],
] }

ndops::all_auto! { @stdmut <N: Sized + Copy> (lhs: &mut X1<N>, *rhs: Y1<N>), (lhs.0) (rhs.0) [
    +=  where [N: AddAssign<N>],
    -=  where [N: SubAssign<N>],
    *=  where [N: MulAssign<N>],
    /=  where [N: DivAssign<N>],
    %=  where [N: RemAssign<N>],
    |=  where [N: BitOrAssign<N>],
    &=  where [N: BitAndAssign<N>],
    ^=  where [N: BitXorAssign<N>],
    <<= where [N: ShlAssign<N>],
    >>= where [N: ShrAssign<N>],
] }

ndops::all_auto! { @stdmut <N: Sized + Copy> (lhs: &mut X1<N>, *rhs: X1<N>), (lhs.0) (rhs.0) [
    +=  where [N: AddAssign<N>],
    -=  where [N: SubAssign<N>],
    *=  where [N: MulAssign<N>],
    /=  where [N: DivAssign<N>],
    %=  where [N: RemAssign<N>],
    |=  where [N: BitOrAssign<N>],
    &=  where [N: BitAndAssign<N>],
    ^=  where [N: BitXorAssign<N>],
    <<= where [N: ShlAssign<N>],
    >>= where [N: ShrAssign<N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: &X0<N>, *rhs: &Y0<N>) -> Z0<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: &X0<N>, *rhs: &X0<N>) -> Z0<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: &X1<N>, *rhs: Y1<N>) -> Z1<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: &X1<N>, *rhs: X1<N>) -> Z1<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: X2<N>, *rhs: &Y2<N>) -> Z2<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: X2<N>, *rhs: &X2<N>) -> Z2<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: X3<N>, *rhs: Y3<N>) -> Z3<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdbin <N: Sized + Copy> (*lhs: X3<N>, *rhs: X3<N>) -> Z3<N>, (lhs.0) (rhs.0) [
    +  where [N: Add<N, Output = N>],
    -  where [N: Sub<N, Output = N>],
    *  where [N: Mul<N, Output = N>],
    /  where [N: Div<N, Output = N>],
    %  where [N: Rem<N, Output = N>],
    |  where [N: BitOr<N, Output = N>],
    &  where [N: BitAnd<N, Output = N>],
    ^  where [N: BitXor<N, Output = N>],
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

ndops::all_auto! { @stdun <N: Sized + Copy> (*value: &X0<N>) -> Z0<N>, (value.0) [
    - where [N: Neg<Output = N>],
    ! where [N: Not<Output = N>],
] }

ndops::all_auto! { @stdun <N: Sized + Copy> (*value: X1<N>) -> Z1<N>, (value.0) [
    - where [N: Neg<Output = N>],
    ! where [N: Not<Output = N>],
] }

#[test]
#[rustfmt::skip]
fn all_ops() {
    let lhs = 32i64;
    let rhs = 2i64;

    assert_ops!(&A0(lhs), &A0(rhs), C0, lhs, rhs);
    assert_ops!(&A0(lhs), &B0(rhs), C0, lhs, rhs);
    assert_ops!(&A0(lhs),  A0(rhs), C0, lhs, rhs);
    assert_ops!(&A0(lhs),  B0(rhs), C0, lhs, rhs);
    assert_ops!( A0(lhs), &A0(rhs), C0, lhs, rhs);
    assert_ops!( A0(lhs), &B0(rhs), C0, lhs, rhs);
    assert_ops!( A0(lhs),  A0(rhs), C0, lhs, rhs);
    assert_ops!( A0(lhs),  B0(rhs), C0, lhs, rhs);

    assert_eq!(-&A0(lhs), C0(-lhs));
    assert_eq!(!&A0(lhs), C0(!lhs));

    assert_eq!(-A0(lhs), C0(-lhs));
    assert_eq!(!A0(lhs), C0(!lhs));
}

#[test]
#[rustfmt::skip]
fn all_ops_gen() {
    let lhs = 32i64;
    let rhs = 2i64;

    assert_ops!(&X0(lhs), &X0(rhs), Z0, lhs, rhs);
    assert_ops!(&X0(lhs), &Y0(rhs), Z0, lhs, rhs);
    assert_ops!(&X0(lhs),  X0(rhs), Z0, lhs, rhs);
    assert_ops!(&X0(lhs),  Y0(rhs), Z0, lhs, rhs);
    assert_ops!( X0(lhs), &X0(rhs), Z0, lhs, rhs);
    assert_ops!( X0(lhs), &Y0(rhs), Z0, lhs, rhs);
    assert_ops!( X0(lhs),  X0(rhs), Z0, lhs, rhs);
    assert_ops!( X0(lhs),  Y0(rhs), Z0, lhs, rhs);

    assert_eq!(-&X0(lhs), Z0(-lhs));
    assert_eq!(!&X0(lhs), Z0(!lhs));

    assert_eq!(-X0(lhs), Z0(-lhs));
    assert_eq!(!X0(lhs), Z0(!lhs));
}

#[test]
#[rustfmt::skip]
fn all_ops_assign() {
    let lhs = 32i64;
    let rhs = 2i64;

    assert_ops_assign!(A0(lhs), &A0(rhs), A0, lhs, rhs);
    assert_ops_assign!(A0(lhs), &B0(rhs), A0, lhs, rhs);
    assert_ops_assign!(A0(lhs),  A0(rhs), A0, lhs, rhs);
    assert_ops_assign!(A0(lhs),  B0(rhs), A0, lhs, rhs);
}

#[test]
#[rustfmt::skip]
fn all_ops_gen_assign() {
    let lhs = 32i64;
    let rhs = 2i64;

    assert_ops_assign!(X0(lhs), &X0(rhs), X0, lhs, rhs);
    assert_ops_assign!(X0(lhs), &Y0(rhs), X0, lhs, rhs);
    assert_ops_assign!(X0(lhs),  X0(rhs), X0, lhs, rhs);
    assert_ops_assign!(X0(lhs),  Y0(rhs), X0, lhs, rhs);
}

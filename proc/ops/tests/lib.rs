use ndcore::ops::*;

macro_rules! struct_def {
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

struct_def!((A0, B0, C0), i64);
struct_def!((A1, B1, C1), i64);
struct_def!((A2, B2, C2), i64);
struct_def!((A3, B3, C3), i64);

struct_def!([N][N: Sized + Copy] (X0, Y0, Z0), N);
struct_def!([N][N: Sized + Copy] (X1, Y1, Z1), N);
struct_def!([N][N: Sized + Copy] (X2, Y2, Z2), N);
struct_def!([N][N: Sized + Copy] (X3, Y3, Z3), N);

ndops::fwd! { @ndmut (lhs: &mut A0, rhs: &B0), (i64) (&mut lhs.0) (&rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }
ndops::fwd! { @ndmut (lhs: &mut A0, rhs: usize), (i64) (&mut lhs.0) (rhs) [<<=, >>=] }

ndops::fwd! { @ndbin (lhs: &A0, rhs: &B0) -> C0, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }
ndops::fwd! { @ndbin (lhs: &A0, rhs: usize) -> C0, (i64) (&lhs.0) (rhs) [<<, >>] }

ndops::fwd! { @ndun (value: &A0) -> C0, (i64) (&value.0) [!, -] }

ndops::fwd! { @ndmut <N: Sized + Copy> (lhs: &mut X0<N>, rhs: &Y0<N>), (N) (&mut lhs.0) (&rhs.0) [
    += where [N: NdAddAssign],
    -= where [N: NdSubAssign],
    *= where [N: NdMulAssign],
    /= where [N: NdDivAssign],
    %= where [N: NdRemAssign],
    |= where [N: NdBitOrAssign],
    &= where [N: NdBitAndAssign],
    ^= where [N: NdBitXorAssign],
] }

ndops::fwd! { @ndmut <N: Sized + Copy> (lhs: &mut X0<N>, rhs: usize), (N) (&mut lhs.0) (rhs) [
    <<= where [N: NdShlAssign],
    >>= where [N: NdShrAssign],
] }

ndops::fwd! { @ndbin <N: Sized + Copy> (lhs: &X0<N>, rhs: &Y0<N>) -> Z0<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

ndops::fwd! { @ndbin <N: Sized + Copy> (lhs: &X0<N>, rhs: usize) -> Z0<N>, (N) (&lhs.0) (rhs) [
    << where [N: NdShl<Type = N>],
    >> where [N: NdShr<Type = N>],
] }

ndops::fwd! { @ndun <N: Sized + Copy> (value: &X0<N>) -> Z0<N>, (N) (&value.0) [
    ! where [N: NdNot<Type = N>],
    - where [N: NdNeg<Type = N>],
] }

ndops::fwd! { @stdmut (lhs: &mut A0, *rhs: &B0), (i64) (&mut lhs.0) (&rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }
ndops::fwd! { @stdmut (lhs: &mut A1, *rhs:  B1), (i64) (&mut lhs.0) (&rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }

ndops::fwd! { @stdmut (lhs: &mut A0, rhs: usize), (i64) (&mut lhs.0) (rhs) [<<=, >>=] }

ndops::fwd! { @stdbin (*lhs: &A0, *rhs: &B0) -> C0, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }
ndops::fwd! { @stdbin (*lhs: &A1, *rhs:  B1) -> C1, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }
ndops::fwd! { @stdbin (*lhs:  A2, *rhs: &B2) -> C2, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }
ndops::fwd! { @stdbin (*lhs:  A3, *rhs:  B3) -> C3, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }

ndops::fwd! { @stdbin (*lhs: &A0, rhs: usize) -> C0, (i64) (&lhs.0) (rhs) [<<, >>] }
ndops::fwd! { @stdbin (*lhs:  A2, rhs: usize) -> C2, (i64) (&lhs.0) (rhs) [<<, >>] }

ndops::fwd! { @stdun (*value: &A0) -> C0, (i64) (&value.0) [!, -] }
ndops::fwd! { @stdun (*value:  A1) -> C1, (i64) (&value.0) [!, -] }

ndops::fwd! { @stdmut <N: Sized + Copy> (lhs: &mut X0<N>, *rhs: &Y0<N>), (N) (&mut lhs.0) (&rhs.0) [
    += where [N: NdAddAssign],
    -= where [N: NdSubAssign],
    *= where [N: NdMulAssign],
    /= where [N: NdDivAssign],
    %= where [N: NdRemAssign],
    |= where [N: NdBitOrAssign],
    &= where [N: NdBitAndAssign],
    ^= where [N: NdBitXorAssign],
] }

ndops::fwd! { @stdmut <N: Sized + Copy> (lhs: &mut X1<N>, *rhs: Y1<N>), (N) (&mut lhs.0) (&rhs.0) [
    += where [N: NdAddAssign],
    -= where [N: NdSubAssign],
    *= where [N: NdMulAssign],
    /= where [N: NdDivAssign],
    %= where [N: NdRemAssign],
    |= where [N: NdBitOrAssign],
    &= where [N: NdBitAndAssign],
    ^= where [N: NdBitXorAssign],
] }

ndops::fwd! { @stdmut <N: Sized + Copy> (lhs: &mut X0<N>, rhs: usize), (N) (&mut lhs.0) (rhs) [
    <<= where [N: NdShlAssign],
    >>= where [N: NdShrAssign],
] }

ndops::fwd! { @stdbin <N: Sized + Copy> (*lhs: &X0<N>, *rhs: &Y0<N>) -> Z0<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

ndops::fwd! { @stdbin <N: Sized + Copy> (*lhs: &X1<N>, *rhs: Y1<N>) -> Z1<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

ndops::fwd! { @stdbin <N: Sized + Copy> (*lhs: X2<N>, *rhs: &Y2<N>) -> Z2<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

ndops::fwd! { @stdbin <N: Sized + Copy> (*lhs: X3<N>, *rhs: Y3<N>) -> Z3<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

ndops::fwd! { @stdbin <N: Sized + Copy> (*lhs: &X0<N>, rhs: usize) -> Z0<N>, (N) (&lhs.0) (rhs) [
    << where [N: NdShl<Type = N>],
    >> where [N: NdShr<Type = N>],
] }

ndops::fwd! { @stdun <N: Sized + Copy> (*value: &X0<N>) -> Z0<N>, (N) (&value.0) [
    ! where [N: NdNot<Type = N>],
    - where [N: NdNeg<Type = N>],
] }

ndops::fwd! { @stdun <N: Sized + Copy> (*value: X1<N>) -> Z1<N>, (N) (&value.0) [
    ! where [N: NdNot<Type = N>],
    - where [N: NdNeg<Type = N>],
] }

mod ops {
    use ndassert::catch;

    use super::*;

    #[test]
    fn all() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            (catch!(&A0(lhs) + &B0(rhs)), catch!(C0(lhs + rhs))),
            (catch!(&A0(lhs) - &B0(rhs)), catch!(C0(lhs - rhs))),
            (catch!(&A0(lhs) * &B0(rhs)), catch!(C0(lhs * rhs))),
            (catch!(&A0(lhs) / &B0(rhs)), catch!(C0(lhs / rhs))),
            (catch!(&A0(lhs) % &B0(rhs)), catch!(C0(lhs % rhs))),

            (catch!(&A0(lhs) + B0(rhs)), catch!(C0(lhs + rhs))),
            (catch!(&A0(lhs) - B0(rhs)), catch!(C0(lhs - rhs))),
            (catch!(&A0(lhs) * B0(rhs)), catch!(C0(lhs * rhs))),
            (catch!(&A0(lhs) / B0(rhs)), catch!(C0(lhs / rhs))),
            (catch!(&A0(lhs) % B0(rhs)), catch!(C0(lhs % rhs))),

            (catch!(A0(lhs) + &B0(rhs)), catch!(C0(lhs + rhs))),
            (catch!(A0(lhs) - &B0(rhs)), catch!(C0(lhs - rhs))),
            (catch!(A0(lhs) * &B0(rhs)), catch!(C0(lhs * rhs))),
            (catch!(A0(lhs) / &B0(rhs)), catch!(C0(lhs / rhs))),
            (catch!(A0(lhs) % &B0(rhs)), catch!(C0(lhs % rhs))),

            (catch!(A0(lhs) + B0(rhs)), catch!(C0(lhs + rhs))),
            (catch!(A0(lhs) - B0(rhs)), catch!(C0(lhs - rhs))),
            (catch!(A0(lhs) * B0(rhs)), catch!(C0(lhs * rhs))),
            (catch!(A0(lhs) / B0(rhs)), catch!(C0(lhs / rhs))),
            (catch!(A0(lhs) % B0(rhs)), catch!(C0(lhs % rhs))),

            (&A0(lhs) | &B0(rhs), C0(lhs | rhs)),
            (&A0(lhs) & &B0(rhs), C0(lhs & rhs)),
            (&A0(lhs) ^ &B0(rhs), C0(lhs ^ rhs)),

            (&A0(lhs) | B0(rhs), C0(lhs | rhs)),
            (&A0(lhs) & B0(rhs), C0(lhs & rhs)),
            (&A0(lhs) ^ B0(rhs), C0(lhs ^ rhs)),

            (A0(lhs) | &B0(rhs), C0(lhs | rhs)),
            (A0(lhs) & &B0(rhs), C0(lhs & rhs)),
            (A0(lhs) ^ &B0(rhs), C0(lhs ^ rhs)),

            (A0(lhs) | B0(rhs), C0(lhs | rhs)),
            (A0(lhs) & B0(rhs), C0(lhs & rhs)),
            (A0(lhs) ^ B0(rhs), C0(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in 0..128,
        ) [
            (catch!(&A0(lhs) << rhs), catch!(C0(lhs << rhs))),
            (catch!(A0(lhs) >> rhs), catch!(C0(lhs >> rhs))),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(i64, 60)) [
            (!&A0(val), C0(!val)),
            (!A0(val), C0(!val)),

            (catch!(-&A0(val)), catch!(C0(-val))),
            (catch!(-A0(val)), catch!(C0(-val))),
        ] }
    }

    #[test]
    #[rustfmt::skip]
    fn all_generic() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            (catch!(&X0(lhs) + &Y0(rhs)), catch!(Z0(lhs + rhs))),
            (catch!(&X0(lhs) - &Y0(rhs)), catch!(Z0(lhs - rhs))),
            (catch!(&X0(lhs) * &Y0(rhs)), catch!(Z0(lhs * rhs))),
            (catch!(&X0(lhs) / &Y0(rhs)), catch!(Z0(lhs / rhs))),
            (catch!(&X0(lhs) % &Y0(rhs)), catch!(Z0(lhs % rhs))),

            (catch!(&X0(lhs) + Y0(rhs)), catch!(Z0(lhs + rhs))),
            (catch!(&X0(lhs) - Y0(rhs)), catch!(Z0(lhs - rhs))),
            (catch!(&X0(lhs) * Y0(rhs)), catch!(Z0(lhs * rhs))),
            (catch!(&X0(lhs) / Y0(rhs)), catch!(Z0(lhs / rhs))),
            (catch!(&X0(lhs) % Y0(rhs)), catch!(Z0(lhs % rhs))),

            (catch!(X0(lhs) + &Y0(rhs)), catch!(Z0(lhs + rhs))),
            (catch!(X0(lhs) - &Y0(rhs)), catch!(Z0(lhs - rhs))),
            (catch!(X0(lhs) * &Y0(rhs)), catch!(Z0(lhs * rhs))),
            (catch!(X0(lhs) / &Y0(rhs)), catch!(Z0(lhs / rhs))),
            (catch!(X0(lhs) % &Y0(rhs)), catch!(Z0(lhs % rhs))),

            (catch!(X0(lhs) + Y0(rhs)), catch!(Z0(lhs + rhs))),
            (catch!(X0(lhs) - Y0(rhs)), catch!(Z0(lhs - rhs))),
            (catch!(X0(lhs) * Y0(rhs)), catch!(Z0(lhs * rhs))),
            (catch!(X0(lhs) / Y0(rhs)), catch!(Z0(lhs / rhs))),
            (catch!(X0(lhs) % Y0(rhs)), catch!(Z0(lhs % rhs))),

            (&X0(lhs) | &Y0(rhs), Z0(lhs | rhs)),
            (&X0(lhs) & &Y0(rhs), Z0(lhs & rhs)),
            (&X0(lhs) ^ &Y0(rhs), Z0(lhs ^ rhs)),

            (&X0(lhs) | Y0(rhs), Z0(lhs | rhs)),
            (&X0(lhs) & Y0(rhs), Z0(lhs & rhs)),
            (&X0(lhs) ^ Y0(rhs), Z0(lhs ^ rhs)),

            (X0(lhs) | &Y0(rhs), Z0(lhs | rhs)),
            (X0(lhs) & &Y0(rhs), Z0(lhs & rhs)),
            (X0(lhs) ^ &Y0(rhs), Z0(lhs ^ rhs)),

            (X0(lhs) | Y0(rhs), Z0(lhs | rhs)),
            (X0(lhs) & Y0(rhs), Z0(lhs & rhs)),
            (X0(lhs) ^ Y0(rhs), Z0(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in 0..128,
        ) [
            (catch!(&X0(lhs) << rhs), catch!(Z0(lhs << rhs))),
            (catch!(X0(lhs) << rhs), catch!(Z0(lhs << rhs))),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(i64, 60)) [
            (!&X0(val), Z0(!val)),
            (!X0(val), Z0(!val)),

            (catch!(-&X0(val)), catch!(Z0(-val))),
            (catch!(-X0(val)), catch!(Z0(-val))),
        ] }
    }

    #[test]
    #[rustfmt::skip]
    fn all_assign() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            (catch!({ let mut val = A0(lhs); val += &B0(rhs); val }), catch!(A0(lhs + rhs))),
            (catch!({ let mut val = A0(lhs); val -= &B0(rhs); val }), catch!(A0(lhs - rhs))),
            (catch!({ let mut val = A0(lhs); val *= &B0(rhs); val }), catch!(A0(lhs * rhs))),
            (catch!({ let mut val = A0(lhs); val /= &B0(rhs); val }), catch!(A0(lhs / rhs))),
            (catch!({ let mut val = A0(lhs); val %= &B0(rhs); val }), catch!(A0(lhs % rhs))),

            (catch!({ let mut val = A0(lhs); val += B0(rhs); val }), catch!(A0(lhs + rhs))),
            (catch!({ let mut val = A0(lhs); val -= B0(rhs); val }), catch!(A0(lhs - rhs))),
            (catch!({ let mut val = A0(lhs); val *= B0(rhs); val }), catch!(A0(lhs * rhs))),
            (catch!({ let mut val = A0(lhs); val /= B0(rhs); val }), catch!(A0(lhs / rhs))),
            (catch!({ let mut val = A0(lhs); val %= B0(rhs); val }), catch!(A0(lhs % rhs))),

            ({ let mut val = A0(lhs); val |= &B0(rhs); val }, A0(lhs | rhs)),
            ({ let mut val = A0(lhs); val &= &B0(rhs); val }, A0(lhs & rhs)),
            ({ let mut val = A0(lhs); val ^= &B0(rhs); val }, A0(lhs ^ rhs)),

            ({ let mut val = A0(lhs); val |= B0(rhs); val }, A0(lhs | rhs)),
            ({ let mut val = A0(lhs); val &= B0(rhs); val }, A0(lhs & rhs)),
            ({ let mut val = A0(lhs); val ^= B0(rhs); val }, A0(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in 0..128,
        ) [
            (catch!({ let mut val = A0(lhs); val <<= rhs; val }), catch!(A0(lhs << rhs))),
        ] }
    }

    #[test]
    #[rustfmt::skip]
    fn all_assign_generic() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            (catch!({ let mut val = X0(lhs); val += &Y0(rhs); val }), catch!(X0(lhs + rhs))),
            (catch!({ let mut val = X0(lhs); val -= &Y0(rhs); val }), catch!(X0(lhs - rhs))),
            (catch!({ let mut val = X0(lhs); val *= &Y0(rhs); val }), catch!(X0(lhs * rhs))),
            (catch!({ let mut val = X0(lhs); val /= &Y0(rhs); val }), catch!(X0(lhs / rhs))),
            (catch!({ let mut val = X0(lhs); val %= &Y0(rhs); val }), catch!(X0(lhs % rhs))),

            (catch!({ let mut val = X0(lhs); val += Y0(rhs); val }), catch!(X0(lhs + rhs))),
            (catch!({ let mut val = X0(lhs); val -= Y0(rhs); val }), catch!(X0(lhs - rhs))),
            (catch!({ let mut val = X0(lhs); val *= Y0(rhs); val }), catch!(X0(lhs * rhs))),
            (catch!({ let mut val = X0(lhs); val /= Y0(rhs); val }), catch!(X0(lhs / rhs))),
            (catch!({ let mut val = X0(lhs); val %= Y0(rhs); val }), catch!(X0(lhs % rhs))),

            ({ let mut val = X0(lhs); val |= &Y0(rhs); val }, X0(lhs | rhs)),
            ({ let mut val = X0(lhs); val &= &Y0(rhs); val }, X0(lhs & rhs)),
            ({ let mut val = X0(lhs); val ^= &Y0(rhs); val }, X0(lhs ^ rhs)),

            ({ let mut val = X0(lhs); val |= Y0(rhs); val }, X0(lhs | rhs)),
            ({ let mut val = X0(lhs); val &= Y0(rhs); val }, X0(lhs & rhs)),
            ({ let mut val = X0(lhs); val ^= Y0(rhs); val }, X0(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in 0..128,
        ) [
            (catch!({ let mut val = X0(lhs); val <<= rhs; val }), catch!(X0(lhs << rhs))),
        ] }
    }
}

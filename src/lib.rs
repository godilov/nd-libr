pub mod cond;
pub mod long;
pub mod math;
pub mod num;
pub mod ops;
pub mod vec;

#[cfg(test)]
mod tests {
    use crate::ops::{
        OpsAll, OpsAllAssign, OpsAllFrom, OpsBitFrom, OpsFrom, OpsNegFrom, OpsNotFrom, OpsRemFrom, OpsShiftFrom,
    };
    use proc::ops_impl;
    use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

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

    macro_rules! ops_struct_impl {
        (@mut $([$($generics:tt)+] $(where [$($where:tt)+])?)? |$($mut:ident)? $type1:ty, $type2:ty|) => {
            ops_impl!(@mut $(<$($generics)+> $(where $($where)+)?)? |a: $($mut)? $type1, b: $type2|
                 += { a.0 += b.0 },
                 -= { a.0 -= b.0 },
                 *= { a.0 *= b.0 },
                 /= { a.0 /= b.0 },
                 %= { a.0 %= b.0 },
                 |= { a.0 |= b.0 },
                 &= { a.0 &= b.0 },
                 ^= { a.0 ^= b.0 },
                 <<= { a.0 <<= b.0 },
                 >>= { a.0 >>= b.0 });
        };
        (@bin $([$($generics:tt)+] $(where [$($where:tt)+])?)? |$type1:ty, $type2:ty| -> $type:ty) => {
            ops_impl!(@bin $(<$($generics)+> $(where $($where)+)?)? |a: $type1, b: $type2| -> $type
                + { (a.0 + b.0).into() },
                - { (a.0 - b.0).into() },
                * { (a.0 * b.0).into() },
                / { (a.0 / b.0).into() },
                % { (a.0 % b.0).into() },
                | { (a.0 | b.0).into() },
                & { (a.0 & b.0).into() },
                ^ { (a.0 ^ b.0).into() },
                << { (a.0 << b.0).into() },
                >> { (a.0 >> b.0).into() });
        };
        (@un $([$($generics:tt)+] $(where [$($where:tt)+])?)? |$type1:ty| -> $type:ty) => {
            ops_impl!(@un $(<$($generics)+> $(where $($where)+)?)? |a: $type1| -> $type - { (-a.0).into() }, ! { (!a.0).into() });
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

    macro_rules! assert_ops_mut {
        (@impl $op:tt $arg1:expr, $arg2:expr, $val:expr) => {{
            let mut val = $arg1;

            val $op $arg2;

            assert_eq!(val, $val);
        }};
        (@ref $arg1:expr, $arg2:expr, $fn:ident, $val1:expr, $val2:expr) => {
            assert_ops_mut!(@impl += $arg1, $arg2, &mut $fn($val1 + $val2));
            assert_ops_mut!(@impl -= $arg1, $arg2, &mut $fn($val1 - $val2));
            assert_ops_mut!(@impl *= $arg1, $arg2, &mut $fn($val1 * $val2));
            assert_ops_mut!(@impl /= $arg1, $arg2, &mut $fn($val1 / $val2));
            assert_ops_mut!(@impl %= $arg1, $arg2, &mut $fn($val1 % $val2));
            assert_ops_mut!(@impl |= $arg1, $arg2, &mut $fn($val1 | $val2));
            assert_ops_mut!(@impl &= $arg1, $arg2, &mut $fn($val1 & $val2));
            assert_ops_mut!(@impl ^= $arg1, $arg2, &mut $fn($val1 ^ $val2));
            assert_ops_mut!(@impl <<= $arg1, $arg2, &mut $fn($val1 << $val2));
            assert_ops_mut!(@impl >>= $arg1, $arg2, &mut $fn($val1 >> $val2));
        };
        (@mut $arg1:expr, $arg2:expr, $fn:ident, $val1:expr, $val2:expr) => {
            assert_ops_mut!(@impl += $arg1, $arg2, $fn($val1 + $val2));
            assert_ops_mut!(@impl -= $arg1, $arg2, $fn($val1 - $val2));
            assert_ops_mut!(@impl *= $arg1, $arg2, $fn($val1 * $val2));
            assert_ops_mut!(@impl /= $arg1, $arg2, $fn($val1 / $val2));
            assert_ops_mut!(@impl %= $arg1, $arg2, $fn($val1 % $val2));
            assert_ops_mut!(@impl |= $arg1, $arg2, $fn($val1 | $val2));
            assert_ops_mut!(@impl &= $arg1, $arg2, $fn($val1 & $val2));
            assert_ops_mut!(@impl ^= $arg1, $arg2, $fn($val1 ^ $val2));
            assert_ops_mut!(@impl <<= $arg1, $arg2, $fn($val1 << $val2));
            assert_ops_mut!(@impl >>= $arg1, $arg2, $fn($val1 >> $val2));
        };
    }

    ops_struct_def!(A0, B0, i64);
    ops_struct_def!(A1, B1, i64);
    ops_struct_def!(A2, B2, i64);
    ops_struct_def!(A3, B3, i64);

    ops_struct_def!([N][N: Sized + Copy] X0, Y0, N);
    ops_struct_def!([N][N: Sized + Copy] X1, Y1, N);
    ops_struct_def!([N][N: Sized + Copy] X2, Y2, N);
    ops_struct_def!([N][N: Sized + Copy] X3, Y3, N);

    ops_struct_impl!(@mut |&mut A0, &B0|);
    ops_struct_impl!(@mut |&mut A0, &A0|);
    ops_struct_impl!(@mut |&mut A1, B1|);
    ops_struct_impl!(@mut |&mut A1, A1|);
    ops_struct_impl!(@mut |mut A2, &B2|);
    ops_struct_impl!(@mut |mut A2, &A2|);
    ops_struct_impl!(@mut |mut A3, B3|);
    ops_struct_impl!(@mut |mut A3, A3|);

    ops_struct_impl!(@bin |&A0, &B0| -> A0);
    ops_struct_impl!(@bin |&A0, &A0| -> A0);
    ops_struct_impl!(@bin |&A1, B1| -> A1);
    ops_struct_impl!(@bin |&A1, A1| -> A1);
    ops_struct_impl!(@bin |A2, &B2| -> A2);
    ops_struct_impl!(@bin |A2, &A2| -> A2);
    ops_struct_impl!(@bin |A3, B3| -> A3);
    ops_struct_impl!(@bin |A3, A3| -> A3);

    ops_struct_impl!(@un |&A0| -> A0);
    ops_struct_impl!(@un |A1| -> A1);

    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |&mut X0<N>, &Y0<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |&mut X0<N>, &X0<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |&mut X1<N>, Y1<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |&mut X1<N>, X1<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |mut X2<N>, &Y2<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |mut X2<N>, &X2<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |mut X3<N>, Y3<N>|);
    ops_struct_impl!(@mut [N: Sized + Copy + OpsAllAssign] |mut X3<N>, X3<N>|);

    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X0<N>: OpsAllFrom<N>] |&X0<N>, &Y0<N>| -> X0<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X0<N>: OpsAllFrom<N>] |&X0<N>, &X0<N>| -> X0<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X1<N>: OpsAllFrom<N>] |&X1<N>, Y1<N>| -> X1<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X1<N>: OpsAllFrom<N>] |&X1<N>, X1<N>| -> X1<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X2<N>: OpsAllFrom<N>] |X2<N>, &Y2<N>| -> X2<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X2<N>: OpsAllFrom<N>] |X2<N>, &X2<N>| -> X2<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X3<N>: OpsAllFrom<N>] |X3<N>, Y3<N>| -> X3<N>);
    ops_struct_impl!(@bin [N: Sized + Copy + OpsAll] where [X3<N>: OpsAllFrom<N>] |X3<N>, X3<N>| -> X3<N>);

    ops_struct_impl!(@un [N: Sized + Copy + Neg + Not] where [X0<N>: OpsNegFrom<N> + OpsNotFrom<N>] |&X0<N>| -> X0<N>);
    ops_struct_impl!(@un [N: Sized + Copy + Neg + Not] where [X1<N>: OpsNegFrom<N> + OpsNotFrom<N>] |X1<N>| -> X1<N>);

    fn a_fn(x: i64) -> A0 {
        A0(x)
    }

    fn b_fn(x: i64) -> B0 {
        B0(x)
    }

    fn x_fn<N: Sized + Copy + OpsAll>(x: N) -> X0<N> {
        X0::<N>(x)
    }

    fn y_fn<N: Sized + Copy + OpsAll>(x: N) -> Y0<N> {
        Y0::<N>(x)
    }

    impl<N: Sized + Copy + OpsAll> OpsFrom<N> for X0<N> where
        Self: From<<N as Add>::Output> + From<<N as Sub>::Output> + From<<N as Mul>::Output> + From<<N as Div>::Output>
    {
    }

    impl<N: Sized + Copy + OpsAll> OpsRemFrom<N> for X0<N> where Self: From<<N as Rem>::Output> {}
    impl<N: Sized + Copy + OpsAll> OpsBitFrom<N> for X0<N> where
        Self: From<<N as BitOr>::Output> + From<<N as BitAnd>::Output> + From<<N as BitXor>::Output>
    {
    }

    impl<N: Sized + Copy + OpsAll> OpsShiftFrom<N> for X0<N> where Self: From<<N as Shl>::Output> + From<<N as Shr>::Output> {}
    impl<N: Sized + Copy + OpsAll> OpsAllFrom<N> for X0<N> where
        Self: OpsFrom<N> + OpsRemFrom<N> + OpsBitFrom<N> + OpsShiftFrom<N>
    {
    }

    impl<N: Sized + Copy + Neg + Not> OpsNegFrom<N> for X0<N> where Self: From<<N as Neg>::Output> {}
    impl<N: Sized + Copy + Neg + Not> OpsNotFrom<N> for X0<N> where Self: From<<N as Not>::Output> {}

    #[test]
    fn ops() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops!(&a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops!(&a_fn(val1), &b_fn(val2), a_fn, val1, val2);

        assert_ops!(&a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops!(&a_fn(val1), b_fn(val2), a_fn, val1, val2);

        assert_ops!(a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops!(a_fn(val1), &b_fn(val2), a_fn, val1, val2);

        assert_ops!(a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops!(a_fn(val1), b_fn(val2), a_fn, val1, val2);

        assert_eq!(-&a_fn(val1), a_fn(-val1));
        assert_eq!(!&a_fn(val1), a_fn(!val1));

        assert_eq!(-a_fn(val1), a_fn(-val1));
        assert_eq!(!a_fn(val1), a_fn(!val1));
    }

    #[test]
    fn ops_gen() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops!(&x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops!(&x_fn(val1), &y_fn(val2), x_fn, val1, val2);

        assert_ops!(&x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops!(&x_fn(val1), y_fn(val2), x_fn, val1, val2);

        assert_ops!(x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops!(x_fn(val1), &y_fn(val2), x_fn, val1, val2);

        assert_ops!(x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops!(x_fn(val1), y_fn(val2), x_fn, val1, val2);

        assert_eq!(-&x_fn(val1), x_fn(-val1));
        assert_eq!(!&x_fn(val1), x_fn(!val1));

        assert_eq!(-x_fn(val1), x_fn(-val1));
        assert_eq!(!x_fn(val1), x_fn(!val1));
    }

    #[test]
    fn ops_mut() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_mut!(@ref &mut a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(@ref &mut a_fn(val1), &b_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(@ref &mut a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(@ref &mut a_fn(val1), b_fn(val2), a_fn, val1, val2);

        assert_ops_mut!(@mut a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(@mut a_fn(val1), &b_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(@mut a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(@mut a_fn(val1), b_fn(val2), a_fn, val1, val2);
    }

    #[test]
    fn ops_gen_mut() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_mut!(@ref &mut x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(@ref &mut x_fn(val1), &y_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(@ref &mut x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(@ref &mut x_fn(val1), y_fn(val2), x_fn, val1, val2);

        assert_ops_mut!(@mut x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(@mut x_fn(val1), &y_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(@mut x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(@mut x_fn(val1), y_fn(val2), x_fn, val1, val2);
    }
}

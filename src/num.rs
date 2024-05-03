use crate::{ops::*, ops_checked_impl};

pub trait Number: Sized + Default + Clone + Copy + Ops + OpsAssign + PartialEq + PartialOrd {
    type Type;

    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;

    fn val(&self) -> &Self::Type;
}

pub trait Int: Number + AddChecked + SubChecked + MulChecked + DivChecked {
    const BITS: u32;
}

pub trait Signed: Int {}
pub trait Unsigned: Int {}
pub trait Float: Number {}

macro_rules! number_impl {
    ($type:ty, $zero:expr, $one:expr $(,)?) => {
        impl Ops<$type> for $type {
            type Output = $type;
        }

        impl Ops<$type> for &$type {
            type Output = $type;
        }

        impl Ops<&$type> for $type {
            type Output = $type;
        }

        impl Ops<&$type> for &$type {
            type Output = $type;
        }

        impl OpsRem<$type> for $type {
            type Output = $type;
        }

        impl OpsRem<$type> for &$type {
            type Output = $type;
        }

        impl OpsRem<&$type> for $type {
            type Output = $type;
        }

        impl OpsRem<&$type> for &$type {
            type Output = $type;
        }

        impl OpsAssign<$type> for $type {
        }

        impl OpsAssign<&$type> for $type {
        }

        impl OpsRemAssign<$type> for $type {
        }

        impl OpsRemAssign<&$type> for $type {
        }

        impl OpsFrom for $type {
        }
        impl OpsRemFrom for $type {
        }

        impl Number for $type {
            type Type = $type;

            const MAX: Self = <$type>::MAX;
            const MIN: Self = <$type>::MIN;
            const ONE: Self = $zero;
            const ZERO: Self = $one;

            fn val(&self) -> &Self::Type {
                self
            }
        }
    };
}

macro_rules! int_impl {
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type, 0, 1);

        impl OpsBit<$type> for $type {
            type Output = $type;
        }

        impl OpsBit<$type> for &$type {
            type Output = $type;
        }

        impl OpsBit<&$type> for $type {
            type Output = $type;
        }

        impl OpsBit<&$type> for &$type {
            type Output = $type;
        }

        impl OpsShift<$type> for $type {
            type Output = $type;
        }

        impl OpsShift<$type> for &$type {
            type Output = $type;
        }

        impl OpsShift<&$type> for $type {
            type Output = $type;
        }

        impl OpsShift<&$type> for &$type {
            type Output = $type;
        }

        impl OpsAll<$type> for $type {
            type Output = $type;
        }

        impl OpsAll<$type> for &$type {
            type Output = $type;
        }

        impl OpsAll<&$type> for $type {
            type Output = $type;
        }

        impl OpsAll<&$type> for &$type {
            type Output = $type;
        }

        impl OpsBitAssign<$type> for $type {
        }

        impl OpsBitAssign<&$type> for $type {
        }

        impl OpsShiftAssign<$type> for $type {
        }

        impl OpsShiftAssign<&$type> for $type {
        }

        impl OpsAssignAll<$type> for $type {
        }

        impl OpsAssignAll<&$type> for $type {
        }

        impl OpsBitFrom for $type {
        }

        impl OpsShiftFrom for $type {
        }

        impl OpsNotFrom for $type {
        }

        impl OpsAllFrom for $type {
        }

        impl Int for $type {
            const BITS: u32 = <$type>::BITS;
        }

        impl $trait for $type {
        }

        ops_checked_impl!($type);
    };
}

macro_rules! float_impl {
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type, 0.0, 1.0);

        impl $trait for $type {
        }
    };
}

macro_rules! int_arr_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(int_impl!($trait, $type,);)+
    };
}

macro_rules! float_arr_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(float_impl!($trait, $type);)+
    };
}

int_arr_impl!(Signed, [i8, i16, i32, i64, i128]);
int_arr_impl!(Unsigned, [u8, u16, u32, u64, u128]);
float_arr_impl!(Float, [f32, f64]);

impl OpsNegFrom for i8 {
}

impl OpsNegFrom for i16 {
}

impl OpsNegFrom for i32 {
}

impl OpsNegFrom for i64 {
}

impl OpsNegFrom for i128 {
}

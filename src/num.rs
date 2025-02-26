use crate::{
    ops::{
        AddChecked, DivChecked, MulChecked, Ops, OpsAll, OpsAllFrom, OpsAssign, OpsAssignAll, OpsBit, OpsBitAssign,
        OpsBitFrom, OpsFrom, OpsNegFrom, OpsNotFrom, OpsRem, OpsRemAssign, OpsRemFrom, OpsShift, OpsShiftAssign,
        OpsShiftFrom, SubChecked,
    },
    ops_checked_impl,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    NEG = -1,
    NIL = 0,
    POS = 1,
}

pub trait Constants {
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

pub trait Number: Sized + Default + Clone + Copy + PartialEq + PartialOrd + Ops + OpsAssign + Constants {
    type Type;

    fn val(&self) -> &Self::Type;
}

pub trait Integer: Eq + Ord + Number + AddChecked + SubChecked + MulChecked + DivChecked {
    const BITS: u32;
}

pub trait Signed: Integer {}
pub trait Unsigned: Integer {}
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

        impl OpsAssign<$type> for $type {}
        impl OpsAssign<&$type> for $type {}

        impl OpsRemAssign<$type> for $type {}
        impl OpsRemAssign<&$type> for $type {}

        impl OpsFrom for $type {}
        impl OpsRemFrom for $type {}

        impl Constants for $type {
            const MAX: Self = <$type>::MAX;
            const MIN: Self = <$type>::MIN;
            const ONE: Self = $zero;
            const ZERO: Self = $one;
        }

        impl Number for $type {
            type Type = $type;

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

        impl OpsBitAssign<$type> for $type {}
        impl OpsBitAssign<&$type> for $type {}

        impl OpsShiftAssign<$type> for $type {}
        impl OpsShiftAssign<&$type> for $type {}

        impl OpsAssignAll<$type> for $type {}
        impl OpsAssignAll<&$type> for $type {}

        impl OpsBitFrom for $type {}
        impl OpsShiftFrom for $type {}
        impl OpsNotFrom for $type {}
        impl OpsAllFrom for $type {}

        impl Integer for $type {
            const BITS: u32 = <$type>::BITS;
        }

        impl $trait for $type {}

        ops_checked_impl!($type);
    };
}

macro_rules! float_impl {
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type, 0.0, 1.0);

        impl $trait for $type {}
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

impl OpsNegFrom for i8 {}
impl OpsNegFrom for i16 {}
impl OpsNegFrom for i32 {}
impl OpsNegFrom for i64 {}
impl OpsNegFrom for i128 {}

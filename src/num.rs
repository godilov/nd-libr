use crate::ops::{
    AddChecked, DivChecked, MulChecked, Ops, OpsAll, OpsAllAssign, OpsAllFrom, OpsAssign, OpsBit, OpsBitAssign,
    OpsBitFrom, OpsChecked, OpsFrom, OpsNegFrom, OpsNotFrom, OpsRem, OpsRemAssign, OpsRemFrom, OpsShift,
    OpsShiftAssign, OpsShiftFrom, SubChecked,
};
use std::fmt::Display;

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    #[default]
    ZERO = 0,
    NEG = -1,
    POS = 1,
}

pub trait Constants {
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

pub trait Number: Sized + Default + Display + Clone + PartialEq + PartialOrd + Constants + Ops + OpsAssign {
    type Type;

    fn val(&self) -> &Self::Type;
}

pub trait Integer: Eq + Ord + Number + OpsChecked {
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
            const ONE: Self = $one;
            const ZERO: Self = $zero;
        }

        impl Number for $type {
            type Type = $type;

            fn val(&self) -> &Self::Type {
                self
            }
        }
    };
}

macro_rules! int_impl_checked {
    ($type:ty $(,)?) => {
        impl AddChecked for $type {
            type Output = $type;

            fn checked_add(self, rhs: Self) -> Option<Self::Output> {
                self.checked_add(rhs)
            }
        }

        impl SubChecked for $type {
            type Output = $type;

            fn checked_sub(self, rhs: Self) -> Option<Self::Output> {
                self.checked_sub(rhs)
            }
        }

        impl MulChecked for $type {
            type Output = $type;

            fn checked_mul(self, rhs: Self) -> Option<Self::Output> {
                self.checked_mul(rhs)
            }
        }

        impl DivChecked for $type {
            type Output = $type;

            fn checked_div(self, rhs: Self) -> Option<Self::Output> {
                self.checked_div(rhs)
            }
        }

        impl OpsChecked for $type {}
    };
}

macro_rules! int_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(int_impl!($trait, $type,);)+
    };
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

        impl OpsAllAssign<$type> for $type {}
        impl OpsAllAssign<&$type> for $type {}

        impl OpsBitFrom for $type {}
        impl OpsShiftFrom for $type {}
        impl OpsNotFrom for $type {}
        impl OpsAllFrom for $type {}

        impl Integer for $type {
            const BITS: u32 = <$type>::BITS;
        }

        impl $trait for $type {}

        int_impl_checked!($type);
    };
}

macro_rules! float_impl {
    ($trait:ty, [$($type:ty),+] $(,)?) => {
        $(float_impl!($trait, $type);)+
    };
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type, 0.0, 1.0);

        impl $trait for $type {}
    };
}

int_impl!(Signed, [i8, i16, i32, i64, i128]);
int_impl!(Unsigned, [u8, u16, u32, u64, u128]);
float_impl!(Float, [f32, f64]);

impl OpsNegFrom for i8 {}
impl OpsNegFrom for i16 {}
impl OpsNegFrom for i32 {}
impl OpsNegFrom for i64 {}
impl OpsNegFrom for i128 {}

use crate::ops::*;

pub trait AddChecked<Rhs = Self> {
    type Output;

    fn checked_add(self, rhs: Rhs) -> Option<Self::Output>;
}

pub trait SubChecked<Rhs = Self> {
    type Output;

    fn checked_sub(self, rhs: Rhs) -> Option<Self::Output>;
}

pub trait MulChecked<Rhs = Self> {
    type Output;

    fn checked_mul(self, rhs: Rhs) -> Option<Self::Output>;
}

pub trait DivChecked<Rhs = Self> {
    type Output;

    fn checked_div(self, rhs: Rhs) -> Option<Self::Output>;
}

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

macro_rules! ops_checked_impl {
    ($type:ty $(,)?) => {
        impl AddChecked for $type {
            type Output = $type;

            fn checked_add(self, rhs: Self) -> Option<Self::Output> { self.checked_add(rhs) }
        }

        impl SubChecked for $type {
            type Output = $type;

            fn checked_sub(self, rhs: Self) -> Option<Self::Output> { self.checked_sub(rhs) }
        }

        impl MulChecked for $type {
            type Output = $type;

            fn checked_mul(self, rhs: Self) -> Option<Self::Output> { self.checked_mul(rhs) }
        }

        impl DivChecked for $type {
            type Output = $type;

            fn checked_div(self, rhs: Self) -> Option<Self::Output> { self.checked_div(rhs) }
        }
    };
}

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

        impl Number for $type {
            type Type = $type;

            const MAX: Self = <$type>::MAX;
            const MIN: Self = <$type>::MIN;
            const ONE: Self = $zero;
            const ZERO: Self = $one;

            fn val(&self) -> &Self::Type { self }
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

        impl Int for $type {
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

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

pub trait Ops<'ops, Rhs: 'ops = Self>:
    'ops
    + Sized
    + Add<Rhs>
    + Sub<Rhs>
    + Mul<Rhs>
    + Div<Rhs>
    + AddAssign<Rhs>
    + SubAssign<Rhs>
    + MulAssign<Rhs>
    + DivAssign<Rhs>
    + Add<&'ops Rhs>
    + Sub<&'ops Rhs>
    + Mul<&'ops Rhs>
    + Div<&'ops Rhs>
    + AddAssign<&'ops Rhs>
    + SubAssign<&'ops Rhs>
    + MulAssign<&'ops Rhs>
    + DivAssign<&'ops Rhs>
where
    &'ops Self: Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs> + Add<&'ops Rhs> + Sub<&'ops Rhs> + Mul<&'ops Rhs> + Div<&'ops Rhs>, {
}

pub trait OpsScalar<'ops, N: 'ops + Number>:
    'ops + Sized + Add<N> + Sub<N> + Mul<N> + Div<N> + AddAssign<N> + SubAssign<N> + MulAssign<N> + DivAssign<N>
where
    N: Add<Self>
        + Sub<Self>
        + Mul<Self>
        + Div<Self>
        + AddAssign<Self>
        + SubAssign<Self>
        + MulAssign<Self>
        + DivAssign<Self>
        + Add<&'ops Self>
        + Sub<&'ops Self>
        + Mul<&'ops Self>
        + Div<&'ops Self>
        + AddAssign<&'ops Self>
        + SubAssign<&'ops Self>
        + MulAssign<&'ops Self>
        + DivAssign<&'ops Self>,
    &'ops N: Add<Self>
        + Sub<Self>
        + Mul<Self>
        + Div<Self>
        + AddAssign<Self>
        + SubAssign<Self>
        + MulAssign<Self>
        + DivAssign<Self>
        + Add<&'ops Self>
        + Sub<&'ops Self>
        + Mul<&'ops Self>
        + Div<&'ops Self>
        + AddAssign<&'ops Self>
        + SubAssign<&'ops Self>
        + MulAssign<&'ops Self>
        + DivAssign<&'ops Self>, {
}

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

pub trait Number: Sized + Clone + Copy + Add + Sub + Mul + Div + PartialEq + PartialOrd {
    type Type;

    const MIN: Self::Type;
    const MAX: Self::Type;

    fn value(&self) -> &Self::Type;
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
    ($type:ty $(,)?) => {
        impl Number for $type {
            type Type = $type;

            const MAX: Self::Type = <$type>::MAX;
            const MIN: Self::Type = <$type>::MIN;

            fn value(&self) -> &Self::Type { self }
        }
    };
}

macro_rules! int_impl {
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type);

        impl Int for $type {
            const BITS: u32 = <$type>::BITS;
        }

        impl $trait for $type {}

        ops_checked_impl!($type);
    };
}

macro_rules! float_impl {
    ($trait:ty, $type:ty $(,)?) => {
        number_impl!($type);

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

pub(crate) use ops_checked_impl;

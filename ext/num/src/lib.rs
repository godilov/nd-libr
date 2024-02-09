use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

pub trait Ops<Rhs = Self>: Sized + Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs>
where
    Rhs: Ops<Self>, {
    type Output;
}

pub trait OpsAssign<Rhs = Self>: AddAssign<Rhs> + SubAssign<Rhs> + MulAssign<Rhs> + DivAssign<Rhs> {
    type Output;
}

pub trait OpsAll<'ops, Rhs = Self>
where
    Rhs: 'ops + Ops<Self> + Ops<&'ops Self>,
    Self: 'ops + Ops<Rhs> + Ops<&'ops Rhs>,
    &'ops Rhs: Ops<Self> + Ops<&'ops Self>,
    &'ops Self: Ops<Rhs> + Ops<&'ops Rhs>, {
}

#[macro_export]
macro_rules! ops_impl {
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | -> $type:ty $fn:block) => {
        impl $op_trait<$type2> for $type1 {
            type Output = <Self as Ops<$type2>>::Output;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $type2) -> Self::Output { (|$lhs: $type1, $rhs: $type2| $fn)(self, rhs) }
        }

        impl $op_trait<$type2> for &$type1 {
            type Output = <Self as Ops<$type2>>::Output;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $type2) -> Self::Output { (|$lhs: &$type1, $rhs: $type2| $fn)(self, rhs) }
        }

        impl $op_trait<&$type2> for $type1 {
            type Output = <Self as Ops<$type2>>::Output;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$type2) -> Self::Output { (|$lhs: $type1, $rhs: &$type2| $fn)(self, rhs) }
        }

        impl $op_trait<&$type2> for &$type1 {
            type Output = <Self as Ops<$type2>>::Output;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$type2) -> Self::Output { (|$lhs: &$type1, $rhs: &$type2| $fn)(self, rhs) }
        }
    };
    (+, | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | -> $type:ty $fn:block) => { ops_impl!(Add, add, |$lhs: $type1, $rhs: $type2| -> $type $fn); };
    (-, | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | -> $type:ty $fn:block) => { ops_impl!(Sub, sub, |$lhs: $type1, $rhs: $type2| -> $type $fn); };
    (*, | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | -> $type:ty $fn:block) => { ops_impl!(Mul, mul, |$lhs: $type1, $rhs: $type2| -> $type $fn); };
    (/, | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | -> $type:ty $fn:block) => { ops_impl!(Div, div, |$lhs: $type1, $rhs: $type2| -> $type $fn); };
    (
        | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | -> $type:ty, + $add:block, - $sub:block, * $mul:block, / $div:block
    ) => {
        ops_impl!(+, |$lhs: $type1, $rhs: $type2| -> $type $add);
        ops_impl!(-, |$lhs: $type1, $rhs: $type2| -> $type $sub);
        ops_impl!(*, |$lhs: $type1, $rhs: $type2| -> $type $mul);
        ops_impl!(/, |$lhs: $type1, $rhs: $type2| -> $type $div);

        impl Ops<$type2> for $type1 { type Output = $type; }
        impl Ops<$type2> for &$type1 { type Output = $type; }
        impl Ops<&$type2> for $type1 { type Output = $type; }
        impl Ops<&$type2> for &$type1 { type Output = $type; }

        impl<'ops> OpsAll<'ops, $type2> for $type1 {}
    };
    (
        | $lhs:ident : $type1:ty, $rhs:ident : $type2:ty | => $type:ty, + $add:block, - $sub:block, * $mul:block, / $div:block
    ) => {
        ops_impl!(|$lhs: $type1, $rhs: $type2| -> $type, + $add, - $sub, * $mul, / $div);
        ops_impl!(|$rhs: $type2, $lhs: $type1| -> $type, + $add, - $sub, * $mul, / $div);
    };
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

#[cfg(test)]
mod tests {
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

    use super::{Ops, OpsAll, OpsAssign};

    struct X {
        x: u64,
    }

    struct A {
        x: u64,
    }

    struct B {
        x: u64,
    }

    ops_impl!(|a: X, b: X| -> X,
          + { X { x: a.x + b.x } },
          - { X { x: a.x - b.x } },
          * { X { x: a.x * b.x } },
          / { X { x: a.x / b.x } });

    ops_impl!(|a: A, b: B| => A,
          + { A { x: a.x + b.x } },
          - { A { x: a.x - b.x } },
          * { A { x: a.x * b.x } },
          / { A { x: a.x / b.x } });

    #[test]
    fn ops() {}
}

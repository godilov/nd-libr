use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};

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

pub trait OpsAssignAll<'ops, Rhs = Self>: OpsAssign<Rhs> + OpsAssign<&'ops Rhs>
where
    Rhs: 'ops, {
}

macro_rules! ops_impl_bin_internal {
    ($op_trait:ident, $op_name:ident, | $lhs:ident : & $typel:ty, $rhs:ident : & $typer:ty | -> $type:ty $fn:block) => {
        impl $op_trait<&$typer> for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$typer) -> Self::Output { (|$lhs: &$typel, $rhs: &$typer| $fn)(self, rhs) }
        }
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : & $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        impl $op_trait<$typer> for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $typer) -> Self::Output { (|$lhs: &$typel, $rhs: $typer| $fn)(self, rhs) }
        }
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty, $rhs:ident : & $typer:ty | -> $type:ty $fn:block) => {
        impl $op_trait<&$typer> for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$typer) -> Self::Output { (|$lhs: $typel, $rhs: &$typer| $fn)(self, rhs) }
        }
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        impl $op_trait<$typer> for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $typer) -> Self::Output { (|$lhs: $typel, $rhs: $typer| $fn)(self, rhs) }
        }
    };
}

macro_rules! ops_impl_internal {
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => {
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => {
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        ops_impl_bin_internal!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    (+ , $($t:tt)+) => { ops_impl_internal!(Add, add, $($t)+); };
    (- , $($t:tt)+) => { ops_impl_internal!(Sub, sub, $($t)+); };
    (* , $($t:tt)+) => { ops_impl_internal!(Mul, mul, $($t)+); };
    (/ , $($t:tt)+) => { ops_impl_internal!(Div, div, $($t)+); };
    (% , $($t:tt)+) => { ops_impl_internal!(Rem, rem, $($t)+); };
}

#[macro_export]
macro_rules! ops_impl {
    ($op:tt, | $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => { ops_impl_internal!($op, |$lhs: &$typel, $rhs: &$typer| -> $type $fn); };
    ($op:tt, | $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => { ops_impl_internal!($op, |$lhs: &$typel, $rhs: $typer| -> $type $fn); };
    ($op:tt, | $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => { ops_impl_internal!($op, |$lhs: $typel, $rhs: &$typer| -> $type $fn); };
    ($op:tt, | $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => { ops_impl_internal!($op, |$lhs: $typel, $rhs: $typer| -> $type $fn); };
    (| $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | -> $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(+, |$lhs: &$typel, $rhs: &$typer| -> $type $add);
        ops_impl!(-, |$lhs: &$typel, $rhs: &$typer| -> $type $sub);
        ops_impl!(*, |$lhs: &$typel, $rhs: &$typer| -> $type $mul);
        ops_impl!(/, |$lhs: &$typel, $rhs: &$typer| -> $type $div);

        impl Ops<$typer> for $typel { type Output = $type; }
        impl Ops<$typer> for &$typel { type Output = $type; }
        impl Ops<&$typer> for $typel { type Output = $type; }
        impl Ops<&$typer> for &$typel { type Output = $type; }

        impl<'ops> OpsAll<'ops, $typer> for $typel {}
    };
    (| $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | -> $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(+, |$lhs: &$typel, $rhs: $typer| -> $type $add);
        ops_impl!(-, |$lhs: &$typel, $rhs: $typer| -> $type $sub);
        ops_impl!(*, |$lhs: &$typel, $rhs: $typer| -> $type $mul);
        ops_impl!(/, |$lhs: &$typel, $rhs: $typer| -> $type $div);

        impl Ops<$typer> for $typel { type Output = $type; }
        impl Ops<$typer> for &$typel { type Output = $type; }
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(+, |$lhs: $typel, $rhs: &$typer| -> $type $add);
        ops_impl!(-, |$lhs: $typel, $rhs: &$typer| -> $type $sub);
        ops_impl!(*, |$lhs: $typel, $rhs: &$typer| -> $type $mul);
        ops_impl!(/, |$lhs: $typel, $rhs: &$typer| -> $type $div);

        impl Ops<$typer> for $typel { type Output = $type; }
        impl Ops<&$typer> for $typel { type Output = $type; }
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(+, |$lhs: $typel, $rhs: $typer| -> $type $add);
        ops_impl!(-, |$lhs: $typel, $rhs: $typer| -> $type $sub);
        ops_impl!(*, |$lhs: $typel, $rhs: $typer| -> $type $mul);
        ops_impl!(/, |$lhs: $typel, $rhs: $typer| -> $type $div);

        impl Ops<$typer> for $typel { type Output = $type; }
    };
    (| $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | => $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(|$lhs: &$typel, $rhs: &$typer| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
        ops_impl!(|$rhs: &$typer, $lhs: &$typel| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
    };
    (| $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | => $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(|$lhs: &$typel, $rhs: $typer| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
        ops_impl!(|$rhs: &$typer, $lhs: $typel| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | => $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(|$lhs: $typel, $rhs: &$typer| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
        ops_impl!(|$rhs: $typer, $lhs: &$typel| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | => $type:ty, + $add:block - $sub:block * $mul:block / $div:block $(% $rem:block)?) => {
        ops_impl!(|$lhs: $typel, $rhs: $typer| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
        ops_impl!(|$rhs: $typer, $lhs: $typel| -> $type, + $add - $sub * $mul / $div $(% $rem)?);
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
    use std::ops::{Add, Div, Mul, Sub};

    use super::{Ops, OpsAll};

    #[derive(Debug, PartialEq, Eq)]
    struct A {
        x: i64,
    }

    #[derive(Debug, PartialEq, Eq)]
    struct B {
        x: i64,
    }

    ops_impl!(|a: &A, b: &A| -> A,
              + { A { x: a.x + b.x } }
              - { A { x: a.x - b.x } }
              * { A { x: a.x * b.x } }
              / { A { x: a.x / b.x } });

    ops_impl!(|a: &A, b: &B| => A,
              + { A { x: a.x + b.x } }
              - { A { x: a.x - b.x } }
              * { A { x: a.x * b.x } }
              / { A { x: a.x / b.x } });

    #[test]
    fn ops() {
        let a1 = A { x: 16 };
        let a2 = A { x: 2 };
        let b = B { x: 2 };

        let a_fn = |x: i64| A { x };
        let b_fn = |x: i64| B { x };

        assert_eq!(&a1 + &a2, A { x: 18 });
        assert_eq!(&a1 - &a2, A { x: 14 });
        assert_eq!(&a1 * &a2, A { x: 32 });
        assert_eq!(&a1 / &a2, A { x: 8 });

        assert_eq!(&a1 + &b, A { x: 18 });
        assert_eq!(&a1 - &b, A { x: 14 });
        assert_eq!(&a1 * &b, A { x: 32 });
        assert_eq!(&a1 / &b, A { x: 8 });

        assert_eq!(a_fn(16) + a_fn(2), A { x: 18 });
        assert_eq!(a_fn(16) - a_fn(2), A { x: 14 });
        assert_eq!(a_fn(16) * a_fn(2), A { x: 32 });
        assert_eq!(a_fn(16) / a_fn(2), A { x: 8 });

        assert_eq!(a_fn(16) + b_fn(2), A { x: 18 });
        assert_eq!(a_fn(16) - b_fn(2), A { x: 14 });
        assert_eq!(a_fn(16) * b_fn(2), A { x: 32 });
        assert_eq!(a_fn(16) / b_fn(2), A { x: 8 });
    }
}

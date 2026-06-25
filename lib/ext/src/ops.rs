#![doc = include_str!("../docs/ops.md")]

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

macro_rules! nd_ops_impl {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(nd_ops_impl!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
        ndops::def! { @ndun crate (value: &$primitive) -> $primitive, [
            ! !value,
            - -value,
            - @checked value.checked_neg(),
            - @strict value.strict_neg(),
            - @wrapping value.wrapping_neg(),
            - @saturating value.saturating_neg(),
            - @overflowing value.overflowing_neg(),
            posx value.abs(),
            posx @checked value.checked_abs(),
            posx @strict value.strict_abs(),
            posx @wrapping value.wrapping_abs(),
            posx @saturating value.saturating_abs(),
            posx @overflowing value.overflowing_abs(),
            negx value.wrapping_abs().wrapping_neg(),
            negx @checked Some(value.wrapping_abs().wrapping_neg()),
            negx @strict value.wrapping_abs().wrapping_neg(),
            negx @wrapping value.wrapping_abs().wrapping_neg(),
            negx @saturating value.wrapping_abs().wrapping_neg(),
            negx @overflowing (value.wrapping_abs().wrapping_neg(), false),
        ] }

        nd_ops_impl!(@impl $primitive);
    };
    (@unsigned $primitive:ty $(,)?) => {
        ndops::def! { @ndun crate (value: &$primitive) -> $primitive, [
            ! !value,
        ] }

        nd_ops_impl!(@impl $primitive);
    };
    (@impl $primitive:ty $(,)?) => {
        ndops::def! { @ndbin crate (lhs: &$primitive, rhs: &$primitive) -> $primitive, [
            + lhs.add(rhs),
            - lhs.sub(rhs),
            * lhs.mul(rhs),
            / lhs.div(rhs),
            % lhs.rem(rhs),
            | lhs.bitor(rhs),
            & lhs.bitand(rhs),
            ^ lhs.bitxor(rhs),
            + @checked lhs.checked_add(*rhs),
            - @checked lhs.checked_sub(*rhs),
            * @checked lhs.checked_mul(*rhs),
            / @checked lhs.checked_div(*rhs),
            % @checked lhs.checked_rem(*rhs),
            + @strict lhs.strict_add(*rhs),
            - @strict lhs.strict_sub(*rhs),
            * @strict lhs.strict_mul(*rhs),
            / @strict lhs.strict_div(*rhs),
            % @strict lhs.strict_rem(*rhs),
            + @wrapping lhs.wrapping_add(*rhs),
            - @wrapping lhs.wrapping_sub(*rhs),
            * @wrapping lhs.wrapping_mul(*rhs),
            / @wrapping lhs.wrapping_div(*rhs),
            % @wrapping lhs.wrapping_rem(*rhs),
            + @saturating lhs.saturating_add(*rhs),
            - @saturating lhs.saturating_sub(*rhs),
            * @saturating lhs.saturating_mul(*rhs),
            / @saturating lhs.saturating_div(*rhs),
            % @saturating lhs.wrapping_rem(*rhs),
            + @overflowing lhs.overflowing_add(*rhs),
            - @overflowing lhs.overflowing_sub(*rhs),
            * @overflowing lhs.overflowing_mul(*rhs),
            / @overflowing lhs.overflowing_div(*rhs),
            % @overflowing lhs.overflowing_rem(*rhs),
        ] }

        ndops::def! { @ndbin crate (lhs: &$primitive, rhs: usize) -> $primitive, [
            << lhs.shl(rhs),
            >> lhs.shr(rhs),
            << @strict lhs.strict_shl(rhs as u32),
            >> @strict lhs.strict_shr(rhs as u32),
            << @checked lhs.checked_shl(rhs as u32),
            >> @checked lhs.checked_shr(rhs as u32),
            << @overflowing lhs.overflowing_shl(rhs as u32),
            >> @overflowing lhs.overflowing_shr(rhs as u32),
            << @unbounded lhs.unbounded_shl(rhs as u32),
            >> @unbounded lhs.unbounded_shr(rhs as u32),
        ] }

        ndops::def! { @ndmut crate (lhs: &mut $primitive, rhs: &$primitive), [
            += lhs.add_assign(rhs),
            -= lhs.sub_assign(rhs),
            *= lhs.mul_assign(rhs),
            /= lhs.div_assign(rhs),
            %= lhs.rem_assign(rhs),
            |= lhs.bitor_assign(rhs),
            &= lhs.bitand_assign(rhs),
            ^= lhs.bitxor_assign(rhs),
            += @strict *lhs = lhs.strict_add(*rhs),
            -= @strict *lhs = lhs.strict_sub(*rhs),
            *= @strict *lhs = lhs.strict_mul(*rhs),
            /= @strict *lhs = lhs.strict_div(*rhs),
            %= @strict *lhs = lhs.strict_rem(*rhs),
            += @wrapping *lhs = lhs.wrapping_add(*rhs),
            -= @wrapping *lhs = lhs.wrapping_sub(*rhs),
            *= @wrapping *lhs = lhs.wrapping_mul(*rhs),
            /= @wrapping *lhs = lhs.wrapping_div(*rhs),
            %= @wrapping *lhs = lhs.wrapping_rem(*rhs),
            += @saturating *lhs = lhs.saturating_add(*rhs),
            -= @saturating *lhs = lhs.saturating_sub(*rhs),
            *= @saturating *lhs = lhs.saturating_mul(*rhs),
            /= @saturating *lhs = lhs.saturating_div(*rhs),
            %= @saturating *lhs = lhs.wrapping_rem(*rhs),
        ] }

        ndops::def! { @ndmut crate (lhs: &mut $primitive, rhs: usize), [
            <<= lhs.shl_assign(rhs),
            >>= lhs.shr_assign(rhs),
            <<= @strict *lhs = lhs.strict_shl(rhs as u32),
            >>= @strict *lhs = lhs.strict_shr(rhs as u32),
            <<= @unbounded *lhs = lhs.unbounded_shl(rhs as u32),
            >>= @unbounded *lhs = lhs.unbounded_shr(rhs as u32),
        ] }
    };
}

macro_rules! nd_opsx_impl {
    ([$($single:ty > $double:ty),+ $(,)?]) => {
        $(nd_opsx_impl!($single > $double);)+
    };
    ($single:ty > $double:ty $(,)?) => {
        ndops::def! { @ndbin crate (&lhs: &$single, &rhs: &$single) -> $double, [
            addx lhs as $double + rhs as $double,
            mulx lhs as $double * rhs as $double,
        ] }
    };
}

/// Number with ops by immutable reference.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with &'num N)]
#[ndfwd::cmp(self.0 with &'num N)]
#[ndfwd::fmt(self.0 with &'num N)]
#[ndfwd::iter(self.0 with &'num N)]
#[derive(Debug, Clone, Copy)]
pub struct Ref<'num, N>(pub &'num N);

/// Number with ops by mutable reference.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with &'num mut N)]
#[ndfwd::cmp(self.0 with &'num mut N)]
#[ndfwd::fmt(self.0 with &'num mut N)]
#[ndfwd::iter(self.0 with &'num mut N)]
#[derive(Debug)]
pub struct Mut<'num, N>(pub &'num mut N);

/// `Nd-kind` extension for [`std::ops::Not`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNot<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_not(value: &Value) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Neg`].
///
/// # Related
///
/// - [`NdNegChecked`] - checked alternative.
/// - [`NdNegStrict`] - strict alternative.
/// - [`NdNegWrapping`] - wrapping alternative.
/// - [`NdNegSaturating`] - saturating alternative.
/// - [`NdNegOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNeg<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_neg(value: &Value) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Neg`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegChecked<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_neg_checked(value: &Value) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Neg`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegStrict<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_neg_strict(value: &Value) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Neg`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegWrapping<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_neg_wrapping(value: &Value) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Neg`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegSaturating<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_neg_saturating(value: &Value) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Neg`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegOverflowing<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_neg_overflowing(value: &Value) -> (Self::Type, bool);
}

/// `Nd-kind` positive absolute value.
///
/// # Related
///
/// - [`NdPosxChecked`] - checked alternative.
/// - [`NdPosxStrict`] - strict alternative.
/// - [`NdPosxWrapping`] - wrapping alternative.
/// - [`NdPosxSaturating`] - saturating alternative.
/// - [`NdPosxOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdPosx<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_posx(value: &Value) -> Self::Type;
}

/// `Nd-kind` positive absolute value with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdPosxChecked<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_posx_checked(value: &Value) -> Option<Self::Type>;
}

/// `Nd-kind` positive absolute value with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdPosxStrict<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_posx_strict(value: &Value) -> Self::Type;
}

/// `Nd-kind` positive absolute value with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdPosxWrapping<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_posx_wrapping(value: &Value) -> Self::Type;
}

/// `Nd-kind` positive absolute value with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdPosxSaturating<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_posx_saturating(value: &Value) -> Self::Type;
}

/// `Nd-kind` positive absolute value with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdPosxOverflowing<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_posx_overflowing(value: &Value) -> (Self::Type, bool);
}

/// `Nd-kind` negative absolute value.
///
/// # Related
///
/// - [`NdNegxChecked`] - checked alternative.
/// - [`NdNegxStrict`] - strict alternative.
/// - [`NdNegxWrapping`] - wrapping alternative.
/// - [`NdNegxSaturating`] - saturating alternative.
/// - [`NdNegxOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegx<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_negx(value: &Value) -> Self::Type;
}

/// `Nd-kind` negative absolute value with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegxChecked<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_negx_checked(value: &Value) -> Option<Self::Type>;
}

/// `Nd-kind` negative absolute value with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegxStrict<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_negx_strict(value: &Value) -> Self::Type;
}

/// `Nd-kind` negative absolute value with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegxWrapping<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_negx_wrapping(value: &Value) -> Self::Type;
}

/// `Nd-kind` negative absolute value with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegxSaturating<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_negx_saturating(value: &Value) -> Self::Type;
}

/// `Nd-kind` negative absolute value with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdNegxOverflowing<Value = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_negx_overflowing(value: &Value) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::Add`].
///
/// # Related
///
/// - [`NdAddx`] - extended alternative.
/// - [`NdAddChecked`] - checked alternative.
/// - [`NdAddStrict`] - strict alternative.
/// - [`NdAddWrapping`] - wrapping alternative.
/// - [`NdAddSaturating`] - saturating alternative.
/// - [`NdAddOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAdd<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_add(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` add extended.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddx<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_addx(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Add`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddChecked<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_add_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Add`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddStrict<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_add_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Add`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddWrapping<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_add_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Add`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddSaturating<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_add_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Add`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddOverflowing<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_add_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::Sub`].
///
/// # Related
///
/// - [`NdSubChecked`] - checked alternative.
/// - [`NdSubStrict`] - strict alternative.
/// - [`NdSubWrapping`] - wrapping alternative.
/// - [`NdSubSaturating`] - saturating alternative.
/// - [`NdSubOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSub<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_sub(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Sub`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubChecked<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_sub_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Sub`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubStrict<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_sub_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Sub`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubWrapping<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_sub_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Sub`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubSaturating<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_sub_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Sub`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubOverflowing<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_sub_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::Mul`].
///
/// # Related
///
/// - [`NdMulx`] - extended alternative.
/// - [`NdMulChecked`] - checked alternative.
/// - [`NdMulStrict`] - strict alternative.
/// - [`NdMulWrapping`] - wrapping alternative.
/// - [`NdMulSaturating`] - saturating alternative.
/// - [`NdMulOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMul<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mul(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` mul extended.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulx<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mulx(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Mul`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulChecked<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mul_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Mul`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulStrict<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mul_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Mul`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulWrapping<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mul_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Mul`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulSaturating<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mul_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Mul`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulOverflowing<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_mul_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::Div`].
///
/// # Related
///
/// - [`NdDivChecked`] - checked alternative.
/// - [`NdDivStrict`] - strict alternative.
/// - [`NdDivWrapping`] - wrapping alternative.
/// - [`NdDivSaturating`] - saturating alternative.
/// - [`NdDivOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDiv<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_div(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Div`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivChecked<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_div_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Div`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivStrict<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_div_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Div`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivWrapping<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_div_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Div`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivSaturating<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_div_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Div`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivOverflowing<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_div_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::Rem`].
///
/// # Related
///
/// - [`NdRemChecked`] - checked alternative.
/// - [`NdRemStrict`] - strict alternative.
/// - [`NdRemWrapping`] - wrapping alternative.
/// - [`NdRemSaturating`] - saturating alternative.
/// - [`NdRemOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRem<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_rem(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Rem`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemChecked<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_rem_checked(lhs: &Lhs, rhs: &Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Rem`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemStrict<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_rem_strict(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Rem`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemWrapping<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_rem_wrapping(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Rem`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemSaturating<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_rem_saturating(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Rem`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemOverflowing<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_rem_overflowing(lhs: &Lhs, rhs: &Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::BitOr`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdBitOr<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_bitor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::BitAnd`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdBitAnd<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_bitand(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::BitXor`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdBitXor<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_bitxor(lhs: &Lhs, rhs: &Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shl`].
///
/// # Related
///
/// - [`NdShlChecked`] - checked alternative.
/// - [`NdShlStrict`] - strict alternative.
/// - [`NdShlUnbounded`] - unbounded alternative.
/// - [`NdShlOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShl<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shl(lhs: &Lhs, rhs: Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shl`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlChecked<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shl_checked(lhs: &Lhs, rhs: Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Shl`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlStrict<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shl_strict(lhs: &Lhs, rhs: Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shl`] with unbounded semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlUnbounded<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shl_unbounded(lhs: &Lhs, rhs: Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shl`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlOverflowing<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shl_overflowing(lhs: &Lhs, rhs: Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::Shr`].
///
/// # Related
///
/// - [`NdShrChecked`] - checked alternative.
/// - [`NdShrStrict`] - strict alternative.
/// - [`NdShrUnbounded`] - unbounded alternative.
/// - [`NdShrOverflowing`] - overflowing alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShr<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shr(lhs: &Lhs, rhs: Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shr`] with checked semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrChecked<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shr_checked(lhs: &Lhs, rhs: Rhs) -> Option<Self::Type>;
}

/// `Nd-kind` extension for [`std::ops::Shr`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrStrict<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shr_strict(lhs: &Lhs, rhs: Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shr`] with unbounded semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrUnbounded<Lhs = Self, Rhs = Self> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shr_unbounded(lhs: &Lhs, rhs: Rhs) -> Self::Type;
}

/// `Nd-kind` extension for [`std::ops::Shr`] with overflowing semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrOverflowing<Lhs = Self, Rhs = usize> {
    /// Operation resulting type.
    type Type;

    /// Operation function.
    fn nd_shr_overflowing(lhs: &Lhs, rhs: Rhs) -> (Self::Type, bool);
}

/// `Nd-kind` extension for [`std::ops::AddAssign`].
///
/// # Related
///
/// - [`NdAddAssignStrict`] - strict alternative.
/// - [`NdAddAssignWrapping`] - wrapping alternative.
/// - [`NdAddAssignSaturating`] - saturating alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_add_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::AddAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddAssignStrict<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_add_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::AddAssign`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddAssignWrapping<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_add_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::AddAssign`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdAddAssignSaturating<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_add_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::SubAssign`].
///
/// # Related
///
/// - [`NdSubAssignStrict`] - strict alternative.
/// - [`NdSubAssignWrapping`] - wrapping alternative.
/// - [`NdSubAssignSaturating`] - saturating alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_sub_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::SubAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubAssignStrict<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_sub_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::SubAssign`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubAssignWrapping<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_sub_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::SubAssign`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdSubAssignSaturating<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_sub_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::MulAssign`].
///
/// # Related
///
/// - [`NdMulAssignStrict`] - strict alternative.
/// - [`NdMulAssignWrapping`] - wrapping alternative.
/// - [`NdMulAssignSaturating`] - saturating alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_mul_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::MulAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulAssignStrict<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_mul_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::MulAssign`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulAssignWrapping<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_mul_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::MulAssign`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdMulAssignSaturating<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_mul_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::DivAssign`].
///
/// # Related
///
/// - [`NdDivAssignStrict`] - strict alternative.
/// - [`NdDivAssignWrapping`] - wrapping alternative.
/// - [`NdDivAssignSaturating`] - saturating alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_div_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::DivAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivAssignStrict<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_div_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::DivAssign`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivAssignWrapping<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_div_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::DivAssign`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdDivAssignSaturating<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_div_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::RemAssign`].
///
/// # Related
///
/// - [`NdRemAssignStrict`] - strict alternative.
/// - [`NdRemAssignWrapping`] - wrapping alternative.
/// - [`NdRemAssignSaturating`] - saturating alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_rem_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::RemAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemAssignStrict<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_rem_assign_strict(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::RemAssign`] with wrapping semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemAssignWrapping<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_rem_assign_wrapping(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::RemAssign`] with saturating semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdRemAssignSaturating<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_rem_assign_saturating(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::BitOrAssign`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdBitOrAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_bitor_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::BitAndAssign`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdBitAndAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_bitand_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::BitXorAssign`].
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdBitXorAssign<Lhs = Self, Rhs = Self> {
    /// Operation function.
    fn nd_bitxor_assign(lhs: &mut Lhs, rhs: &Rhs);
}

/// `Nd-kind` extension for [`std::ops::ShlAssign`].
///
/// # Related
///
/// - [`NdShlAssignStrict`] - strict alternative.
/// - [`NdShlAssignUnbounded`] - unbounded alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlAssign<Lhs = Self, Rhs = usize> {
    /// Operation function.
    fn nd_shl_assign(lhs: &mut Lhs, rhs: Rhs);
}

/// `Nd-kind` extension for [`std::ops::ShlAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlAssignStrict<Lhs = Self, Rhs = usize> {
    /// Operation function.
    fn nd_shl_assign_strict(lhs: &mut Lhs, rhs: Rhs);
}

/// `Nd-kind` extension for [`std::ops::ShlAssign`] with unbounded semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShlAssignUnbounded<Lhs = Self, Rhs = usize> {
    /// Operation function.
    fn nd_shl_assign_unbounded(lhs: &mut Lhs, rhs: Rhs);
}

/// `Nd-kind` extension for [`std::ops::ShrAssign`].
///
/// # Related
///
/// - [`NdShrAssignStrict`] - strict alternative.
/// - [`NdShrAssignUnbounded`] - unbounded alternative.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrAssign<Lhs = Self, Rhs = usize> {
    /// Operation function.
    fn nd_shr_assign(lhs: &mut Lhs, rhs: Rhs);
}

/// `Nd-kind` extension for [`std::ops::ShrAssign`] with strict semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrAssignStrict<Lhs = Self, Rhs = usize> {
    /// Operation function.
    fn nd_shr_assign_strict(lhs: &mut Lhs, rhs: Rhs);
}

/// `Nd-kind` extension for [`std::ops::ShrAssign`] with unbounded semantics.
///
/// For more info, see [module-level](crate::ops) and [crate-level](crate) documentation.
pub trait NdShrAssignUnbounded<Lhs = Self, Rhs = usize> {
    /// Operation function.
    fn nd_shr_assign_unbounded(lhs: &mut Lhs, rhs: Rhs);
}

/// Aggregate trait for all **non-assign** binary operations in [`std::ops`].
///
/// Auto-implemented for all types with required operations.
///
/// Requires [`Clone`] and [`Copy`] to avoid HRTB.
pub trait Ops<Rhs = Self, ShiftRhs = usize>:
    Sized
    + Copy
    + Add<Rhs, Output = Self::Type>
    + Sub<Rhs, Output = Self::Type>
    + Mul<Rhs, Output = Self::Type>
    + Div<Rhs, Output = Self::Type>
    + Rem<Rhs, Output = Self::Type>
    + BitOr<Rhs, Output = Self::Type>
    + BitAnd<Rhs, Output = Self::Type>
    + BitXor<Rhs, Output = Self::Type>
    + Shl<ShiftRhs, Output = Self::Type>
    + Shr<ShiftRhs, Output = Self::Type>
{
    /// Operations shared resulting type.
    type Type;
}

/// Aggregate trait for all **assign** binary operations in [`std::ops`].
///
/// Auto-implemented for all types with required operations.
///
/// Requires [`Clone`] and [`Copy`] to avoid HRTB.
pub trait OpsAssign<Rhs = Self, ShiftRhs = usize>:
    Copy
    + AddAssign<Rhs>
    + SubAssign<Rhs>
    + MulAssign<Rhs>
    + DivAssign<Rhs>
    + RemAssign<Rhs>
    + BitOrAssign<Rhs>
    + BitAndAssign<Rhs>
    + BitXorAssign<Rhs>
    + ShlAssign<ShiftRhs>
    + ShrAssign<ShiftRhs>
{
}

/// Aggregate trait for all **non-assign** binary operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOps<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAdd<Lhs, Rhs, Type = Self::All>
    + NdSub<Lhs, Rhs, Type = Self::All>
    + NdMul<Lhs, Rhs, Type = Self::All>
    + NdDiv<Lhs, Rhs, Type = Self::All>
    + NdRem<Lhs, Rhs, Type = Self::All>
    + NdBitOr<Lhs, Rhs, Type = Self::All>
    + NdBitAnd<Lhs, Rhs, Type = Self::All>
    + NdBitXor<Lhs, Rhs, Type = Self::All>
    + NdShl<Lhs, ShiftRhs, Type = Self::All>
    + NdShr<Lhs, ShiftRhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **non-assign** binary checked operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsChecked<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddChecked<Lhs, Rhs, Type = Self::All>
    + NdSubChecked<Lhs, Rhs, Type = Self::All>
    + NdMulChecked<Lhs, Rhs, Type = Self::All>
    + NdDivChecked<Lhs, Rhs, Type = Self::All>
    + NdRemChecked<Lhs, Rhs, Type = Self::All>
    + NdShlChecked<Lhs, ShiftRhs, Type = Self::All>
    + NdShrChecked<Lhs, ShiftRhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **non-assign** binary strict operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsStrict<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddStrict<Lhs, Rhs, Type = Self::All>
    + NdSubStrict<Lhs, Rhs, Type = Self::All>
    + NdMulStrict<Lhs, Rhs, Type = Self::All>
    + NdDivStrict<Lhs, Rhs, Type = Self::All>
    + NdRemStrict<Lhs, Rhs, Type = Self::All>
    + NdShlStrict<Lhs, ShiftRhs, Type = Self::All>
    + NdShrStrict<Lhs, ShiftRhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **non-assign** binary wrapping operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsWrapping<Lhs = Self, Rhs = Self>:
    NdAddWrapping<Lhs, Rhs, Type = Self::All>
    + NdSubWrapping<Lhs, Rhs, Type = Self::All>
    + NdMulWrapping<Lhs, Rhs, Type = Self::All>
    + NdDivWrapping<Lhs, Rhs, Type = Self::All>
    + NdRemWrapping<Lhs, Rhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **non-assign** binary saturating operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsSaturating<Lhs = Self, Rhs = Self>:
    NdAddSaturating<Lhs, Rhs, Type = Self::All>
    + NdSubSaturating<Lhs, Rhs, Type = Self::All>
    + NdMulSaturating<Lhs, Rhs, Type = Self::All>
    + NdDivSaturating<Lhs, Rhs, Type = Self::All>
    + NdRemSaturating<Lhs, Rhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **non-assign** binary overflowing operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsOverflowing<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddOverflowing<Lhs, Rhs, Type = Self::All>
    + NdSubOverflowing<Lhs, Rhs, Type = Self::All>
    + NdMulOverflowing<Lhs, Rhs, Type = Self::All>
    + NdDivOverflowing<Lhs, Rhs, Type = Self::All>
    + NdRemOverflowing<Lhs, Rhs, Type = Self::All>
    + NdShlOverflowing<Lhs, ShiftRhs, Type = Self::All>
    + NdShrOverflowing<Lhs, ShiftRhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **non-assign** binary unbounded operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsUnbounded<Lhs = Self, Rhs = Self>:
    NdShlUnbounded<Lhs, Rhs, Type = Self::All> + NdShrUnbounded<Lhs, Rhs, Type = Self::All>
{
    /// Operations shared resulting type.
    type All;
}

/// Aggregate trait for all **assign** binary operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsAssign<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddAssign<Lhs, Rhs>
    + NdSubAssign<Lhs, Rhs>
    + NdMulAssign<Lhs, Rhs>
    + NdDivAssign<Lhs, Rhs>
    + NdRemAssign<Lhs, Rhs>
    + NdBitOrAssign<Lhs, Rhs>
    + NdBitAndAssign<Lhs, Rhs>
    + NdBitXorAssign<Lhs, Rhs>
    + NdShlAssign<Lhs, ShiftRhs>
    + NdShrAssign<Lhs, ShiftRhs>
{
}

/// Aggregate trait for all **assign** binary strict operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsAssignStrict<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddAssignStrict<Lhs, Rhs>
    + NdSubAssignStrict<Lhs, Rhs>
    + NdMulAssignStrict<Lhs, Rhs>
    + NdDivAssignStrict<Lhs, Rhs>
    + NdRemAssignStrict<Lhs, Rhs>
    + NdShlAssignStrict<Lhs, Rhs>
    + NdShrAssignStrict<Lhs, Rhs>
{
}

/// Aggregate trait for all **assign** binary wrapping operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsAssignWrapping<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddAssignWrapping<Lhs, Rhs>
    + NdSubAssignWrapping<Lhs, Rhs>
    + NdMulAssignWrapping<Lhs, Rhs>
    + NdDivAssignWrapping<Lhs, Rhs>
    + NdRemAssignWrapping<Lhs, Rhs>
{
}

/// Aggregate trait for all **assign** binary saturating operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsAssignSaturating<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdAddAssignSaturating<Lhs, Rhs>
    + NdSubAssignSaturating<Lhs, Rhs>
    + NdMulAssignSaturating<Lhs, Rhs>
    + NdDivAssignSaturating<Lhs, Rhs>
    + NdRemAssignSaturating<Lhs, Rhs>
{
}

/// Aggregate trait for all **assign** binary unbounded operations in [`crate::ops`].
///
/// Auto-implemented for all types with required operations.
pub trait NdOpsAssignUnbounded<Lhs = Self, Rhs = Self, ShiftRhs = usize>:
    NdShlAssignUnbounded<Lhs, Rhs> + NdShrAssignUnbounded<Lhs, Rhs>
{
}

impl<'num, N> From<&'num N> for Ref<'num, N> {
    #[inline]
    fn from(value: &'num N) -> Self {
        Self(value)
    }
}

impl<'num, N> From<&'num mut N> for Mut<'num, N> {
    #[inline]
    fn from(value: &'num mut N) -> Self {
        Self(value)
    }
}

ndops::fwd! { @ndun crate <'num, Value, N> (value: &Ref<'num, Value>) -> N for Ref<'num, N>, (Value) (&value.0) [
    ! where                     [Value: NdNot               <Value, Type = N>],
    - where                     [Value: NdNeg               <Value, Type = N>],
    - @checked where            [Value: NdNegChecked        <Value, Type = N>],
    - @strict where             [Value: NdNegStrict         <Value, Type = N>],
    - @wrapping where           [Value: NdNegWrapping       <Value, Type = N>],
    - @saturating where         [Value: NdNegSaturating     <Value, Type = N>],
    - @overflowing where        [Value: NdNegOverflowing    <Value, Type = N>],
    posx where                  [Value: NdPosx              <Value, Type = N>],
    posx @checked where         [Value: NdPosxChecked       <Value, Type = N>],
    posx @strict where          [Value: NdPosxStrict        <Value, Type = N>],
    posx @wrapping where        [Value: NdPosxWrapping      <Value, Type = N>],
    posx @saturating where      [Value: NdPosxSaturating    <Value, Type = N>],
    posx @overflowing where     [Value: NdPosxOverflowing   <Value, Type = N>],
    negx where                  [Value: NdNegx              <Value, Type = N>],
    negx @checked where         [Value: NdNegxChecked       <Value, Type = N>],
    negx @strict where          [Value: NdNegxStrict        <Value, Type = N>],
    negx @wrapping where        [Value: NdNegxWrapping      <Value, Type = N>],
    negx @saturating where      [Value: NdNegxSaturating    <Value, Type = N>],
    negx @overflowing where     [Value: NdNegxOverflowing   <Value, Type = N>],
] }

ndops::fwd! { @ndun crate <'num, Value, N> (value: &Mut<'num, Value>) -> N for Mut<'num, N>, (Value) (&value.0) [
    ! where                     [Value: NdNot               <Value, Type = N>],
    - where                     [Value: NdNeg               <Value, Type = N>],
    - @checked where            [Value: NdNegChecked        <Value, Type = N>],
    - @strict where             [Value: NdNegStrict         <Value, Type = N>],
    - @wrapping where           [Value: NdNegWrapping       <Value, Type = N>],
    - @saturating where         [Value: NdNegSaturating     <Value, Type = N>],
    - @overflowing where        [Value: NdNegOverflowing    <Value, Type = N>],
    posx where                  [Value: NdPosx              <Value, Type = N>],
    posx @checked where         [Value: NdPosxChecked       <Value, Type = N>],
    posx @strict where          [Value: NdPosxStrict        <Value, Type = N>],
    posx @wrapping where        [Value: NdPosxWrapping      <Value, Type = N>],
    posx @saturating where      [Value: NdPosxSaturating    <Value, Type = N>],
    posx @overflowing where     [Value: NdPosxOverflowing   <Value, Type = N>],
    negx where                  [Value: NdNegx              <Value, Type = N>],
    negx @checked where         [Value: NdNegxChecked       <Value, Type = N>],
    negx @strict where          [Value: NdNegxStrict        <Value, Type = N>],
    negx @wrapping where        [Value: NdNegxWrapping      <Value, Type = N>],
    negx @saturating where      [Value: NdNegxSaturating    <Value, Type = N>],
    negx @overflowing where     [Value: NdNegxOverflowing   <Value, Type = N>],
] }

ndops::fwd! { @ndbin crate <'num, Lhs, Rhs, N> (lhs: &Ref<'num, Lhs>, rhs: &Ref<'num, Rhs>) -> N for Ref<'num, N>, (Lhs) (&lhs.0) (&rhs.0) [
    + where                 [Lhs: NdAdd             <Lhs, Rhs, Type = N>],
    - where                 [Lhs: NdSub             <Lhs, Rhs, Type = N>],
    * where                 [Lhs: NdMul             <Lhs, Rhs, Type = N>],
    / where                 [Lhs: NdDiv             <Lhs, Rhs, Type = N>],
    % where                 [Lhs: NdRem             <Lhs, Rhs, Type = N>],
    | where                 [Lhs: NdBitOr           <Lhs, Rhs, Type = N>],
    & where                 [Lhs: NdBitAnd          <Lhs, Rhs, Type = N>],
    ^ where                 [Lhs: NdBitXor          <Lhs, Rhs, Type = N>],
    + @checked where        [Lhs: NdAddChecked      <Lhs, Rhs, Type = N>],
    - @checked where        [Lhs: NdSubChecked      <Lhs, Rhs, Type = N>],
    * @checked where        [Lhs: NdMulChecked      <Lhs, Rhs, Type = N>],
    / @checked where        [Lhs: NdDivChecked      <Lhs, Rhs, Type = N>],
    % @checked where        [Lhs: NdRemChecked      <Lhs, Rhs, Type = N>],
    + @strict where         [Lhs: NdAddStrict       <Lhs, Rhs, Type = N>],
    - @strict where         [Lhs: NdSubStrict       <Lhs, Rhs, Type = N>],
    * @strict where         [Lhs: NdMulStrict       <Lhs, Rhs, Type = N>],
    / @strict where         [Lhs: NdDivStrict       <Lhs, Rhs, Type = N>],
    % @strict where         [Lhs: NdRemStrict       <Lhs, Rhs, Type = N>],
    + @wrapping where       [Lhs: NdAddWrapping     <Lhs, Rhs, Type = N>],
    - @wrapping where       [Lhs: NdSubWrapping     <Lhs, Rhs, Type = N>],
    * @wrapping where       [Lhs: NdMulWrapping     <Lhs, Rhs, Type = N>],
    / @wrapping where       [Lhs: NdDivWrapping     <Lhs, Rhs, Type = N>],
    % @wrapping where       [Lhs: NdRemWrapping     <Lhs, Rhs, Type = N>],
    + @saturating where     [Lhs: NdAddSaturating   <Lhs, Rhs, Type = N>],
    - @saturating where     [Lhs: NdSubSaturating   <Lhs, Rhs, Type = N>],
    * @saturating where     [Lhs: NdMulSaturating   <Lhs, Rhs, Type = N>],
    / @saturating where     [Lhs: NdDivSaturating   <Lhs, Rhs, Type = N>],
    % @saturating where     [Lhs: NdRemSaturating   <Lhs, Rhs, Type = N>],
    + @overflowing where    [Lhs: NdAddOverflowing  <Lhs, Rhs, Type = N>],
    - @overflowing where    [Lhs: NdSubOverflowing  <Lhs, Rhs, Type = N>],
    * @overflowing where    [Lhs: NdMulOverflowing  <Lhs, Rhs, Type = N>],
    / @overflowing where    [Lhs: NdDivOverflowing  <Lhs, Rhs, Type = N>],
    % @overflowing where    [Lhs: NdRemOverflowing  <Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @ndbin crate <'num, Lhs, Rhs, N> (lhs: &Mut<'num, Lhs>, rhs: &Ref<'num, Rhs>) -> N for Mut<'num, N>, (Lhs) (&lhs.0) (&rhs.0) [
    + where                 [Lhs: NdAdd             <Lhs, Rhs, Type = N>],
    - where                 [Lhs: NdSub             <Lhs, Rhs, Type = N>],
    * where                 [Lhs: NdMul             <Lhs, Rhs, Type = N>],
    / where                 [Lhs: NdDiv             <Lhs, Rhs, Type = N>],
    % where                 [Lhs: NdRem             <Lhs, Rhs, Type = N>],
    | where                 [Lhs: NdBitOr           <Lhs, Rhs, Type = N>],
    & where                 [Lhs: NdBitAnd          <Lhs, Rhs, Type = N>],
    ^ where                 [Lhs: NdBitXor          <Lhs, Rhs, Type = N>],
    + @checked where        [Lhs: NdAddChecked      <Lhs, Rhs, Type = N>],
    - @checked where        [Lhs: NdSubChecked      <Lhs, Rhs, Type = N>],
    * @checked where        [Lhs: NdMulChecked      <Lhs, Rhs, Type = N>],
    / @checked where        [Lhs: NdDivChecked      <Lhs, Rhs, Type = N>],
    % @checked where        [Lhs: NdRemChecked      <Lhs, Rhs, Type = N>],
    + @strict where         [Lhs: NdAddStrict       <Lhs, Rhs, Type = N>],
    - @strict where         [Lhs: NdSubStrict       <Lhs, Rhs, Type = N>],
    * @strict where         [Lhs: NdMulStrict       <Lhs, Rhs, Type = N>],
    / @strict where         [Lhs: NdDivStrict       <Lhs, Rhs, Type = N>],
    % @strict where         [Lhs: NdRemStrict       <Lhs, Rhs, Type = N>],
    + @wrapping where       [Lhs: NdAddWrapping     <Lhs, Rhs, Type = N>],
    - @wrapping where       [Lhs: NdSubWrapping     <Lhs, Rhs, Type = N>],
    * @wrapping where       [Lhs: NdMulWrapping     <Lhs, Rhs, Type = N>],
    / @wrapping where       [Lhs: NdDivWrapping     <Lhs, Rhs, Type = N>],
    % @wrapping where       [Lhs: NdRemWrapping     <Lhs, Rhs, Type = N>],
    + @saturating where     [Lhs: NdAddSaturating   <Lhs, Rhs, Type = N>],
    - @saturating where     [Lhs: NdSubSaturating   <Lhs, Rhs, Type = N>],
    * @saturating where     [Lhs: NdMulSaturating   <Lhs, Rhs, Type = N>],
    / @saturating where     [Lhs: NdDivSaturating   <Lhs, Rhs, Type = N>],
    % @saturating where     [Lhs: NdRemSaturating   <Lhs, Rhs, Type = N>],
    + @overflowing where    [Lhs: NdAddOverflowing  <Lhs, Rhs, Type = N>],
    - @overflowing where    [Lhs: NdSubOverflowing  <Lhs, Rhs, Type = N>],
    * @overflowing where    [Lhs: NdMulOverflowing  <Lhs, Rhs, Type = N>],
    / @overflowing where    [Lhs: NdDivOverflowing  <Lhs, Rhs, Type = N>],
    % @overflowing where    [Lhs: NdRemOverflowing  <Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @ndbin crate <'num, Lhs, Rhs, N> (lhs: &Ref<'num, Lhs>, rhs: Rhs) -> N for Ref<'num, N>, (Lhs) (&lhs.0) (rhs) [
    << where                [Lhs: NdShl             <Lhs, Rhs, Type = N>],
    >> where                [Lhs: NdShr             <Lhs, Rhs, Type = N>],
    << @checked where       [Lhs: NdShlChecked      <Lhs, Rhs, Type = N>],
    >> @checked where       [Lhs: NdShrChecked      <Lhs, Rhs, Type = N>],
    << @strict where        [Lhs: NdShlStrict       <Lhs, Rhs, Type = N>],
    >> @strict where        [Lhs: NdShrStrict       <Lhs, Rhs, Type = N>],
    << @overflowing where   [Lhs: NdShlOverflowing  <Lhs, Rhs, Type = N>],
    >> @overflowing where   [Lhs: NdShrOverflowing  <Lhs, Rhs, Type = N>],
    << @unbounded where     [Lhs: NdShlUnbounded    <Lhs, Rhs, Type = N>],
    >> @unbounded where     [Lhs: NdShrUnbounded    <Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @ndbin crate <'num, Lhs, Rhs, N> (lhs: &Mut<'num, Lhs>, rhs: Rhs) -> N for Mut<'num, N>, (Lhs) (&lhs.0) (rhs) [
    << where                [Lhs: NdShl             <Lhs, Rhs, Type = N>],
    >> where                [Lhs: NdShr             <Lhs, Rhs, Type = N>],
    << @checked where       [Lhs: NdShlChecked      <Lhs, Rhs, Type = N>],
    >> @checked where       [Lhs: NdShrChecked      <Lhs, Rhs, Type = N>],
    << @strict where        [Lhs: NdShlStrict       <Lhs, Rhs, Type = N>],
    >> @strict where        [Lhs: NdShrStrict       <Lhs, Rhs, Type = N>],
    << @overflowing where   [Lhs: NdShlOverflowing  <Lhs, Rhs, Type = N>],
    >> @overflowing where   [Lhs: NdShrOverflowing  <Lhs, Rhs, Type = N>],
    << @unbounded where     [Lhs: NdShlUnbounded    <Lhs, Rhs, Type = N>],
    >> @unbounded where     [Lhs: NdShrUnbounded    <Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @ndmut crate <'num, Lhs, Rhs> (lhs: &mut Mut<'num, Lhs>, rhs: &Ref<'num, Rhs>) for Mut<'num, Lhs>, (Lhs) (&mut lhs.0) (&rhs.0) [
    += where                [Lhs: NdAddAssign           <Lhs, Rhs>],
    -= where                [Lhs: NdSubAssign           <Lhs, Rhs>],
    *= where                [Lhs: NdMulAssign           <Lhs, Rhs>],
    /= where                [Lhs: NdDivAssign           <Lhs, Rhs>],
    %= where                [Lhs: NdRemAssign           <Lhs, Rhs>],
    |= where                [Lhs: NdBitOrAssign         <Lhs, Rhs>],
    &= where                [Lhs: NdBitAndAssign        <Lhs, Rhs>],
    ^= where                [Lhs: NdBitXorAssign        <Lhs, Rhs>],
    += @strict where        [Lhs: NdAddAssignStrict     <Lhs, Rhs>],
    -= @strict where        [Lhs: NdSubAssignStrict     <Lhs, Rhs>],
    *= @strict where        [Lhs: NdMulAssignStrict     <Lhs, Rhs>],
    /= @strict where        [Lhs: NdDivAssignStrict     <Lhs, Rhs>],
    %= @strict where        [Lhs: NdRemAssignStrict     <Lhs, Rhs>],
    += @wrapping where      [Lhs: NdAddAssignWrapping   <Lhs, Rhs>],
    -= @wrapping where      [Lhs: NdSubAssignWrapping   <Lhs, Rhs>],
    *= @wrapping where      [Lhs: NdMulAssignWrapping   <Lhs, Rhs>],
    /= @wrapping where      [Lhs: NdDivAssignWrapping   <Lhs, Rhs>],
    %= @wrapping where      [Lhs: NdRemAssignWrapping   <Lhs, Rhs>],
    += @saturating where    [Lhs: NdAddAssignSaturating <Lhs, Rhs>],
    -= @saturating where    [Lhs: NdSubAssignSaturating <Lhs, Rhs>],
    *= @saturating where    [Lhs: NdMulAssignSaturating <Lhs, Rhs>],
    /= @saturating where    [Lhs: NdDivAssignSaturating <Lhs, Rhs>],
    %= @saturating where    [Lhs: NdRemAssignSaturating <Lhs, Rhs>],
] }

ndops::fwd! { @ndmut crate <'num, Lhs, Rhs> (lhs: &mut Mut<'num, Lhs>, rhs: Rhs) for Mut<'num, Lhs>, (Lhs) (&mut lhs.0) (rhs) [
    <<= where               [Lhs: NdShlAssign           <Lhs, Rhs>],
    >>= where               [Lhs: NdShrAssign           <Lhs, Rhs>],
    <<= @strict where       [Lhs: NdShlAssignStrict     <Lhs, Rhs>],
    >>= @strict where       [Lhs: NdShrAssignStrict     <Lhs, Rhs>],
    <<= @unbounded where    [Lhs: NdShlAssignUnbounded  <Lhs, Rhs>],
    >>= @unbounded where    [Lhs: NdShrAssignUnbounded  <Lhs, Rhs>],
] }

ndops::fwd! { @stdun crate <'num, Value, N> (*value: &Ref<'num, Value>) -> N, (Value) (&value.0) [
    - where [Value: NdNeg<Value, Type = N>],
    ! where [Value: NdNot<Value, Type = N>],
] }

ndops::fwd! { @stdun crate <'num, Value, N> (*value: &Mut<'num, Value>) -> N, (Value) (&value.0) [
    - where [Value: NdNeg<Value, Type = N>],
    ! where [Value: NdNot<Value, Type = N>],
] }

ndops::fwd! { @stdbin crate <'num, Lhs, Rhs, N> (*lhs: &Ref<'num, Lhs>, *rhs: &Ref<'num, Rhs>) -> N, (Lhs) (&lhs.0) (&rhs.0) [
    + where [Lhs: NdAdd   <Lhs, Rhs, Type = N>],
    - where [Lhs: NdSub   <Lhs, Rhs, Type = N>],
    * where [Lhs: NdMul   <Lhs, Rhs, Type = N>],
    / where [Lhs: NdDiv   <Lhs, Rhs, Type = N>],
    % where [Lhs: NdRem   <Lhs, Rhs, Type = N>],
    | where [Lhs: NdBitOr <Lhs, Rhs, Type = N>],
    & where [Lhs: NdBitAnd<Lhs, Rhs, Type = N>],
    ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @stdbin crate <'num, Lhs, Rhs, N> (*lhs: &Mut<'num, Lhs>, *rhs: &Ref<'num, Rhs>) -> N, (Lhs) (&lhs.0) (&rhs.0) [
    + where [Lhs: NdAdd   <Lhs, Rhs, Type = N>],
    - where [Lhs: NdSub   <Lhs, Rhs, Type = N>],
    * where [Lhs: NdMul   <Lhs, Rhs, Type = N>],
    / where [Lhs: NdDiv   <Lhs, Rhs, Type = N>],
    % where [Lhs: NdRem   <Lhs, Rhs, Type = N>],
    | where [Lhs: NdBitOr <Lhs, Rhs, Type = N>],
    & where [Lhs: NdBitAnd<Lhs, Rhs, Type = N>],
    ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @stdbin crate <'num, Lhs, Rhs, N> (*lhs: &Ref<'num, Lhs>, rhs: Rhs) -> N, (Lhs) (&lhs.0) (rhs) [
    << where [Lhs: NdShl<Lhs, Rhs, Type = N>],
    >> where [Lhs: NdShr<Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @stdbin crate <'num, Lhs, Rhs, N> (*lhs: &Mut<'num, Lhs>, rhs: Rhs) -> N, (Lhs) (&lhs.0) (rhs) [
    << where [Lhs: NdShl<Lhs, Rhs, Type = N>],
    >> where [Lhs: NdShr<Lhs, Rhs, Type = N>],
] }

ndops::fwd! { @stdmut crate <'num, Lhs, Rhs> (lhs: &mut Mut<'num, Lhs>, *rhs: &Ref<'num, Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where [Lhs: NdAddAssign   <Lhs, Rhs>],
    -= where [Lhs: NdSubAssign   <Lhs, Rhs>],
    *= where [Lhs: NdMulAssign   <Lhs, Rhs>],
    /= where [Lhs: NdDivAssign   <Lhs, Rhs>],
    %= where [Lhs: NdRemAssign   <Lhs, Rhs>],
    |= where [Lhs: NdBitOrAssign <Lhs, Rhs>],
    &= where [Lhs: NdBitAndAssign<Lhs, Rhs>],
    ^= where [Lhs: NdBitXorAssign<Lhs, Rhs>],
] }

ndops::fwd! { @stdmut crate <'num, Lhs, Rhs> (lhs: &mut Mut<'num, Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where [Lhs: NdShlAssign<Lhs, Rhs>],
    >>= where [Lhs: NdShrAssign<Lhs, Rhs>],
] }

impl<Lhs, Rhs, ShiftRhs, Type> Ops<Rhs, ShiftRhs> for Lhs
where
    Self: Sized
        + Clone
        + Copy
        + Add<Rhs, Output = Type>
        + Sub<Rhs, Output = Type>
        + Mul<Rhs, Output = Type>
        + Div<Rhs, Output = Type>
        + Rem<Rhs, Output = Type>
        + BitOr<Rhs, Output = Type>
        + BitAnd<Rhs, Output = Type>
        + BitXor<Rhs, Output = Type>
        + Shl<ShiftRhs, Output = Type>
        + Shr<ShiftRhs, Output = Type>,
{
    type Type = Type;
}

impl<Lhs, Rhs, ShiftRhs> OpsAssign<Rhs, ShiftRhs> for Lhs where
    Self: Copy
        + AddAssign<Rhs>
        + SubAssign<Rhs>
        + MulAssign<Rhs>
        + DivAssign<Rhs>
        + RemAssign<Rhs>
        + BitOrAssign<Rhs>
        + BitAndAssign<Rhs>
        + BitXorAssign<Rhs>
        + ShlAssign<ShiftRhs>
        + ShrAssign<ShiftRhs>
{
}

impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOps<Lhs, Rhs, ShiftRhs> for Any
where
    Any: NdAdd<Lhs, Rhs, Type = Type>
        + NdSub<Lhs, Rhs, Type = Type>
        + NdMul<Lhs, Rhs, Type = Type>
        + NdDiv<Lhs, Rhs, Type = Type>
        + NdRem<Lhs, Rhs, Type = Type>
        + NdBitOr<Lhs, Rhs, Type = Type>
        + NdBitAnd<Lhs, Rhs, Type = Type>
        + NdBitXor<Lhs, Rhs, Type = Type>
        + NdShl<Lhs, ShiftRhs, Type = Type>
        + NdShr<Lhs, ShiftRhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOpsChecked<Lhs, Rhs, ShiftRhs> for Any
where
    Any: NdAddChecked<Lhs, Rhs, Type = Type>
        + NdSubChecked<Lhs, Rhs, Type = Type>
        + NdMulChecked<Lhs, Rhs, Type = Type>
        + NdDivChecked<Lhs, Rhs, Type = Type>
        + NdRemChecked<Lhs, Rhs, Type = Type>
        + NdShlChecked<Lhs, ShiftRhs, Type = Type>
        + NdShrChecked<Lhs, ShiftRhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOpsStrict<Lhs, Rhs, ShiftRhs> for Any
where
    Any: NdAddStrict<Lhs, Rhs, Type = Type>
        + NdSubStrict<Lhs, Rhs, Type = Type>
        + NdMulStrict<Lhs, Rhs, Type = Type>
        + NdDivStrict<Lhs, Rhs, Type = Type>
        + NdRemStrict<Lhs, Rhs, Type = Type>
        + NdShlStrict<Lhs, ShiftRhs, Type = Type>
        + NdShrStrict<Lhs, ShiftRhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, Type> NdOpsWrapping<Lhs, Rhs> for Any
where
    Any: NdAddWrapping<Lhs, Rhs, Type = Type>
        + NdSubWrapping<Lhs, Rhs, Type = Type>
        + NdMulWrapping<Lhs, Rhs, Type = Type>
        + NdDivWrapping<Lhs, Rhs, Type = Type>
        + NdRemWrapping<Lhs, Rhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, Type> NdOpsSaturating<Lhs, Rhs> for Any
where
    Any: NdAddSaturating<Lhs, Rhs, Type = Type>
        + NdSubSaturating<Lhs, Rhs, Type = Type>
        + NdMulSaturating<Lhs, Rhs, Type = Type>
        + NdDivSaturating<Lhs, Rhs, Type = Type>
        + NdRemSaturating<Lhs, Rhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, ShiftRhs, Type> NdOpsOverflowing<Lhs, Rhs, ShiftRhs> for Any
where
    Any: NdAddOverflowing<Lhs, Rhs, Type = Type>
        + NdSubOverflowing<Lhs, Rhs, Type = Type>
        + NdMulOverflowing<Lhs, Rhs, Type = Type>
        + NdDivOverflowing<Lhs, Rhs, Type = Type>
        + NdRemOverflowing<Lhs, Rhs, Type = Type>
        + NdShlOverflowing<Lhs, ShiftRhs, Type = Type>
        + NdShrOverflowing<Lhs, ShiftRhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, Type> NdOpsUnbounded<Lhs, Rhs> for Any
where
    Any: NdShlUnbounded<Lhs, Rhs, Type = Type> + NdShrUnbounded<Lhs, Rhs, Type = Type>,
{
    type All = Type;
}

impl<Any, Lhs, Rhs, ShiftRhs> NdOpsAssign<Lhs, Rhs, ShiftRhs> for Any where
    Any: NdAddAssign<Lhs, Rhs>
        + NdSubAssign<Lhs, Rhs>
        + NdMulAssign<Lhs, Rhs>
        + NdDivAssign<Lhs, Rhs>
        + NdRemAssign<Lhs, Rhs>
        + NdBitOrAssign<Lhs, Rhs>
        + NdBitAndAssign<Lhs, Rhs>
        + NdBitXorAssign<Lhs, Rhs>
        + NdShlAssign<Lhs, ShiftRhs>
        + NdShrAssign<Lhs, ShiftRhs>
{
}

impl<Any, Lhs, Rhs> NdOpsAssignStrict<Lhs, Rhs> for Any where
    Any: NdAddAssignStrict<Lhs, Rhs>
        + NdSubAssignStrict<Lhs, Rhs>
        + NdMulAssignStrict<Lhs, Rhs>
        + NdDivAssignStrict<Lhs, Rhs>
        + NdRemAssignStrict<Lhs, Rhs>
        + NdShlAssignStrict<Lhs, Rhs>
        + NdShrAssignStrict<Lhs, Rhs>
{
}

impl<Any, Lhs, Rhs> NdOpsAssignWrapping<Lhs, Rhs> for Any where
    Any: NdAddAssignWrapping<Lhs, Rhs>
        + NdSubAssignWrapping<Lhs, Rhs>
        + NdMulAssignWrapping<Lhs, Rhs>
        + NdDivAssignWrapping<Lhs, Rhs>
        + NdRemAssignWrapping<Lhs, Rhs>
{
}

impl<Any, Lhs, Rhs> NdOpsAssignSaturating<Lhs, Rhs> for Any where
    Any: NdAddAssignSaturating<Lhs, Rhs>
        + NdSubAssignSaturating<Lhs, Rhs>
        + NdMulAssignSaturating<Lhs, Rhs>
        + NdDivAssignSaturating<Lhs, Rhs>
        + NdRemAssignSaturating<Lhs, Rhs>
{
}

impl<Any, Lhs, Rhs> NdOpsAssignUnbounded<Lhs, Rhs> for Any where
    Any: NdShlAssignUnbounded<Lhs, Rhs> + NdShrAssignUnbounded<Lhs, Rhs>
{
}

nd_ops_impl!(@signed [i8, i16, i32, i64, i128, isize]);
nd_ops_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);

nd_opsx_impl!([i8 > i16, i16 > i32, i32 > i64, i64 > i128]);
nd_opsx_impl!([u8 > u16, u16 > u32, u32 > u64, u64 > u128]);

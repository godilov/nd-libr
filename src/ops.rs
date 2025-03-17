use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

pub trait Ops<Rhs = Self>: Sized + Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs> {}
pub trait OpsRem<Rhs = Self>: Sized + Rem<Rhs> {}
pub trait OpsBit<Rhs = Self>: Sized + BitOr<Rhs> + BitAnd<Rhs> + BitXor<Rhs> {}
pub trait OpsShift<Rhs = Self>: Sized + Shl<Rhs> + Shr<Rhs> {}
pub trait OpsAll<Rhs = Self>: Ops<Rhs> + OpsRem<Rhs> + OpsBit<Rhs> + OpsShift<Rhs> {}

pub trait OpsAssign<Rhs = Self>: AddAssign<Rhs> + SubAssign<Rhs> + MulAssign<Rhs> + DivAssign<Rhs> {}
pub trait OpsRemAssign<Rhs = Self>: RemAssign<Rhs> {}
pub trait OpsBitAssign<Rhs = Self>: BitOrAssign<Rhs> + BitAndAssign<Rhs> + BitXorAssign<Rhs> {}
pub trait OpsShiftAssign<Rhs = Self>: ShlAssign<Rhs> + ShrAssign<Rhs> {}
pub trait OpsAllAssign<Rhs = Self>:
    OpsAssign<Rhs> + OpsRemAssign<Rhs> + OpsShiftAssign<Rhs> + OpsBitAssign<Rhs>
{
}

pub trait OpsFrom<Lhs: Ops<Rhs>, Rhs>:
    From<<Lhs as Add<Rhs>>::Output>
    + From<<Lhs as Sub<Rhs>>::Output>
    + From<<Lhs as Mul<Rhs>>::Output>
    + From<<Lhs as Div<Rhs>>::Output>
{
}

pub trait OpsRemFrom<Lhs: OpsRem<Rhs>, Rhs>: From<<Lhs as Rem<Rhs>>::Output> {}

pub trait OpsBitFrom<Lhs: OpsBit<Rhs>, Rhs>:
    From<<Lhs as BitOr<Rhs>>::Output> + From<<Lhs as BitAnd<Rhs>>::Output> + From<<Lhs as BitXor<Rhs>>::Output>
{
}

pub trait OpsShiftFrom<Lhs: OpsShift<Rhs>, Rhs>:
    From<<Lhs as Shl<Rhs>>::Output> + From<<Lhs as Shr<Rhs>>::Output>
{
}

pub trait OpsNegFrom<Lhs: Neg = Self>: From<<Lhs as Neg>::Output> {}
pub trait OpsNotFrom<Lhs: Not = Self>: From<<Lhs as Not>::Output> {}

pub trait OpsAllFrom<Lhs: OpsAll<Rhs>, Rhs>:
    OpsFrom<Lhs, Rhs> + OpsRemFrom<Lhs, Rhs> + OpsBitFrom<Lhs, Rhs> + OpsShiftFrom<Lhs, Rhs>
{
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

pub trait OpsChecked<Rhs = Self>: AddChecked<Rhs> + SubChecked<Rhs> + MulChecked<Rhs> + DivChecked<Rhs> {}

impl<Lhs, Rhs> Ops<Rhs> for Lhs where Lhs: Sized + Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs> {}
impl<Lhs, Rhs> OpsRem<Rhs> for Lhs where Self: Sized + Rem<Rhs> {}
impl<Lhs, Rhs> OpsBit<Rhs> for Lhs where Self: Sized + BitOr<Rhs> + BitAnd<Rhs> + BitXor<Rhs> {}
impl<Lhs, Rhs> OpsShift<Rhs> for Lhs where Self: Sized + Shl<Rhs> + Shr<Rhs> {}
impl<Lhs, Rhs> OpsAll<Rhs> for Lhs where Self: Sized + Ops<Rhs> + OpsRem<Rhs> + OpsBit<Rhs> + OpsShift<Rhs> {}

impl<Lhs, Rhs> OpsAssign<Rhs> for Lhs where
    Self: Sized + AddAssign<Rhs> + SubAssign<Rhs> + MulAssign<Rhs> + DivAssign<Rhs>
{
}

impl<Lhs, Rhs> OpsRemAssign<Rhs> for Lhs where Self: Sized + RemAssign<Rhs> {}
impl<Lhs, Rhs> OpsBitAssign<Rhs> for Lhs where Self: Sized + BitOrAssign<Rhs> + BitAndAssign<Rhs> + BitXorAssign<Rhs> {}
impl<Lhs, Rhs> OpsShiftAssign<Rhs> for Lhs where Self: Sized + ShlAssign<Rhs> + ShrAssign<Rhs> {}
impl<Lhs, Rhs> OpsAllAssign<Rhs> for Lhs where
    Self: Sized + OpsAssign<Rhs> + OpsRemAssign<Rhs> + OpsBitAssign<Rhs> + OpsShiftAssign<Rhs>
{
}

impl<Any, Lhs: Ops<Rhs>, Rhs> OpsFrom<Lhs, Rhs> for Any where
    Self: From<<Lhs as Add<Rhs>>::Output>
        + From<<Lhs as Sub<Rhs>>::Output>
        + From<<Lhs as Mul<Rhs>>::Output>
        + From<<Lhs as Div<Rhs>>::Output>
{
}

impl<Any, Lhs: OpsRem<Rhs>, Rhs> OpsRemFrom<Lhs, Rhs> for Any where Self: From<<Lhs as Rem<Rhs>>::Output> {}

impl<Any, Lhs: OpsBit<Rhs>, Rhs> OpsBitFrom<Lhs, Rhs> for Any where
    Self: From<<Lhs as BitOr<Rhs>>::Output> + From<<Lhs as BitAnd<Rhs>>::Output> + From<<Lhs as BitXor<Rhs>>::Output>
{
}

impl<Any, Lhs: OpsShift<Rhs>, Rhs> OpsShiftFrom<Lhs, Rhs> for Any where
    Self: From<<Lhs as Shl<Rhs>>::Output> + From<<Lhs as Shr<Rhs>>::Output>
{
}

impl<Any, Lhs: Neg> OpsNegFrom<Lhs> for Any where Self: From<<Lhs as Neg>::Output> {}
impl<Any, Lhs: Not> OpsNotFrom<Lhs> for Any where Self: From<<Lhs as Not>::Output> {}

impl<Any, Lhs: OpsAll<Rhs>, Rhs> OpsAllFrom<Lhs, Rhs> for Any where
    Self: OpsFrom<Lhs, Rhs> + OpsRemFrom<Lhs, Rhs> + OpsBitFrom<Lhs, Rhs> + OpsShiftFrom<Lhs, Rhs>
{
}

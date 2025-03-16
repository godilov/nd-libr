use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

pub trait Ops<Rhs: Ops<Self> = Self>: Sized + Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs> {
    type Output;
}

pub trait OpsRem<Rhs: OpsRem<Self> = Self>: Sized + Rem<Rhs> {
    type Output;
}

pub trait OpsBit<Rhs: OpsBit<Self> = Self>: Sized + BitOr<Rhs> + BitAnd<Rhs> + BitXor<Rhs> {
    type Output;
}

pub trait OpsShift<Rhs: OpsShift<Self> = Self>: Sized + Shl<Rhs> + Shr<Rhs> {
    type Output;
}

pub trait OpsAll<Rhs: OpsAll<Self> = Self>: Ops<Rhs> + OpsRem<Rhs> + OpsBit<Rhs> + OpsShift<Rhs> {
    type Output;
}

pub trait OpsAssign<Rhs = Self>: AddAssign<Rhs> + SubAssign<Rhs> + MulAssign<Rhs> + DivAssign<Rhs> {}

pub trait OpsRemAssign<Rhs = Self>: RemAssign<Rhs> {}

pub trait OpsBitAssign<Rhs = Self>: BitOrAssign<Rhs> + BitAndAssign<Rhs> + BitXorAssign<Rhs> {}

pub trait OpsShiftAssign<Rhs = Self>: ShlAssign<Rhs> + ShrAssign<Rhs> {}

pub trait OpsAllAssign<Rhs = Self>:
    OpsAssign<Rhs> + OpsRemAssign<Rhs> + OpsShiftAssign<Rhs> + OpsBitAssign<Rhs>
{
}

pub trait OpsFrom<Lhs: Ops<Rhs> = Self, Rhs: Ops<Lhs> = Lhs>:
    From<<Lhs as Add<Rhs>>::Output>
    + From<<Lhs as Sub<Rhs>>::Output>
    + From<<Lhs as Mul<Rhs>>::Output>
    + From<<Lhs as Div<Rhs>>::Output>
{
}

pub trait OpsRemFrom<Lhs: OpsRem<Rhs> = Self, Rhs: OpsRem<Lhs> = Lhs>: From<<Lhs as Rem<Rhs>>::Output> {}

pub trait OpsBitFrom<Lhs: OpsBit<Rhs> = Self, Rhs: OpsBit<Lhs> = Lhs>:
    From<<Lhs as BitOr<Rhs>>::Output> + From<<Lhs as BitAnd<Rhs>>::Output> + From<<Lhs as BitXor<Rhs>>::Output>
{
}

pub trait OpsShiftFrom<Lhs: OpsShift<Rhs> = Self, Rhs: OpsShift<Lhs> = Lhs>:
    From<<Lhs as Shl<Rhs>>::Output> + From<<Lhs as Shr<Rhs>>::Output>
{
}

pub trait OpsNegFrom<T: Neg = Self>: From<<T as Neg>::Output> {}
pub trait OpsNotFrom<T: Not = Self>: From<<T as Not>::Output> {}

pub trait OpsAllFrom<Lhs: OpsAll<Rhs> = Self, Rhs: OpsAll<Lhs> = Lhs>:
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

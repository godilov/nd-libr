use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

pub trait Ops<Rhs = Self, ShiftRhs = usize>
where
    Self: Sized
        + Add<Rhs>
        + Sub<Rhs>
        + Mul<Rhs>
        + Div<Rhs>
        + Rem<Rhs>
        + BitOr<Rhs>
        + BitAnd<Rhs>
        + BitXor<Rhs>
        + Shl<ShiftRhs>
        + Shr<ShiftRhs>,
{
}

pub trait OpsAssign<Rhs = Self, ShiftRhs = usize>
where
    Self: AddAssign<Rhs>
        + SubAssign<Rhs>
        + MulAssign<Rhs>
        + DivAssign<Rhs>
        + RemAssign<Rhs>
        + BitOrAssign<Rhs>
        + BitAndAssign<Rhs>
        + BitXorAssign<Rhs>
        + ShlAssign<ShiftRhs>
        + ShrAssign<ShiftRhs>,
{
}

pub trait OpsFrom<Lhs: Ops<Rhs, ShiftRhs> = Self, Rhs = Lhs, ShiftRhs = usize>
where
    Self: From<<Lhs as Add<Rhs>>::Output>
        + From<<Lhs as Sub<Rhs>>::Output>
        + From<<Lhs as Mul<Rhs>>::Output>
        + From<<Lhs as Div<Rhs>>::Output>
        + From<<Lhs as Rem<Rhs>>::Output>
        + From<<Lhs as BitOr<Rhs>>::Output>
        + From<<Lhs as BitAnd<Rhs>>::Output>
        + From<<Lhs as BitXor<Rhs>>::Output>
        + From<<Lhs as Shl<ShiftRhs>>::Output>
        + From<<Lhs as Shr<ShiftRhs>>::Output>,
{
}

pub trait OpsNegFrom<Lhs: Neg = Self>: From<<Lhs as Neg>::Output> {}
pub trait OpsNotFrom<Lhs: Not = Self>: From<<Lhs as Not>::Output> {}

pub trait IteratorExt: Iterator {
    fn collect_with<Collection>(&mut self, mut collection: Collection) -> Collection
    where
        Self: Sized,
        for<'item> &'item mut Collection: IntoIterator<Item = &'item mut Self::Item>,
    {
        collection.into_iter().zip(self).for_each(|(dst, src)| *dst = src);
        collection
    }
}

impl<Lhs, Rhs, ShiftRhs> Ops<Rhs, ShiftRhs> for Lhs where
    Self: Sized
        + Add<Rhs>
        + Sub<Rhs>
        + Mul<Rhs>
        + Div<Rhs>
        + Rem<Rhs>
        + BitOr<Rhs>
        + BitAnd<Rhs>
        + BitXor<Rhs>
        + Shl<ShiftRhs>
        + Shr<ShiftRhs>
{
}

impl<Lhs, Rhs, ShiftRhs> OpsAssign<Rhs, ShiftRhs> for Lhs where
    Self: AddAssign<Rhs>
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

impl<Any, Lhs: Ops<Rhs, ShiftRhs>, Rhs, ShiftRhs> OpsFrom<Lhs, Rhs, ShiftRhs> for Any where
    Any: From<<Lhs as Add<Rhs>>::Output>
        + From<<Lhs as Sub<Rhs>>::Output>
        + From<<Lhs as Mul<Rhs>>::Output>
        + From<<Lhs as Div<Rhs>>::Output>
        + From<<Lhs as Rem<Rhs>>::Output>
        + From<<Lhs as BitOr<Rhs>>::Output>
        + From<<Lhs as BitAnd<Rhs>>::Output>
        + From<<Lhs as BitXor<Rhs>>::Output>
        + From<<Lhs as Shl<ShiftRhs>>::Output>
        + From<<Lhs as Shr<ShiftRhs>>::Output>
{
}

impl<Any, Lhs: Neg> OpsNegFrom<Lhs> for Any where Self: From<<Lhs as Neg>::Output> {}
impl<Any, Lhs: Not> OpsNotFrom<Lhs> for Any where Self: From<<Lhs as Not>::Output> {}

impl<Iter: Iterator> IteratorExt for Iter {}

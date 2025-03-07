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

pub trait OpsNegFrom: Neg + From<<Self as Neg>::Output> {}
pub trait OpsNotFrom: Not + From<<Self as Not>::Output> {}

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

// TODO: Consider cmp_impl's for std::cmp::*

// TODO: Consider ways to make procedural macro instead of declarative
#[macro_export]
macro_rules! ops_impl_std {
    (@mut $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<&$typer> for $typel {
            #[allow(clippy::redundant_closure_call)]
            fn $op_name(&mut self, rhs: &$typer) { (|$lhs: &mut $typel, $rhs: &$typer| $fn)(self, rhs); }
        }
    };
    (@mut $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<$typer> for $typel {
            #[allow(clippy::redundant_closure_call)]
            fn $op_name(&mut self, rhs: $typer) { (|$lhs: &mut $typel, $rhs: $typer| $fn)(self, rhs); }
        }
    };

    (@binary $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<&$typer> for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$typer) -> Self::Output { (|$lhs: &$typel, $rhs: &$typer| $fn)(self, rhs) }
        }
    };
    (@binary $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<$typer> for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $typer) -> Self::Output { (|$lhs: &$typel, $rhs: $typer| $fn)(self, rhs) }
        }
    };
    (@binary $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<&$typer> for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$typer) -> Self::Output { (|$lhs: $typel, $rhs: &$typer| $fn)(self, rhs) }
        }
    };
    (@binary $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<$typer> for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $typer) -> Self::Output { (|$lhs: $typel, $rhs: $typer| $fn)(self, rhs) }
        }
    };

    (@unary $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self) -> Self::Output { (|$lhs: &$typel| $fn)(self) }
        }
    };
    (@unary $op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self) -> Self::Output { (|$lhs: $typel| $fn)(self) }
        }
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        $crate::ops_impl_std!(@mut $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $fn);
        $crate::ops_impl_std!(@mut $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        $crate::ops_impl_std!(@mut $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $fn);
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!(@binary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!(@unary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $fn);
        $crate::ops_impl_std!(@unary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!(@unary $op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $fn);
    };
}

// TODO: Consider ways to make procedural macro instead of declarative
#[macro_export]
macro_rules! ops_impl {
    (@mut $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $fn);
    };
    (@mut $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $fn);
    };

    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
    };
    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $fn);
    };
    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $fn);
    };
    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    (@unary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $fn);
    };
    (@unary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $fn);
    };

    (@mut $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |) => {};
    (@mut $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |) => {};

    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path) => {};
    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path) => {};
    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path) => {};
    (@binary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path) => {};

    (@unary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path | -> $type:path) => {};
    (@unary $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path | -> $type:path) => {};

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |,
     $(+= $add:block)? $(-= $sub:block)? $(*= $mul:block)? $(/= $div:block)? $(%= $rem:block)?
     $(|= $or:block)? $(&= $and:block)? $(^= $xor:block)? $(<<= $shl:block)? $(>>= $shr:block)?) => {
        $crate::ops_impl!(@mut AddAssign,    add_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($add)?);
        $crate::ops_impl!(@mut SubAssign,    sub_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($sub)?);
        $crate::ops_impl!(@mut MulAssign,    mul_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($mul)?);
        $crate::ops_impl!(@mut DivAssign,    div_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($div)?);
        $crate::ops_impl!(@mut RemAssign,    rem_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($rem)?);
        $crate::ops_impl!(@mut BitOrAssign,  bitor_assign,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($or)?);
        $crate::ops_impl!(@mut BitAndAssign, bitand_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($and)?);
        $crate::ops_impl!(@mut BitXorAssign, bitxor_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($xor)?);
        $crate::ops_impl!(@mut ShlAssign,    shl_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($shl)?);
        $crate::ops_impl!(@mut ShrAssign,    shr_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($shr)?);

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAssign<$typer> for $typel {}
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAssign<&$typer> for $typel {}
        });

        $crate::if_all!(($($rem)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRemAssign<$typer> for $typel {}
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRemAssign<&$typer> for $typel {}
        });

        $crate::if_all!(($($or)?) ($($and)?) ($($xor)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBitAssign<$typer> for $typel {}
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBitAssign<&$typer> for $typel {}
        });

        $crate::if_all!(($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShiftAssign<$typer> for $typel {}
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShiftAssign<&$typer> for $typel {}
        });

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) ($($rem)?) ($($or)?) ($($and)?) ($($xor)?) ($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAllAssign<$typer> for $typel {}
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAllAssign<&$typer> for $typel {}
        });
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |,
     $(+= $add:block)? $(-= $sub:block)? $(*= $mul:block)? $(/= $div:block)? $(%= $rem:block)?
     $(|= $or:block)? $(&= $and:block)? $(^= $xor:block)? $(<<= $shl:block)? $(>>= $shr:block)?) => {
        $crate::ops_impl!(@mut AddAssign,    add_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($add)?);
        $crate::ops_impl!(@mut SubAssign,    sub_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($sub)?);
        $crate::ops_impl!(@mut MulAssign,    mul_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($mul)?);
        $crate::ops_impl!(@mut DivAssign,    div_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($div)?);
        $crate::ops_impl!(@mut RemAssign,    rem_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($rem)?);
        $crate::ops_impl!(@mut BitOrAssign,  bitor_assign,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($or)?);
        $crate::ops_impl!(@mut BitAndAssign, bitand_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($and)?);
        $crate::ops_impl!(@mut BitXorAssign, bitxor_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($xor)?);
        $crate::ops_impl!(@mut ShlAssign,    shl_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($shl)?);
        $crate::ops_impl!(@mut ShrAssign,    shr_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($shr)?);

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAssign<$typer> for $typel {}
        });

        $crate::if_all!(($($rem)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRemAssign<$typer> for $typel {}
        });

        $crate::if_all!(($($or)?) ($($and)?) ($($xor)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBitAssign<$typer> for $typel {}
        });

        $crate::if_all!(($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShiftAssign<$typer> for $typel {}
        });

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) ($($rem)?) ($($or)?) ($($and)?) ($($xor)?) ($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAllAssign<$typer> for $typel {}
        });
    };

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!(@binary Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($add)?);
        $crate::ops_impl!(@binary Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($sub)?);
        $crate::ops_impl!(@binary Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($mul)?);
        $crate::ops_impl!(@binary Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($div)?);
        $crate::ops_impl!(@binary Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($rem)?);
        $crate::ops_impl!(@binary BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($or)?);
        $crate::ops_impl!(@binary BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($and)?);
        $crate::ops_impl!(@binary BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($xor)?);
        $crate::ops_impl!(@binary Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($shl)?);
        $crate::ops_impl!(@binary Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($shr)?);

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<$typer> for &$typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<&$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<&$typer> for &$typel { type Output = $type; }
        });

        $crate::if_all!(($($rem)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<$typer> for &$typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<&$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<&$typer> for &$typel { type Output = $type; }
        });

        $crate::if_all!(($($or)?) ($($and)?) ($($xor)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<$typer> for &$typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<&$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<&$typer> for &$typel { type Output = $type; }
        });

        $crate::if_all!(($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<$typer> for &$typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<&$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<&$typer> for &$typel { type Output = $type; }
        });

        $crate::if_all!(($($add)?)($($sub)?) ($($mul)?) ($($div)?) ($($rem)?) ($($or)?) ($($and)?) ($($xor)?) ($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<$typer> for &$typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<&$typer> for $typel { type Output = $type; }
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<&$typer> for &$typel { type Output = $type; }
        });
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!(@binary Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($add)?);
        $crate::ops_impl!(@binary Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($sub)?);
        $crate::ops_impl!(@binary Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($mul)?);
        $crate::ops_impl!(@binary Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($div)?);
        $crate::ops_impl!(@binary Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($rem)?);
        $crate::ops_impl!(@binary BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($or)?);
        $crate::ops_impl!(@binary BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($and)?);
        $crate::ops_impl!(@binary BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($xor)?);
        $crate::ops_impl!(@binary Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($shl)?);
        $crate::ops_impl!(@binary Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($shr)?);

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($rem)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($or)?) ($($and)?) ($($xor)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) ($($rem)?) ($($or)?) ($($and)?) ($($xor)?) ($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<$typer> for $typel { type Output = $type; }
        });
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!(@binary Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($add)?);
        $crate::ops_impl!(@binary Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($sub)?);
        $crate::ops_impl!(@binary Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($mul)?);
        $crate::ops_impl!(@binary Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($div)?);
        $crate::ops_impl!(@binary Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($rem)?);
        $crate::ops_impl!(@binary BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($or)?);
        $crate::ops_impl!(@binary BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($and)?);
        $crate::ops_impl!(@binary BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($xor)?);
        $crate::ops_impl!(@binary Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($shl)?);
        $crate::ops_impl!(@binary Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($shr)?);

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($rem)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($or)?) ($($and)?) ($($xor)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) ($($rem)?) ($($or)?) ($($and)?) ($($xor)?) ($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<$typer> for $typel { type Output = $type; }
        });
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!(@binary Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($add)?);
        $crate::ops_impl!(@binary Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($sub)?);
        $crate::ops_impl!(@binary Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($mul)?);
        $crate::ops_impl!(@binary Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($div)?);
        $crate::ops_impl!(@binary Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($rem)?);
        $crate::ops_impl!(@binary BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($or)?);
        $crate::ops_impl!(@binary BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($and)?);
        $crate::ops_impl!(@binary BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($xor)?);
        $crate::ops_impl!(@binary Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($shl)?);
        $crate::ops_impl!(@binary Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($shr)?);

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::Ops<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($rem)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsRem<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($or)?) ($($and)?) ($($xor)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsBit<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsShift<$typer> for $typel { type Output = $type; }
        });

        $crate::if_all!(($($add)?) ($($sub)?) ($($mul)?) ($($div)?) ($($rem)?) ($($or)?) ($($and)?) ($($xor)?) ($($shl)?) ($($shr)?) {
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAll<$typer> for $typel { type Output = $type; }
        });
    };

    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$lhs: &$typel, $rhs: &$typer| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$rhs: &$typer, $lhs: &$typel| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$lhs: &$typel, $rhs: $typer| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$rhs: &$typer, $lhs: $typel| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$lhs: $typel, $rhs: &$typer| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$rhs: $typer, $lhs: &$typel| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$lhs: $typel, $rhs: $typer| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                        |$rhs: $typer, $lhs: $typel| -> $type,
                        $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                        $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path, $(neg $neg:block)? $(not $not:block)?) => {
        $crate::ops_impl!(@unary Neg, neg, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $($neg)?);
        $crate::ops_impl!(@unary Not, not, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $($not)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path, $(neg $neg:block)? $(not $not:block)?) => {
        $crate::ops_impl!(@unary Neg, neg, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $($neg)?);
        $crate::ops_impl!(@unary Not, not, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $($not)?);
    };
}

// TODO: Consider ways to make procedural macro instead of declarative
#[macro_export]
macro_rules! ops_impl_auto {
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer |, $($op { $lhs_expr $op $rhs_expr })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer |, $($op { $lhs_expr $op $rhs_expr })+);
    };

    (@bin $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };
    (@bin $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };
    (@bin $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };
    (@bin $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };

    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };
    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };
    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };
    (@diff $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr) ($rhs_expr:expr)) => {
        $crate::ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type, $($op { ($lhs_expr $op $rhs_expr).into() })+);
    };

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr)) => {
        $crate::ops_impl!(@unary $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type, $($op { ($op $lhs_expr).into() })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path, [$($op:tt)+] ($lhs_expr:expr)) => {
        $crate::ops_impl!(@unary $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type, $($op { ($op $lhs_expr).into() })+);
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! ops_struct_def {
        ($type1:ident, $type2:ident $(,)?) => {
            #[derive(Debug, PartialEq, Eq)]
            struct $type1 {
                x: i64,
            }

            #[derive(Debug, PartialEq, Eq)]
            struct $type2 {
                x: i64,
            }

            impl From<i64> for $type1 {
                fn from(value: i64) -> Self {
                    Self { x: value }
                }
            }

            impl From<i64> for $type2 {
                fn from(value: i64) -> Self {
                    Self { x: value }
                }
            }
        };
        ($type1:ident, $type2:ident, $trait:ident $(+ $traits:ident)* $(,)?) => {
            #[derive(Debug, PartialEq, Eq)]
            struct $type1<N: $trait $(+ $traits)*> {
                x: N,
            }

            #[derive(Debug, PartialEq, Eq)]
            struct $type2<N: $trait$(+ $traits)*> {
                x: N,
            }
        };
    }

    macro_rules! ops_struct_impl {
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |&mut $type1:path, &$type2:path|) => {
            ops_impl_auto!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &mut $type1, b: &$type1|, [+= -= *= /= %= |= &= ^= <<= >>=] (a.x) (b.x));
            ops_impl_auto!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &mut $type1, b: &$type2|, [+= -= *= /= %= |= &= ^= <<= >>=] (a.x) (b.x));
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |&mut $type1:path, $type2:path|) => {
            ops_impl_auto!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &mut $type1, b: $type1|, [+= -= *= /= %= |= &= ^= <<= >>=] (a.x) (b.x));
            ops_impl_auto!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &mut $type1, b: $type2|, [+= -= *= /= %= |= &= ^= <<= >>=] (a.x) (b.x));
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |&$type1:path, &$type2:path| -> $type:path) => {
            // ops_impl_auto!(@bin $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &$type1, b: &$type1| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));
            // ops_impl_auto!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &$type1, b: &$type2| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: &$type1| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });

            ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: &$type2| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |&$type1:path, $type2:path| -> $type:path) => {
            // ops_impl_auto!(@bin $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &$type1, b: $type1| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));
            // ops_impl_auto!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: &$type1, b: $type2| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: $type1| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });

            ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: $type2| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |$type1:path, &$type2:path| -> $type:path) => {
            // ops_impl_auto!(@bin $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: $type1, b: &$type1| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));
            // ops_impl_auto!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: $type1, b: &$type2| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: &$type1| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });

            ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: $type1, b: &$type2| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |$type1:path, $type2:path| -> $type:path) => {
            // ops_impl_auto!(@bin $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: $type1, b: $type1| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));
            // ops_impl_auto!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |a: $type1, b: $type2| -> $type, [+ - * / % | & ^ << >>] (a.x) (b.x));

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: $type1| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });

            ops_impl!(@diff $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: $type2| -> $type,
                    + { $type { x: (a.x + b.x).into() } }
                    - { $type { x: (a.x - b.x).into() } }
                    * { $type { x: (a.x * b.x).into() } }
                    / { $type { x: (a.x / b.x).into() } }
                    % { $type { x: (a.x % b.x).into() } }
                    | { $type { x: (a.x | b.x).into() } }
                    & { $type { x: (a.x & b.x).into() } }
                    ^ { $type { x: (a.x ^ b.x).into() } }
                    << { $type { x: (a.x << b.x).into() } }
                    >> { $type { x: (a.x >> b.x).into() } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |&$type1:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1| -> $type,
                    neg { $type { x: (-a.x).into() } }
                    not { $type { x: (-a.x).into() } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? |$type1:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1| -> $type,
                    neg { $type { x: (-a.x).into() } }
                    not { $type { x: (-a.x).into() } });
        };
    }

    ops_struct_def!(A0, B0);
    ops_struct_def!(A1, B1);
    ops_struct_def!(A2, B2);
    ops_struct_def!(A3, B3);

    ops_struct_def!(X0, Y0, Sized + Clone + Copy);
    ops_struct_def!(X1, Y1, Sized + Clone + Copy);
    ops_struct_def!(X2, Y2, Sized + Clone + Copy);
    ops_struct_def!(X3, Y3, Sized + Clone + Copy);

    ops_struct_impl!(|&mut A0, &B0|);
    ops_struct_impl!(|&mut A1, B1|);

    ops_struct_impl!(|&A0, &B0| -> A0);
    ops_struct_impl!(|&A1, B1| -> A1);
    ops_struct_impl!(|A2, &B2| -> A2);
    ops_struct_impl!(|A3, B3| -> A3);

    ops_struct_impl!(|&A0| -> A0);
    ops_struct_impl!(|A1| -> A1);

    ops_struct_impl!(<N: Sized + Clone + Copy + OpsAllAssign> |&mut X0<N>, &Y0<N>|);
    ops_struct_impl!(<N: Sized + Clone + Copy + OpsAllAssign> |&mut X1<N>, Y1<N>|);

    ops_struct_impl!(<N: Sized + Clone + Copy + OpsAll + OpsAllFrom> |&X0<N>, &Y0<N>| -> X0<N>);
    ops_struct_impl!(<N: Sized + Clone + Copy + OpsAll + OpsAllFrom> |&X1<N>, Y1<N>| -> X0<N>);
    ops_struct_impl!(<N: Sized + Clone + Copy + OpsAll + OpsAllFrom> |X2<N>, &Y2<N>| -> X0<N>);
    ops_struct_impl!(<N: Sized + Clone + Copy + OpsAll + OpsAllFrom> |X3<N>, Y3<N>| -> X0<N>);

    ops_struct_impl!(<N: Sized + Clone + Copy + OpsNegFrom + OpsNotFrom> |&X0<N>| -> X0<N>);
    ops_struct_impl!(<N: Sized + Clone + Copy + OpsNegFrom + OpsNotFrom> |X1<N>| -> X1<N>);

    macro_rules! assert_ops {
        ($argl:expr, $argr:expr, $fn:ident, $val1:expr, $val2:expr) => {
            assert_eq!($argl + $argr, $fn($val1 + $val2));
            assert_eq!($argl - $argr, $fn($val1 - $val2));
            assert_eq!($argl * $argr, $fn($val1 * $val2));
            assert_eq!($argl / $argr, $fn($val1 / $val2));
            assert_eq!($argl % $argr, $fn($val1 % $val2));
            assert_eq!($argl | $argr, $fn($val1 | $val2));
            assert_eq!($argl & $argr, $fn($val1 & $val2));
            assert_eq!($argl ^ $argr, $fn($val1 ^ $val2));
            assert_eq!($argl << $argr, $fn($val1 << $val2));
            assert_eq!($argl >> $argr, $fn($val1 >> $val2));
        };
    }

    macro_rules! assert_ops_mut {
        ($op:tt $argl:expr, $argr:expr, $val:expr) => {{
            let mut val = $argl;

            val $op $argr;

            assert_eq!(val, $val);
        }};
        ($argl:expr, $argr:expr, $fn:ident, $val1:expr, $val2:expr) => {
            assert_ops_mut!(+= $argl, $argr, $fn($val1 + $val2));
            assert_ops_mut!(-= $argl, $argr, $fn($val1 - $val2));
            assert_ops_mut!(*= $argl, $argr, $fn($val1 * $val2));
            assert_ops_mut!(/= $argl, $argr, $fn($val1 / $val2));
            assert_ops_mut!(%= $argl, $argr, $fn($val1 % $val2));
            assert_ops_mut!(|= $argl, $argr, $fn($val1 | $val2));
            assert_ops_mut!(&= $argl, $argr, $fn($val1 & $val2));
            assert_ops_mut!(^= $argl, $argr, $fn($val1 ^ $val2));
            assert_ops_mut!(<<= $argl, $argr, $fn($val1 << $val2));
            assert_ops_mut!(>>= $argl, $argr, $fn($val1 >> $val2));
        };
    }

    fn a_fn(x: i64) -> A0 {
        A0 { x }
    }

    fn b_fn(x: i64) -> B0 {
        B0 { x }
    }

    fn x_fn<N: Sized + Copy>(x: N) -> X0<N> {
        X0::<N> { x }
    }

    fn y_fn<N: Sized + Copy>(x: N) -> Y0<N> {
        Y0::<N> { x }
    }

    #[test]
    fn ops() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops!(&a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops!(&a_fn(val1), &b_fn(val2), a_fn, val1, val2);

        assert_ops!(&a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops!(&a_fn(val1), b_fn(val2), a_fn, val1, val2);

        assert_ops!(a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops!(a_fn(val1), &b_fn(val2), a_fn, val1, val2);

        assert_ops!(a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops!(a_fn(val1), b_fn(val2), a_fn, val1, val2);

        assert_eq!(-&a_fn(val1), a_fn(-val1));
        assert_eq!(!&a_fn(val1), a_fn(-val1));

        assert_eq!(-a_fn(val1), a_fn(-val1));
        assert_eq!(!a_fn(val1), a_fn(-val1));
    }

    #[test]
    fn ops_gen() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops!(&x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops!(&x_fn(val1), &y_fn(val2), x_fn, val1, val2);

        assert_ops!(&x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops!(&x_fn(val1), y_fn(val2), x_fn, val1, val2);

        assert_ops!(x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops!(x_fn(val1), &y_fn(val2), x_fn, val1, val2);

        assert_ops!(x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops!(x_fn(val1), y_fn(val2), x_fn, val1, val2);

        assert_eq!(-&x_fn(val1), x_fn(-val1));
        assert_eq!(!&x_fn(val1), x_fn(-val1));

        assert_eq!(-x_fn(val1), x_fn(-val1));
        assert_eq!(!x_fn(val1), x_fn(-val1));
    }

    #[test]
    fn ops_mut() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_mut!(a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(a_fn(val1), &b_fn(val2), a_fn, val1, val2);

        assert_ops_mut!(a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(a_fn(val1), b_fn(val2), a_fn, val1, val2);
    }

    #[test]
    fn ops_gen_mut() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_mut!(x_fn(val1), &x_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(x_fn(val1), &y_fn(val2), x_fn, val1, val2);

        assert_ops_mut!(x_fn(val1), x_fn(val2), x_fn, val1, val2);
        assert_ops_mut!(x_fn(val1), y_fn(val2), x_fn, val1, val2);
    }
}

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

pub trait Ops<Rhs = Self>: Sized + Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs>
where
    Rhs: Ops<Self>,
{
    type Output;
}

pub trait OpsRem<Rhs = Self>: Sized + Rem<Rhs>
where
    Rhs: OpsRem<Self>,
{
    type Output;
}

pub trait OpsBit<Rhs = Self>: Sized + BitOr<Rhs> + BitAnd<Rhs> + BitXor<Rhs>
where
    Rhs: OpsBit<Self>,
{
    type Output;
}

pub trait OpsShift<Rhs = Self>: Sized + Shl<Rhs> + Shr<Rhs>
where
    Rhs: OpsShift<Self>,
{
    type Output;
}

pub trait OpsAll<Rhs = Self>: Ops<Rhs> + OpsRem<Rhs> + OpsBit<Rhs> + OpsShift<Rhs>
where
    Rhs: OpsAll<Self>,
{
    type Output;
}

pub trait OpsAssign<Rhs = Self>: AddAssign<Rhs> + SubAssign<Rhs> + MulAssign<Rhs> + DivAssign<Rhs> {}

pub trait OpsRemAssign<Rhs = Self>: RemAssign<Rhs> {}

pub trait OpsBitAssign<Rhs = Self>: BitOrAssign<Rhs> + BitAndAssign<Rhs> + BitXorAssign<Rhs> {}

pub trait OpsShiftAssign<Rhs = Self>: ShlAssign<Rhs> + ShrAssign<Rhs> {}

pub trait OpsAssignAll<Rhs = Self>:
    OpsAssign<Rhs> + OpsRemAssign<Rhs> + OpsShiftAssign<Rhs> + OpsBitAssign<Rhs>
{
}

pub trait OpsFrom<Rhs = Self>:
    Ops<Rhs>
    + From<<Self as Add<Rhs>>::Output>
    + From<<Self as Sub<Rhs>>::Output>
    + From<<Self as Mul<Rhs>>::Output>
    + From<<Self as Div<Rhs>>::Output>
where
    Rhs: Ops<Self>,
{
}

pub trait OpsRemFrom<Rhs = Self>: OpsRem<Rhs> + From<<Self as Rem<Rhs>>::Output>
where
    Rhs: OpsRem<Self>,
{
}

pub trait OpsBitFrom<Rhs = Self>:
    OpsBit<Rhs>
    + From<<Self as BitOr<Rhs>>::Output>
    + From<<Self as BitAnd<Rhs>>::Output>
    + From<<Self as BitXor<Rhs>>::Output>
where
    Rhs: OpsBit<Self>,
{
}

pub trait OpsShiftFrom<Rhs = Self>:
    OpsShift<Rhs> + From<<Self as Shl<Rhs>>::Output> + From<<Self as Shr<Rhs>>::Output>
where
    Rhs: OpsShift<Self>,
{
}

pub trait OpsNegFrom: Neg + From<<Self as Neg>::Output> {}
pub trait OpsNotFrom: Not + From<<Self as Not>::Output> {}

pub trait OpsAllFrom<Rhs = Self>:
    OpsAll<Rhs> + OpsFrom<Rhs> + OpsRemFrom<Rhs> + OpsBitFrom<Rhs> + OpsShiftFrom<Rhs>
where
    Rhs: OpsAll<Self>,
{
}

pub trait AddChecked<Rhs = Self> {
    type Output;

    fn checked_add(
        self,
        rhs: Rhs,
    ) -> Option<Self::Output>;
}

pub trait SubChecked<Rhs = Self> {
    type Output;

    fn checked_sub(
        self,
        rhs: Rhs,
    ) -> Option<Self::Output>;
}

pub trait MulChecked<Rhs = Self> {
    type Output;

    fn checked_mul(
        self,
        rhs: Rhs,
    ) -> Option<Self::Output>;
}

pub trait DivChecked<Rhs = Self> {
    type Output;

    fn checked_div(
        self,
        rhs: Rhs,
    ) -> Option<Self::Output>;
}

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

#[macro_export]
macro_rules! ops_impl_mut {
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $fn);
    };
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $fn);
    };

    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |) => {};
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |) => {};

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |,
     $(+= $add:block)? $(-= $sub:block)? $(*= $mul:block)? $(/= $div:block)? $(%= $rem:block)?
     $(|= $or:block)? $(&= $and:block)? $(^= $xor:block)? $(<<= $shl:block)? $(>>= $shr:block)?) => {
        $crate::ops_impl_mut!(@impl AddAssign,    add_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($add)?);
        $crate::ops_impl_mut!(@impl SubAssign,    sub_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($sub)?);
        $crate::ops_impl_mut!(@impl MulAssign,    mul_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($mul)?);
        $crate::ops_impl_mut!(@impl DivAssign,    div_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($div)?);
        $crate::ops_impl_mut!(@impl RemAssign,    rem_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($rem)?);
        $crate::ops_impl_mut!(@impl BitOrAssign,  bitor_assign,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($or)?);
        $crate::ops_impl_mut!(@impl BitAndAssign, bitand_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($and)?);
        $crate::ops_impl_mut!(@impl BitXorAssign, bitxor_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($xor)?);
        $crate::ops_impl_mut!(@impl ShlAssign,    shl_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($shl)?);
        $crate::ops_impl_mut!(@impl ShrAssign,    shr_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($shr)?);

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
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAssignAll<$typer> for $typel {}
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAssignAll<&$typer> for $typel {}
        });
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |,
     $(+= $add:block)? $(-= $sub:block)? $(*= $mul:block)? $(/= $div:block)? $(%= $rem:block)?
     $(|= $or:block)? $(&= $and:block)? $(^= $xor:block)? $(<<= $shl:block)? $(>>= $shr:block)?) => {
        $crate::ops_impl_mut!(@impl AddAssign,    add_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($add)?);
        $crate::ops_impl_mut!(@impl SubAssign,    sub_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($sub)?);
        $crate::ops_impl_mut!(@impl MulAssign,    mul_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($mul)?);
        $crate::ops_impl_mut!(@impl DivAssign,    div_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($div)?);
        $crate::ops_impl_mut!(@impl RemAssign,    rem_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($rem)?);
        $crate::ops_impl_mut!(@impl BitOrAssign,  bitor_assign,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($or)?);
        $crate::ops_impl_mut!(@impl BitAndAssign, bitand_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($and)?);
        $crate::ops_impl_mut!(@impl BitXorAssign, bitxor_assign, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($xor)?);
        $crate::ops_impl_mut!(@impl ShlAssign,    shl_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($shl)?);
        $crate::ops_impl_mut!(@impl ShrAssign,    shr_assign,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($shr)?);

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
            impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? $crate::ops::OpsAssignAll<$typer> for $typel {}
        });
    };
}

#[macro_export]
macro_rules! ops_impl_bin {
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
    };
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $fn);
    };
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $fn);
    };
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path) => {};
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path) => {};
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path) => {};
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path) => {};

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl_bin!(@impl Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($add)?);
        $crate::ops_impl_bin!(@impl Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($sub)?);
        $crate::ops_impl_bin!(@impl Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($mul)?);
        $crate::ops_impl_bin!(@impl Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($div)?);
        $crate::ops_impl_bin!(@impl Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($rem)?);
        $crate::ops_impl_bin!(@impl BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($or)?);
        $crate::ops_impl_bin!(@impl BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($and)?);
        $crate::ops_impl_bin!(@impl BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($xor)?);
        $crate::ops_impl_bin!(@impl Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($shl)?);
        $crate::ops_impl_bin!(@impl Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($shr)?);

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
        $crate::ops_impl_bin!(@impl Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($add)?);
        $crate::ops_impl_bin!(@impl Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($sub)?);
        $crate::ops_impl_bin!(@impl Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($mul)?);
        $crate::ops_impl_bin!(@impl Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($div)?);
        $crate::ops_impl_bin!(@impl Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($rem)?);
        $crate::ops_impl_bin!(@impl BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($or)?);
        $crate::ops_impl_bin!(@impl BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($and)?);
        $crate::ops_impl_bin!(@impl BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($xor)?);
        $crate::ops_impl_bin!(@impl Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($shl)?);
        $crate::ops_impl_bin!(@impl Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($shr)?);

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
        $crate::ops_impl_bin!(@impl Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($add)?);
        $crate::ops_impl_bin!(@impl Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($sub)?);
        $crate::ops_impl_bin!(@impl Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($mul)?);
        $crate::ops_impl_bin!(@impl Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($div)?);
        $crate::ops_impl_bin!(@impl Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($rem)?);
        $crate::ops_impl_bin!(@impl BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($or)?);
        $crate::ops_impl_bin!(@impl BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($and)?);
        $crate::ops_impl_bin!(@impl BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($xor)?);
        $crate::ops_impl_bin!(@impl Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($shl)?);
        $crate::ops_impl_bin!(@impl Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($shr)?);

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
        $crate::ops_impl_bin!(@impl Add,    add,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($add)?);
        $crate::ops_impl_bin!(@impl Sub,    sub,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($sub)?);
        $crate::ops_impl_bin!(@impl Mul,    mul,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($mul)?);
        $crate::ops_impl_bin!(@impl Div,    div,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($div)?);
        $crate::ops_impl_bin!(@impl Rem,    rem,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($rem)?);
        $crate::ops_impl_bin!(@impl BitOr,  bitor,  $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($or)?);
        $crate::ops_impl_bin!(@impl BitAnd, bitand, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($and)?);
        $crate::ops_impl_bin!(@impl BitXor, bitxor, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($xor)?);
        $crate::ops_impl_bin!(@impl Shl,    shl,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($shl)?);
        $crate::ops_impl_bin!(@impl Shr,    shr,    $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($shr)?);

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

    (@rev $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: &$typer| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$rhs: &$typer, $lhs: &$typel| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
    (@rev $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: $typer| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$rhs: &$typer, $lhs: $typel| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
    (@rev $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: &$typer| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$rhs: $typer, $lhs: &$typel| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
    (@rev $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block)? $(- $sub:block)? $(* $mul:block)? $(/ $div:block)? $(% $rem:block)?
     $(| $or:block)? $(& $and:block)? $(^ $xor:block)? $(<< $shl:block)? $(>> $shr:block)?) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: $typer| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);

        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$rhs: $typer, $lhs: $typel| -> $type,
                              $(+ $add)? $(- $sub)? $(* $mul)? $(/ $div)? $(% $rem)?
                              $(| $or)? $(& $and)? $(^ $xor)? $(<< $shl)? $(>> $shr)?);
    };
}

#[macro_export]
macro_rules! ops_impl {
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $fn);
    };
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $fn);
    };

    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path | -> $type:path) => {};
    (@impl $op_trait:ident, $op_name:ident, $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path | -> $type:path) => {};

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path, $(neg $neg:block)? $(not $not:block)?) => {
        $crate::ops_impl!(@impl Neg, neg, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $($neg)?);
        $crate::ops_impl!(@impl Not, not, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $($not)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path, $(neg $neg:block)? $(not $not:block)?) => {
        $crate::ops_impl!(@impl Neg, neg, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $($neg)?);
        $crate::ops_impl!(@impl Not, not, $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $($not)?);
    };
}

#[macro_export]
macro_rules! ops_impl_mut_auto {
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |, { $lhs_expr:expr } [$($op:tt)+] { $rhs_expr:expr }) => {
        $crate::ops_impl_mut!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer |, $($op { $lhs_expr $op $rhs_expr })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |, { $lhs_expr:expr } [$($op:tt)+] { $rhs_expr:expr }) => {
        $crate::ops_impl_mut!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer |, $($op { $lhs_expr $op $rhs_expr })+);
    };
}

#[macro_export]
macro_rules! ops_impl_bin_auto {
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
}

#[macro_export]
macro_rules! ops_impl_bin_diff_auto {
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| => $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| => $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| => $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path, ($lhs_expr:expr) [$($op:tt)+] ($rhs_expr:expr) -> $fn:expr) => {
        $crate::ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| => $type, $($op { $fn($lhs_expr $op $rhs_expr) })+);
    };
}

#[macro_export]
macro_rules! ops_checked_impl {
    ($type:ty $(,)?) => {
        impl AddChecked for $type {
            type Output = $type;

            fn checked_add(
                self,
                rhs: Self,
            ) -> Option<Self::Output> {
                self.checked_add(rhs)
            }
        }

        impl SubChecked for $type {
            type Output = $type;

            fn checked_sub(
                self,
                rhs: Self,
            ) -> Option<Self::Output> {
                self.checked_sub(rhs)
            }
        }

        impl MulChecked for $type {
            type Output = $type;

            fn checked_mul(
                self,
                rhs: Self,
            ) -> Option<Self::Output> {
                self.checked_mul(rhs)
            }
        }

        impl DivChecked for $type {
            type Output = $type;

            fn checked_div(
                self,
                rhs: Self,
            ) -> Option<Self::Output> {
                self.checked_div(rhs)
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::OpsAssignAll;
    use crate::{
        num::Number,
        ops::{OpsAllFrom, OpsNegFrom, OpsNotFrom},
        ops_impl,
    };

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
        };
        ($type1:ident, $type2:ident, $trait:ident $(,)?) => {
            #[derive(Debug, PartialEq, Eq)]
            struct $type1<T: $trait> {
                x: T,
            }

            #[derive(Debug, PartialEq, Eq)]
            struct $type2<T: $trait> {
                x: T,
            }
        };
    }

    macro_rules! ops_struct_impl {
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&mut $type1:path, &$type2:path|) => {
            ops_impl_mut!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &mut $type1, b: &$type1|,
                    += { a.x += b.x }
                    -= { a.x -= b.x }
                    *= { a.x *= b.x }
                    /= { a.x /= b.x }
                    %= { a.x %= b.x }
                    |= { a.x |= b.x }
                    &= { a.x &= b.x }
                    ^= { a.x ^= b.x }
                    <<= { a.x <<= b.x }
                    >>= { a.x >>= b.x });

            ops_impl_mut!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &mut $type1, b: &$type2|,
                    += { a.x += b.x }
                    -= { a.x -= b.x }
                    *= { a.x *= b.x }
                    /= { a.x /= b.x }
                    %= { a.x %= b.x }
                    |= { a.x |= b.x }
                    &= { a.x &= b.x }
                    ^= { a.x ^= b.x }
                    <<= { a.x <<= b.x }
                    >>= { a.x >>= b.x });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&mut $type1:path, $type2:path|) => {
            ops_impl_mut!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &mut $type1, b: $type1|,
                    += { a.x += b.x }
                    -= { a.x -= b.x }
                    *= { a.x *= b.x }
                    /= { a.x /= b.x }
                    %= { a.x %= b.x }
                    |= { a.x |= b.x }
                    &= { a.x &= b.x }
                    ^= { a.x ^= b.x }
                    <<= { a.x <<= b.x }
                    >>= { a.x >>= b.x });

            ops_impl_mut!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &mut $type1, b: $type2|,
                    += { a.x += b.x }
                    -= { a.x -= b.x }
                    *= { a.x *= b.x }
                    /= { a.x /= b.x }
                    %= { a.x %= b.x }
                    |= { a.x |= b.x }
                    &= { a.x &= b.x }
                    ^= { a.x ^= b.x }
                    <<= { a.x <<= b.x }
                    >>= { a.x >>= b.x });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&$type1:path, &$type2:path| -> $type:path) => {
            ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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

            ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&$type1:path, $type2:path| -> $type:path) => {
            ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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

            ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |$type1:path, &$type2:path| -> $type:path) => {
            ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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

            ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: &$type2| -> $type,
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
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |$type1:path, $type2:path| -> $type:path) => {
            ops_impl_bin!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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

            ops_impl_bin!(@rev $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&$type1:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1| -> $type,
                    neg { $type { x: (-a.x).into() } }
                    not { $type { x: (-a.x).into() } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |$type1:path| -> $type:path) => {
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

    ops_struct_def!(X0, Y0, Number);
    ops_struct_def!(X1, Y1, Number);
    ops_struct_def!(X2, Y2, Number);
    ops_struct_def!(X3, Y3, Number);

    ops_struct_impl!(|&mut A0, &B0|);
    ops_struct_impl!(|&mut A1, B1|);

    ops_struct_impl!(|&A0, &B0| -> A0);
    ops_struct_impl!(|&A1, B1| -> A1);
    ops_struct_impl!(|A2, &B2| -> A2);
    ops_struct_impl!(|A3, B3| -> A3);

    ops_struct_impl!(|&A0| -> A0);
    ops_struct_impl!(|A1| -> A1);

    ops_struct_impl!(<N: Number + OpsAssignAll> |&mut X0<N>, &Y0<N>|);
    ops_struct_impl!(<N: Number + OpsAssignAll> |&mut X1<N>, Y1<N>|);

    ops_struct_impl!(<N: Number + OpsAllFrom> |&X0<N>, &Y0<N>| -> X0<N>);
    ops_struct_impl!(<N: Number + OpsAllFrom> |&X1<N>, Y1<N>| -> X0<N>);
    ops_struct_impl!(<N: Number + OpsAllFrom> |X2<N>, &Y2<N>| -> X0<N>);
    ops_struct_impl!(<N: Number + OpsAllFrom> |X3<N>, Y3<N>| -> X0<N>);

    ops_struct_impl!(<N: Number + OpsNegFrom + OpsNotFrom> |&X0<N>| -> X0<N>);
    ops_struct_impl!(<N: Number + OpsNegFrom + OpsNotFrom> |X1<N>| -> X1<N>);

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

    fn x_fn<N: Number>(x: N) -> X0<N> {
        X0::<N> { x }
    }
    fn y_fn<N: Number>(x: N) -> Y0<N> {
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

use std::ops::{
    Add,
    AddAssign,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Div,
    DivAssign,
    Mul,
    MulAssign,
    Neg,
    Not,
    Rem,
    RemAssign,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign,
    Sub,
    SubAssign,
};

pub trait Ops<Rhs = Self>: Sized + Add<Rhs> + Sub<Rhs> + Mul<Rhs> + Div<Rhs>
where
    Rhs: Ops<Self>, {
    type Output;
}

pub trait OpsBit<Rhs = Self>: Sized + BitOr<Rhs> + BitAnd<Rhs> + BitXor<Rhs>
where
    Rhs: OpsBit<Self>, {
    type Output;
}

pub trait OpsShift<Rhs = Self>: Sized + Shl<Rhs> + Shr<Rhs>
where
    Rhs: OpsShift<Self>, {
    type Output;
}

pub trait OpsAssign<Rhs = Self>: AddAssign<Rhs> + SubAssign<Rhs> + MulAssign<Rhs> + DivAssign<Rhs> {}
pub trait OpsBitAssign<Rhs = Self>: BitOrAssign<Rhs> + BitAndAssign<Rhs> + BitXorAssign<Rhs> {}
pub trait OpsShiftAssign<Rhs = Self>: ShlAssign<Rhs> + ShrAssign<Rhs> {}

pub trait OpsAll<'ops, Rhs = Self>
where
    Rhs: 'ops + Ops<Self> + Ops<&'ops Self>,
    Self: 'ops + Ops<Rhs> + Ops<&'ops Rhs>,
    &'ops Rhs: Ops<Self> + Ops<&'ops Self>,
    &'ops Self: Ops<Rhs> + Ops<&'ops Rhs>, {
}

pub trait OpsBitAll<'ops, Rhs = Self>
where
    Rhs: 'ops + OpsBit<Self> + OpsBit<&'ops Self>,
    Self: 'ops + OpsBit<Rhs> + OpsBit<&'ops Rhs>,
    &'ops Rhs: OpsBit<Self> + OpsBit<&'ops Self>,
    &'ops Self: OpsBit<Rhs> + OpsBit<&'ops Rhs>, {
}

pub trait OpsShiftAll<'ops, Rhs = Self>
where
    Rhs: 'ops + OpsShift<Self> + OpsShift<&'ops Self>,
    Self: 'ops + OpsShift<Rhs> + OpsShift<&'ops Rhs>,
    &'ops Rhs: OpsShift<Self> + OpsShift<&'ops Self>,
    &'ops Self: OpsShift<Rhs> + OpsShift<&'ops Rhs>, {
}

pub trait OpsAssignAll<'ops, Rhs = Self>: OpsAssign<Rhs> + OpsAssign<&'ops Rhs>
where
    Rhs: 'ops, {
}

pub trait OpsBitAssignAll<'ops, Rhs = Self>: OpsBitAssign<Rhs> + OpsBitAssign<&'ops Rhs>
where
    Rhs: 'ops, {
}

pub trait OpsShiftAssignAll<'ops, Rhs = Self>: OpsShiftAssign<Rhs> + OpsShiftAssign<&'ops Rhs>
where
    Rhs: 'ops, {
}

#[macro_export]
macro_rules! ops_impl_std {
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &mut $typel:ty, $rhs:ident : & $typer:ty | -> $type:ty $fn:block) => {
        impl $op_trait<&$typer> for $typel {
            #[allow(clippy::redundant_closure_call)]
            fn $op_name(&mut self, rhs: &$typer) { (|$lhs: &mut $typel, $rhs: &$typer| $fn)(self, rhs); }
        }
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &mut $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        impl $op_trait<$typer> for $typel {
            #[allow(clippy::redundant_closure_call)]
            fn $op_name(&mut self, rhs: $typer) { (|$lhs: &mut $typel, $rhs: $typer| $fn)(self, rhs); }
        }
    };

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

    ($op_trait:ident, $op_name:ident, | $lhs:ident : & $typel:ty | -> $type:ty $fn:block) => {
        impl $op_trait for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self) -> Self::Output { (|$lhs: &$typel| $fn)(self) }
        }
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty | -> $type:ty $fn:block) => {
        impl $op_trait for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self) -> Self::Output { (|$lhs: $typel| $fn)(self) }
        }
    };
}

#[macro_export]
macro_rules! ops_impl_std_complete {
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &mut $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &mut $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &mut $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &mut $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &mut $typel, $rhs: $typer| -> $type $fn);
    };

    ($op_trait:ident, $op_name:ident, | $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    ($op_trait:ident, $op_name:ident, | $lhs:ident : &$typel:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: &$typel| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident, | $lhs:ident : $typel:ty | -> $type:ty $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name, |$lhs: $typel| -> $type $fn);
    };
}

#[macro_export]
macro_rules! ops_impl_raw {
    (+ $($t:tt)+) => { $crate::ops_impl_std_complete!(Add, add, $($t)+); };
    (- $($t:tt)+) => { $crate::ops_impl_std_complete!(Sub, sub, $($t)+); };
    (* $($t:tt)+) => { $crate::ops_impl_std_complete!(Mul, mul, $($t)+); };
    (/ $($t:tt)+) => { $crate::ops_impl_std_complete!(Div, div, $($t)+); };
    (% $($t:tt)+) => { $crate::ops_impl_std_complete!(Rem, rem, $($t)+); };
    (| $($t:tt)+) => { $crate::ops_impl_std_complete!(BitOr, bitor, $($t)+); };
    (& $($t:tt)+) => { $crate::ops_impl_std_complete!(BitAnd, bitand, $($t)+); };
    (^ $($t:tt)+) => { $crate::ops_impl_std_complete!(BitXor, bitxor, $($t)+); };
    (<< $($t:tt)+) => { $crate::ops_impl_std_complete!(Shl, shl, $($t)+); };
    (>> $($t:tt)+) => { $crate::ops_impl_std_complete!(Shr, shr, $($t)+); };

    (+= $($t:tt)+) => { $crate::ops_impl_std_complete!(AddAssign, add_assign, $($t)+); };
    (-= $($t:tt)+) => { $crate::ops_impl_std_complete!(SubAssign, sub_assign, $($t)+); };
    (*= $($t:tt)+) => { $crate::ops_impl_std_complete!(MulAssign, mul_assign, $($t)+); };
    (/= $($t:tt)+) => { $crate::ops_impl_std_complete!(DivAssign, div_assign, $($t)+); };
    (%= $($t:tt)+) => { $crate::ops_impl_std_complete!(RemAssign, rem_assign, $($t)+); };
    (|= $($t:tt)+) => { $crate::ops_impl_std_complete!(BitOrAssign, bitor_assign, $($t)+); };
    (&= $($t:tt)+) => { $crate::ops_impl_std_complete!(BitAndAssign, bitand_assign, $($t)+); };
    (^= $($t:tt)+) => { $crate::ops_impl_std_complete!(BitXorAssign, bitxor_assign, $($t)+); };
    (<<= $($t:tt)+) => { $crate::ops_impl_std_complete!(ShlAssign, shl_assign, $($t)+); };
    (>>= $($t:tt)+) => { $crate::ops_impl_std_complete!(ShrAssign, shr_assign, $($t)+); };

    (neg $($t:tt)+) => { $crate::ops_impl_std_complete!(Neg, neg, $($t)+); };
    (not $($t:tt)+) => { $crate::ops_impl_std_complete!(Not, not, $($t)+); };
}

#[macro_export]
macro_rules! ops_impl {
    ($op:tt | $lhs:ident : &mut $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: &mut $typel, $rhs: &$typer| -> $type $fn); };
    ($op:tt | $lhs:ident : &mut $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: &mut $typel, $rhs: $typer| -> $type $fn); };

    ($op:tt | $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: &$typel, $rhs: &$typer| -> $type $fn); };
    ($op:tt | $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: &$typel, $rhs: $typer| -> $type $fn); };
    ($op:tt | $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: $typel, $rhs: &$typer| -> $type $fn); };
    ($op:tt | $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: $typel, $rhs: $typer| -> $type $fn); };

    ($op:ident | $lhs:ident : &$typel:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: &$typel| -> $type $fn); };
    ($op:ident | $lhs:ident : $typel:ty | -> $type:ty $fn:block) => { $crate::ops_impl_raw!($op |$lhs: $typel| -> $type $fn); };

    (| $lhs:ident : &mut $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty,
     $(+= $add:block -= $sub:block *= $mul:block /= $div:block)? $(%= $rem:block)?
     $(|= $or:block &= $and:block ^= $xor:block)? $(<<= $shl:block >>= $shr:block)?) => {
        $(
            $crate::ops_impl!(+= |$lhs: &mut $typel, $rhs: &$typer| -> $type $add);
            $crate::ops_impl!(-= |$lhs: &mut $typel, $rhs: &$typer| -> $type $sub);
            $crate::ops_impl!(*= |$lhs: &mut $typel, $rhs: &$typer| -> $type $mul);
            $crate::ops_impl!(/= |$lhs: &mut $typel, $rhs: &$typer| -> $type $div);

            impl OpsAssign<$typer> for $typel {}
            impl OpsAssign<&$typer> for $typel {}

            impl OpsAssignAll<'_, $typer> for $typel {}
        )?

        $($crate::ops_impl!(%= |$lhs: &mut $typel, $rhs: &$typer| -> $type $rem);)?
        $(
            $crate::ops_impl!(|= |$lhs: &mut $typel, $rhs: &$typer| -> $type $or);
            $crate::ops_impl!(&= |$lhs: &mut $typel, $rhs: &$typer| -> $type $and);
            $crate::ops_impl!(^= |$lhs: &mut $typel, $rhs: &$typer| -> $type $xor);

            impl OpsBitAssign<$typer> for $typel {}
            impl OpsBitAssign<&$typer> for $typel {}

            impl OpsBitAssignAll<'_, $typer> for $typel {}
        )?
        $(
            $crate::ops_impl!(<<= |$lhs: &mut $typel, $rhs: &$typer| -> $type $shl);
            $crate::ops_impl!(>>= |$lhs: &mut $typel, $rhs: &$typer| -> $type $shr);

            impl OpsShiftAssign<$typer> for $typel {}
            impl OpsShiftAssign<&$typer> for $typel {}

            impl OpsShiftAssignAll<'_, $typer> for $typel {}
        )?
    };
    (| $lhs:ident : &mut $typel:ty, $rhs:ident : $typer:ty | -> $type:ty,
     $(+= $add:block -= $sub:block *= $mul:block /= $div:block)? $(%= $rem:block)?
     $(|= $or:block &= $and:block ^= $xor:block)? $(<<= $shl:block >>= $shr:block)?) => {
        $(
            $crate::ops_impl!(+= |$lhs: &mut $typel, $rhs: $typer| -> $type $add);
            $crate::ops_impl!(-= |$lhs: &mut $typel, $rhs: $typer| -> $type $sub);
            $crate::ops_impl!(*= |$lhs: &mut $typel, $rhs: $typer| -> $type $mul);
            $crate::ops_impl!(/= |$lhs: &mut $typel, $rhs: $typer| -> $type $div);

            impl OpsAssign<$typer> for $typel {}
        )?

        $($crate::ops_impl!(%= |$lhs: &mut $typel, $rhs: $typer| -> $type $rem);)?
        $(
            $crate::ops_impl!(|= |$lhs: &mut $typel, $rhs: $typer| -> $type $or);
            $crate::ops_impl!(&= |$lhs: &mut $typel, $rhs: $typer| -> $type $and);
            $crate::ops_impl!(^= |$lhs: &mut $typel, $rhs: $typer| -> $type $xor);

            impl OpsBitAssign<$typer> for $typel {}
        )?
        $(
            $crate::ops_impl!(<<= |$lhs: &mut $typel, $rhs: $typer| -> $type $shl);
            $crate::ops_impl!(>>= |$lhs: &mut $typel, $rhs: $typer| -> $type $shr);

            impl OpsShiftAssign<$typer> for $typel {}
        )?
    };

    (| $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | -> $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $(
            $crate::ops_impl!(+ |$lhs: &$typel, $rhs: &$typer| -> $type $add);
            $crate::ops_impl!(- |$lhs: &$typel, $rhs: &$typer| -> $type $sub);
            $crate::ops_impl!(* |$lhs: &$typel, $rhs: &$typer| -> $type $mul);
            $crate::ops_impl!(/ |$lhs: &$typel, $rhs: &$typer| -> $type $div);

            impl Ops<$typer> for $typel { type Output = $type; }
            impl Ops<$typer> for &$typel { type Output = $type; }
            impl Ops<&$typer> for $typel { type Output = $type; }
            impl Ops<&$typer> for &$typel { type Output = $type; }

            impl OpsAll<'_, $typer> for $typel {}
        )?

        $($crate::ops_impl!(% |$lhs: &$typel, $rhs: &$typer| -> $type $rem);)?
        $(
            $crate::ops_impl!(| |$lhs: &$typel, $rhs: &$typer| -> $type $or);
            $crate::ops_impl!(& |$lhs: &$typel, $rhs: &$typer| -> $type $and);
            $crate::ops_impl!(^ |$lhs: &$typel, $rhs: &$typer| -> $type $xor);

            impl OpsBit<$typer> for $typel { type Output = $type; }
            impl OpsBit<$typer> for &$typel { type Output = $type; }
            impl OpsBit<&$typer> for $typel { type Output = $type; }
            impl OpsBit<&$typer> for &$typel { type Output = $type; }

            impl OpsBitAll<'_, $typer> for $typel {}
        )?
        $(
            $crate::ops_impl!(<< |$lhs: &$typel, $rhs: &$typer| -> $type $shl);
            $crate::ops_impl!(>> |$lhs: &$typel, $rhs: &$typer| -> $type $shr);

            impl OpsShift<$typer> for $typel { type Output = $type; }
            impl OpsShift<$typer> for &$typel { type Output = $type; }
            impl OpsShift<&$typer> for $typel { type Output = $type; }
            impl OpsShift<&$typer> for &$typel { type Output = $type; }

            impl OpsShiftAll<'_, $typer> for $typel {}
        )?
    };
    (| $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | -> $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $(
            $crate::ops_impl!(+ |$lhs: &$typel, $rhs: $typer| -> $type $add);
            $crate::ops_impl!(- |$lhs: &$typel, $rhs: $typer| -> $type $sub);
            $crate::ops_impl!(* |$lhs: &$typel, $rhs: $typer| -> $type $mul);
            $crate::ops_impl!(/ |$lhs: &$typel, $rhs: $typer| -> $type $div);
        )?

        $($crate::ops_impl!(% |$lhs: &$typel, $rhs: $typer| -> $type $rem);)?
        $(
            $crate::ops_impl!(| |$lhs: &$typel, $rhs: $typer| -> $type $or);
            $crate::ops_impl!(& |$lhs: &$typel, $rhs: $typer| -> $type $and);
            $crate::ops_impl!(^ |$lhs: &$typel, $rhs: $typer| -> $type $xor);
        )?
        $(
            $crate::ops_impl!(<< |$lhs: &$typel, $rhs: $typer| -> $type $shl);
            $crate::ops_impl!(>> |$lhs: &$typel, $rhs: $typer| -> $type $shr);
        )?
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | -> $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $(
            $crate::ops_impl!(+ |$lhs: $typel, $rhs: &$typer| -> $type $add);
            $crate::ops_impl!(- |$lhs: $typel, $rhs: &$typer| -> $type $sub);
            $crate::ops_impl!(* |$lhs: $typel, $rhs: &$typer| -> $type $mul);
            $crate::ops_impl!(/ |$lhs: $typel, $rhs: &$typer| -> $type $div);
        )?

        $($crate::ops_impl!(% |$lhs: $typel, $rhs: &$typer| -> $type $rem);)?
        $(
            $crate::ops_impl!(| |$lhs: $typel, $rhs: &$typer| -> $type $or);
            $crate::ops_impl!(& |$lhs: $typel, $rhs: &$typer| -> $type $and);
            $crate::ops_impl!(^ |$lhs: $typel, $rhs: &$typer| -> $type $xor);
        )?
        $(
            $crate::ops_impl!(<< |$lhs: $typel, $rhs: &$typer| -> $type $shl);
            $crate::ops_impl!(>> |$lhs: $typel, $rhs: &$typer| -> $type $shr);
        )?
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | -> $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $(
            $crate::ops_impl!(+ |$lhs: $typel, $rhs: $typer| -> $type $add);
            $crate::ops_impl!(- |$lhs: $typel, $rhs: $typer| -> $type $sub);
            $crate::ops_impl!(* |$lhs: $typel, $rhs: $typer| -> $type $mul);
            $crate::ops_impl!(/ |$lhs: $typel, $rhs: $typer| -> $type $div);

            impl Ops<$typer> for $typel { type Output = $type; }
        )?

        $($crate::ops_impl!(% |$lhs: $typel, $rhs: $typer| -> $type $rem);)?
        $(
            $crate::ops_impl!(| |$lhs: $typel, $rhs: $typer| -> $type $or);
            $crate::ops_impl!(& |$lhs: $typel, $rhs: $typer| -> $type $and);
            $crate::ops_impl!(^ |$lhs: $typel, $rhs: $typer| -> $type $xor);

            impl OpsBit<$typer> for $typel { type Output = $type; }
        )?
        $(
            $crate::ops_impl!(<< |$lhs: $typel, $rhs: $typer| -> $type $shl);
            $crate::ops_impl!(>> |$lhs: $typel, $rhs: $typer| -> $type $shr);

            impl OpsShift<$typer> for $typel { type Output = $type; }
        )?
    };
    (| $lhs:ident : &$typel:ty, $rhs:ident : &$typer:ty | => $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(|$lhs: &$typel, $rhs: &$typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!(|$rhs: &$typer, $lhs: &$typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };
    (| $lhs:ident : &$typel:ty, $rhs:ident : $typer:ty | => $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(|$lhs: &$typel, $rhs: $typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!(|$rhs: &$typer, $lhs: $typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : &$typer:ty | => $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(|$lhs: $typel, $rhs: &$typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!(|$rhs: $typer, $lhs: &$typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };
    (| $lhs:ident : $typel:ty, $rhs:ident : $typer:ty | => $type:ty,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(|$lhs: $typel, $rhs: $typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!(|$rhs: $typer, $lhs: $typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };

    (| $lhs:ident : &$typel:ty | -> $type:ty, $(neg $neg:block)? $(not $not:block)?) => {
        $($crate::ops_impl!(neg |$lhs: &$typel| -> $type $neg);)?
        $($crate::ops_impl!(not |$lhs: &$typel| -> $type $not);)?
    };
    (| $lhs:ident : $typel:ty | -> $type:ty, $(neg $neg:block)? $(not $not:block)?) => {
        $($crate::ops_impl!(neg |$lhs: $typel| -> $type $neg);)?
        $($crate::ops_impl!(not |$lhs: $typel| -> $type $not);)?
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

#[cfg(test)]
mod tests {
    use std::ops::{
        Add,
        AddAssign,
        BitAnd,
        BitAndAssign,
        BitOr,
        BitOrAssign,
        BitXor,
        BitXorAssign,
        Div,
        DivAssign,
        Mul,
        MulAssign,
        Neg,
        Not,
        Rem,
        RemAssign,
        Shl,
        ShlAssign,
        Shr,
        ShrAssign,
        Sub,
        SubAssign,
    };

    use super::*;

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
              / { A { x: a.x / b.x } }
              % { A { x: a.x % b.x } }
              | { A { x: a.x | b.x } }
              & { A { x: a.x & b.x } }
              ^ { A { x: a.x ^ b.x } }
              << { A { x: a.x << b.x } }
              >> { A { x: a.x >> b.x } });

    ops_impl!(|a: &A, b: &B| => A,
              + { A { x: a.x + b.x } }
              - { A { x: a.x - b.x } }
              * { A { x: a.x * b.x } }
              / { A { x: a.x / b.x } }
              % { A { x: a.x % b.x } }
              | { A { x: a.x | b.x } }
              & { A { x: a.x & b.x } }
              ^ { A { x: a.x ^ b.x } }
              << { A { x: a.x << b.x } }
              >> { A { x: a.x >> b.x } });

    ops_impl!(|a: &mut A, b: &A| -> A,
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

    ops_impl!(|a: &mut A, b: &B| -> A,
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

    ops_impl!(|a: &A| -> A,
              neg { A { x: -a.x } }
              not { A { x: -a.x } });

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

        assert_eq!(-&a1, A { x: -16 });
        assert_eq!(!&a1, A { x: -16 });
    }

    #[test]
    fn ops_mut() {
        let mut val = A { x: 16 };
        let a = A { x: 2 };
        let b = B { x: 2 };

        val += &a;

        assert_eq!(val, A { x: 18 });

        val -= &a;

        assert_eq!(val, A { x: 16 });

        val *= &a;

        assert_eq!(val, A { x: 32 });

        val /= &a;

        assert_eq!(val, A { x: 16 });

        val += &b;

        assert_eq!(val, A { x: 18 });

        val -= &b;

        assert_eq!(val, A { x: 16 });

        val *= &b;

        assert_eq!(val, A { x: 32 });

        val /= &b;

        assert_eq!(val, A { x: 16 });
    }
}

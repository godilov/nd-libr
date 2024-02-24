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
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<&$typer> for $typel {
            #[allow(clippy::redundant_closure_call)]
            fn $op_name(&mut self, rhs: &$typer) { (|$lhs: &mut $typel, $rhs: &$typer| $fn)(self, rhs); }
        }
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<$typer> for $typel {
            #[allow(clippy::redundant_closure_call)]
            fn $op_name(&mut self, rhs: $typer) { (|$lhs: &mut $typel, $rhs: $typer| $fn)(self, rhs); }
        }
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<&$typer> for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$typer) -> Self::Output { (|$lhs: &$typel, $rhs: &$typer| $fn)(self, rhs) }
        }
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<$typer> for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $typer) -> Self::Output { (|$lhs: &$typel, $rhs: $typer| $fn)(self, rhs) }
        }
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<&$typer> for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: &$typer) -> Self::Output { (|$lhs: $typel, $rhs: &$typer| $fn)(self, rhs) }
        }
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait<$typer> for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self, rhs: $typer) -> Self::Output { (|$lhs: $typel, $rhs: $typer| $fn)(self, rhs) }
        }
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait for &$typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self) -> Self::Output { (|$lhs: &$typel| $fn)(self) }
        }
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        impl $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? std::ops::$op_trait for $typel {
            type Output = $type;

            #[allow(clippy::redundant_closure_call)]
            fn $op_name(self) -> Self::Output { (|$lhs: $typel| $fn)(self) }
        }
    };
}

#[macro_export]
macro_rules! ops_impl_std_complete {
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &mut $typel, $rhs: &$typer| $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &mut $typel, $rhs: $typer| $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &mut $typel, $rhs: $typer| $fn);
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: $typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: &$typer| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel| -> $type $fn);
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel| -> $type $fn);
    };
    ($op_trait:ident, $op_name:ident,
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_std!($op_trait, $op_name,
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel| -> $type $fn);
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
    ($op:tt
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path | $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &mut $typel, $rhs: &$typer| $fn);
    };
    ($op:tt
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path | $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &mut $typel, $rhs: $typer| $fn);
    };

    ($op:tt
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
    };
    ($op:tt
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel, $rhs: $typer| -> $type $fn);
    };
    ($op:tt
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: &$typer| -> $type $fn);
    };
    ($op:tt
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel, $rhs: $typer| -> $type $fn);
    };

    ($op:ident
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: &$typel| -> $type $fn);
    };
    ($op:ident
     $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path $fn:block) => {
        $crate::ops_impl_raw!($op
                              $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                              |$lhs: $typel| -> $type $fn);
    };

    ($op:tt $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |) => {};
    ($op:tt $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |) => {};

    ($op:tt $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path) => {};
    ($op:tt $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path) => {};
    ($op:tt $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path) => {};
    ($op:tt $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path) => {};

    ($op:ident $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : &$typel:path | -> $type:path) => {};
    ($op:ident $(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)? | $lhs:ident : $typel:path | -> $type:path) => {};

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : &$typer:path |,
     $(+= $add:block -= $sub:block *= $mul:block /= $div:block)? $(%= $rem:block)?
     $(|= $or:block &= $and:block ^= $xor:block)? $(<<= $shl:block >>= $shr:block)?) => {
        $crate::ops_impl!(+= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($add)?);
        $crate::ops_impl!(-= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($sub)?);
        $crate::ops_impl!(*= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($mul)?);
        $crate::ops_impl!(/= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($div)?);
        $crate::ops_impl!(%= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($rem)?);
        $crate::ops_impl!(|= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($or)?);
        $crate::ops_impl!(&= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($and)?);
        $crate::ops_impl!(^= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($xor)?);
        $crate::ops_impl!(<<= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($shl)?);
        $crate::ops_impl!(>>= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: &$typer| $($shr)?);

        $crate::if_block!($($add)?
            impl $crate::ops::OpsAssign<$typer> for $typel {}
            impl $crate::ops::OpsAssign<&$typer> for $typel {}
            impl $crate::ops::OpsAssignAll<'_, $typer> for $typel {}
        );

        $crate::if_block!($($or)?
            impl $crate::ops::OpsBitAssign<$typer> for $typel {}
            impl $crate::ops::OpsBitAssign<&$typer> for $typel {}
            impl $crate::ops::OpsBitAssignAll<'_, $typer> for $typel {}
        );

        $crate::if_block!($($shl)?
            impl $crate::ops::OpsShiftAssign<$typer> for $typel {}
            impl $crate::ops::OpsShiftAssign<&$typer> for $typel {}
            impl $crate::ops::OpsShiftAssignAll<'_, $typer> for $typel {}
        );
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &mut $typel:path, $rhs:ident : $typer:path |,
     $(+= $add:block -= $sub:block *= $mul:block /= $div:block)? $(%= $rem:block)?
     $(|= $or:block &= $and:block ^= $xor:block)? $(<<= $shl:block >>= $shr:block)?) => {
        $crate::ops_impl!(+= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($add)?);
        $crate::ops_impl!(-= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($sub)?);
        $crate::ops_impl!(*= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($mul)?);
        $crate::ops_impl!(/= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($div)?);
        $crate::ops_impl!(%= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($rem)?);
        $crate::ops_impl!(|= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($or)?);
        $crate::ops_impl!(&= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($and)?);
        $crate::ops_impl!(^= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($xor)?);
        $crate::ops_impl!(<<= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($shl)?);
        $crate::ops_impl!(>>= $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &mut $typel, $rhs: $typer| $($shr)?);

        $crate::if_block!($($add)?
            impl $crate::ops::OpsAssign<$typer> for $typel {}
        );

        $crate::if_block!($($or)?
            impl $crate::ops::OpsBitAssign<$typer> for $typel {}
        );

        $crate::if_block!($($shl)?
            impl $crate::ops::OpsShiftAssign<$typer> for $typel {}
        );
    };

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(+ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($add)?);
        $crate::ops_impl!(- $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($sub)?);
        $crate::ops_impl!(* $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($mul)?);
        $crate::ops_impl!(/ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($div)?);
        $crate::ops_impl!(% $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($rem)?);
        $crate::ops_impl!(| $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($or)?);
        $crate::ops_impl!(& $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($and)?);
        $crate::ops_impl!(^ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($xor)?);
        $crate::ops_impl!(<< $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($shl)?);
        $crate::ops_impl!(>> $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $($shr)?);

        $crate::if_block!($($add)?
            impl $crate::ops::Ops<$typer> for $typel { type Output = $type; }
            impl $crate::ops::Ops<$typer> for &$typel { type Output = $type; }
            impl $crate::ops::Ops<&$typer> for $typel { type Output = $type; }
            impl $crate::ops::Ops<&$typer> for &$typel { type Output = $type; }

            impl $crate::ops::OpsAll<'_, $typer> for $typel {}
        );

        $crate::if_block!($($or)?
            impl $crate::ops::OpsBit<$typer> for $typel { type Output = $type; }
            impl $crate::ops::OpsBit<$typer> for &$typel { type Output = $type; }
            impl $crate::ops::OpsBit<&$typer> for $typel { type Output = $type; }
            impl $crate::ops::OpsBit<&$typer> for &$typel { type Output = $type; }

            impl $crate::ops::OpsBitAll<'_, $typer> for $typel {}
        );

        $crate::if_block!($($shl)?
            impl $crate::ops::OpsShift<$typer> for $typel { type Output = $type; }
            impl $crate::ops::OpsShift<$typer> for &$typel { type Output = $type; }
            impl $crate::ops::OpsShift<&$typer> for $typel { type Output = $type; }
            impl $crate::ops::OpsShift<&$typer> for &$typel { type Output = $type; }

            impl $crate::ops::OpsShiftAll<'_, $typer> for $typel {}
        );
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(+ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($add)?);
        $crate::ops_impl!(- $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($sub)?);
        $crate::ops_impl!(* $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($mul)?);
        $crate::ops_impl!(/ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($div)?);
        $crate::ops_impl!(% $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($rem)?);
        $crate::ops_impl!(| $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($or)?);
        $crate::ops_impl!(& $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($and)?);
        $crate::ops_impl!(^ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($xor)?);
        $crate::ops_impl!(<< $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($shl)?);
        $crate::ops_impl!(>> $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: $typer| -> $type $($shr)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | -> $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(+ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($add)?);
        $crate::ops_impl!(- $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($sub)?);
        $crate::ops_impl!(* $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($mul)?);
        $crate::ops_impl!(/ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($div)?);
        $crate::ops_impl!(% $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($rem)?);
        $crate::ops_impl!(| $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($or)?);
        $crate::ops_impl!(& $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($and)?);
        $crate::ops_impl!(^ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($xor)?);
        $crate::ops_impl!(<< $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($shl)?);
        $crate::ops_impl!(>> $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: &$typer| -> $type $($shr)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | -> $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!(+ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($add)?);
        $crate::ops_impl!(- $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($sub)?);
        $crate::ops_impl!(* $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($mul)?);
        $crate::ops_impl!(/ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($div)?);
        $crate::ops_impl!(% $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($rem)?);
        $crate::ops_impl!(| $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($or)?);
        $crate::ops_impl!(& $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($and)?);
        $crate::ops_impl!(^ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($xor)?);
        $crate::ops_impl!(<< $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($shl)?);
        $crate::ops_impl!(>> $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel, $rhs: $typer| -> $type $($shr)?);

        $crate::if_block!($($add)?
            impl $crate::ops::Ops<$typer> for $typel { type Output = $type; }
        );

        $crate::if_block!($($or)?
            impl $crate::ops::OpsBit<$typer> for $typel { type Output = $type; }
        );

        $crate::if_block!($($shl)?
            impl $crate::ops::OpsShift<$typer> for $typel { type Output = $type; }
        );
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | => $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$lhs: &$typel, $rhs: &$typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$rhs: &$typer, $lhs: &$typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path, $rhs:ident : $typer:path | => $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$lhs: &$typel, $rhs: $typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$rhs: &$typer, $lhs: $typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : &$typer:path | => $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$lhs: $typel, $rhs: &$typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$rhs: $typer, $lhs: &$typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path, $rhs:ident : $typer:path | => $type:path,
     $(+ $add:block - $sub:block * $mul:block / $div:block)? $(% $rem:block)?
     $(| $or:block & $and:block ^ $xor:block)? $(<< $shl:block >> $shr:block)?) => {
        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$lhs: $typel, $rhs: $typer| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);

        $crate::ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                          |$rhs: $typer, $lhs: $typel| -> $type,
                          $(+ $add - $sub * $mul / $div)? $(% $rem)?
                          $(| $or & $and ^ $xor)? $(<< $shl >> $shr)?);
    };

    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : &$typel:path | -> $type:path, $(neg $neg:block)? $(not $not:block)?) => {
        $crate::ops_impl!(neg $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $($neg)?);
        $crate::ops_impl!(not $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel| -> $type $($not)?);
    };
    ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
     | $lhs:ident : $typel:path | -> $type:path, $(neg $neg:block)? $(not $not:block)?) => {
        $crate::ops_impl!(neg $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $($neg)?);
        $crate::ops_impl!(not $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: $typel| -> $type $($not)?);
    };
}

#[cfg(test)]
mod tests {
    use crate::{num::Number, ops_impl};

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
        ($type1:ident, $type2:ident, $t:ident, $trait:ident $(,)?) => {
            #[derive(Debug, PartialEq, Eq)]
            struct $type1<$t: $trait> {
                x: $t,
            }

            #[derive(Debug, PartialEq, Eq)]
            struct $type2<$t: $trait> {
                x: $t,
            }
        };
    }

    macro_rules! ops_struct_impl {
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&mut $type1:path, &$type2:path|) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
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
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: &$type1| -> $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: &$type2| => $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&$type1:path, $type2:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: $type1| -> $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1, b: $type2| => $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |$type1:path, &$type2:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: &$type1| -> $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: &$type2| => $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |$type1:path, $type2:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: $type1| -> $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });

            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1, b: $type2| => $type,
                    + { $type { x: a.x + b.x } }
                    - { $type { x: a.x - b.x } }
                    * { $type { x: a.x * b.x } }
                    / { $type { x: a.x / b.x } }
                    % { $type { x: a.x % b.x } }
                    | { $type { x: a.x | b.x } }
                    & { $type { x: a.x & b.x } }
                    ^ { $type { x: a.x ^ b.x } }
                    << { $type { x: a.x << b.x } }
                    >> { $type { x: a.x >> b.x } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |&$type1:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: &$type1| -> $type,
                    neg { $type { x: -a.x } }
                    not { $type { x: -a.x } });
        };
        ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
         |$type1:path| -> $type:path) => {
            ops_impl!($(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)?
                |a: $type1| -> $type,
                    neg { $type { x: -a.x } }
                    not { $type { x: -a.x } });
        };
    }

    ops_struct_def!(A, B);
    ops_struct_def!(A1, B1);
    ops_struct_def!(A2, B2);
    ops_struct_def!(A3, B3);

    ops_struct_def!(X, Y, N, Number);
    ops_struct_def!(X1, Y1, N, Number);
    ops_struct_def!(X2, Y2, N, Number);
    ops_struct_def!(X3, Y3, N, Number);

    ops_struct_impl!(|&mut A, &B|);
    ops_struct_impl!(|&mut A1, B1|);

    ops_struct_impl!(|&A, &B| -> A);
    ops_struct_impl!(|&A1, B1| -> A1);
    ops_struct_impl!(|A2, &B2| -> A2);
    ops_struct_impl!(|A3, B3| -> A3);

    ops_struct_impl!(|&A| -> A);
    ops_struct_impl!(|A1| -> A1);

    // TODO: repair ops_impl!
    // Success // ops_impl_std!(Add, add, <N: Number + std::convert::From<<N as std::ops::Add<N>>::Output>> |a: &X<N>, b: &Y<N>| -> X<N> { X::<N> { x: (a.x + b.x).into() } });
    // Success // ops_impl_std_complete!(Add, add, <N: Number> |a: &X<N>, b: &X<N>| -> X<N> { X::<N> { x: N::default() } });
    // Success // ops_impl_raw!(+ <N: Number> |a: &X<N>, b: &X<N>| -> X<N> { X::<N> { x: N::default() } });
    // Success // ops_impl!(+ <N: Number> |a: &X<N>, b: &X<N>| -> X<N> { X::<N> { x: N::default() } });

    // macro_rules! ops_impl_wrap {
    //     ($(< $($(($const:ident))? $t:ident $(: $trait:ident $(+ $trait_seq:path)*)? $(,)?)+ >)?
    //      | $lhs:ident : &$typel:path, $rhs:ident : &$typer:path | -> $type:path $fn:block) => {
    //         ops_impl!(+ $(<$($($const)? $t $(: $trait $(+ $trait_seq)*)? ,)+>)? |$lhs: &$typel, $rhs: &$typer| -> $type $fn);
    //     };
    // }

    // ops_impl_wrap!(<N: Number> |a: &X<N>, b: &X<N>| -> X<N> { X::<N> { x: N::default() } });

    // TODO: repair ops_impl! - this one
    // ops_impl!(<N: Number> |a: &X<N>, b: &Y<N>| -> X<N>,
    //           + { X::<N> { x: N::deafult() } }
    //           - { X::<N> { x: N::deafult() } }
    //           * { X::<N> { x: N::deafult() } }
    //           / { X::<N> { x: N::deafult() } });

    // ops_struct_impl!(<N: Number> |&X<N>, &Y<N>| -> X<N>);

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

    fn a_fn(x: i64) -> A { A { x } }
    fn b_fn(x: i64) -> B { B { x } }

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
    fn ops_mut() {
        let val1 = 32i64;
        let val2 = 2i64;

        assert_ops_mut!(a_fn(val1), &a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(a_fn(val1), &b_fn(val2), a_fn, val1, val2);

        assert_ops_mut!(a_fn(val1), a_fn(val2), a_fn, val1, val2);
        assert_ops_mut!(a_fn(val1), b_fn(val2), a_fn, val1, val2);
    }
}

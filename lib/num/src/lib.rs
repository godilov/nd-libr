#![doc = include_str!("../README.md")]

use std::{cmp::Ordering, fmt::Debug, marker::PhantomData};

use ndext::ops::*;

pub mod arch;
pub mod long;
pub mod prime;

macro_rules! num_impl {
    (@signed [$($primitive:ty),+] $(,)?) => {
        $(num_impl!(@impl $primitive);)+
        $(num_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+] $(,)?) => {
        $(num_impl!(@impl $primitive);)+
        $(num_impl!(@unsigned $primitive);)+
    };
    (@impl $primitive:ty $(,)?) => {
        impl BytesExt for $primitive {
            fn read(&self, offset: Offset) -> u64 {
                match offset {
                    Offset::Left(val) => self.unbounded_shr(val as u32) as u64,
                    Offset::Right(val) => self.unbounded_shr(<$primitive>::BITS.saturating_sub(val as u32)) as u64,
                }
            }

            fn write_bitor(&mut self, mask: u64, offset: Offset) -> &mut Self {
                match offset {
                    Offset::Left(val) => *self |= (mask as $primitive).unbounded_shl(val as u32),
                    Offset::Right(val) => *self |= (mask as $primitive).unbounded_shl(<$primitive>::BITS.saturating_sub(val as u32)),
                }

                self
            }

            fn write_bitand(&mut self, mask: u64, offset: Offset) -> &mut Self {
                use std::ops::Not;

                match offset {
                    Offset::Left(val) => *self &= (mask.not() as $primitive).unbounded_shl(val as u32).not(),
                    Offset::Right(val) => *self &= (mask.not() as $primitive).unbounded_shl(<$primitive>::BITS.saturating_sub(val as u32)).not(),
                }

                self
            }

            fn write_bitxor(&mut self, mask: u64, offset: Offset) -> &mut Self {
                match offset {
                    Offset::Left(val) => *self ^= (mask as $primitive).unbounded_shl(val as u32),
                    Offset::Right(val) => *self ^= (mask as $primitive).unbounded_shl(<$primitive>::BITS.saturating_sub(val as u32)),
                }

                self
            }
        }

        impl NumFn for $primitive {}

        impl NumFnChecked for $primitive {}

        impl NumExt for $primitive {}

        impl Num for $primitive {}

        impl Zero for $primitive {
            const ZERO: Self = 0;
        }

        impl One for $primitive {
            const ONE: Self = 1;
        }

        impl Min for $primitive {
            const MIN: Self = Self::MIN;
        }

        impl Max for $primitive {
            const MAX: Self = Self::MAX;
        }

        impl Binary for $primitive {
            const BITS: usize = <$primitive>::BITS as usize;
            const BYTES: usize = <$primitive>::BITS as usize / 8;
        }
    };
    (@signed $primitive:ty $(,)?) => {
        impl NumSigned for $primitive {}
    };
    (@unsigned $primitive:ty $(,)?) => {
        impl NumUnsigned for $primitive {
            fn order(&self) -> usize {
                self.ilog2() as usize
            }

            fn log(&self) -> Self {
                self.ilog2() as $primitive
            }

            fn sqrt(&self) -> Self {
                self.isqrt() as $primitive
            }
        }
    };
}

#[cfg(feature = "const-time")]
macro_rules! num_ct_impl {
    (@signed [$($signed:ty:$unsigned:ty),+ $(,)?]) => {
        $(num_ct_impl!(@signed $signed:$unsigned);)+
    };
    (@unsigned [$($unsigned:ty),+ $(,)?]) => {
        $(num_ct_impl!(@unsigned $unsigned);)+
    };
    (@signed $signed:ty:$unsigned:ty $(,)?) => {
        impl EqCt for $signed {
            fn eq_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let diff = lhs ^ rhs;
                let diff = (diff | diff.wrapping_neg()) >> (<$signed>::BITS - 1);

                diff.wrapping_sub(1) as MaskCt
            }
        }

        impl LtCt for $signed {
            fn lt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let lt = (lhs.wrapping_sub(rhs) >> (<$unsigned>::BITS - 1)) as u8;

                let lhs_neg = (lhs >> (<$unsigned>::BITS - 1)) as u8;
                let rhs_neg = (rhs >> (<$unsigned>::BITS - 1)) as u8;

                let xor = lhs_neg ^ rhs_neg;
                let res = xor & lhs_neg | !xor & lt;

                MaskCt::ZERO.wrapping_sub(res)
            }
        }

        impl GtCt for $signed {
            fn gt_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let gt = (rhs.wrapping_sub(lhs) >> (<$unsigned>::BITS - 1)) as u8;

                let lhs_neg = (lhs >> (<$unsigned>::BITS - 1)) as u8;
                let rhs_neg = (rhs >> (<$unsigned>::BITS - 1)) as u8;

                let xor = lhs_neg ^ rhs_neg;
                let res = xor & rhs_neg | !xor & gt;

                MaskCt::ZERO.wrapping_sub(res)
            }
        }

        impl LeCt for $signed {}
        impl GeCt for $signed {}
        impl CmpCt for $signed {}
        impl MinCt for $signed {}
        impl MaxCt for $signed {}

        num_ct_impl!(@select $signed);
    };
    (@unsigned $unsigned:ty $(,)?) => {
        impl EqCt for $unsigned {
            fn eq_ct(&self, other: &Self) -> MaskCt {
                let lhs = *self as $unsigned;
                let rhs = *other as $unsigned;

                let diff = lhs ^ rhs;
                let diff = (diff | diff.wrapping_neg()) >> (<$unsigned>::BITS - 1);

                diff.wrapping_sub(1) as MaskCt
            }
        }

        impl LtCt for $unsigned {
            fn lt_ct(&self, other: &Self) -> MaskCt {
                let lhs = self;
                let rhs = other;

                let neg = (lhs.wrapping_sub(*rhs) >> (<$unsigned>::BITS - 1)) as MaskCt;

                MaskCt::ZERO.wrapping_sub(neg)
            }
        }

        impl GtCt for $unsigned {
            fn gt_ct(&self, other: &Self) -> MaskCt {
                let lhs = self;
                let rhs = other;

                let neg = (rhs.wrapping_sub(*lhs) >> (<$unsigned>::BITS - 1)) as MaskCt;

                MaskCt::ZERO.wrapping_sub(neg)
            }
        }

        impl LeCt for $unsigned {}
        impl GeCt for $unsigned {}
        impl CmpCt for $unsigned {}
        impl MinCt for $unsigned {}
        impl MaxCt for $unsigned {}

        num_ct_impl!(@select $unsigned);
    };
    (@select $primitive:ty $(,)?) => {
        impl SelectCt for $primitive {
            fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self {
                let lhs_mask = <$primitive>::from_ne_bytes([mask; (<$primitive>::BITS / 8) as usize]);
                let rhs_mask = <$primitive>::from_ne_bytes([!mask; (<$primitive>::BITS / 8) as usize]);

                lhs & lhs_mask | rhs & rhs_mask
            }
        }
    };
}

macro_rules! sign_from {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(sign_from!(@unsigned $primitive);)+
    };
    (@signed $primitive:ty $(,)?) => {
        impl From<$primitive> for Sign {
            fn from(value: $primitive) -> Self {
                match value.cmp(&0) {
                    Ordering::Less => Sign::NEG,
                    Ordering::Equal => Sign::ZERO,
                    Ordering::Greater => Sign::POS,
                }
            }
        }
    };
    (@unsigned $primitive:ty $(,)?) => {
        impl From<$primitive> for Sign {
            fn from(value: $primitive) -> Self {
                match value {
                    0 => Sign::ZERO,
                    _ => Sign::POS,
                }
            }
        }
    };
}

/// Number with Strict operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: BytesExt)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumFnChecked)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: Num)]
pub struct Strict<N>(pub N);

/// Number with Wrapping operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: BytesExt)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumFnChecked)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: Num)]
pub struct Wrapping<N>(pub N);

/// Number with Saturating operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: BytesExt)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumFnChecked)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: Num)]
pub struct Saturating<N>(pub N);

/// Number with Unbounded operations semantics.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: BytesExt)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumFnChecked)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: Num)]
pub struct Unbounded<N>(pub N);

/// Number with specified binary width.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: BytesExt)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumFnChecked)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Width<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize>(pub N);

/// Number with specified modulus.
///
/// Implements (conditionally) all standard Rust traits and operations if underlying type supports it.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::std(self.0 with N)]
#[ndfwd::cmp(self.0 with N)]
#[ndfwd::fmt(self.0 with N)]
#[ndfwd::def(self.0 with N: BytesExt)]
#[ndfwd::def(self.0 with N: NumFn)]
#[ndfwd::def(self.0 with N: NumFnChecked)]
#[ndfwd::def(self.0 with N: NumExt)]
#[ndfwd::def(self.0 with N: Num)]
#[ndfwd::def(self.0 with N: NumUnsigned)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Modular<N: Num + NumExt + NumUnsigned, M: Modulus<N>>(pub N, pub PhantomData<M>);

/// Number sign.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    /// Zero number variant.
    #[default]
    ZERO = 0,

    /// Negative number variant.
    NEG = -1,

    /// Positive number variant.
    POS = 1,
}

/// Offset for reading/writing binary mask.
///
/// - `Offset::Left(val)` specifies `val`-bits offset from `0`.
/// - `Offset::Right(val)` specifies `val`-bits offset from `N = size_of::<Self>()`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Offset {
    /// Offset in left direction of usize bits.
    Left(usize),
    /// Offset in right direction of usize bits.
    Right(usize),
}

#[cfg(feature = "const-time")]
type MaskCt = u8;

#[cfg(feature = "const-time")]
type SignCt = i8;

/// Bytes extensions.
///
/// Allows reading/writing in raw binary representation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait BytesExt: Sized {
    /// Reads 64-bits of underlying value at specified Offset in bits.
    fn read(&self, offset: Offset) -> u64;

    /// Writes 64-bits as bitor operation to underlying value at specified Offset in bits.
    #[ndfwd::as_self]
    fn write_bitor(&mut self, mask: u64, offset: Offset) -> &mut Self;

    /// Writes 64-bits as bitand operation to underlying value at specified Offset in bits.
    #[ndfwd::as_self]
    fn write_bitand(&mut self, mask: u64, offset: Offset) -> &mut Self;

    /// Writes 64-bits as bitxor operation to underlying value at specified Offset in bits.
    #[ndfwd::as_self]
    fn write_bitxor(&mut self, mask: u64, offset: Offset) -> &mut Self;

    /// Writes 64-bits as bitor operation to underlying value at specified Offset in bits.
    #[ndfwd::as_into]
    fn into_bitor(mut self, mask: u64, offset: Offset) -> Self {
        self.write_bitor(mask, offset);
        self
    }

    /// Writes 64-bits as bitand operation to underlying value at specified Offset in bits.
    #[ndfwd::as_into]
    fn into_bitand(mut self, mask: u64, offset: Offset) -> Self {
        self.write_bitand(mask, offset);
        self
    }

    /// Writes 64-bits as bitxor operation to underlying value at specified Offset in bits.
    #[ndfwd::as_into]
    fn into_bitxor(mut self, mask: u64, offset: Offset) -> Self {
        self.write_bitxor(mask, offset);
        self
    }
}

/// Numbers functions with default semantics.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumFn:
    Sized + Default + Clone + PartialEq + Eq + PartialOrd + Ord + NdOps<All = Self> + NdOpsAssign + ZeroFn + OneFn
{
    /// Calculates Greatest Common Divisor of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NumFnChecked`] for checked semantics.
    #[ndfwd::as_into]
    fn gcd(mut lhs: Self, mut rhs: Self) -> Self {
        let zero = Self::zero();

        while rhs != zero {
            let rem = Self::nd_rem(&lhs, &rhs);

            lhs = rhs;
            rhs = rem;
        }

        lhs
    }

    /// Calculates Greatest Common Divisor Extended of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NumFnChecked`] for checked semantics.
    #[ndfwd::as_expr(|(r, x, y)| (Self::from(r), Self::from(x), Self::from(y)))]
    fn gcde(lhs: Self, rhs: Self) -> (Self, Self, Self) {
        let zero = Self::zero();
        let one = Self::one();

        let mut r0 = lhs;
        let mut r1 = rhs;
        let mut x0 = one.clone();
        let mut x1 = zero.clone();
        let mut y0 = zero.clone();
        let mut y1 = one.clone();

        while r1 != zero {
            let div = Self::nd_div(&r0, &r1);

            let r = Self::nd_sub(&r0, &Self::nd_mul(&div, &r1));
            let x = Self::nd_sub(&x0, &Self::nd_mul(&div, &x1));
            let y = Self::nd_sub(&y0, &Self::nd_mul(&div, &y1));

            r0 = r1;
            r1 = r;

            x0 = x1;
            x1 = x;

            y0 = y1;
            y1 = y;
        }

        (r0, x0, y0)
    }

    /// Calculates Least Common Multiple of two numbers.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    ///
    /// See [`NumFnChecked`] for checked semantics.
    #[ndfwd::as_into]
    fn lcm(lhs: Self, rhs: Self) -> Self {
        let val = Self::gcd(lhs.clone(), rhs.clone());
        let val = Self::nd_div(&lhs, &val);

        Self::nd_mul(&val, &rhs)
    }
}

/// Numbers functions with checked semantics.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumFnChecked: NumFn + NdOpsChecked<All = Self> {
    /// Calculates Greatest Common Divisor of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[ndfwd::as_map(Self::from)]
    fn gcd_checked(mut lhs: Self, mut rhs: Self) -> Option<Self> {
        let zero = Self::zero();

        while rhs != zero {
            let rem = Self::nd_rem_checked(&lhs, &rhs)?;

            lhs = rhs;
            rhs = rem;
        }

        Some(lhs)
    }

    /// Calculates Greatest Common Divisor Extended of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[ndfwd::as_map(|(r, x, y)| (Self::from(r), Self::from(x), Self::from(y)))]
    fn gcde_checked(lhs: Self, rhs: Self) -> Option<(Self, Self, Self)> {
        let zero = Self::zero();
        let one = Self::one();

        let mut r0 = lhs;
        let mut r1 = rhs;
        let mut x0 = one.clone();
        let mut x1 = zero.clone();
        let mut y0 = zero.clone();
        let mut y1 = one.clone();

        while r1 != zero {
            let div = Self::nd_div(&r0, &r1);

            let r = Self::nd_sub_checked(&r0, &Self::nd_mul_checked(&div, &r1)?)?;
            let x = Self::nd_sub_checked(&x0, &Self::nd_mul_checked(&div, &x1)?)?;
            let y = Self::nd_sub_checked(&y0, &Self::nd_mul_checked(&div, &y1)?)?;

            r0 = r1;
            r1 = r;

            x0 = x1;
            x1 = x;

            y0 = y1;
            y1 = y;
        }

        Some((r0, x0, y0))
    }

    /// Calculates Least Common Multiple of two numbers.
    ///
    /// # Returns
    ///
    /// - `Some` when value exists.
    /// - `None` when non-checked could panic.
    #[ndfwd::as_map(Self::from)]
    fn lcm_checked(lhs: Self, rhs: Self) -> Option<Self> {
        let val = Self::gcd_checked(lhs.clone(), rhs.clone())?;
        let val = Self::nd_div_checked(&lhs, &val)?;

        Self::nd_mul_checked(&val, &rhs)
    }
}

/// Numbers extensions.
///
/// Exposes additional functions on top of [`NumFn`] and [`BytesExt`].
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait NumExt: NumFn + BytesExt {
    /// Writes odd number.
    #[ndfwd::as_self]
    fn write_odd(&mut self) -> &mut Self {
        self.write_bitor(1, Offset::Left(0));
        self
    }

    /// Writes even number.
    #[ndfwd::as_self]
    fn write_even(&mut self) -> &mut Self {
        self.write_bitand(u64::MAX - 1, Offset::Left(0));
        self
    }

    /// Alters odd/even number.
    #[ndfwd::as_self]
    fn write_alt(&mut self) -> &mut Self {
        self.write_bitxor(1, Offset::Left(0));
        self
    }

    /// Writes odd number.
    #[ndfwd::as_into]
    fn into_odd(mut self) -> Self {
        self.write_odd();
        self
    }

    /// Writes even number.
    #[ndfwd::as_into]
    fn into_even(mut self) -> Self {
        self.write_even();
        self
    }

    /// Alters odd/even number.
    #[ndfwd::as_into]
    fn into_alt(mut self) -> Self {
        self.write_alt();
        self
    }

    /// Checks number is odd.
    fn is_odd(&self) -> bool {
        self.read(Offset::Left(0)) & 1 != 0
    }

    /// Checks number is even.
    fn is_even(&self) -> bool {
        self.read(Offset::Left(0)) & 1 == 0
    }

    /// Creates random number.
    ///
    /// Order represents position of the most significant bit.
    ///
    /// # Panics
    ///
    /// - When `order` is zero.
    /// - When `BytesExt` implementation panics.
    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn rand<Rng: rand::Rng>(order: usize, rng: &mut Rng) -> Self {
        let shift = order - 1;
        let div = shift / 64;
        let rem = shift % 64;
        let bit = 1 << rem;

        let mut res = Self::zero();

        res.write_bitor(bit | (bit - 1) & rng.next_u64(), Offset::Left(div * 64));

        for idx in 0..div {
            res.write_bitor(rng.next_u64(), Offset::Left(idx * 64));
        }

        res
    }

    /// Calculates `self ^ exp`.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    #[ndfwd::as_into]
    fn pow(self, mut exp: Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            if exp.is_odd() {
                Self::nd_mul_assign(&mut res, &acc);
            }

            let val = acc.clone();

            Self::nd_mul_assign(&mut acc, &val);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }

    /// Calculates `self ^ exp % rem`.
    ///
    /// # Panics
    ///
    /// May panic if [`NdOps`] or [`NdOpsAssign`] implementation panics.
    #[ndfwd::as_into]
    fn powrem(self, mut exp: Self, rem: &Self) -> Self {
        let zero = Self::zero();
        let one = Self::one();

        let mut acc = self;
        let mut res = one;

        while exp != zero {
            if exp.is_odd() {
                Self::nd_mul_assign(&mut res, &acc);
                Self::nd_rem_assign(&mut res, rem);
            }

            let val = acc.clone();

            Self::nd_mul_assign(&mut acc, &val);
            Self::nd_rem_assign(&mut acc, rem);
            Self::nd_shr_assign(&mut exp, 1);
        }

        res
    }
}

/// Number with static allocation.
#[ndfwd::decl]
pub trait Num: NumFn + Zero + One + Copy {}

/// Number with dynamic allocation.
#[ndfwd::decl]
pub trait NumDyn: NumFn {}

/// Number with sign.
#[ndfwd::decl]
pub trait NumSigned: NumFn + From<i8> {}

/// Number without sign.
#[ndfwd::decl]
pub trait NumUnsigned: NumFn + From<u8> {
    /// Order of number.
    ///
    /// Represents position of the most significant bit.
    fn order(&self) -> usize;

    /// Logarithm (base 2) of number.
    #[ndfwd::as_into]
    fn log(&self) -> Self;

    /// Square root of number.
    #[ndfwd::as_into]
    fn sqrt(&self) -> Self;
}

/// Modulus for [`Modular`] numbers.
pub trait Modulus<N: Num>: Default + Debug + Clone + Copy {
    /// Modulus for arithmetics.
    const MOD: N;
}

/// Zero with static allocation.
pub trait Zero {
    /// Zero value.
    const ZERO: Self;
}

/// One with static allocation.
pub trait One {
    /// One value.
    const ONE: Self;
}

/// Minimum with static allocation.
pub trait Min {
    /// Minimum value.
    const MIN: Self;
}

/// Maximum with static allocation.
pub trait Max {
    /// Maximum value.
    const MAX: Self;
}

/// Numbers representable in binary statically.
#[ndfwd::decl]
pub trait Binary {
    /// Allocated static size in bits.
    const BITS: usize;

    /// Allocated static size in bytes.
    const BYTES: usize;
}

/// Zero with dynamic allocation.
#[ndfwd::decl]
pub trait ZeroFn {
    /// Returns zero value.
    #[ndfwd::as_into]
    fn zero() -> Self;
}

/// One with dynamic allocation.
#[ndfwd::decl]
pub trait OneFn {
    /// Returns one value.
    #[ndfwd::as_into]
    fn one() -> Self;
}

/// Minimum with dynamic allocation.
#[ndfwd::decl]
pub trait MinFn {
    /// Returns minimum value.
    #[ndfwd::as_into]
    fn min() -> Self;
}

/// Maximum with dynamic allocation.
#[ndfwd::decl]
pub trait MaxFn {
    /// Returns maximum value.
    #[ndfwd::as_into]
    fn max() -> Self;
}

/// Numbers representable in binary dynamically.
#[ndfwd::decl]
pub trait BinaryFn {
    /// Allocated dynamic size in bits.
    fn bits(&self) -> usize;

    /// Allocated dynamic size in bytes.
    fn bytes(&self) -> usize;
}

/// Const-time equality comparison.
#[cfg(feature = "const-time")]
pub trait EqCt {
    /// Const-time equality function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs != rhs`.
    /// - `MaskCt::MAX` => `lhs == rhs`.
    fn eq_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time less-then comparison.
#[cfg(feature = "const-time")]
pub trait LtCt {
    /// Const-time less-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs >= rhs`.
    /// - `MaskCt::MAX` => `lhs < rhs`.
    fn lt_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time greater-then comparison.
#[cfg(feature = "const-time")]
pub trait GtCt {
    /// Const-time greater-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs <= rhs`.
    /// - `MaskCt::MAX` => `lhs > rhs`.
    fn gt_ct(&self, other: &Self) -> MaskCt;
}

/// Const-time less-or-equal-then comparison.
#[cfg(feature = "const-time")]
pub trait LeCt {
    /// Const-time less-or-equal-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs > rhs`.
    /// - `MaskCt::MAX` => `lhs <= rhs`.
    fn le_ct(&self, other: &Self) -> MaskCt
    where
        Self: GtCt,
    {
        !self.gt_ct(other)
    }
}

/// Const-time greater-or-equal-then comparison.
#[cfg(feature = "const-time")]
pub trait GeCt {
    /// Const-time greater-or-equal-then function.
    ///
    /// # Returns
    ///
    /// - `MaskCt::MIN` => `lhs < rhs`.
    /// - `MaskCt::MAX` => `lhs >= rhs`.
    fn ge_ct(&self, other: &Self) -> MaskCt
    where
        Self: LtCt,
    {
        !self.lt_ct(other)
    }
}

/// Const-time comparison.
#[cfg(feature = "const-time")]
pub trait CmpCt {
    /// Const-time comparison function.
    ///
    /// # Returns
    ///
    /// - `-1` => `lhs < rhs`
    /// - `0` => `lhs == rhs`.
    /// - `1` => `lhs > rhs`
    fn cmp_ct(&self, other: &Self) -> SignCt
    where
        Self: EqCt + LtCt + GtCt,
    {
        let lt = self.lt_ct(other) as SignCt;
        let gt = self.gt_ct(other) as SignCt;

        lt | gt & 1
    }
}

/// Const-time minimum value.
#[cfg(feature = "const-time")]
pub trait MinCt: Copy {
    /// Const-time minimum function.
    fn min_ct(&self, other: &Self) -> Self
    where
        Self: LtCt + SelectCt,
    {
        SelectCt::select_ct(self, other, self.lt_ct(other))
    }
}

/// Const-time maximum value.
#[cfg(feature = "const-time")]
pub trait MaxCt: Copy {
    /// Const-time maximum function.
    fn max_ct(&self, other: &Self) -> Self
    where
        Self: GtCt + SelectCt,
    {
        SelectCt::select_ct(self, other, self.gt_ct(other))
    }
}

/// Const-time select value.
#[cfg(feature = "const-time")]
pub trait SelectCt: Copy {
    /// Const-time select function.
    ///
    /// # Returns
    ///
    /// `lhs & mask | rhs & !mask`
    ///
    /// `mask` is repeated to match `size_of::<Self>()`.
    fn select_ct(lhs: &Self, rhs: &Self, mask: MaskCt) -> Self;
}

num_impl!(@signed [i8, i16, i32, i64, i128, isize]);
num_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);

#[cfg(feature = "const-time")]
num_ct_impl!(@signed [i8:u8, i16:u16, i32:u32, i64:u64, i128:u128, isize:usize]);

#[cfg(feature = "const-time")]
num_ct_impl!(@unsigned [u8, u16, u32, u64, u128, usize]);

sign_from!(@signed [i8, i16, i32, i64, i128, isize]);
sign_from!(@unsigned [u8, u16, u32, u64, u128, usize]);

ndops::def! { @stdbin (lhs: Sign, rhs: Sign) -> Sign, [* (lhs as i8) * (rhs as i8)] }

impl<N> From<N> for Strict<N> {
    fn from(value: N) -> Self {
        Strict(value)
    }
}

impl<N> From<N> for Wrapping<N> {
    fn from(value: N) -> Self {
        Wrapping(value)
    }
}

impl<N> From<N> for Saturating<N> {
    fn from(value: N) -> Self {
        Saturating(value)
    }
}

impl<N> From<N> for Unbounded<N> {
    fn from(value: N) -> Self {
        Unbounded(value)
    }
}

impl<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize> From<N> for Width<N, BITS> {
    fn from(value: N) -> Self {
        Self(value).normalized()
    }
}

impl<N: Num + NumExt + NumUnsigned, M: Modulus<N>> From<N> for Modular<N, M> {
    fn from(value: N) -> Self {
        Self(value, PhantomData).normalized()
    }
}

impl<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize> Binary for Width<N, BITS> {
    const BITS: usize = BITS;
    const BYTES: usize = BITS / 8;
}

impl<N: Num + NumExt + NumUnsigned + Binary, const BITS: usize> Width<N, BITS> {
    #[allow(unused)]
    const CHECK: () = assert!(0 < BITS && BITS <= N::BITS);

    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> &mut Self {
        if N::BITS <= BITS {
            return self;
        }

        let diff = N::BITS - BITS;
        let div = diff / 64;
        let rem = diff % 64;

        for idx in 0..div {
            self.write_bitand(0, Offset::Right((idx + 1) * 64));
        }

        self.write_bitand(u64::MAX.unbounded_shr(rem as u32), Offset::Right((div + 1) * 64));
        self
    }
}

impl<N: Num + NumExt + NumUnsigned, M: Modulus<N>> Modular<N, M> {
    pub(crate) fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    pub(crate) fn normalize(&mut self) -> &mut Self {
        N::nd_rem_assign(&mut self.0, &M::MOD);

        self
    }
}

impl<Any: Zero> ZeroFn for Any {
    fn zero() -> Self {
        Any::ZERO
    }
}

impl<Any: One> OneFn for Any {
    fn one() -> Self {
        Any::ONE
    }
}

impl<Any: Min> MinFn for Any {
    fn min() -> Self {
        Any::MIN
    }
}

impl<Any: Max> MaxFn for Any {
    fn max() -> Self {
        Any::MAX
    }
}

impl<Any: Binary> BinaryFn for Any {
    fn bits(&self) -> usize {
        Any::BITS
    }

    fn bytes(&self) -> usize {
        Any::BYTES
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 40).map(|val| val + 1)) [
            (u64::gcd(val, 0), val),
            (u64::gcd(0, val), val),
            (u64::gcd(val, 1), 1),
            (u64::gcd(1, val), 1),
            (u64::gcd(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 12,
            rhs in 1..=1 << 12,
        ) [
            (u64::gcd(lhs, rhs), u64::gcd(rhs, lhs)),
            (lhs % u64::gcd(lhs, rhs), 0),
            (rhs % u64::gcd(lhs, rhs), 0),
            (u64::gcd(lhs, rhs) * u64::lcm(lhs, rhs), lhs * rhs),
            {
                let res = u64::gcd(lhs, rhs);

                (u64::gcd(lhs / res, rhs / res), 1)
            },
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
              k in 1..=1 << 8,
        ) [
            (u64::gcd(k * lhs, k * rhs), k * u64::gcd(lhs, rhs)),
        ] }
    }

    #[test]
    fn gcde() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 40).map(|val| val + 1)) [
            (i64::gcde(val, 0), (val, 1, 0)),
            (i64::gcde(0, val), (val, 0, 1)),
            (i64::gcde(val, 1), (1, 0, 1)),
            (i64::gcde(1, val), (1, 1, 0)),
            (i64::gcde(val, val), (val, 0, 1)),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 12,
            rhs in 1..=1 << 12,
        ) [
            (i64::gcde(lhs, rhs).0, i64::gcde(rhs, lhs).0),
            (lhs % i64::gcde(lhs, rhs).0, 0),
            (rhs % i64::gcde(lhs, rhs).0, 0),
            (i64::gcde(lhs, rhs).0 * i64::lcm(lhs, rhs), lhs * rhs),
            {
                let res = i64::gcde(lhs, rhs).0;

                (i64::gcde(lhs / res, rhs / res).0, 1)
            },
            {
                let res = i64::gcde(lhs, rhs);

                (lhs * res.1 + rhs * res.2, res.0)
            }
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
              k in 1..=1 << 8,
        ) [
            (i64::gcde(k * lhs, k * rhs).0, k * i64::gcde(lhs, rhs).0),
        ] }
    }

    #[test]
    fn lcm() {
        ndassert::check! { @eq (val in ndassert::range!(u64, 40).map(|val| val + 1)) [
            (u64::lcm(val, 0), 0),
            (u64::lcm(0, val), 0),
            (u64::lcm(val, 1), val),
            (u64::lcm(1, val), val),
            (u64::lcm(val, val), val),
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 12,
            rhs in 1..=1 << 12,
        ) [
            (u64::lcm(lhs, rhs), u64::lcm(rhs, lhs)),
            (u64::lcm(lhs, rhs) % lhs, 0),
            (u64::lcm(lhs, rhs) % rhs, 0),
            (u64::lcm(lhs, rhs) * u64::gcd(lhs, rhs), lhs * rhs),
            {
                let res = u64::lcm(lhs, rhs);

                (u64::gcd(res / lhs, res / rhs), 1)
            },
        ] }

        ndassert::check! { @eq (
            lhs in 1..=1 << 8,
            rhs in 1..=1 << 8,
              k in 1..=1 << 8,
        ) [
            (u64::lcm(k * lhs, k * rhs), k * u64::lcm(lhs, rhs)),
        ] }
    }

    #[test]
    fn pow() {
        // const POW: u64 = ndassert::prime!(16, 0);
        // const MOD: u64 = ndassert::prime!(16, 1);
    }

    #[test]
    fn strict() {}

    #[test]
    fn wrapping() {}

    #[test]
    fn saturating() {}

    #[test]
    fn unbounded() {}

    #[test]
    fn width() {}

    #[test]
    fn modular() {}
}

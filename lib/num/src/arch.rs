#![doc = include_str!("../docs/arch.md")]

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};

use ndext::ops::*;
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::*;

macro_rules! word_def {
    (($single:ty, $double:ty), { $($tokens:tt)* } $(,)?) => {
        /// Single CPU-word unsigned primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use std::mem::size_of;
        /// # use ndnum::arch::word::*;
        /// assert_eq!(size_of::<Single>(), size_of::<usize>());
        /// ```
        ///
        /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
        pub type Single = $single;

        /// Double CPU-word unsigned primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use std::mem::size_of;
        /// # use ndnum::arch::word::*;
        /// assert_eq!(size_of::<Double>(), 2 * size_of::<usize>());
        /// ```
        ///
        /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
        pub type Double = $double;

        $($tokens)*
    };
}

macro_rules! word_impl {
    ([$($primitive:ty),+ $(,)?]) => {
        $(word_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
#[rustfmt::skip]
        impl Word for $primitive {
            const BITS: usize = Self::BITS as usize;
            const BYTES: usize = Self::BITS as usize / 8;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            fn from_usize(value: usize) -> Self {
                value as Self
            }

            fn from_single(value: Single) -> Self {
                value as Self
            }

            fn from_double(value: Double) -> Self {
                value as Self
            }

            fn as_usize(self) -> usize {
                self as usize
            }

            fn as_single(self) -> Single {
                self as Single
            }

            fn as_double(self) -> Double {
                self as Double
            }

            fn order(self) -> usize {
                self.ilog2() as usize
            }

            fn is_pow2(self) -> bool {
                (self & (self - 1) == 0) && self != 0
            }
        }
    };
}

pub mod word {
    //! CPU-word related definitions.
    //!
    //! For more info, see [module-level](crate::arch) and [crate-level](crate) documentation.

    use super::*;

    #[cfg(all(target_pointer_width = "64", not(test)))]
    word_def!((u64, u128), {
        pub(crate) const DEC_RADIX: Double = 10_000_000_000_000_000_000;
        pub(crate) const DEC_WIDTH: u8 = 19;

        pub(crate) const OCT_RADIX: Double = 1 << 63;
        pub(crate) const OCT_WIDTH: u8 = 21;

        word_impl!([u8, u16, u32, u64, usize]);
    });

    #[cfg(all(target_pointer_width = "32", not(test)))]
    word_def!((u32, u64), {
        pub(crate) const DEC_RADIX: Double = 1_000_000_000;
        pub(crate) const DEC_WIDTH: u8 = 9;

        pub(crate) const OCT_RADIX: Double = 1 << 30;
        pub(crate) const OCT_WIDTH: u8 = 10;

        word_impl!([u8, u16, u32, usize]);
    });

    #[cfg(test)]
    word_def!((u8, u16), {
        pub(crate) const DEC_RADIX: Double = 100;
        pub(crate) const DEC_WIDTH: u8 = 2;

        pub(crate) const OCT_RADIX: Double = 1 << 6;
        pub(crate) const OCT_WIDTH: u8 = 2;

        word_impl!([u8]);
    });

    /// Maximum CPU-word unsigned value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ndnum::arch::word::*;
    /// assert_eq!(MAX, Single::MAX);
    /// ```
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub const MAX: Single = Single::MAX;

    /// Minimum CPU-word unsigned value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ndnum::arch::word::*;
    /// assert_eq!(MIN, Single::MIN);
    /// ```
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub const MIN: Single = Single::MIN;

    /// Bits per CPU-word primitive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ndnum::arch::word::*;
    /// assert_eq!(BITS, Single::BITS as usize);
    /// ```
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub const BITS: usize = Single::BITS as usize;

    /// Bytes per CPU-word primitive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ndnum::arch::word::*;
    /// assert_eq!(BYTES, Single::BITS as usize / 8);
    /// ```
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub const BYTES: usize = Single::BITS as usize / 8;

    /// Radix of CPU-word primitive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ndnum::arch::word::*;
    /// assert_eq!(RADIX, Single::MAX as Double + 1);
    /// ```
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub const RADIX: Double = Single::MAX as Double + 1;

    /// Word-like primitive.
    ///
    /// - On **64-bit** tragets, implemented for: [`usize`], [`u8`], [`u16`], [`u32`], [`u64`].
    /// - On **32-bit** tragets, implemented for: [`usize`], [`u8`], [`u16`], [`u32`].
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    #[rustfmt::skip]
    pub trait Word: Clone + Copy
        + PartialEq + Eq
        + PartialOrd + Ord
        + Debug + Display + Binary + Octal + LowerHex + UpperHex
        + FromBytes + IntoBytes + Immutable
    {
        /// Bits per Word-like primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use ndnum::arch::word::*;
        /// assert_eq!(<u8 as Word>::BITS, u8::BITS as usize);
        /// assert_eq!(<u16 as Word>::BITS, u16::BITS as usize);
        /// ```
        const BITS: usize;

        /// Bytes per Word-like primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use ndnum::arch::word::*;
        /// assert_eq!(<u8 as Word>::BYTES, u8::BITS as usize / 8);
        /// assert_eq!(<u16 as Word>::BYTES, u16::BITS as usize / 8);
        /// ```
        const BYTES: usize;

        /// Zero value of Word-like primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use ndnum::arch::word::*;
        /// assert_eq!(<u8 as Word>::ZERO, 0);
        /// assert_eq!(<u16 as Word>::ZERO, 0);
        /// ```
        const ZERO: Self;

        /// One value of Word-like primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use ndnum::arch::word::*;
        /// assert_eq!(<u8 as Word>::ONE, 1);
        /// assert_eq!(<u16 as Word>::ONE, 1);
        /// ```
        const ONE: Self;

        /// Word-like primitive from [`usize`].
        ///
        /// Truncates on overflow.
        fn from_usize(value: usize) -> Self;

        /// Word-like primitive from [`Single`].
        ///
        /// Truncates on overflow.
        fn from_single(value: Single) -> Self;

        /// Word-like primitive from [`Double`].
        ///
        /// Truncates on overflow.
        fn from_double(value: Double) -> Self;

        /// Word-like primitive to [`usize`].
        fn as_usize(self) -> usize;

        /// Word-like primitive to [`Single`].
        fn as_single(self) -> Single;

        /// Word-like primitive to [`Double`].
        fn as_double(self) -> Double;

        /// Order of Word-like value.
        ///
        /// Represents position of the most significant bit.
        fn order(self) -> usize;

        /// Checks if Word-like value is power of 2.
        fn is_pow2(self) -> bool;
    }

    /// Iterator of Word-like primitives.
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub trait WordsIterator: Clone + Iterator + ExactSizeIterator
    where
        <Self as Iterator>::Item: Word,
    {
    }

    impl<Iter> WordsIterator for Iter
    where
        Iter: Clone + Iterator + ExactSizeIterator,
        Iter::Item: Word,
    {
    }
}

/// Aligned to approximate architecture cacheline size type.
///
/// Implements (conditionally) all standard Rust traits and operations of
/// `Std-kind` and `Nd-kind` if underlying type supports it.
///
/// | Architecture | Alignment |
/// | ------------ | --------- |
/// | **x86-32**   | 64 bytes  |
/// | **x86-64**   | 64 bytes  |
/// | **arm32**    | 64 bytes  |
/// | **arm64**    | 64 bytes  |
/// | **riscv32**  | 64 bytes  |
/// | **riscv64**  | 64 bytes  |
/// | **wasm32**   | 64 bytes  |
/// | **wasm64**   | 64 bytes  |
///
/// # Examples
///
/// ```rust
/// # use std::mem::align_of;
/// # use ndnum::arch::*;
/// #[cfg(target_arch = "x86")]
/// assert_eq!(align_of::<Aligned::<usize>>(), 64);
///
/// #[cfg(target_arch = "x86_64")]
/// assert_eq!(align_of::<Aligned::<usize>>(), 64);
///
/// assert_eq!(Aligned(1).eq(&Aligned(2)), 1.eq(&2));
/// assert_eq!(Aligned(1).cmp(&Aligned(2)), 1.cmp(&2));
///
/// assert_eq!(format!("{:}", Aligned(1)), format!("{:}", 1));
/// assert_eq!(format!("{:b}", Aligned(1)), format!("{:b}", 1));
/// assert_eq!(format!("{:o}", Aligned(1)), format!("{:o}", 1));
/// assert_eq!(format!("{:x}", Aligned(1)), format!("{:x}", 1));
/// assert_eq!(format!("{:X}", Aligned(1)), format!("{:X}", 1));
///
/// assert_eq!((Aligned(1) + Aligned(2)), Aligned(1 + 2));
/// assert_eq!((Aligned(1) - Aligned(2)), Aligned(1 - 2));
/// assert_eq!((Aligned(1) * Aligned(2)), Aligned(1 * 2));
/// assert_eq!((Aligned(1) / Aligned(2)), Aligned(1 / 2));
/// ```
///
/// For more info, see [module-level](crate::arch) and [crate-level](crate) documentation.
#[rustfmt::skip]
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::NumFnChecked)]
#[ndfwd::def(self.0 with T: crate::NumExt)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[cfg_attr(target_arch = "x86",     repr(align(64)))]
#[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
#[cfg_attr(target_arch = "arm",     repr(align(64)))]
#[cfg_attr(target_arch = "aarch64", repr(align(64)))]
#[cfg_attr(target_arch = "riscv32", repr(align(64)))]
#[cfg_attr(target_arch = "riscv64", repr(align(64)))]
#[cfg_attr(target_arch = "wasm32",  repr(align(64)))]
#[cfg_attr(target_arch = "wasm64",  repr(align(64)))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned<T>(pub T);

impl<T> From<T> for Aligned<T> {
    fn from(value: T) -> Self {
        Aligned(value)
    }
}

ndops::fwd! { @ndun <T> (value: &Aligned<T>) -> Aligned<T>, (T) (&value.0) [
    ! where                 [T: NdNot           <Type = T>],
    - where                 [T: NdNeg           <Type = T>],
    - @checked where        [T: NdNegChecked    <Type = T>],
    - @strict where         [T: NdNegStrict     <Type = T>],
    - @wrapping where       [T: NdNegWrapping   <Type = T>],
    - @saturating where     [T: NdNegSaturating <Type = T>],
    - @overflowing where    [T: NdNegOverflowing<Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned<Lhs>, rhs: &Aligned<Rhs>) -> Aligned<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + where [Lhs: NdAdd   <Lhs, Rhs, Type = T>],
    - where [Lhs: NdSub   <Lhs, Rhs, Type = T>],
    * where [Lhs: NdMul   <Lhs, Rhs, Type = T>],
    / where [Lhs: NdDiv   <Lhs, Rhs, Type = T>],
    % where [Lhs: NdRem   <Lhs, Rhs, Type = T>],
    | where [Lhs: NdBitOr <Lhs, Rhs, Type = T>],
    & where [Lhs: NdBitAnd<Lhs, Rhs, Type = T>],
    ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned<Lhs>, rhs: Rhs) -> Aligned<T>, (Lhs) (&lhs.0) (rhs) [
    << where                [Lhs: NdShl             <Lhs, Rhs, Type = T>],
    >> where                [Lhs: NdShr             <Lhs, Rhs, Type = T>],
    << @checked where       [Lhs: NdShlChecked      <Lhs, Rhs, Type = T>],
    >> @checked where       [Lhs: NdShrChecked      <Lhs, Rhs, Type = T>],
    << @strict where        [Lhs: NdShlStrict       <Lhs, Rhs, Type = T>],
    >> @strict where        [Lhs: NdShrStrict       <Lhs, Rhs, Type = T>],
    << @overflowing where   [Lhs: NdShlOverflowing  <Lhs, Rhs, Type = T>],
    >> @overflowing where   [Lhs: NdShrOverflowing  <Lhs, Rhs, Type = T>],
    << @unbounded where     [Lhs: NdShlUnbounded    <Lhs, Rhs, Type = T>],
    >> @unbounded where     [Lhs: NdShrUnbounded    <Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, rhs: &Aligned<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where [Lhs: NdAddAssign   <Lhs, Rhs>],
    -= where [Lhs: NdSubAssign   <Lhs, Rhs>],
    *= where [Lhs: NdMulAssign   <Lhs, Rhs>],
    /= where [Lhs: NdDivAssign   <Lhs, Rhs>],
    %= where [Lhs: NdRemAssign   <Lhs, Rhs>],
    |= where [Lhs: NdBitOrAssign <Lhs, Rhs>],
    &= where [Lhs: NdBitAndAssign<Lhs, Rhs>],
    ^= where [Lhs: NdBitXorAssign<Lhs, Rhs>],
] }

ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where               [Lhs: NdShlAssign           <Lhs, Rhs>],
    >>= where               [Lhs: NdShrAssign           <Lhs, Rhs>],
    <<= @strict where       [Lhs: NdShlAssignStrict     <Lhs, Rhs>],
    >>= @strict where       [Lhs: NdShrAssignStrict     <Lhs, Rhs>],
    <<= @unbounded where    [Lhs: NdShlAssignUnbounded  <Lhs, Rhs>],
    >>= @unbounded where    [Lhs: NdShrAssignUnbounded  <Lhs, Rhs>],
] }

ndops::fwd! { @stdun <T> (*value: &Aligned<T>) -> Aligned<T>, (T) (&value.0) [
    - where [T: NdNeg<T, Type = T>],
    ! where [T: NdNot<T, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>, *rhs: &Aligned<Rhs>) -> Aligned<T>, (Lhs) (&lhs.0) (&rhs.0) [
    + where [Lhs: NdAdd   <Lhs, Rhs, Type = T>],
    - where [Lhs: NdSub   <Lhs, Rhs, Type = T>],
    * where [Lhs: NdMul   <Lhs, Rhs, Type = T>],
    / where [Lhs: NdDiv   <Lhs, Rhs, Type = T>],
    % where [Lhs: NdRem   <Lhs, Rhs, Type = T>],
    | where [Lhs: NdBitOr <Lhs, Rhs, Type = T>],
    & where [Lhs: NdBitAnd<Lhs, Rhs, Type = T>],
    ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>, rhs: Rhs) -> Aligned<T>, (Lhs) (&lhs.0) (rhs) [
    << where [Lhs: NdShl<Lhs, Rhs, Type = T>],
    >> where [Lhs: NdShr<Lhs, Rhs, Type = T>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, *rhs: &Aligned<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
    += where [Lhs: NdAddAssign   <Lhs, Rhs>],
    -= where [Lhs: NdSubAssign   <Lhs, Rhs>],
    *= where [Lhs: NdMulAssign   <Lhs, Rhs>],
    /= where [Lhs: NdDivAssign   <Lhs, Rhs>],
    %= where [Lhs: NdRemAssign   <Lhs, Rhs>],
    |= where [Lhs: NdBitOrAssign <Lhs, Rhs>],
    &= where [Lhs: NdBitAndAssign<Lhs, Rhs>],
    ^= where [Lhs: NdBitXorAssign<Lhs, Rhs>],
] }

ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
    <<= where [Lhs: NdShlAssign<Lhs, Rhs>],
    >>= where [Lhs: NdShrAssign<Lhs, Rhs>],
] }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::long::{S64, U64};

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn std() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 48).map(S64::from)) [
            (*Aligned(val), val),
            (*Aligned(Aligned(val)), Aligned(val)),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(u64, 48).map(U64::from)) [
            (*Aligned(val), val),
            (*Aligned(Aligned(val)), Aligned(val)),
        ] }
    }

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn cmp() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56).map(S64::from),
            rhs in ndassert::range!(i64, 56).map(S64::from),
        ) [
            (Aligned(lhs).eq (&Aligned(rhs)), lhs.eq (&rhs)),
            (Aligned(lhs).cmp(&Aligned(rhs)), lhs.cmp(&rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56).map(U64::from),
            rhs in ndassert::range!(u64, 56).map(U64::from),
        ) [
            (Aligned(lhs).eq (&Aligned(rhs)), lhs.eq (&rhs)),
            (Aligned(lhs).cmp(&Aligned(rhs)), lhs.cmp(&rhs)),
        ] }
    }

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn fmt() {
        ndassert::check! { @eq (val in ndassert::range!(i64, 48).map(S64::from)) [
            (format!("{:}",   Aligned(val)), format!("{:}",   val)),
            (format!("{:b}",  Aligned(val)), format!("{:b}",  val)),
            (format!("{:o}",  Aligned(val)), format!("{:o}",  val)),
            (format!("{:x}",  Aligned(val)), format!("{:x}",  val)),
            (format!("{:X}",  Aligned(val)), format!("{:X}",  val)),
            (format!("{:#}",  Aligned(val)), format!("{:#}",  val)),
            (format!("{:#b}", Aligned(val)), format!("{:#b}", val)),
            (format!("{:#o}", Aligned(val)), format!("{:#o}", val)),
            (format!("{:#x}", Aligned(val)), format!("{:#x}", val)),
            (format!("{:#X}", Aligned(val)), format!("{:#X}", val)),
        ] }

        ndassert::check! { @eq (val in ndassert::range!(u64, 48).map(U64::from)) [
            (format!("{:}",   Aligned(val)), format!("{:}",   val)),
            (format!("{:b}",  Aligned(val)), format!("{:b}",  val)),
            (format!("{:o}",  Aligned(val)), format!("{:o}",  val)),
            (format!("{:x}",  Aligned(val)), format!("{:x}",  val)),
            (format!("{:X}",  Aligned(val)), format!("{:X}",  val)),
            (format!("{:#}",  Aligned(val)), format!("{:#}",  val)),
            (format!("{:#b}", Aligned(val)), format!("{:#b}", val)),
            (format!("{:#o}", Aligned(val)), format!("{:#o}", val)),
            (format!("{:#x}", Aligned(val)), format!("{:#x}", val)),
            (format!("{:#X}", Aligned(val)), format!("{:#X}", val)),
        ] }
    }

    #[test]
    fn ops() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1).map(S64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1).map(S64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1).map(U64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            (Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1).map(U64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 48).map(S64::from),
            rhs in 0..128,
        ) [
            (Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            (Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 48).map(U64::from),
            rhs in 0..128,
        ) [
            (Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            (Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }
    }

    #[test]
    fn ops_assign() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1).map(S64::from),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(S64::from),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1).map(U64::from),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(U64::from),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            ({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),
            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 48).map(S64::from),
            rhs in 0..128,
        ) [
            ({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 48).map(U64::from),
            rhs in 0..128,
        ) [
            ({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }
    }
}

#![doc = include_str!("../docs/arch.md")]

use std::{
    fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex},
    ops::{Deref, DerefMut},
};

use ndext::ops::*;
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::{arch::word::*, *};

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

            #[inline]
            fn from_usize(value: usize) -> Self {
                value as Self
            }

            #[inline]
            fn from_single(value: Single) -> Self {
                value as Self
            }

            #[inline]
            fn from_double(value: Double) -> Self {
                value as Self
            }

            #[inline]
            fn as_usize(self) -> usize {
                self as usize
            }

            #[inline]
            fn as_single(self) -> Single {
                self as Single
            }

            #[inline]
            fn as_double(self) -> Double {
                self as Double
            }

            #[inline]
            fn order(self) -> usize {
                self.ilog2() as usize
            }

            #[inline]
            fn is_pow2(self) -> bool {
                (self & (self - 1) == 0) && self != 0
            }

            #[cfg(feature = "rand")]
            #[inline]
            fn rand<Rng: rand::Rng>(rng: &mut Rng) -> Self {
                let mut bytes = [0; <Self as Word>::BYTES];

                rng.fill_bytes(&mut bytes);

                Self::from_ne_bytes(bytes)
            }
        }
    };
}

macro_rules! aligned_impl {
    ($aligned:ident) => {
        impl<T> From<T> for $aligned<T> {
            #[inline]
            fn from(value: T) -> Self {
                Self(value)
            }
        }

        impl<T> Deref for $aligned<T> {
            type Target = T;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl<T> DerefMut for $aligned<T> {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }

        ndops::fwd! { @ndun <T> (value: &$aligned<T>) -> $aligned<T>, (T) (&value.0) [
            ! where                 [T: NdNot           <Type = T>],
            - where                 [T: NdNeg           <Type = T>],
            - @checked where        [T: NdNegChecked    <Type = T>],
            - @strict where         [T: NdNegStrict     <Type = T>],
            - @wrapping where       [T: NdNegWrapping   <Type = T>],
            - @saturating where     [T: NdNegSaturating <Type = T>],
            - @overflowing where    [T: NdNegOverflowing<Type = T>],
        ] }

        ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &$aligned<Lhs>, rhs: &$aligned<Rhs>) -> $aligned<T>, (Lhs) (&lhs.0) (&rhs.0) [
            + where                 [Lhs: NdAdd             <Lhs, Rhs, Type = T>],
            - where                 [Lhs: NdSub             <Lhs, Rhs, Type = T>],
            * where                 [Lhs: NdMul             <Lhs, Rhs, Type = T>],
            / where                 [Lhs: NdDiv             <Lhs, Rhs, Type = T>],
            % where                 [Lhs: NdRem             <Lhs, Rhs, Type = T>],
            | where                 [Lhs: NdBitOr           <Lhs, Rhs, Type = T>],
            & where                 [Lhs: NdBitAnd          <Lhs, Rhs, Type = T>],
            ^ where                 [Lhs: NdBitXor          <Lhs, Rhs, Type = T>],
            + @checked where        [Lhs: NdAddChecked      <Lhs, Rhs, Type = T>],
            - @checked where        [Lhs: NdSubChecked      <Lhs, Rhs, Type = T>],
            * @checked where        [Lhs: NdMulChecked      <Lhs, Rhs, Type = T>],
            / @checked where        [Lhs: NdDivChecked      <Lhs, Rhs, Type = T>],
            % @checked where        [Lhs: NdRemChecked      <Lhs, Rhs, Type = T>],
            + @strict where         [Lhs: NdAddStrict       <Lhs, Rhs, Type = T>],
            - @strict where         [Lhs: NdSubStrict       <Lhs, Rhs, Type = T>],
            * @strict where         [Lhs: NdMulStrict       <Lhs, Rhs, Type = T>],
            / @strict where         [Lhs: NdDivStrict       <Lhs, Rhs, Type = T>],
            % @strict where         [Lhs: NdRemStrict       <Lhs, Rhs, Type = T>],
            + @wrapping where       [Lhs: NdAddWrapping     <Lhs, Rhs, Type = T>],
            - @wrapping where       [Lhs: NdSubWrapping     <Lhs, Rhs, Type = T>],
            * @wrapping where       [Lhs: NdMulWrapping     <Lhs, Rhs, Type = T>],
            / @wrapping where       [Lhs: NdDivWrapping     <Lhs, Rhs, Type = T>],
            % @wrapping where       [Lhs: NdRemWrapping     <Lhs, Rhs, Type = T>],
            + @saturating where     [Lhs: NdAddSaturating   <Lhs, Rhs, Type = T>],
            - @saturating where     [Lhs: NdSubSaturating   <Lhs, Rhs, Type = T>],
            * @saturating where     [Lhs: NdMulSaturating   <Lhs, Rhs, Type = T>],
            / @saturating where     [Lhs: NdDivSaturating   <Lhs, Rhs, Type = T>],
            % @saturating where     [Lhs: NdRemSaturating   <Lhs, Rhs, Type = T>],
            + @overflowing where    [Lhs: NdAddOverflowing  <Lhs, Rhs, Type = T>],
            - @overflowing where    [Lhs: NdSubOverflowing  <Lhs, Rhs, Type = T>],
            * @overflowing where    [Lhs: NdMulOverflowing  <Lhs, Rhs, Type = T>],
            / @overflowing where    [Lhs: NdDivOverflowing  <Lhs, Rhs, Type = T>],
            % @overflowing where    [Lhs: NdRemOverflowing  <Lhs, Rhs, Type = T>],
        ] }

        ndops::fwd! { @ndbin <Lhs, Rhs, T> (lhs: &$aligned<Lhs>, rhs: Rhs) -> $aligned<T>, (Lhs) (&lhs.0) (rhs) [
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

        ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut $aligned<Lhs>, rhs: &$aligned<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
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

        ndops::fwd! { @ndmut <Lhs, Rhs> (lhs: &mut $aligned<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
            <<= where               [Lhs: NdShlAssign           <Lhs, Rhs>],
            >>= where               [Lhs: NdShrAssign           <Lhs, Rhs>],
            <<= @strict where       [Lhs: NdShlAssignStrict     <Lhs, Rhs>],
            >>= @strict where       [Lhs: NdShrAssignStrict     <Lhs, Rhs>],
            <<= @unbounded where    [Lhs: NdShlAssignUnbounded  <Lhs, Rhs>],
            >>= @unbounded where    [Lhs: NdShrAssignUnbounded  <Lhs, Rhs>],
        ] }

        ndops::fwd! { @stdun <T> (*value: &$aligned<T>) -> $aligned<T>, (T) (&value.0) [
            - where [T: NdNeg<T, Type = T>],
            ! where [T: NdNot<T, Type = T>],
        ] }

        ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &$aligned<Lhs>, *rhs: &$aligned<Rhs>) -> $aligned<T>, (Lhs) (&lhs.0) (&rhs.0) [
            + where [Lhs: NdAdd   <Lhs, Rhs, Type = T>],
            - where [Lhs: NdSub   <Lhs, Rhs, Type = T>],
            * where [Lhs: NdMul   <Lhs, Rhs, Type = T>],
            / where [Lhs: NdDiv   <Lhs, Rhs, Type = T>],
            % where [Lhs: NdRem   <Lhs, Rhs, Type = T>],
            | where [Lhs: NdBitOr <Lhs, Rhs, Type = T>],
            & where [Lhs: NdBitAnd<Lhs, Rhs, Type = T>],
            ^ where [Lhs: NdBitXor<Lhs, Rhs, Type = T>],
        ] }

        ndops::fwd! { @stdbin <Lhs, Rhs, T> (*lhs: &$aligned<Lhs>, rhs: Rhs) -> $aligned<T>, (Lhs) (&lhs.0) (rhs) [
            << where [Lhs: NdShl<Lhs, Rhs, Type = T>],
            >> where [Lhs: NdShr<Lhs, Rhs, Type = T>],
        ] }

        ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut $aligned<Lhs>, *rhs: &$aligned<Rhs>), (Lhs) (&mut lhs.0) (&rhs.0) [
            += where [Lhs: NdAddAssign   <Lhs, Rhs>],
            -= where [Lhs: NdSubAssign   <Lhs, Rhs>],
            *= where [Lhs: NdMulAssign   <Lhs, Rhs>],
            /= where [Lhs: NdDivAssign   <Lhs, Rhs>],
            %= where [Lhs: NdRemAssign   <Lhs, Rhs>],
            |= where [Lhs: NdBitOrAssign <Lhs, Rhs>],
            &= where [Lhs: NdBitAndAssign<Lhs, Rhs>],
            ^= where [Lhs: NdBitXorAssign<Lhs, Rhs>],
        ] }

        ndops::fwd! { @stdmut <Lhs, Rhs> (lhs: &mut $aligned<Lhs>, rhs: Rhs), (Lhs) (&mut lhs.0) (rhs) [
            <<= where [Lhs: NdShlAssign<Lhs, Rhs>],
            >>= where [Lhs: NdShrAssign<Lhs, Rhs>],
        ] }
    };
}

pub mod word {
    //! # Word
    //!
    //! **CPU-word related definitions**
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

        /// Random Word-like value.
        #[cfg(feature = "rand")]
        fn rand<Rng: rand::Rng>(rng: &mut Rng) -> Self;
    }

    /// Word-like primitives iterator.
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    pub trait WordsIterator: Clone + Iterator<Item: Word> {}

    impl<Iter> WordsIterator for Iter
    where
        Iter: Clone + Iterator,
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
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: BytesLen)]
#[ndfwd::def(self.0 with T: BytesFn)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::NumPow)]
#[ndfwd::def(self.0 with T: crate::NumGcd)]
#[ndfwd::def(self.0 with T: crate::NumGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumRand)]
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
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::EqCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::LtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::GtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::SelectCt))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned<T>(pub T);

/// Aligned to 32-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[rustfmt::skip]
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: BytesLen)]
#[ndfwd::def(self.0 with T: BytesFn)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::NumPow)]
#[ndfwd::def(self.0 with T: crate::NumGcd)]
#[ndfwd::def(self.0 with T: crate::NumGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumRand)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::EqCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::LtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::GtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::SelectCt))]
#[repr(align(32))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned32<T>(pub T);

/// Aligned to 64-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[rustfmt::skip]
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: BytesLen)]
#[ndfwd::def(self.0 with T: BytesFn)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::NumPow)]
#[ndfwd::def(self.0 with T: crate::NumGcd)]
#[ndfwd::def(self.0 with T: crate::NumGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumRand)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::EqCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::LtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::GtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::SelectCt))]
#[repr(align(64))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned64<T>(pub T);

/// Aligned to 128-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[rustfmt::skip]
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: BytesLen)]
#[ndfwd::def(self.0 with T: BytesFn)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::NumPow)]
#[ndfwd::def(self.0 with T: crate::NumGcd)]
#[ndfwd::def(self.0 with T: crate::NumGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumRand)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::EqCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::LtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::GtCt))]
#[cfg_attr(feature = "const-time", ndfwd::def(self.0 with T: crate::SelectCt))]
#[repr(align(128))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned128<T>(pub T);

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

/// Bytes length.
#[ndfwd::decl]
pub trait BytesLen {
    /// Effective static allocation len in bits.
    const BITS: usize;

    /// Effective static allocation len in bytes.
    const BYTES: usize;
}

/// Bytes functions.
///
/// Allows reading/writing in raw binary representation.
///
/// For more info, see [crate-level](crate) documentation.
#[ndfwd::decl]
pub trait BytesFn: Sized + Default + BytesLen {
    /// As ref-slice of bytes.
    fn as_bytes_ref(&self) -> &[u8];

    /// As mut-slice of bytes.
    fn as_bytes_mut(&mut self) -> &mut [u8];

    /// Reads 64-bits of underlying value at specified Offset in bits.
    fn read(&self, offset: Offset) -> Single;

    /// Writes 64-bits as bitor operation to underlying value at specified Offset in bits.
    #[ndfwd::as_self]
    fn write_bitor(&mut self, mask: Single, offset: Offset) -> &mut Self;

    /// Writes 64-bits as bitand operation to underlying value at specified Offset in bits.
    #[ndfwd::as_self]
    fn write_bitand(&mut self, mask: Single, offset: Offset) -> &mut Self;

    /// Writes 64-bits as bitxor operation to underlying value at specified Offset in bits.
    #[ndfwd::as_self]
    fn write_bitxor(&mut self, mask: Single, offset: Offset) -> &mut Self;

    /// Writes 64-bits as bitor operation to underlying value at specified Offset in bits.
    #[inline]
    #[ndfwd::as_into]
    fn into_bitor(mut self, mask: Single, offset: Offset) -> Self {
        self.write_bitor(mask, offset);
        self
    }

    /// Writes 64-bits as bitand operation to underlying value at specified Offset in bits.
    #[inline]
    #[ndfwd::as_into]
    fn into_bitand(mut self, mask: Single, offset: Offset) -> Self {
        self.write_bitand(mask, offset);
        self
    }

    /// Writes 64-bits as bitxor operation to underlying value at specified Offset in bits.
    #[inline]
    #[ndfwd::as_into]
    fn into_bitxor(mut self, mask: Single, offset: Offset) -> Self {
        self.write_bitxor(mask, offset);
        self
    }

    /// Creates random bytes.
    #[cfg(feature = "rand")]
    #[inline]
    #[ndfwd::as_into]
    fn rand_bytes<Rng: rand::Rng>(rng: &mut Rng) -> Self {
        let mut res = Self::default();

        rng.fill_bytes(res.as_bytes_mut());

        res
    }
}

aligned_impl!(Aligned);
aligned_impl!(Aligned32);
aligned_impl!(Aligned64);
aligned_impl!(Aligned128);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::long::alias::{S64, U64};

    #[test]
    #[allow(clippy::unnecessary_cast)]
    fn std() {
        ndassert::check! { (val in ndassert::range!(i64, 60)) [
            Aligned(Box::new(val)).as_ref() == &val,
            Aligned(Box::new(val)).as_mut() == &val,

            Aligned(vec![val]) == Aligned::<Vec<i64>>::from_iter([val]),
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
        ndassert::check! { @eq (val in ndassert::range!(i64, 52).map(S64::from)) [
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

        ndassert::check! { @eq (val in ndassert::range!(u64, 52).map(U64::from)) [
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
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1).map(S64::from),
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
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1),
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
            lhs in ndassert::range!(i64, 60, 0),
            rhs in ndassert::range!(i64, 60, 1).map(S64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1).map(U64::from),
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
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1),
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
            lhs in ndassert::range!(u64, 60, 0),
            rhs in ndassert::range!(u64, 60, 1).map(U64::from),
        ) [
            (Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            (Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60).map(S64::from),
            rhs in 0..96,
        ) [
            (Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            (Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60).map(U64::from),
            rhs in 0..96,
        ) [
            (Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            (Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }
    }

    #[test]
    fn ops_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1).map(S64::from),
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
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1),
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
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1).map(U64::from),
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
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1),
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
            lhs in ndassert::range!(i64, 60).map(S64::from),
            rhs in 0..96,
        ) [
            ({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60).map(U64::from),
            rhs in 0..96,
        ) [
            ({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }
    }

    #[cfg(feature = "const-time")]
    #[test]
    fn cmp_ct() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0),
            rhs in ndassert::range!(i64, 56, 1),
        ) [
            (Aligned(lhs).eq_ct(&Aligned(rhs)), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (Aligned(lhs).lt_ct(&Aligned(rhs)), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (Aligned(lhs).gt_ct(&Aligned(rhs)), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (Aligned(lhs).le_ct(&Aligned(rhs)), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (Aligned(lhs).ge_ct(&Aligned(rhs)), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (Aligned(lhs).cmp_ct(&Aligned(rhs)), lhs.cmp(&rhs) as SignCt),
            (Aligned(lhs).min_ct(&Aligned(rhs)), Aligned(lhs.min(rhs))),
            (Aligned(lhs).max_ct(&Aligned(rhs)), Aligned(lhs.max(rhs))),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0),
            rhs in ndassert::range!(u64, 56, 1),
        ) [
            (Aligned(lhs).eq_ct(&Aligned(rhs)), MaskCt::MAX * (lhs == rhs) as MaskCt),
            (Aligned(lhs).lt_ct(&Aligned(rhs)), MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (Aligned(lhs).gt_ct(&Aligned(rhs)), MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (Aligned(lhs).le_ct(&Aligned(rhs)), MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (Aligned(lhs).ge_ct(&Aligned(rhs)), MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (Aligned(lhs).cmp_ct(&Aligned(rhs)), lhs.cmp(&rhs) as SignCt),
            (Aligned(lhs).min_ct(&Aligned(rhs)), Aligned(lhs.min(rhs))),
            (Aligned(lhs).max_ct(&Aligned(rhs)), Aligned(lhs.max(rhs))),
        ] }
    }
}

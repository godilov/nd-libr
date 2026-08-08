#![doc = include_str!("../docs/arch.md")]

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};

use ndext::{convert::NdxFrom, ops::*};
use zerocopy::{FromBytes, Immutable, IntoBytes, transmute_ref};

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
    (@ext [$($primitive:ty),+ $(,)?]) => {
        $(word_impl!(@ext $primitive);)+
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
        }
    };
    (@ext $primitive:ty $(,)?) => {
        impl WordExt for $primitive {
            #[inline]
            fn as_words<W: Word>(&self) -> &[W] {
                transmute_ref!(self)
            }
        }
    };
}

macro_rules! bytes_impl {
    ([$($primitive:ty),+] $(,)?) => {
        $(bytes_impl!($primitive);)+
    };
    ($primitive:ty $(,)?) => {
        impl AsBytesRef for $primitive {
            #[inline]
            fn as_bytes_ref(&self) -> &[u8] {
                self.as_bytes()
            }
        }

        impl AsBytesMut for $primitive {
            #[inline]
            fn as_bytes_mut(&mut self) -> &mut [u8] {
                self.as_mut_bytes()
            }
        }

        impl Rand for $primitive {}
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
        word_impl!(@ext [u128]);
    });

    #[cfg(all(target_pointer_width = "32", not(test)))]
    word_def!((u32, u64), {
        pub(crate) const DEC_RADIX: Double = 1_000_000_000;
        pub(crate) const DEC_WIDTH: u8 = 9;

        pub(crate) const OCT_RADIX: Double = 1 << 30;
        pub(crate) const OCT_WIDTH: u8 = 10;

        word_impl!([u8, u16, u32, usize]);
        word_impl!(@ext [u64, u128]);
    });

    #[cfg(test)]
    word_def!((u8, u16), {
        pub(crate) const DEC_RADIX: Double = 100;
        pub(crate) const DEC_WIDTH: u8 = 2;

        pub(crate) const OCT_RADIX: Double = 1 << 6;
        pub(crate) const OCT_WIDTH: u8 = 2;

        word_impl!([u8]);
        word_impl!(@ext [u16, u32, u64, u128, usize]);
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
    pub trait Word: Sized + Clone + Copy
        + PartialEq + Eq
        + PartialOrd + Ord
        + Debug + Display + Binary + Octal + LowerHex + UpperHex
        + AsBytesRef + AsBytesMut
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

    /// Word-extension primitive.
    ///
    /// - On **64-bit** tragets, implemented for: [`u128`].
    /// - On **32-bit** tragets, implemented for: [`u128`], [`u64`].
    ///
    /// For more info, see [module-level](crate::arch::word) and [crate-level](crate) documentation.
    #[rustfmt::skip]
    pub trait WordExt: Clone + Copy
        + PartialEq + Eq
        + PartialOrd + Ord
        + Debug + Display + Binary + Octal + LowerHex + UpperHex
        + AsBytesRef + AsBytesMut
        + FromBytes + IntoBytes + Immutable
    {
        /// Word-extension primitive to words.
        fn as_words<W: Word>(&self) -> &[W];
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
#[ndfwd::def(self.0 with T: AsBytesRef)]
#[ndfwd::def(self.0 with T: AsBytesMut)]
#[ndfwd::def(self.0 with T: AsWordsRef)]
#[ndfwd::def(self.0 with T: AsWordsMut)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumExt)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumSignedCt)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsignedCt)]
#[ndfwd::def(self.0 with T: crate::NumBinary)]
#[ndfwd::def(self.0 with T: crate::NumCt)]
#[ndfwd::def(self.0 with T: crate::NumExtCt)]
#[ndfwd::def(self.0 with T: crate::NdPow)]
#[ndfwd::def(self.0 with T: crate::NdGcd)]
#[ndfwd::def(self.0 with T: crate::NdGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Zero { const ZERO: Self = Self(T::ZERO); })]
#[ndfwd::def(self.0 with T: crate::One { const ONE: Self = Self(T::ONE); })]
#[ndfwd::def(self.0 with T: crate::Min { const MIN: Self = Self(T::MIN); })]
#[ndfwd::def(self.0 with T: crate::Max { const MAX: Self = Self(T::MAX); })]
#[ndfwd::def(self.0 with T: crate::IsZeroCt)]
#[ndfwd::def(self.0 with T: crate::IsOneCt)]
#[ndfwd::def(self.0 with T: crate::IsPosCt)]
#[ndfwd::def(self.0 with T: crate::IsNegCt)]
#[ndfwd::def(self.0 with T: crate::EqCt)]
#[ndfwd::def(self.0 with T: crate::LtCt)]
#[ndfwd::def(self.0 with T: crate::GtCt)]
#[ndfwd::def(self.0 with T: crate::LeCt)]
#[ndfwd::def(self.0 with T: crate::GeCt)]
#[ndfwd::def(self.0 with T: crate::SignCt)]
#[ndfwd::def(self.0 with T: crate::CmpCt)]
#[ndfwd::def(self.0 with T: crate::MinCt)]
#[ndfwd::def(self.0 with T: crate::MaxCt)]
#[ndfwd::def(self.0 with T: crate::PosxCt)]
#[ndfwd::def(self.0 with T: crate::NegxCt)]
#[ndfwd::def(self.0 with T: crate::SelectCt)]
#[ndfwd::def(self.0 with T: crate::PowCt)]
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

/// Aligned to 32-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsBytesRef)]
#[ndfwd::def(self.0 with T: AsBytesMut)]
#[ndfwd::def(self.0 with T: AsWordsRef)]
#[ndfwd::def(self.0 with T: AsWordsMut)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumExt)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumSignedCt)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsignedCt)]
#[ndfwd::def(self.0 with T: crate::NumBinary)]
#[ndfwd::def(self.0 with T: crate::NumCt)]
#[ndfwd::def(self.0 with T: crate::NumExtCt)]
#[ndfwd::def(self.0 with T: crate::NdPow)]
#[ndfwd::def(self.0 with T: crate::NdGcd)]
#[ndfwd::def(self.0 with T: crate::NdGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Zero { const ZERO: Self = Self(T::ZERO); })]
#[ndfwd::def(self.0 with T: crate::One { const ONE: Self = Self(T::ONE); })]
#[ndfwd::def(self.0 with T: crate::Min { const MIN: Self = Self(T::MIN); })]
#[ndfwd::def(self.0 with T: crate::Max { const MAX: Self = Self(T::MAX); })]
#[ndfwd::def(self.0 with T: crate::IsZeroCt)]
#[ndfwd::def(self.0 with T: crate::IsOneCt)]
#[ndfwd::def(self.0 with T: crate::IsPosCt)]
#[ndfwd::def(self.0 with T: crate::IsNegCt)]
#[ndfwd::def(self.0 with T: crate::EqCt)]
#[ndfwd::def(self.0 with T: crate::LtCt)]
#[ndfwd::def(self.0 with T: crate::GtCt)]
#[ndfwd::def(self.0 with T: crate::LeCt)]
#[ndfwd::def(self.0 with T: crate::GeCt)]
#[ndfwd::def(self.0 with T: crate::SignCt)]
#[ndfwd::def(self.0 with T: crate::CmpCt)]
#[ndfwd::def(self.0 with T: crate::MinCt)]
#[ndfwd::def(self.0 with T: crate::MaxCt)]
#[ndfwd::def(self.0 with T: crate::PosxCt)]
#[ndfwd::def(self.0 with T: crate::NegxCt)]
#[ndfwd::def(self.0 with T: crate::SelectCt)]
#[ndfwd::def(self.0 with T: crate::PowCt)]
#[repr(align(32))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned32<T>(pub T);

/// Aligned to 64-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsBytesRef)]
#[ndfwd::def(self.0 with T: AsBytesMut)]
#[ndfwd::def(self.0 with T: AsWordsRef)]
#[ndfwd::def(self.0 with T: AsWordsMut)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumExt)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumSignedCt)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsignedCt)]
#[ndfwd::def(self.0 with T: crate::NumBinary)]
#[ndfwd::def(self.0 with T: crate::NumCt)]
#[ndfwd::def(self.0 with T: crate::NumExtCt)]
#[ndfwd::def(self.0 with T: crate::NdPow)]
#[ndfwd::def(self.0 with T: crate::NdGcd)]
#[ndfwd::def(self.0 with T: crate::NdGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Zero { const ZERO: Self = Self(T::ZERO); })]
#[ndfwd::def(self.0 with T: crate::One { const ONE: Self = Self(T::ONE); })]
#[ndfwd::def(self.0 with T: crate::Min { const MIN: Self = Self(T::MIN); })]
#[ndfwd::def(self.0 with T: crate::Max { const MAX: Self = Self(T::MAX); })]
#[ndfwd::def(self.0 with T: crate::IsZeroCt)]
#[ndfwd::def(self.0 with T: crate::IsOneCt)]
#[ndfwd::def(self.0 with T: crate::IsPosCt)]
#[ndfwd::def(self.0 with T: crate::IsNegCt)]
#[ndfwd::def(self.0 with T: crate::EqCt)]
#[ndfwd::def(self.0 with T: crate::LtCt)]
#[ndfwd::def(self.0 with T: crate::GtCt)]
#[ndfwd::def(self.0 with T: crate::LeCt)]
#[ndfwd::def(self.0 with T: crate::GeCt)]
#[ndfwd::def(self.0 with T: crate::SignCt)]
#[ndfwd::def(self.0 with T: crate::CmpCt)]
#[ndfwd::def(self.0 with T: crate::MinCt)]
#[ndfwd::def(self.0 with T: crate::MaxCt)]
#[ndfwd::def(self.0 with T: crate::PosxCt)]
#[ndfwd::def(self.0 with T: crate::NegxCt)]
#[ndfwd::def(self.0 with T: crate::SelectCt)]
#[ndfwd::def(self.0 with T: crate::PowCt)]
#[repr(align(64))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned64<T>(pub T);

/// Aligned to 128-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsBytesRef)]
#[ndfwd::def(self.0 with T: AsBytesMut)]
#[ndfwd::def(self.0 with T: AsWordsRef)]
#[ndfwd::def(self.0 with T: AsWordsMut)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: crate::NumFn)]
#[ndfwd::def(self.0 with T: crate::Num)]
#[ndfwd::def(self.0 with T: crate::NumExt)]
#[ndfwd::def(self.0 with T: crate::NumSigned)]
#[ndfwd::def(self.0 with T: crate::NumSignedCt)]
#[ndfwd::def(self.0 with T: crate::NumUnsigned)]
#[ndfwd::def(self.0 with T: crate::NumUnsignedCt)]
#[ndfwd::def(self.0 with T: crate::NumBinary)]
#[ndfwd::def(self.0 with T: crate::NumCt)]
#[ndfwd::def(self.0 with T: crate::NumExtCt)]
#[ndfwd::def(self.0 with T: crate::NdPow)]
#[ndfwd::def(self.0 with T: crate::NdGcd)]
#[ndfwd::def(self.0 with T: crate::NdGcdChecked)]
#[ndfwd::def(self.0 with T: crate::Zero { const ZERO: Self = Self(T::ZERO); })]
#[ndfwd::def(self.0 with T: crate::One { const ONE: Self = Self(T::ONE); })]
#[ndfwd::def(self.0 with T: crate::Min { const MIN: Self = Self(T::MIN); })]
#[ndfwd::def(self.0 with T: crate::Max { const MAX: Self = Self(T::MAX); })]
#[ndfwd::def(self.0 with T: crate::IsZeroCt)]
#[ndfwd::def(self.0 with T: crate::IsOneCt)]
#[ndfwd::def(self.0 with T: crate::IsPosCt)]
#[ndfwd::def(self.0 with T: crate::IsNegCt)]
#[ndfwd::def(self.0 with T: crate::EqCt)]
#[ndfwd::def(self.0 with T: crate::LtCt)]
#[ndfwd::def(self.0 with T: crate::GtCt)]
#[ndfwd::def(self.0 with T: crate::LeCt)]
#[ndfwd::def(self.0 with T: crate::GeCt)]
#[ndfwd::def(self.0 with T: crate::SignCt)]
#[ndfwd::def(self.0 with T: crate::CmpCt)]
#[ndfwd::def(self.0 with T: crate::MinCt)]
#[ndfwd::def(self.0 with T: crate::MaxCt)]
#[ndfwd::def(self.0 with T: crate::PosxCt)]
#[ndfwd::def(self.0 with T: crate::NegxCt)]
#[ndfwd::def(self.0 with T: crate::SelectCt)]
#[ndfwd::def(self.0 with T: crate::PowCt)]
#[repr(align(128))]
#[derive(Debug, Default, Clone, Copy)]
pub struct Aligned128<T>(pub T);

/// Aligned to 4096-KiB type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsBytesRef)]
#[ndfwd::def(self.0 with T: AsBytesMut)]
#[ndfwd::def(self.0 with T: AsWordsRef)]
#[ndfwd::def(self.0 with T: AsWordsMut)]
#[ndfwd::def(self.0 with T: Rand)]
#[repr(align(4096))]
#[derive(Debug, Default, Clone, Copy)]
pub struct AlignedX<T>(pub T);

/// As bytes slice (reference).
#[ndfwd::decl]
pub trait AsBytesRef {
    /// As ref-slice of words.
    fn as_bytes_ref(&self) -> &[u8];
}

/// As bytes slice (mutable).
#[ndfwd::decl]
pub trait AsBytesMut {
    /// As mut-slice of words.
    fn as_bytes_mut(&mut self) -> &mut [u8];
}

/// As words slice (reference).
#[ndfwd::decl]
pub trait AsWordsRef: AsBytesRef {
    /// As ref-slice of words.
    fn as_words_ref<W: Word>(&self) -> &[W];
}

/// As words slice (mutable).
#[ndfwd::decl]
pub trait AsWordsMut: AsBytesMut {
    /// As mut-slice of words.
    fn as_words_mut<W: Word>(&mut self) -> &mut [W];
}

/// Random.
#[ndfwd::decl]
pub trait Rand: Sized + Default + AsBytesRef + AsBytesMut {
    /// Creates random bytes.
    #[inline]
    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn rand<Rng: rand::Rng>(rng: &mut Rng) -> Self {
        let mut res = Self::default();

        rng.fill_bytes(res.as_bytes_mut());

        res
    }

    /// Creates random bytes with length.
    #[inline]
    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn rand_ext<Rng: rand::Rng>(rng: &mut Rng, len: usize) -> Self {
        if len == 0 {
            return Self::default();
        }

        let len = len.min(std::mem::size_of::<Self>());
        let idx = len.div_ceil(u8::BITS as usize) - 1;

        let shift = len % u8::BITS as usize;
        let mask = u8::MAX.unbounded_shr(u8::BITS - shift as u32);
        let bit = 1u8 << shift;

        let mut res = Self::default();

        let bytes = &mut res.as_bytes_mut()[..idx + 1];

        rng.fill_bytes(bytes);

        bytes[idx] &= mask;
        bytes[idx] |= bit;

        res
    }
}

impl<T> From<T> for Aligned<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> From<T> for Aligned32<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> From<T> for Aligned64<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> From<T> for Aligned128<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> From<T> for AlignedX<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<U, V: NdxFrom<U, ()>> NdxFrom<U, ()> for Aligned<V> {
    #[inline]
    fn ndx_from(value: U, _: ()) -> Self {
        Self(V::ndx_from(value, ()))
    }
}

impl<U, V: NdxFrom<U, ()>> NdxFrom<U, ()> for Aligned32<V> {
    #[inline]
    fn ndx_from(value: U, _: ()) -> Self {
        Self(V::ndx_from(value, ()))
    }
}

impl<U, V: NdxFrom<U, ()>> NdxFrom<U, ()> for Aligned64<V> {
    #[inline]
    fn ndx_from(value: U, _: ()) -> Self {
        Self(V::ndx_from(value, ()))
    }
}

impl<U, V: NdxFrom<U, ()>> NdxFrom<U, ()> for Aligned128<V> {
    #[inline]
    fn ndx_from(value: U, _: ()) -> Self {
        Self(V::ndx_from(value, ()))
    }
}

impl<U, V: NdxFrom<U, ()>> NdxFrom<U, ()> for AlignedX<V> {
    #[inline]
    fn ndx_from(value: U, _: ()) -> Self {
        Self(V::ndx_from(value, ()))
    }
}

ndops::auto! { @ndun <Value, T> (value: &Aligned<Value>)    -> Aligned<T>,    (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &Aligned32<Value>)  -> Aligned32<T>,  (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &Aligned64<Value>)  -> Aligned64<T>,  (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &Aligned128<Value>) -> Aligned128<T>, (Value) (T) (&value.0) }

ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned<Lhs>,    rhs: &Aligned<Rhs>)    -> Aligned<T>,    (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned32<Lhs>,  rhs: &Aligned32<Rhs>)  -> Aligned32<T>,  (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned64<Lhs>,  rhs: &Aligned64<Rhs>)  -> Aligned64<T>,  (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned128<Lhs>, rhs: &Aligned128<Rhs>) -> Aligned128<T>, (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }

ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned<Lhs>,    rhs: Rhs) -> Aligned<T>,    (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned32<Lhs>,  rhs: Rhs) -> Aligned32<T>,  (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned64<Lhs>,  rhs: Rhs) -> Aligned64<T>,  (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned128<Lhs>, rhs: Rhs) -> Aligned128<T>, (Lhs) (Rhs) (T) (&lhs.0) (rhs) }

ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,    rhs: &Aligned<Rhs>),    (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,  rhs: &Aligned32<Rhs>),  (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,  rhs: &Aligned64<Rhs>),  (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>, rhs: &Aligned128<Rhs>), (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }

ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,    rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,  rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,  rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>, rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }

ndops::auto! { @stdun <Value, T> (*value: &Aligned<Value>)    -> Aligned<T>,    (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &Aligned32<Value>)  -> Aligned32<T>,  (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &Aligned64<Value>)  -> Aligned64<T>,  (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &Aligned128<Value>) -> Aligned128<T>, (Value) (T) (&value.0) }

ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>,    *rhs: &Aligned<Rhs>)    -> Aligned<T>,    (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned32<Lhs>,  *rhs: &Aligned32<Rhs>)  -> Aligned32<T>,  (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned64<Lhs>,  *rhs: &Aligned64<Rhs>)  -> Aligned64<T>,  (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned128<Lhs>, *rhs: &Aligned128<Rhs>) -> Aligned128<T>, (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }

ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>,    rhs: Rhs) -> Aligned<T>,    (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned32<Lhs>,  rhs: Rhs) -> Aligned32<T>,  (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned64<Lhs>,  rhs: Rhs) -> Aligned64<T>,  (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned128<Lhs>, rhs: Rhs) -> Aligned128<T>, (Lhs) (Rhs) (T) (&lhs.0) (rhs) }

ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,    *rhs: &Aligned<Rhs>),    (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,  *rhs: &Aligned32<Rhs>),  (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,  *rhs: &Aligned64<Rhs>),  (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>, *rhs: &Aligned128<Rhs>), (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }

ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,    rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,  rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,  rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>, rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }

bytes_impl!([i8, i16, i32, i64, i128, isize]);
bytes_impl!([u8, u16, u32, u64, u128, usize]);

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
        ndassert::check! { @eq (val in ndassert::range!(i64, 52)) [
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

        ndassert::check! { @eq (val in ndassert::range!(u64, 52)) [
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
            ndassert::catch!(Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            ndassert::catch!(Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            ndassert::catch!(Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            ndassert::catch!(Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            ndassert::catch!(Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),

            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            ndassert::catch!(Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            ndassert::catch!(Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            ndassert::catch!(Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            ndassert::catch!(Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            ndassert::catch!(Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),

            ndassert::catch!(Aligned(rhs) + Aligned(lhs), Aligned(rhs + lhs)),
            ndassert::catch!(Aligned(rhs) - Aligned(lhs), Aligned(rhs - lhs)),
            ndassert::catch!(Aligned(rhs) * Aligned(lhs), Aligned(rhs * lhs)),

            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),

            (Aligned(rhs) | Aligned(lhs), Aligned(rhs | lhs)),
            (Aligned(rhs) & Aligned(lhs), Aligned(rhs & lhs)),
            (Aligned(rhs) ^ Aligned(lhs), Aligned(rhs ^ lhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1).map(U64::from),
        ) [
            ndassert::catch!(Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            ndassert::catch!(Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            ndassert::catch!(Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            ndassert::catch!(Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            ndassert::catch!(Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),

            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1),
        ) [
            ndassert::catch!(Aligned(lhs) + Aligned(rhs), Aligned(lhs + rhs)),
            ndassert::catch!(Aligned(lhs) - Aligned(rhs), Aligned(lhs - rhs)),
            ndassert::catch!(Aligned(lhs) * Aligned(rhs), Aligned(lhs * rhs)),
            ndassert::catch!(Aligned(lhs) / Aligned(rhs), Aligned(lhs / rhs)),
            ndassert::catch!(Aligned(lhs) % Aligned(rhs), Aligned(lhs % rhs)),

            ndassert::catch!(Aligned(rhs) + Aligned(lhs), Aligned(rhs + lhs)),
            ndassert::catch!(Aligned(rhs) - Aligned(lhs), Aligned(rhs - lhs)),
            ndassert::catch!(Aligned(rhs) * Aligned(lhs), Aligned(rhs * lhs)),

            (Aligned(lhs) | Aligned(rhs), Aligned(lhs | rhs)),
            (Aligned(lhs) & Aligned(rhs), Aligned(lhs & rhs)),
            (Aligned(lhs) ^ Aligned(rhs), Aligned(lhs ^ rhs)),

            (Aligned(rhs) | Aligned(lhs), Aligned(rhs | lhs)),
            (Aligned(rhs) & Aligned(lhs), Aligned(rhs & lhs)),
            (Aligned(rhs) ^ Aligned(lhs), Aligned(rhs ^ lhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60).map(S64::from),
            rhs in 0..96,
        ) [
            ndassert::catch!(Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            ndassert::catch!(Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60).map(U64::from),
            rhs in 0..96,
        ) [
            ndassert::catch!(Aligned(lhs) << rhs, Aligned(lhs << rhs)),
            ndassert::catch!(Aligned(lhs) >> rhs, Aligned(lhs >> rhs)),
        ] }
    }

    #[test]
    fn ops_mut() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1).map(S64::from),
        ) [
            ndassert::catch!({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),

            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0).map(S64::from),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            ndassert::catch!({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),

            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1).map(U64::from),
        ) [
            ndassert::catch!({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),

            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60, 0).map(U64::from),
            rhs in ndassert::range!(u64, 60, 1),
        ) [
            ndassert::catch!({ let mut val = Aligned(lhs); val += Aligned(rhs); val }, Aligned(lhs + rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val -= Aligned(rhs); val }, Aligned(lhs - rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val *= Aligned(rhs); val }, Aligned(lhs * rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val /= Aligned(rhs); val }, Aligned(lhs / rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val %= Aligned(rhs); val }, Aligned(lhs % rhs)),

            ({ let mut val = Aligned(lhs); val |= Aligned(rhs); val }, Aligned(lhs | rhs)),
            ({ let mut val = Aligned(lhs); val &= Aligned(rhs); val }, Aligned(lhs & rhs)),
            ({ let mut val = Aligned(lhs); val ^= Aligned(rhs); val }, Aligned(lhs ^ rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60).map(S64::from),
            rhs in 0..96,
        ) [
            ndassert::catch!({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 60).map(U64::from),
            rhs in 0..96,
        ) [
            ndassert::catch!({ let mut val = Aligned(lhs); val <<= rhs; val }, Aligned(lhs << rhs)),
            ndassert::catch!({ let mut val = Aligned(lhs); val >>= rhs; val }, Aligned(lhs >> rhs)),
        ] }
    }

    #[test]
    fn cmp_ct() {
        #![allow(clippy::absurd_extreme_comparisons)]
        #![allow(unused_comparisons)]

        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 56, 0).map(Aligned),
            rhs in ndassert::range!(i64, 56, 1).map(Aligned),
        ) [
            (lhs.eq_ct(&rhs),  MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs.cmp_ct(&rhs), lhs.0.cmp(&rhs.0) as RelCt),
            (lhs.sign_ct(),    lhs.0.cmp(&0)     as RelCt),

            (lhs.is_zero_ct(), MaskCt::MAX * (lhs.0 == 0) as MaskCt),
            (lhs.is_one_ct(),  MaskCt::MAX * (lhs.0 == 1) as MaskCt),
            (lhs.is_pos_ct(),  MaskCt::MAX * (lhs.0 >  0) as MaskCt),
            (lhs.is_neg_ct(),  MaskCt::MAX * (lhs.0 <  0) as MaskCt),
            (lhs.lt_ct(&rhs),  MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs.gt_ct(&rhs),  MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs.le_ct(&rhs),  MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs.ge_ct(&rhs),  MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs.min_ct(&rhs), Aligned(lhs.0.min(rhs.0))),
            (lhs.max_ct(&rhs), Aligned(lhs.0.max(rhs.0))),
            (lhs.posx_ct(),    Aligned(lhs.0.wrapping_abs())),
            (lhs.negx_ct(),    Aligned(lhs.0.wrapping_abs().wrapping_neg())),
        ] }

        ndassert::check! { @eq (
            lhs in ndassert::range!(u64, 56, 0).map(Aligned),
            rhs in ndassert::range!(u64, 56, 1).map(Aligned),
        ) [
            (lhs.eq_ct(&rhs),  MaskCt::MAX * (lhs == rhs) as MaskCt),
            (lhs.cmp_ct(&rhs), lhs.0.cmp(&rhs.0) as RelCt),
            (lhs.sign_ct(),    lhs.0.cmp(&0)     as RelCt),

            (lhs.is_zero_ct(), MaskCt::MAX * (lhs.0 == 0) as MaskCt),
            (lhs.is_one_ct(),  MaskCt::MAX * (lhs.0 == 1) as MaskCt),
            (lhs.is_pos_ct(),  MaskCt::MAX * (lhs.0 >  0) as MaskCt),
            (lhs.is_neg_ct(),  MaskCt::MAX * (lhs.0 <  0) as MaskCt),
            (lhs.lt_ct(&rhs),  MaskCt::MAX * (lhs <  rhs) as MaskCt),
            (lhs.gt_ct(&rhs),  MaskCt::MAX * (lhs >  rhs) as MaskCt),
            (lhs.le_ct(&rhs),  MaskCt::MAX * (lhs <= rhs) as MaskCt),
            (lhs.ge_ct(&rhs),  MaskCt::MAX * (lhs >= rhs) as MaskCt),
            (lhs.min_ct(&rhs), Aligned(lhs.0.min(rhs.0))),
            (lhs.max_ct(&rhs), Aligned(lhs.0.max(rhs.0))),
        ] }
    }
}

#![doc = include_str!("../docs/arch.md")]

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};

use ndext::{convert::NdxFrom, iter::*};
use thiserror::Error;
use zerocopy::{FromBytes, Immutable, IntoBytes, transmute_ref};

use crate::{arch::codec::*, arch::word::*, *};

macro_rules! aligned_impl {
    ($aligned:ident [$($primitive:ty),+ $(,)?]) => {
        $(aligned_impl!($aligned, $primitive);)+
    };
    ($aligned:ident, $primitive:ty $(,)?) => {
        impl $aligned<$primitive> {
            /// Aligned array length.
            const LEN: usize = std::mem::align_of::<$aligned<()>>().div_ceil(<$primitive>::BITS as usize / 8);

            /// Aligned array.
            #[inline]
            pub fn array() -> $aligned<[$primitive; Self::LEN]> {
                $aligned::from([0; Self::LEN])
            }
        }

        impl<const L: usize> $aligned<[$primitive; L]> {
            #![allow(clippy::len_without_is_empty)]

            /// Aligned array length.
            #[inline]
            pub fn len(&self) -> usize {
                self.0.len()
            }
        }
    };
}

macro_rules! word_def {
    (($single:ty, $double:ty), { $($tokens:tt)* } $(,)?) => {
        /// Single CPU-word unsigned primitive.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use std::mem::size_of;
        /// # use ndnum::arch::word::*;
        /// assert_eq!(size_of::<Single>(), 1 * size_of::<usize>());
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
        impl AsWordsRef<u8> for $primitive {
            #[inline]
            fn as_words_ref(&self) -> &[u8] {
                self.as_bytes()
            }
        }

        impl AsWordsMut<u8> for $primitive {
            #[inline]
            fn as_words_mut(&mut self) -> &mut [u8] {
                self.as_mut_bytes()
            }
        }

        impl Rand for $primitive {}

        impl Encode<u8> for $primitive {}
        impl Decode<u8> for $primitive {}
    };
}

pub mod word {
    //! # Word
    //!
    //! **CPU-word related definitions**
    //!
    //! For more info, see [module-level](crate::arch) and [crate-level](crate) documentation.

    use std::ops::*;

    use super::*;

    #[cfg(all(target_pointer_width = "64", not(test)))]
    word_def!((u64, u128), {
        word_impl!([u8, u16, u32, u64, usize]);
        word_impl!(@ext [u128]);
    });

    #[cfg(all(target_pointer_width = "32", not(test)))]
    word_def!((u32, u64), {
        word_impl!([u8, u16, u32, usize]);
        word_impl!(@ext [u64, u128]);
    });

    #[cfg(test)]
    word_def!((u8, u16), {
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
        + AsWordsRef<u8> + AsWordsMut<u8>
        + FromBytes + IntoBytes + Immutable
        + BitOr<Self> + BitAnd<Self> + BitXor<Self>
        + BitOrAssign + BitAndAssign + BitXorAssign
        + NdOps<All = Self> + NdOpsAssign
        + NdOpsRelaxed<All = Self> + NdOpsAssignRelaxed
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
        + AsWordsRef<u8> + AsWordsMut<u8>
        + FromBytes + IntoBytes + Immutable
    {
        /// Word-extension primitive to words.
        fn as_words<W: Word>(&self) -> &[W];
    }
}

pub mod codec {
    //! # Codec
    //!
    //! **Codec (encode/decode) related definitions**
    //!
    //! For more info, see [module-level](crate::arch) and [crate-level](crate) documentation.

    use std::fmt::Formatter;

    use super::*;

    /// Array.
    #[macro_export]
    macro_rules! array {
        ($word:ty, $codec:path, $len:expr) => {
            [0 as $word; $crate::arch::codec::len::<$word, $codec>($len)]
        };
    }

    pub use array;

    /// Dec.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Dec;

    /// Bin codec.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Bin;

    /// Oct codec.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Oct;

    /// Hex codec.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Hex;

    /// X64 codec.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct X64;

    /// Encoded definitions.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Encoded;

    /// Decoded definitions.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct Decoded;

    /// Codec error.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
    pub enum Error {
        /// Found invalid entry.
        #[error("Found invalid entry")]
        InvalidEntry,
    }

    /// Codec.
    pub trait Codec: Debug + Default + Clone + Copy + PartialEq + Eq {
        /// Codec ASCII alphabet bit-length.
        const BITS: usize;

        /// Encode ASCII table.
        const ENCODE: Aligned<[u8; 256]>;

        /// Decode ASCII table.
        const DECODE: Aligned<[u8; 256]>;

        /// Codec prefix.
        const PREFIX: &'static str;

        /// Checks `Self::LEN`.
        const _CHECK: () = assert!(Self::BITS <= u8::BITS as usize);

        /// Encodes words in Codec configuration.
        #[inline]
        fn encode<W: Word, Words: AsWordsRef<W>>(
            words: &Words,
        ) -> impl ExactSizeIterator<Item = u8> + DoubleEndedIterator {
            let bits = Self::BITS;

            Encoded::read(words, bits).map(|idx| Self::ENCODE[idx.as_usize()])
        }

        /// Decodes words in Codec configuration.
        #[inline]
        fn decode<W: Word, Words: AsWordsMut<W>>(
            words: Words,
            iter: impl ExactSizeIterator<Item = u8> + DoubleEndedIterator,
        ) -> Words {
            let bits = Self::BITS;

            Decoded::write(
                words,
                bits,
                iter.map(|idx| W::from_single(Self::DECODE[idx as usize] as Single)),
            )
        }

        /// Decodes words in Codec configuration (checked).
        #[inline]
        fn try_decode<W: Word, Words: AsWordsMut<W>>(
            words: Words,
            iter: impl ExactSizeIterator<Item = u8> + DoubleEndedIterator,
        ) -> Result<Words, Error> {
            let mut flag = 0u8;

            let words = Self::decode(words, iter.inspect(|&byte| flag |= Self::DECODE[byte as usize]));

            match flag {
                u8::MAX => Err(Error::InvalidEntry),
                _ => Ok(words),
            }
        }
    }

    /// Encode functions.
    #[ndfwd::decl]
    pub trait Encode<W: Word>: Sized + AsWordsRef<W> {
        /// Encodes from self.
        fn encoded<C: Codec>(&self) -> impl ExactSizeIterator<Item = u8> + DoubleEndedIterator {
            C::encode(self)
        }
    }

    /// Decode functions.
    #[ndfwd::decl]
    pub trait Decode<W: Word>: Sized + AsWordsMut<W> {
        /// Decodes into self.
        #[ndfwd::as_into]
        fn decoded<C: Codec>(self, iter: impl ExactSizeIterator<Item = u8> + DoubleEndedIterator) -> Self {
            C::decode(self, iter)
        }
    }

    impl Encoded {
        /// Length for encoded array.
        #[inline]
        pub const fn len<W: Word>(len: usize, bits: usize) -> usize {
            (W::BITS * len).div_ceil(bits)
        }

        /// Reads from words in bits-len for encoding.
        #[inline]
        pub fn read<W: Word, Words: AsWordsRef<W>>(
            words: &Words,
            bits: usize,
        ) -> impl ExactSizeIterator<Item = W> + DoubleEndedIterator {
            let one = Relaxed(W::ONE);
            let len = Encoded::len::<W>(words.as_words_ref().len(), bits);

            let mask = (one << bits) - one;

            (0..len).map(move |idx| {
                let offset = idx * bits;

                let shl = offset % W::BITS;
                let shr = W::BITS - shl;

                let idxs = [offset / W::BITS, (offset + bits) / W::BITS];
                let vals = [
                    Relaxed(*words.as_words_ref().get(idxs[0]).unwrap_or(&W::ZERO)) & (mask << shl),
                    Relaxed(*words.as_words_ref().get(idxs[1]).unwrap_or(&W::ZERO)) & (mask >> shr),
                ];

                (vals[0] >> shl | vals[1] << shr).0
            })
        }
    }

    impl Decoded {
        /// Length for decoded array.
        #[inline]
        pub const fn len<W: Word>(len: usize, bits: usize) -> usize {
            (bits * len).div_ceil(W::BITS)
        }

        /// Writes into words in bits-len for decoding.
        #[inline]
        pub fn write<W: Word, Words: AsWordsMut<W>>(
            mut words: Words,
            bits: usize,
            iter: impl ExactSizeIterator<Item = W> + DoubleEndedIterator,
        ) -> Words {
            #![allow(clippy::option_map_unit_fn)]

            let one = Relaxed(W::ONE);
            let len = Encoded::len::<W>(words.as_words_ref().len(), bits);

            let mask = (one << bits) - one;

            for (idx, word) in iter.take(len).enumerate() {
                let offset = idx * bits;

                let shl = offset % W::BITS;
                let shr = W::BITS - shl;

                let idxs = [offset / W::BITS, (offset + bits) / W::BITS];
                let vals = [
                    (Relaxed(word) << shl) & (mask << shl),
                    (Relaxed(word) >> shr) & (mask >> shr),
                ];

                words.as_words_mut().get_mut(idxs[0]).map(|word| *word |= vals[0].0);
                words.as_words_mut().get_mut(idxs[1]).map(|word| *word |= vals[1].0);
            }

            words
        }

        /// Writes into words in bits-len for decoding (checked).
        #[inline]
        pub fn try_write<W: Word, Words: AsWordsMut<W>>(
            words: Words,
            bits: usize,
            iter: impl ExactSizeIterator<Item = W> + DoubleEndedIterator,
        ) -> Result<Words, Error> {
            let mut flag = W::ZERO;

            let words = Decoded::write(words, bits, iter.inspect(|&word| flag |= word));

            if (Relaxed(W::ONE) << bits) <= Relaxed(flag) {
                return Err(Error::InvalidEntry);
            }

            Ok(words)
        }
    }

    #[rustfmt::skip]
    impl Dec {
        /// Decode ASCII table.
        pub const DECODE: Aligned<[u8; 256]> = ascii(255, &[
            (b'0' as usize, 0), (b'1' as usize, 1),
            (b'2' as usize, 2), (b'3' as usize, 3),
            (b'4' as usize, 4), (b'5' as usize, 5),
            (b'6' as usize, 6), (b'7' as usize, 7),
            (b'8' as usize, 8), (b'9' as usize, 9),
        ]);

        /// Radix in [`Single`].
        pub const RADIX: Double = (10 as Double).pow(Self::DIGITS as u32);

        /// Digits in [`Single`].
        pub const DIGITS: usize = RADIX.ilog10() as usize;
    }

    #[rustfmt::skip]
    impl Codec for Bin {
        const BITS: usize = 1;

        const ENCODE: Aligned<[u8; 256]> = ascii(0, &[
            (0, b'0'), (1, b'1'),
        ]);

        const DECODE: Aligned<[u8; 256]> = ascii(255, &[
            (b'0' as usize, 0), (b'1' as usize, 1),
        ]);

        const PREFIX: &'static str = "0b";
    }

    #[rustfmt::skip]
    impl Codec for Oct {
        const BITS: usize = 3;

        const ENCODE: Aligned<[u8; 256]> = ascii(0, &[
            (0, b'0'), (1, b'1'),
            (2, b'2'), (3, b'3'),
            (4, b'4'), (5, b'5'),
            (6, b'6'), (7, b'7'),
        ]);

        const DECODE: Aligned<[u8; 256]> = ascii(255, &[
            (b'0' as usize, 0), (b'1' as usize, 1),
            (b'2' as usize, 2), (b'3' as usize, 3),
            (b'4' as usize, 4), (b'5' as usize, 5),
            (b'6' as usize, 6), (b'7' as usize, 7),
        ]);

        const PREFIX: &'static str = "0o";
    }

    #[rustfmt::skip]
    impl Codec for Hex {
        const BITS: usize = 4;

        const ENCODE: Aligned<[u8; 256]> = ascii(0, &[
            ( 0, b'0'), ( 1, b'1'),
            ( 2, b'2'), ( 3, b'3'),
            ( 4, b'4'), ( 5, b'5'),
            ( 6, b'6'), ( 7, b'7'),
            ( 8, b'8'), ( 9, b'9'),
            (10, b'A'), (11, b'B'),
            (12, b'C'), (13, b'D'),
            (14, b'E'), (15, b'F'),
        ]);

        const DECODE: Aligned<[u8; 256]> = ascii(255, &[
            (b'0' as usize,  0), (b'1' as usize,  1),
            (b'2' as usize,  2), (b'3' as usize,  3),
            (b'4' as usize,  4), (b'5' as usize,  5),
            (b'6' as usize,  6), (b'7' as usize,  7),
            (b'8' as usize,  8), (b'9' as usize,  9),
            (b'A' as usize, 10), (b'B' as usize, 11),
            (b'C' as usize, 12), (b'D' as usize, 13),
            (b'E' as usize, 14), (b'F' as usize, 15),
            (b'a' as usize, 10), (b'b' as usize, 11),
            (b'c' as usize, 12), (b'd' as usize, 13),
            (b'e' as usize, 14), (b'f' as usize, 15),
        ]);

        const PREFIX: &'static str = "0x";
    }

    #[rustfmt::skip]
    impl Codec for X64 {
        const BITS: usize = 6;

        const ENCODE: Aligned<[u8; 256]> = ascii(0, &[
            ( 0, b'A'), ( 1, b'B'),
            ( 2, b'C'), ( 3, b'D'),
            ( 4, b'E'), ( 5, b'F'),
            ( 6, b'G'), ( 7, b'H'),
            ( 8, b'I'), ( 9, b'J'),
            (10, b'K'), (11, b'L'),
            (12, b'M'), (13, b'N'),
            (14, b'O'), (15, b'P'),
            (16, b'Q'), (17, b'R'),
            (18, b'S'), (19, b'T'),
            (20, b'U'), (21, b'V'),
            (22, b'W'), (23, b'X'),
            (24, b'Y'), (25, b'Z'),
            (26, b'a'), (27, b'b'),
            (28, b'c'), (29, b'd'),
            (30, b'e'), (31, b'f'),
            (32, b'g'), (33, b'h'),
            (34, b'i'), (35, b'j'),
            (36, b'k'), (37, b'l'),
            (38, b'm'), (39, b'n'),
            (40, b'o'), (41, b'p'),
            (42, b'q'), (43, b'r'),
            (44, b's'), (45, b't'),
            (46, b'u'), (47, b'v'),
            (48, b'w'), (49, b'x'),
            (50, b'y'), (51, b'z'),
            (52, b'0'), (53, b'1'),
            (54, b'2'), (55, b'3'),
            (56, b'4'), (57, b'5'),
            (58, b'6'), (59, b'7'),
            (60, b'8'), (61, b'9'),
            (62, b'-'), (63, b'_'),
        ]);

        const DECODE: Aligned<[u8; 256]> = ascii(255, &[
            (b'A' as usize,  0), (b'B' as usize,  1),
            (b'C' as usize,  2), (b'D' as usize,  3),
            (b'E' as usize,  4), (b'F' as usize,  5),
            (b'G' as usize,  6), (b'H' as usize,  7),
            (b'I' as usize,  8), (b'J' as usize,  9),
            (b'K' as usize, 10), (b'L' as usize, 11),
            (b'M' as usize, 12), (b'N' as usize, 13),
            (b'O' as usize, 14), (b'P' as usize, 15),
            (b'Q' as usize, 16), (b'R' as usize, 17),
            (b'S' as usize, 18), (b'T' as usize, 19),
            (b'U' as usize, 20), (b'V' as usize, 21),
            (b'W' as usize, 22), (b'X' as usize, 23),
            (b'Y' as usize, 24), (b'Z' as usize, 25),
            (b'a' as usize, 26), (b'b' as usize, 27),
            (b'c' as usize, 28), (b'd' as usize, 29),
            (b'e' as usize, 30), (b'f' as usize, 31),
            (b'g' as usize, 32), (b'h' as usize, 33),
            (b'i' as usize, 34), (b'j' as usize, 35),
            (b'k' as usize, 36), (b'l' as usize, 37),
            (b'm' as usize, 38), (b'n' as usize, 39),
            (b'o' as usize, 40), (b'p' as usize, 41),
            (b'q' as usize, 42), (b'r' as usize, 43),
            (b's' as usize, 44), (b't' as usize, 45),
            (b'u' as usize, 46), (b'v' as usize, 47),
            (b'w' as usize, 48), (b'x' as usize, 49),
            (b'y' as usize, 50), (b'z' as usize, 51),
            (b'0' as usize, 52), (b'1' as usize, 53),
            (b'2' as usize, 54), (b'3' as usize, 55),
            (b'4' as usize, 56), (b'5' as usize, 57),
            (b'6' as usize, 58), (b'7' as usize, 59),
            (b'8' as usize, 60), (b'9' as usize, 61),
            (b'-' as usize, 62), (b'_' as usize, 63),
        ]);

        const PREFIX: &'static str = "";
    }

    /// Writes ASCII iterator into Formatter.
    #[inline]
    pub fn write<Ascii: ExactSizeIterator<Item = u8>>(fmt: &mut Formatter<'_>, mut ascii: Ascii) -> std::fmt::Result {
        let lenx = AlignedX::<u8>::array().len();

        for _ in 0..ascii.len().div_ceil(lenx) {
            let len = ascii.len().min(lenx);

            let bytes = ascii.collect_with(AlignedX::<u8>::array());

            let str = match str::from_utf8(&bytes[..len]) {
                Ok(val) => val,
                Err(_) => return Err(std::fmt::Error),
            };

            fmt.write_str(str)?;
        }

        Ok(())
    }

    /// ASCII identity iterator.
    #[inline]
    pub fn ident<Ascii: ExactSizeIterator<Item = u8> + DoubleEndedIterator>(
        ascii: Ascii,
    ) -> impl ExactSizeIterator<Item = u8> + DoubleEndedIterator {
        ascii
    }

    /// ASCII uppercase iterator.
    #[inline]
    pub fn uppercase<Ascii: ExactSizeIterator<Item = u8> + DoubleEndedIterator>(
        ascii: Ascii,
    ) -> impl ExactSizeIterator<Item = u8> + DoubleEndedIterator {
        const ASCII: Aligned<[u8; 256]> = {
            let mut res = [0; 256];
            let mut idx = 0usize;

            while idx < res.len() {
                res[idx] = (idx as u8 as char).to_ascii_uppercase() as u8;
                idx += 1;
            }

            Aligned(res)
        };

        ascii.map(|byte| ASCII[byte as usize])
    }

    /// ASCII lowercase iterator.
    #[inline]
    pub fn lowercase<Ascii: ExactSizeIterator<Item = u8> + DoubleEndedIterator>(
        ascii: Ascii,
    ) -> impl ExactSizeIterator<Item = u8> + DoubleEndedIterator {
        const ASCII: Aligned<[u8; 256]> = {
            let mut res = [0; 256];
            let mut idx = 0usize;

            while idx < res.len() {
                res[idx] = (idx as u8 as char).to_ascii_lowercase() as u8;
                idx += 1;
            }

            Aligned(res)
        };

        ascii.map(|byte| ASCII[byte as usize])
    }

    #[inline]
    const fn ascii<T: Copy>(default: T, slice: &[(usize, T)]) -> Aligned<[T; 256]> {
        let mut idx = 0;
        let mut res = [default; 256];

        while idx < slice.len() {
            let (i, x) = slice[idx];

            res[i] = x;
            idx += 1;
        }

        Aligned(res)
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
#[ndfwd::idx(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsWordsRef<W>)]
#[ndfwd::def(self.0 with T: AsWordsMut<W>)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: codec::Encode<W>)]
#[ndfwd::def(self.0 with T: codec::Decode<W>)]
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
#[ndfwd::idx(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsWordsRef<W>)]
#[ndfwd::def(self.0 with T: AsWordsMut<W>)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: codec::Encode<W>)]
#[ndfwd::def(self.0 with T: codec::Decode<W>)]
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
#[ndfwd::idx(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsWordsRef<W>)]
#[ndfwd::def(self.0 with T: AsWordsMut<W>)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: codec::Encode<W>)]
#[ndfwd::def(self.0 with T: codec::Decode<W>)]
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
#[ndfwd::idx(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsWordsRef<W>)]
#[ndfwd::def(self.0 with T: AsWordsMut<W>)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: codec::Encode<W>)]
#[ndfwd::def(self.0 with T: codec::Decode<W>)]
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

/// Aligned to architecture SIMD length type.
///
/// Implements (conditionally) all standard Rust traits and operations of
/// `Std-kind` and `Nd-kind` if underlying type supports it.
///
/// | Architecture | Feature     | Alignment |
/// | ------------ | ----------- | --------- |
/// | **x86-64**   | **SSE**     | 16 bytes  |
/// | **x86-64**   | **AVX**     | 16 bytes  |
/// | **x86-64**   | **AVX2**    | 32 bytes  |
/// | **x86-64**   | **AVX512**  | 64 bytes  |
/// | **ARM**      | **Neon**    | 16 bytes  |
/// | **WASM**     | **SIMD128** | 16 bytes  |
/// | **Any**      | None        | 16 bytes  |
///
/// For more info, see [module-level](crate::arch) and [crate-level](crate) documentation.
#[rustfmt::skip]
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::idx(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsWordsRef<W>)]
#[ndfwd::def(self.0 with T: AsWordsMut<W>)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: codec::Encode<W>)]
#[ndfwd::def(self.0 with T: codec::Decode<W>)]
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
#[cfg_attr(all(any(
    target_feature = "sse",
    target_feature = "avx",
    target_feature = "neon",
    target_feature = "simd128",
), not(any(
    target_feature = "avx2",
    target_feature = "avx512f",
))), repr(align(16)))]
#[cfg_attr(all(any(
    target_feature = "avx2",
), not(any(
    target_feature = "avx512f",
    target_feature = "neon",
    target_feature = "simd128",
))), repr(align(32)))]
#[cfg_attr(all(any(
    target_feature = "avx512f",
), not(any(
    target_feature = "neon",
    target_feature = "simd128",
))), repr(align(64)))]
#[cfg_attr(not(any(
    target_feature = "sse",
    target_feature = "avx",
    target_feature = "avx2",
    target_feature = "avx512f",
    target_feature = "neon",
    target_feature = "simd128",
)), repr(align(16)))]
#[derive(Debug, Default, Clone, Copy)]
pub struct AlignedSimd<T>(pub T);

/// Aligned to 4096-bytes type.
///
/// For more info, see [Aligned], [module-level](crate::arch) and [crate-level](crate) documentation.
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::idx(self.0 with T)]
#[ndfwd::iter(self.0 with T)]
#[ndfwd::def(self.0 with T: AsWordsRef<W>)]
#[ndfwd::def(self.0 with T: AsWordsMut<W>)]
#[ndfwd::def(self.0 with T: Rand)]
#[ndfwd::def(self.0 with T: codec::Encode<W>)]
#[ndfwd::def(self.0 with T: codec::Decode<W>)]
#[repr(align(4096))]
#[derive(Debug, Default, Clone, Copy)]
pub struct AlignedX<T>(pub T);

/// As words slice (reference).
#[ndfwd::decl]
pub trait AsWordsRef<W: Word> {
    /// As ref-slice of words.
    fn as_words_ref(&self) -> &[W];
}

/// As words slice (mutable).
#[ndfwd::decl]
pub trait AsWordsMut<W: Word>: AsWordsRef<W> {
    /// As mut-slice of words.
    fn as_words_mut(&mut self) -> &mut [W];
}

/// Random.
#[ndfwd::decl]
pub trait Rand: Sized + Default + AsWordsRef<u8> + AsWordsMut<u8> {
    /// Creates random bytes.
    #[inline]
    #[cfg(feature = "rand")]
    #[ndfwd::as_into]
    fn rand<Rng: rand::Rng>(rng: &mut Rng) -> Self {
        let mut res = Self::default();

        rng.fill_bytes(res.as_words_mut());

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

        let bytes = &mut res.as_words_mut()[..idx + 1];

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

impl<T> From<T> for AlignedSimd<T> {
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

impl<U, V: NdxFrom<U, ()>> NdxFrom<U, ()> for AlignedSimd<V> {
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

impl<Any: AsWordsRef<W>, W: Word> AsWordsRef<W> for &Any {
    fn as_words_ref(&self) -> &[W] {
        Any::as_words_ref(self)
    }
}

impl<Any: AsWordsRef<W>, W: Word> AsWordsRef<W> for &mut Any {
    fn as_words_ref(&self) -> &[W] {
        Any::as_words_ref(self)
    }
}

impl<Any: AsWordsMut<W> + AsWordsRef<W>, W: Word> AsWordsMut<W> for &mut Any {
    fn as_words_mut(&mut self) -> &mut [W] {
        Any::as_words_mut(self)
    }
}

ndops::auto! { @ndun <Value, T> (value: &Aligned<Value>)     -> Aligned<T>,     (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &Aligned32<Value>)   -> Aligned32<T>,   (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &Aligned64<Value>)   -> Aligned64<T>,   (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &Aligned128<Value>)  -> Aligned128<T>,  (Value) (T) (&value.0) }
ndops::auto! { @ndun <Value, T> (value: &AlignedSimd<Value>) -> AlignedSimd<T>, (Value) (T) (&value.0) }

ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned<Lhs>,     rhs: &Aligned<Rhs>)     -> Aligned<T>,     (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned32<Lhs>,   rhs: &Aligned32<Rhs>)   -> Aligned32<T>,   (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned64<Lhs>,   rhs: &Aligned64<Rhs>)   -> Aligned64<T>,   (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &Aligned128<Lhs>,  rhs: &Aligned128<Rhs>)  -> Aligned128<T>,  (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @ndbin <Lhs, Rhs, T> (lhs: &AlignedSimd<Lhs>, rhs: &AlignedSimd<Rhs>) -> AlignedSimd<T>, (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }

ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned<Lhs>,    rhs: Rhs)  -> Aligned<T>,     (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned32<Lhs>,  rhs: Rhs)  -> Aligned32<T>,   (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned64<Lhs>,  rhs: Rhs)  -> Aligned64<T>,   (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &Aligned128<Lhs>, rhs: Rhs)  -> Aligned128<T>,  (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @ndbin @shift <Lhs, Rhs, T> (lhs: &AlignedSimd<Lhs>, rhs: Rhs) -> AlignedSimd<T>, (Lhs) (Rhs) (T) (&lhs.0) (rhs) }

ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,     rhs: &Aligned<Rhs>),     (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,   rhs: &Aligned32<Rhs>),   (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,   rhs: &Aligned64<Rhs>),   (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>,  rhs: &Aligned128<Rhs>),  (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @ndmut <Lhs, Rhs> (lhs: &mut AlignedSimd<Lhs>, rhs: &AlignedSimd<Rhs>), (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }

ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,     rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,   rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,   rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>,  rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @ndmut @shift <Lhs, Rhs> (lhs: &mut AlignedSimd<Lhs>, rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }

ndops::auto! { @stdun <Value, T> (*value: &Aligned<Value>)     -> Aligned<T>,     (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &Aligned32<Value>)   -> Aligned32<T>,   (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &Aligned64<Value>)   -> Aligned64<T>,   (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &Aligned128<Value>)  -> Aligned128<T>,  (Value) (T) (&value.0) }
ndops::auto! { @stdun <Value, T> (*value: &AlignedSimd<Value>) -> AlignedSimd<T>, (Value) (T) (&value.0) }

ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>,     *rhs: &Aligned<Rhs>)     -> Aligned<T>,     (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned32<Lhs>,   *rhs: &Aligned32<Rhs>)   -> Aligned32<T>,   (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned64<Lhs>,   *rhs: &Aligned64<Rhs>)   -> Aligned64<T>,   (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &Aligned128<Lhs>,  *rhs: &Aligned128<Rhs>)  -> Aligned128<T>,  (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }
ndops::auto! { @stdbin <Lhs, Rhs, T> (*lhs: &AlignedSimd<Lhs>, *rhs: &AlignedSimd<Rhs>) -> AlignedSimd<T>, (Lhs) (Rhs) (T) (&lhs.0) (&rhs.0) }

ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned<Lhs>,     rhs: Rhs) -> Aligned<T>,     (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned32<Lhs>,   rhs: Rhs) -> Aligned32<T>,   (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned64<Lhs>,   rhs: Rhs) -> Aligned64<T>,   (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &Aligned128<Lhs>,  rhs: Rhs) -> Aligned128<T>,  (Lhs) (Rhs) (T) (&lhs.0) (rhs) }
ndops::auto! { @stdbin @shift <Lhs, Rhs, T> (*lhs: &AlignedSimd<Lhs>, rhs: Rhs) -> AlignedSimd<T>, (Lhs) (Rhs) (T) (&lhs.0) (rhs) }

ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,     *rhs: &Aligned<Rhs>),     (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,   *rhs: &Aligned32<Rhs>),   (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,   *rhs: &Aligned64<Rhs>),   (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>,  *rhs: &Aligned128<Rhs>),  (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }
ndops::auto! { @stdmut <Lhs, Rhs> (lhs: &mut AlignedSimd<Lhs>, *rhs: &AlignedSimd<Rhs>), (Lhs) (Rhs) (&mut lhs.0) (&rhs.0) }

ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned<Lhs>,     rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned32<Lhs>,   rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned64<Lhs>,   rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut Aligned128<Lhs>,  rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }
ndops::auto! { @stdmut @shift <Lhs, Rhs> (lhs: &mut AlignedSimd<Lhs>, rhs: Rhs), (Lhs) (Rhs) (&mut lhs.0) (rhs) }

aligned_impl!(Aligned     [i8, i16, i32, i64, i128, isize]);
aligned_impl!(Aligned     [u8, u16, u32, u64, u128, usize]);
aligned_impl!(Aligned32   [i8, i16, i32, i64, i128, isize]);
aligned_impl!(Aligned32   [u8, u16, u32, u64, u128, usize]);
aligned_impl!(Aligned64   [i8, i16, i32, i64, i128, isize]);
aligned_impl!(Aligned64   [u8, u16, u32, u64, u128, usize]);
aligned_impl!(Aligned128  [i8, i16, i32, i64, i128, isize]);
aligned_impl!(Aligned128  [u8, u16, u32, u64, u128, usize]);
aligned_impl!(AlignedSimd [i8, i16, i32, i64, i128, isize]);
aligned_impl!(AlignedSimd [u8, u16, u32, u64, u128, usize]);
aligned_impl!(AlignedX    [i8, i16, i32, i64, i128, isize]);
aligned_impl!(AlignedX    [u8, u16, u32, u64, u128, usize]);

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
    fn encode() {
        ndassert::check! { (
            val in ndassert::range!(u64, 48, 0),
        ) [
            (val.encoded::<Bin>().zip(format!("{:b}", val).bytes().rev()).fold(true, |acc, (lhs, rhs)| acc & (lhs == rhs))),
            (val.encoded::<Oct>().zip(format!("{:o}", val).bytes().rev()).fold(true, |acc, (lhs, rhs)| acc & (lhs == rhs))),
            (val.encoded::<Hex>().zip(format!("{:X}", val).bytes().rev()).fold(true, |acc, (lhs, rhs)| acc & (lhs == rhs))),
        ] }

        ndassert::check! { (
            val in ndassert::range!(u64, 48, 0),
        ) [
            (Aligned(val).encoded::<Bin>().zip(format!("{:b}", val).bytes().rev()).fold(true, |acc, (lhs, rhs)| acc & (lhs == rhs))),
            (Aligned(val).encoded::<Oct>().zip(format!("{:o}", val).bytes().rev()).fold(true, |acc, (lhs, rhs)| acc & (lhs == rhs))),
            (Aligned(val).encoded::<Hex>().zip(format!("{:X}", val).bytes().rev()).fold(true, |acc, (lhs, rhs)| acc & (lhs == rhs))),
        ] }
    }

    #[test]
    fn decode() {
        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48, 0),
        ) [
            (0u64.decoded::<Bin>(val.encoded::<Bin>()), val),
            (0u64.decoded::<Oct>(val.encoded::<Oct>()), val),
            (0u64.decoded::<Hex>(val.encoded::<Hex>()), val),
            (0u64.decoded::<X64>(val.encoded::<X64>()), val),
        ] }

        ndassert::check! { @eq (
            val in ndassert::range!(u64, 48, 0),
        ) [
            (Aligned(0u64).decoded::<Bin>(Aligned(val).encoded::<Bin>()), Aligned(val)),
            (Aligned(0u64).decoded::<Oct>(Aligned(val).encoded::<Oct>()), Aligned(val)),
            (Aligned(0u64).decoded::<Hex>(Aligned(val).encoded::<Hex>()), Aligned(val)),
            (Aligned(0u64).decoded::<X64>(Aligned(val).encoded::<X64>()), Aligned(val)),
        ] }
    }
}

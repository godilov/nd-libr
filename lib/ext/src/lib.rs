#![doc = include_str!("../README.md")]

pub mod convert;
pub mod iter;
pub mod ops;

pub mod seq {
    //! # Sequences
    //!
    //! For more info, see [crate-level](crate) documentation.

    /// Index sequence.
    pub struct Idx<const L: usize> {}

    /// Morph sequence.
    pub struct Morph<const L: usize, Seq: Sequence<L, Elem = V>, V, U, F: Fn(V) -> U> {
        seq: Seq,
        func: F,
    }

    /// Sequence.
    pub trait Sequence<const L: usize> {
        /// Sequence elem.
        type Elem;

        /// Sequence iterator.
        fn seq(self) -> impl Iterator<Item = Self::Elem>;

        /// Sequence with morph.
        #[inline]
        fn with<T, F: Fn(Self::Elem) -> T>(self, func: F) -> Morph<L, Self, Self::Elem, T, F>
        where
            Self: Sized,
        {
            Morph { seq: self, func }
        }
    }

    impl<const L: usize> Sequence<L> for Idx<L> {
        type Elem = usize;

        #[inline]
        fn seq(self) -> impl Iterator<Item = Self::Elem> {
            0..L
        }
    }

    impl<const L: usize, Seq: Sequence<L, Elem = V>, V, U, F: Fn(V) -> U> Sequence<L> for Morph<L, Seq, V, U, F> {
        type Elem = U;

        #[inline]
        fn seq(self) -> impl Iterator<Item = Self::Elem> {
            self.seq.seq().map(self.func)
        }
    }

    impl<const L: usize, T> Sequence<L> for [T; L] {
        type Elem = T;

        #[inline]
        fn seq(self) -> impl Iterator<Item = Self::Elem> {
            self.into_iter()
        }
    }

    impl<'seq, const L: usize, T> Sequence<L> for &'seq [T; L] {
        type Elem = &'seq T;

        #[inline]
        fn seq(self) -> impl Iterator<Item = Self::Elem> {
            self.iter()
        }
    }

    impl<'seq, const L: usize, T> Sequence<L> for &'seq mut [T; L] {
        type Elem = &'seq mut T;

        #[inline]
        fn seq(self) -> impl Iterator<Item = Self::Elem> {
            self.iter_mut()
        }
    }
}

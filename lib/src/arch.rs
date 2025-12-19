use std::{
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, DerefMut, Div,
        DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign,
    },
};

use zerocopy::{FromBytes, Immutable, IntoBytes};

macro_rules! aligned_display_impl {
    ([$($display:ident),+ $(,)?]) => {
        $(aligned_display_impl!($display);)+
    };
    ($display:ident) => {
        impl<T: $display> $display for Aligned<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}

macro_rules! aligned_ops_impl {
    ([$($op:ident => $fn:ident),+ $(,)?]) => {
        $(aligned_ops_impl!($op => $fn);)+
    };
    ($op:ident => $fn:ident) => {
        impl<U, V: $op<U, Output = V>> $op<U> for Aligned<V> {
            type Output = Aligned<V>;

            fn $fn(self, rhs: U) -> Self::Output {
                Aligned(self.0.$fn(rhs))
            }
        }
    };
}

macro_rules! aligned_ops_mut_impl {
    ([$($op:ident => $fn:ident),+ $(,)?]) => {
        $(aligned_ops_mut_impl!($op => $fn);)+
    };
    ($op:ident => $fn:ident) => {
        impl<U, V: $op<U>> $op<U> for Aligned<V> {
            fn $fn(&mut self, rhs: U) {
                self.0.$fn(rhs);
            }
        }
    };
}

macro_rules! word_def {
    (($single:ty, $double:ty), { $($body:tt)* }) => {
        pub type Single = $single;
        pub type Double = $double;

        $($body)*
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

            fn from_single(value: Single) -> Self {
                value as Self
            }

            fn from_double(value: Double) -> Self {
                value as Self
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

pub const MAX: Single = Single::MAX;
pub const MIN: Single = Single::MIN;
pub const BITS: usize = Single::BITS as usize;
pub const BYTES: usize = Single::BITS as usize / u8::BITS as usize;
pub const RADIX: Double = Single::MAX as Double + 1;

#[ndproc::align]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Aligned<T>(pub T);

#[rustfmt::skip]
pub trait Word: Clone + Copy
    + PartialEq + Eq
    + PartialOrd + Ord
    + Debug + Display + Binary + Octal + LowerHex + UpperHex
    + FromBytes + IntoBytes + Immutable
{
    const BITS: usize;
    const BYTES: usize;
    const ZERO: Self;
    const ONE: Self;

    fn from_single(value: Single) -> Self;
    fn from_double(value: Double) -> Self;

    fn as_single(self) -> Single;
    fn as_double(self) -> Double;

    fn order(self) -> usize;

    fn is_pow2(self) -> bool;
}

pub trait WordsIterator: Clone + Iterator + ExactSizeIterator
where
    <Self as Iterator>::Item: Word,
{
}

impl<T> Deref for Aligned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Aligned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> From<T> for Aligned<T> {
    fn from(value: T) -> Self {
        Aligned(value)
    }
}

impl<U, V: FromIterator<U>> FromIterator<U> for Aligned<V> {
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        Aligned(V::from_iter(iter))
    }
}

impl<U, V: AsRef<U>> AsRef<U> for Aligned<V> {
    fn as_ref(&self) -> &U {
        self.0.as_ref()
    }
}

impl<U, V: AsMut<U>> AsMut<U> for Aligned<V> {
    fn as_mut(&mut self) -> &mut U {
        self.0.as_mut()
    }
}

aligned_display_impl!([Display, Binary, Octal, LowerHex, UpperHex]);

aligned_ops_impl!([
    Add => add,
    Sub => sub,
    Mul => mul,
    Div => div,
    Rem => rem,
    BitOr => bitor,
    BitAnd => bitand,
    BitXor => bitxor,
]);

aligned_ops_mut_impl!([
    AddAssign => add_assign,
    SubAssign => sub_assign,
    MulAssign => mul_assign,
    DivAssign => div_assign,
    RemAssign => rem_assign,
    BitOrAssign => bitor_assign,
    BitAndAssign => bitand_assign,
    BitXorAssign => bitxor_assign,
]);

impl<Iter> WordsIterator for Iter
where
    Iter: Clone + Iterator + ExactSizeIterator,
    Iter::Item: Word,
{
}

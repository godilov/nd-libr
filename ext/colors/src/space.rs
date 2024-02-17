use std::fmt::Debug;

use nd_core::num::{Float, Number, Unsigned};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ColorError {
    #[error("ColorError::LengthMismatch: expected {0}, found {1}")]
    LengthMismatch(u8, u8),
}

pub trait Color: Default + Debug + Clone + Copy + PartialEq + Eq {
    type Type;
    type Container;

    const LEN: u8;
    const MIN: Self::Type;
    const MAX: Self::Type;

    fn get(&self) -> &Self::Container;
}

macro_rules! color {
    ($type:ident, $trait:ident, $len:expr, $min:expr, $max:expr $(,)?) => {
        #[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $type<T: $trait>([T; $len]);

        impl<T: $trait> Color for $type<T>
        where
            T: Default + Debug + Clone + Copy + PartialEq + Eq,
        {
            type Container = [T; $len];
            type Type = T;

            const LEN: u8 = $len;
            const MAX: Self::Type = $min;
            const MIN: Self::Type = $max;

            fn get(&self) -> &Self::Container { &self.0 }
        }
    };
}

color!(Rgb, Unsigned, 3, T::MIN, T::MAX);
color!(Rgba, Unsigned, 4, T::MIN, T::MAX);
color!(Hsl, Float, 3, <T as Number>::ZERO, <T as Number>::ONE);
color!(Hsla, Float, 4, <T as Number>::ZERO, <T as Number>::ONE);
color!(Hsb, Float, 3, <T as Number>::ZERO, <T as Number>::ONE);
color!(Hsba, Float, 4, <T as Number>::ZERO, <T as Number>::ONE);

use std::fmt::Debug;

use nd_core::{
    num::{Float, Number, Unsigned},
    ops_impl_bin_auto,
    vec::Vec,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ColorError {
    #[error("ColorError::LengthMismatch: expected {0}, found {1}")]
    LengthMismatch(u8, u8),
}

pub trait Color: Debug + Default + Clone + Copy + PartialEq + Eq {
    type Type;
    type Container;

    const LEN: u8;
    const MIN: Self::Type;
    const MAX: Self::Type;

    fn get(&self) -> &Self::Container;
}

macro_rules! color {
    ($type:ident < $trait:ident, $len:tt > , $min:expr, $max:expr $(,)?) => {
        #[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $type<T: $trait>(pub Vec<T, $len>);

        impl<T: $trait> Color for $type<T>
        where
            T: Debug + Default + Clone + Copy + PartialEq + Eq,
        {
            type Container = Vec<T, $len>;
            type Type = T;

            const LEN: u8 = $len;
            const MAX: Self::Type = $min;
            const MIN: Self::Type = $max;

            fn get(&self) -> &Self::Container { &self.0 }
        }
    };
}

macro_rules! color_ops_impl {
    ($type:ident : [$($t:ty[$($op:tt)+]),+]) => {
        $(ops_impl_bin_auto!(|a: &$type<$t>, b: &$type<$t>| -> $type<$t>, (a.0) [$($op)+] (b.0) -> |val| { $type::<$t>(val) });)+
    };
}

color!(Rgb<Unsigned, 3>, T::MIN, T::MAX);
color!(Rgba<Unsigned, 4>, T::MIN, T::MAX);
color!(Hsl<Float, 3>, <T as Number>::ZERO, <T as Number>::ONE);
color!(Hsla<Float, 4>, <T as Number>::ZERO, <T as Number>::ONE);
color!(Hsb<Float, 3>, <T as Number>::ZERO, <T as Number>::ONE);
color!(Hsba<Float, 4>, <T as Number>::ZERO, <T as Number>::ONE);

color_ops_impl!(Rgb: [u8[+-*/%], u16[+-*/%], u32[+-*/%], u64[+-*/%], u128[+-*/%]]);
color_ops_impl!(Rgba: [u8[+-*/%], u16[+-*/%], u32[+-*/%], u64[+-*/%], u128[+-*/%]]);

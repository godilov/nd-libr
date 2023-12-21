use std::{
    fmt::Debug,
    ops::{Add, Div, Mul, Sub},
};

use nd_arr::as_arr;
use nd_num::{Float, Number, Ops, Unsigned};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ColorError {
    #[error("ColorError::LengthMismatch: expected {0}, found {1}")]
    LengthMismatch(u8, u8),
}

pub trait ColorOps<'ops, Container>: Ops<'ops, Self> + Ops<'ops, Container>
where
    Container: 'ops,
    &'ops Self: Add<Self>
        + Sub<Self>
        + Mul<Self>
        + Div<Self>
        + Add<&'ops Self>
        + Sub<&'ops Self>
        + Mul<&'ops Self>
        + Div<&'ops Self>
        + Add<Container>
        + Sub<Container>
        + Mul<Container>
        + Div<Container>
        + Add<&'ops Container>
        + Sub<&'ops Container>
        + Mul<&'ops Container>
        + Div<&'ops Container>, {
}

pub trait Color<'ops>: ColorOps<'ops, Self::Container> + Default + Debug + Clone + Copy + PartialEq + Eq {
    type Type;
    type Container;

    const LEN: u8;
    const MIN: Self::Type;
    const MAX: Self::Type;

    fn get(&self) -> &Self::Container;
}

macro_rules! color {
    ($type:ident, $trait:path, $len:expr, $min:expr, $max:expr $(,)?) => {
        #[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $type<T: $trait>([T; $len]);

        impl<'ops, T: $trait> Color<'ops> for $type<T> {
            type Container = [T; $len];
            type Type = T;

            const LEN: u8 = $len;
            const MAX: Self::Type = $max;
            const MIN: Self::Type = $min;

            fn get(&self) -> &Self::Container { &self.0 }
        }

        impl<T: $trait> From<&[T; $len]> for $type<T> {
            fn from(value: &[T; $len]) -> Self { $type::<T>(*value) }
        }

        impl<T: $trait> TryFrom<&[T]> for $type<T> {
            type Error = ColorError;

            fn try_from(value: &[T]) -> Result<Self, Self::Error> {
                if value.len() == $len {
                    Ok($type::<T>(*as_arr!(value, 0, $len)))
                } else {
                    Err(ColorError::LengthMismatch($len as u8, value.len() as u8))
                }
            }
        }

        impl<T: $trait> TryFrom<&Vec<T>> for $type<T> {
            type Error = ColorError;

            fn try_from(value: &Vec<T>) -> Result<Self, Self::Error> {
                if value.len() == $len {
                    Ok($type::<T>(*as_arr!(&value[..], 0, $len)))
                } else {
                    Err(ColorError::LengthMismatch($len as u8, value.len() as u8))
                }
            }
        }
    };
}

color!(Rgb, Unsigned, 3, T::MIN, T::MAX);
color!(Rgba, Unsigned, 4, T::MIN, T::MAX);
color!(Hsl, Float, 3, 0.0, 1.0);
color!(Hsla, Float, 4, 0.0, 1.0);
color!(Hsb, Float, 3, 0.0, 1.0);
color!(Hsba, Float, 4, 0.0, 1.0);

impl<T: Unsigned> Add<Self> for Rgb<T> {
    type Output = Rgb<T>;

    fn add(self, rhs: Self) -> Self::Output { todo!() }
}

impl<T: Unsigned> Add<Self> for &Rgb<T> {
    type Output = Rgb<T>;

    fn add(self, rhs: Self) -> Self::Output { todo!() }
}

impl<T: Unsigned> Add<&Self> for Rgb<T> {
    type Output = Rgb<T>;

    fn add(self, rhs: &Self) -> Self::Output { todo!() }
}

impl<T: Unsigned> Add<&Self> for &Rgb<T> {
    type Output = Rgb<T>;

    fn add(self, rhs: &Self) -> Self::Output { todo!() }
}

#[cfg(test)]
mod tests {
    use super::Rgb;

    #[test]
    fn rgb_from() {
        let rgb_raw = [32, 32, 32];
        let rgb_vec = vec![32u8, 32u8, 32u8];

        let rgb_raw_res = Rgb::<u8>::from(&rgb_raw);
        let rgb_slice_res = Rgb::<u8>::try_from(&rgb_raw[0..3]);
        let rgb_vec_res = Rgb::<u8>::try_from(&rgb_vec);

        let rgb_slice_res_err = Rgb::<u8>::try_from(&rgb_raw[0..2]);
        let rgb_vec_res_err = Rgb::<u8>::try_from(&rgb_vec[0..2]);

        assert!(rgb_slice_res.is_ok());
        assert!(rgb_vec_res.is_ok());

        assert!(rgb_slice_res_err.is_err());
        assert!(rgb_vec_res_err.is_err());

        let rgb_slice_res_val = rgb_slice_res.unwrap();
        let rgb_vec_res_val = rgb_vec_res.unwrap();

        assert_eq!(rgb_raw_res.0[0], rgb_raw[0]);
        assert_eq!(rgb_raw_res.0[1], rgb_raw[1]);
        assert_eq!(rgb_raw_res.0[2], rgb_raw[2]);

        assert_eq!(rgb_slice_res_val.0[0], rgb_raw[0]);
        assert_eq!(rgb_slice_res_val.0[1], rgb_raw[1]);
        assert_eq!(rgb_slice_res_val.0[2], rgb_raw[2]);

        assert_eq!(rgb_vec_res_val.0[0], rgb_raw[0]);
        assert_eq!(rgb_vec_res_val.0[1], rgb_raw[1]);
        assert_eq!(rgb_vec_res_val.0[2], rgb_raw[2]);
    }
}

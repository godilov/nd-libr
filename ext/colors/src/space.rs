use nd_core::{num::Number, vec::Vec as NdVec};

pub type Rgb<T> = NdVec<T, 3>;
pub type Rgba<T> = NdVec<T, 4>;
pub type Hsl<T> = NdVec<T, 3>;
pub type Hsla<T> = NdVec<T, 4>;
pub type Hsb<T> = NdVec<T, 3>;
pub type Hsba<T> = NdVec<T, 4>;
pub type Scale<T> = NdVec<T, 1>;

pub enum Color<T: Number> {
    Rgb(Rgb<T>),
    Hsl(Hsl<T>),
    Hsb(Hsb<T>),
}

pub enum ColorAlpha<T: Number> {
    Rgba(Rgba<T>),
    Hsla(Hsla<T>),
    Hsba(Hsba<T>),
}

pub enum ColorArr {
    Rgb8(Vec<Rgb<u8>>),
    Rgb16(Vec<Rgb<u16>>),
    Rgb32(Vec<Rgb<u32>>),
    Rgb64(Vec<Rgb<u64>>),
    Rgb128(Vec<Rgb<u128>>),
    Hsl32(Vec<Hsl<f32>>),
    Hsl64(Vec<Hsl<f64>>),
    Hsb32(Vec<Hsb<f32>>),
    Hsb64(Vec<Hsb<f64>>),
    Rgba8(Vec<Rgba<u8>>),
    Rgba16(Vec<Rgba<u16>>),
    Rgba32(Vec<Rgba<u32>>),
    Rgba64(Vec<Rgba<u64>>),
    Rgba128(Vec<Rgba<u128>>),
    Hsla32(Vec<Hsla<f32>>),
    Hsla64(Vec<Hsla<f64>>),
    Hsba32(Vec<Hsba<f32>>),
    Hsba64(Vec<Hsba<f64>>),
    Scale32(Vec<Scale<f32>>),
    Scale64(Vec<Scale<f64>>),
}

use std::compile_error;

macro_rules! cast {
    (@rgb_from: $n:tt $val:ident, $from:ty, $to:ty) => {
        if $n < 3 || $n > 4 {
            compile_error!("cast:rgb_from $n takes only 3 or 4, found {}");
        } else {
            $val.iter()
                .map(|x| {
                    let ratio = <$from>::MAX / <$to>::MAX as $from;
                    let r = x.0[0] / ratio;
                    let g = x.0[1] / ratio;
                    let b = x.0[2] / ratio;

                    NdVec::<$to, 3>([r as $to, g as $to, b as $to])
                })
                .collect::<Vec<Rgb<$to>>>()
        }
    };
    (@rgb_to: $n:tt $val:ident, $from:ty, $to:ty) => {
        $val.iter()
            .map(|x| {
                let ratio = <$to>::MAX / <$from>::MAX as $to;
                let r = x.0[0] as $to * ratio;
                let g = x.0[1] as $to * ratio;
                let b = x.0[2] as $to * ratio;

                NdVec::<$to, 3>([r as $to, g as $to, b as $to])
            })
            .collect::<Vec<Rgb<$to>>>()
    };
}

impl ColorArr {
    fn to_rgb8(&self) -> Vec<Rgb<u8>> {
        match self {
            | ColorArr::Rgb8(val) => val.clone(),
            | ColorArr::Rgb16(val) => cast!(@rgb_from:3 val, u16, u8),
            | ColorArr::Rgb32(val) => cast!(@rgb_from:3 val, u32, u8),
            | ColorArr::Rgb64(val) => cast!(@rgb_from:3 val, u64, u8),
            | ColorArr::Rgb128(val) => cast!(@rgb_from:3 val, u128, u8),

            | ColorArr::Rgba8(val) => cast!(@rgb_from:3 val, u8, u8),
            | ColorArr::Rgba16(val) => cast!(@rgb_from:3 val, u16, u8),
            | ColorArr::Rgba32(val) => cast!(@rgb_from:3 val, u32, u8),
            | ColorArr::Rgba64(val) => cast!(@rgb_from:3 val, u64, u8),
            | ColorArr::Rgba128(val) => cast!(@rgb_from:3 val, u128, u8),
            | _ => todo!(),
        }
    }

    fn to_rgb16(&self) -> Vec<Rgb<u16>> {
        match self {
            | ColorArr::Rgb8(val) => cast!(@rgb_to:3 val, u8, u16),
            | ColorArr::Rgb16(val) => val.clone(),
            | ColorArr::Rgb32(val) => cast!(@rgb_from:3 val, u32, u16),
            | ColorArr::Rgb64(val) => cast!(@rgb_from:3 val, u64, u16),
            | ColorArr::Rgb128(val) => cast!(@rgb_from:3 val, u128, u16),

            | ColorArr::Rgba8(val) => cast!(@rgb_from:3 val, u8, u16),
            | ColorArr::Rgba16(val) => cast!(@rgb_from:3 val, u16, u16),
            | ColorArr::Rgba32(val) => cast!(@rgb_from:3 val, u32, u16),
            | ColorArr::Rgba64(val) => cast!(@rgb_from:3 val, u64, u16),
            | ColorArr::Rgba128(val) => cast!(@rgb_from:3 val, u128, u16),
            | _ => todo!(),
        }
    }

    fn to_rgb32(&self) -> Vec<Rgb<u32>> {
        match self {
            | ColorArr::Rgb8(val) => cast!(@rgb_to:3 val, u8, u32),
            | ColorArr::Rgb16(val) => cast!(@rgb_to:3 val, u16, u32),
            | ColorArr::Rgb32(val) => val.clone(),
            | ColorArr::Rgb64(val) => cast!(@rgb_from:3 val, u64, u32),
            | ColorArr::Rgb128(val) => cast!(@rgb_from:3 val, u128, u32),

            | ColorArr::Rgba8(val) => cast!(@rgb_from:3 val, u8, u32),
            | ColorArr::Rgba16(val) => cast!(@rgb_from:3 val, u16, u32),
            | ColorArr::Rgba32(val) => cast!(@rgb_from:3 val, u32, u32),
            | ColorArr::Rgba64(val) => cast!(@rgb_from:3 val, u64, u32),
            | ColorArr::Rgba128(val) => cast!(@rgb_from:3 val, u128, u32),
            | _ => todo!(),
        }
    }

    fn to_rgb64(&self) -> Vec<Rgb<u64>> {
        match self {
            | ColorArr::Rgb8(val) => cast!(@rgb_to:3 val, u8, u64),
            | ColorArr::Rgb16(val) => cast!(@rgb_to:3 val, u16, u64),
            | ColorArr::Rgb32(val) => cast!(@rgb_to:3 val, u16, u64),
            | ColorArr::Rgb64(val) => val.clone(),
            | ColorArr::Rgb128(val) => cast!(@rgb_from:3 val, u128, u64),

            | ColorArr::Rgba8(val) => cast!(@rgb_from:3 val, u8, u64),
            | ColorArr::Rgba16(val) => cast!(@rgb_from:3 val, u16, u64),
            | ColorArr::Rgba32(val) => cast!(@rgb_from:3 val, u32, u64),
            | ColorArr::Rgba64(val) => cast!(@rgb_from:3 val, u64, u64),
            | ColorArr::Rgba128(val) => cast!(@rgb_from:3 val, u128, u64),
            | _ => todo!(),
        }
    }

    fn to_rgb128(&self) -> Vec<Rgb<u128>> {
        match self {
            | ColorArr::Rgb8(val) => cast!(@rgb_to:3 val, u8, u128),
            | ColorArr::Rgb16(val) => cast!(@rgb_to:3 val, u16, u128),
            | ColorArr::Rgb32(val) => cast!(@rgb_to:3 val, u16, u128),
            | ColorArr::Rgb64(val) => cast!(@rgb_to:3 val, u16, u128),
            | ColorArr::Rgb128(val) => val.clone(),

            | ColorArr::Rgba8(val) => cast!(@rgb_from:3 val, u8, u128),
            | ColorArr::Rgba16(val) => cast!(@rgb_from:3 val, u16, u128),
            | ColorArr::Rgba32(val) => cast!(@rgb_from:3 val, u32, u128),
            | ColorArr::Rgba64(val) => cast!(@rgb_from:3 val, u64, u128),
            | ColorArr::Rgba128(val) => cast!(@rgb_from:3 val, u128, u128),
            | _ => todo!(),
        }
    }

    fn to_hsl32(&self) -> Vec<Hsl<f32>> {
        todo!();
    }

    fn to_hsl64(&self) -> Vec<Hsl<f64>> {
        todo!();
    }

    fn to_hsb32(&self) -> Vec<Hsb<f32>> {
        todo!();
    }

    fn to_hsb64(&self) -> Vec<Hsb<f64>> {
        todo!();
    }

    fn to_rgba8(&self) -> Vec<Rgba<u8>> {
        todo!();
    }

    fn to_rgba16(&self) -> Vec<Rgba<u16>> {
        todo!();
    }

    fn to_rgba32(&self) -> Vec<Rgba<u32>> {
        todo!();
    }

    fn to_rgba64(&self) -> Vec<Rgba<u64>> {
        todo!();
    }

    fn to_rgba128(&self) -> Vec<Rgba<u128>> {
        todo!();
    }

    fn to_hsla32(&self) -> Vec<Hsla<f32>> {
        todo!();
    }

    fn to_hsla64(&self) -> Vec<Hsla<f64>> {
        todo!();
    }

    fn to_hsba32(&self) -> Vec<Hsba<f32>> {
        todo!();
    }

    fn to_hsba64(&self) -> Vec<Hsba<f64>> {
        todo!();
    }

    fn to_scale32(&self) -> Vec<Scale<f32>> {
        todo!();
    }

    fn to_scale64(&self) -> Vec<Scale<f64>> {
        todo!();
    }
}

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

impl ColorArr {
    fn to_rgb8(&self) -> Self {
        match self {
            | ColorArr::Rgb8(val) => ColorArr::Rgb8(*val),
            | ColorArr::Rgb16(val) => ColorArr::Rgb8(
                val.iter()
                    .map(|x| {
                        let ratio = u16::MAX / u8::MAX as u16;
                        let r = x.0[0] / ratio;
                        let g = x.0[1] / ratio;
                        let b = x.0[2] / ratio;

                        NdVec::<u8, 3>([r as u8, g as u8, b as u8])
                    })
                    .collect::<Vec<Rgb<u8>>>(),
            ),
            | ColorArr::Rgb32(val) => ColorArr::Rgb8(
                val.iter()
                    .map(|x| {
                        let ratio = u32::MAX / u8::MAX as u32;
                        let r = x.0[0] / ratio;
                        let g = x.0[1] / ratio;
                        let b = x.0[2] / ratio;

                        NdVec::<u8, 3>([r as u8, g as u8, b as u8])
                    })
                    .collect::<Vec<Rgb<u8>>>(),
            ),
            | ColorArr::Rgb64(val) => ColorArr::Rgb8(
                val.iter()
                    .map(|x| {
                        let ratio = u64::MAX / u8::MAX as u64;
                        let r = x.0[0] / ratio;
                        let g = x.0[1] / ratio;
                        let b = x.0[2] / ratio;

                        NdVec::<u8, 3>([r as u8, g as u8, b as u8])
                    })
                    .collect::<Vec<Rgb<u8>>>(),
            ),
            | ColorArr::Rgb128(val) => ColorArr::Rgb8(
                val.iter()
                    .map(|x| {
                        let ratio = u128::MAX / u8::MAX as u128;
                        let r = x.0[0] / ratio;
                        let g = x.0[1] / ratio;
                        let b = x.0[2] / ratio;

                        NdVec::<u8, 3>([r as u8, g as u8, b as u8])
                    })
                    .collect::<Vec<Rgb<u8>>>(),
            ),
        }
    }

    fn to_rgb16(&self) -> Self { todo!() }

    fn to_rgb32(&self) -> Self { todo!() }

    fn to_rgb64(&self) -> Self { todo!() }

    fn to_rgb128(&self) -> Self { todo!() }

    fn to_hsl32(&self) -> Self { todo!() }

    fn to_hsl64(&self) -> Self { todo!() }

    fn to_hsb32(&self) -> Self { todo!() }

    fn to_hsb64(&self) -> Self { todo!() }

    fn to_rgba8(&self) -> Self { todo!() }

    fn to_rgba16(&self) -> Self { todo!() }

    fn to_rgba32(&self) -> Self { todo!() }

    fn to_rgba64(&self) -> Self { todo!() }

    fn to_rgba128(&self) -> Self { todo!() }

    fn to_hsla32(&self) -> Self { todo!() }

    fn to_hsla64(&self) -> Self { todo!() }

    fn to_hsba32(&self) -> Self { todo!() }

    fn to_hsba64(&self) -> Self { todo!() }

    fn to_scale32(&self) -> Self { todo!() }

    fn to_scale64(&self) -> Self { todo!() }
}

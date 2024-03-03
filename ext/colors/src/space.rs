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
}

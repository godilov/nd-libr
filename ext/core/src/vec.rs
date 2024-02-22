use crate::{num::Number, ops_impl};

pub struct Vec<N: Number, const L: usize>([N; L]);

type Vec1u8 = Vec<u8, 1>;
type Vec2u8 = Vec<u8, 2>;
type Vec3u8 = Vec<u8, 3>;
type Vec4u8 = Vec<u8, 4>;

type Vec1u16 = Vec<u16, 1>;
type Vec2u16 = Vec<u16, 2>;
type Vec3u16 = Vec<u16, 3>;
type Vec4u16 = Vec<u16, 4>;

type Vec1u32 = Vec<u32, 1>;
type Vec2u32 = Vec<u32, 2>;
type Vec3u32 = Vec<u32, 3>;
type Vec4u32 = Vec<u32, 4>;

type Vec1u64 = Vec<u64, 1>;
type Vec2u64 = Vec<u64, 2>;
type Vec3u64 = Vec<u64, 3>;
type Vec4u64 = Vec<u64, 4>;

type Vec1i8 = Vec<i8, 1>;
type Vec2i8 = Vec<i8, 2>;
type Vec3i8 = Vec<i8, 3>;
type Vec4i8 = Vec<i8, 4>;

type Vec1i16 = Vec<i16, 1>;
type Vec2i16 = Vec<i16, 2>;
type Vec3i16 = Vec<i16, 3>;
type Vec4i16 = Vec<i16, 4>;

type Vec1i32 = Vec<i32, 1>;
type Vec2i32 = Vec<i32, 2>;
type Vec3i32 = Vec<i32, 3>;
type Vec4i32 = Vec<i32, 4>;

type Vec1i64 = Vec<i64, 1>;
type Vec2i64 = Vec<i64, 2>;
type Vec3i64 = Vec<i64, 3>;
type Vec4i64 = Vec<i64, 4>;

type Vec1f32 = Vec<f32, 1>;
type Vec2f32 = Vec<f32, 2>;
type Vec3f32 = Vec<f32, 3>;
type Vec4f32 = Vec<f32, 4>;

type Vec1f64 = Vec<f64, 1>;
type Vec2f64 = Vec<f64, 2>;
type Vec3f64 = Vec<f64, 3>;
type Vec4f64 = Vec<f64, 4>;

mod std_impl {
    use super::*;

    macro_rules! vec_impl {
        (1: [$($type:ident),+]) => {
            $(
                ops_impl!(|a: &$type, b: &$type| -> $type,
                        + { $type {0: [a.0[0] + b.0[0]]} }
                        - { $type {0: [a.0[0] - b.0[0]]} }
                        * { $type {0: [a.0[0] * b.0[0]]} }
                        / { $type {0: [a.0[0] / b.0[0]]} });
            )+
        };
        (2: [$($type:ident),+]) => {
            $(
                ops_impl!(|a: &$type, b: &$type| -> $type,
                        + { $type {0: [a.0[0] + b.0[0], a.0[1] + b.0[1]]} }
                        - { $type {0: [a.0[0] - b.0[0], a.0[1] - b.0[1]]} }
                        * { $type {0: [a.0[0] * b.0[0], a.0[1] * b.0[1]]} }
                        / { $type {0: [a.0[0] / b.0[0], a.0[1] / b.0[1]]} });
            )+
        };
        (3: [$($type:ident),+]) => {
            $(
                ops_impl!(|a: &$type, b: &$type| -> $type,
                        + { $type {0: [a.0[0] + b.0[0], a.0[1] + b.0[1], a.0[2] + b.0[2]]} }
                        - { $type {0: [a.0[0] - b.0[0], a.0[1] - b.0[1], a.0[2] - b.0[2]]} }
                        * { $type {0: [a.0[0] * b.0[0], a.0[1] * b.0[1], a.0[2] * b.0[2]]} }
                        / { $type {0: [a.0[0] / b.0[0], a.0[1] / b.0[1], a.0[2] / b.0[2]]} });
            )+
        };
        (4: [$($type:ident),+]) => {
            $(
                ops_impl!(|a: &$type, b: &$type| -> $type,
                        + { $type {0: [a.0[0] + b.0[0], a.0[1] + b.0[1], a.0[2] + b.0[2], a.0[3] + b.0[3]]} }
                        - { $type {0: [a.0[0] - b.0[0], a.0[1] - b.0[1], a.0[2] - b.0[2], a.0[3] - b.0[3]]} }
                        * { $type {0: [a.0[0] * b.0[0], a.0[1] * b.0[1], a.0[2] * b.0[2], a.0[3] * b.0[3]]} }
                        / { $type {0: [a.0[0] / b.0[0], a.0[1] / b.0[1], a.0[2] / b.0[2], a.0[3] / b.0[3]]} });
            )+
        };
    }

    vec_impl!(1: [Vec1u8, Vec1u16, Vec1u32, Vec1u64]);
    vec_impl!(1: [Vec1i8, Vec1i16, Vec1i32, Vec1i64]);
    vec_impl!(1: [Vec1f32, Vec1f64]);

    vec_impl!(2: [Vec2u8, Vec2u16, Vec2u32, Vec2u64]);
    vec_impl!(2: [Vec2i8, Vec2i16, Vec2i32, Vec2i64]);
    vec_impl!(2: [Vec2f32, Vec2f64]);

    vec_impl!(3: [Vec3u8, Vec3u16, Vec3u32, Vec3u64]);
    vec_impl!(3: [Vec3i8, Vec3i16, Vec3i32, Vec3i64]);
    vec_impl!(3: [Vec3f32, Vec3f64]);

    vec_impl!(4: [Vec4u8, Vec4u16, Vec4u32, Vec4u64]);
    vec_impl!(4: [Vec4i8, Vec4i16, Vec4i32, Vec4i64]);
    vec_impl!(4: [Vec4f32, Vec4f64]);

    // use std::ops::Add;

    // impl<N: Number + From<<N as Add<N>>::Output>> Add<N> for Vec<N, 4> {
    //     type Output = Vec<N, 4>;

    //     fn add(self, rhs: N) -> Self::Output {
    //         Vec::<N, 4>([
    //             (self.0[0] + rhs).into(),
    //             (self.0[1] + rhs).into(),
    //             (self.0[2] + rhs).into(),
    //             (self.0[3] + rhs).into()
    //         ])
    //     }
    // }
}

use crate::{num::Number, ops_impl_bin};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Vec<N: Number, const L: usize>(pub [N; L]);

impl<N: Number, const L: usize> Default for Vec<N, L> {
    fn default() -> Self { Vec::<N, L>([N::default(); L]) }
}

macro_rules! vec_impl {
    (1: [$($type:path),+]) => {
        $(
            ops_impl_bin!(|a: &$type, b: &$type| -> $type,
                    + { $type ([a.0[0] + b.0[0]]) }
                    - { $type ([a.0[0] - b.0[0]]) }
                    * { $type ([a.0[0] * b.0[0]]) }
                    / { $type ([a.0[0] / b.0[0]]) });
        )+
    };
    (2: [$($type:path),+]) => {
        $(
            ops_impl_bin!(|a: &$type, b: &$type| -> $type,
                    + { $type ([a.0[0] + b.0[0], a.0[1] + b.0[1]]) }
                    - { $type ([a.0[0] - b.0[0], a.0[1] - b.0[1]]) }
                    * { $type ([a.0[0] * b.0[0], a.0[1] * b.0[1]]) }
                    / { $type ([a.0[0] / b.0[0], a.0[1] / b.0[1]]) });
        )+
    };
    (3: [$($type:path),+]) => {
        $(
            ops_impl_bin!(|a: &$type, b: &$type| -> $type,
                    + { $type ([a.0[0] + b.0[0], a.0[1] + b.0[1], a.0[2] + b.0[2]]) }
                    - { $type ([a.0[0] - b.0[0], a.0[1] - b.0[1], a.0[2] - b.0[2]]) }
                    * { $type ([a.0[0] * b.0[0], a.0[1] * b.0[1], a.0[2] * b.0[2]]) }
                    / { $type ([a.0[0] / b.0[0], a.0[1] / b.0[1], a.0[2] / b.0[2]]) });
        )+
    };
    (4: [$($type:path),+]) => {
        $(
            ops_impl_bin!(|a: &$type, b: &$type| -> $type,
                    + { $type ([a.0[0] + b.0[0], a.0[1] + b.0[1], a.0[2] + b.0[2], a.0[3] + b.0[3]]) }
                    - { $type ([a.0[0] - b.0[0], a.0[1] - b.0[1], a.0[2] - b.0[2], a.0[3] - b.0[3]]) }
                    * { $type ([a.0[0] * b.0[0], a.0[1] * b.0[1], a.0[2] * b.0[2], a.0[3] * b.0[3]]) }
                    / { $type ([a.0[0] / b.0[0], a.0[1] / b.0[1], a.0[2] / b.0[2], a.0[3] / b.0[3]]) });
        )+
    };
}

vec_impl!(1: [Vec<u8, 1>, Vec<u16, 1>, Vec<u32, 1>, Vec<u64, 1>, Vec<u128, 1>]);
vec_impl!(1: [Vec<i8, 1>, Vec<i16, 1>, Vec<i32, 1>, Vec<i64, 1>, Vec<i128, 1>]);
vec_impl!(1: [Vec<f32, 1>, Vec<f64, 1>]);

vec_impl!(2: [Vec<u8, 2>, Vec<u16, 2>, Vec<u32, 2>, Vec<u64, 2>, Vec<u128, 2>]);
vec_impl!(2: [Vec<i8, 2>, Vec<i16, 2>, Vec<i32, 2>, Vec<i64, 2>, Vec<i128, 2>]);
vec_impl!(2: [Vec<f32, 2>, Vec<f64, 2>]);

vec_impl!(3: [Vec<u8, 3>, Vec<u16, 3>, Vec<u32, 3>, Vec<u64, 3>, Vec<u128, 3>]);
vec_impl!(3: [Vec<i8, 3>, Vec<i16, 3>, Vec<i32, 3>, Vec<i64, 3>, Vec<i128, 3>]);
vec_impl!(3: [Vec<f32, 3>, Vec<f64, 3>]);

vec_impl!(4: [Vec<u8, 4>, Vec<u16, 4>, Vec<u32, 4>, Vec<u64, 4>, Vec<u128, 4>]);
vec_impl!(4: [Vec<i8, 4>, Vec<i16, 4>, Vec<i32, 4>, Vec<i64, 4>, Vec<i128, 4>]);
vec_impl!(4: [Vec<f32, 4>, Vec<f64, 4>]);

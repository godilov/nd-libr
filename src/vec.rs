use crate::{num::Number, ops_impl_bin};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Vec<N: Number, const L: usize>(pub [N; L]);

impl<N: Number, const L: usize> Default for Vec<N, L> {
    fn default() -> Self {
        Vec::<N, L>([N::default(); L])
    }
}

macro_rules! vec_ops_arr {
    (8: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(7: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (7: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(6: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (6: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(5: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (5: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(4: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (4: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(3: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (3: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(2: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (2: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(1: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (1: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { vec_ops_arr!(0: ($a) $op ($b) [$ind + 1] -> [$($body)* $a[$ind] $op $b[$ind],]) };
    (0: ($a:expr) $op:tt ($b:expr) [$ind:expr] -> [$($body:tt)*]) => { [$($body)*] };
}

// TODO: Make scalar version of vec_ops_arr

macro_rules! vec_ops_impl {
    (+ $n:tt: [$($type:path),+]) => {
        $(
            ops_impl_bin!(|a: &$type, b: &$type| -> $type,
                    + { $type (vec_ops_arr!($n: (a.0) + (b.0) [0] -> [])) }
                    - { $type (vec_ops_arr!($n: (a.0) - (b.0) [0] -> [])) }
                    * { $type (vec_ops_arr!($n: (a.0) * (b.0) [0] -> [])) }
                    / { $type (vec_ops_arr!($n: (a.0) / (b.0) [0] -> [])) }
                    % { $type (vec_ops_arr!($n: (a.0) % (b.0) [0] -> [])) }
                    | { $type (vec_ops_arr!($n: (a.0) | (b.0) [0] -> [])) }
                    & { $type (vec_ops_arr!($n: (a.0) & (b.0) [0] -> [])) }
                    ^ { $type (vec_ops_arr!($n: (a.0) ^ (b.0) [0] -> [])) }
                    << { $type (vec_ops_arr!($n: (a.0) << (b.0) [0] -> [])) }
                    >> { $type (vec_ops_arr!($n: (a.0) >> (b.0) [0] -> [])) });
        )+
    };
    ($n:tt: [$($type:path),+]) => {
        $(
            ops_impl_bin!(|a: &$type, b: &$type| -> $type,
                    + { $type (vec_ops_arr!($n: (a.0) + (b.0) [0] -> [])) }
                    - { $type (vec_ops_arr!($n: (a.0) - (b.0) [0] -> [])) }
                    * { $type (vec_ops_arr!($n: (a.0) * (b.0) [0] -> [])) }
                    / { $type (vec_ops_arr!($n: (a.0) / (b.0) [0] -> [])) }
                    % { $type (vec_ops_arr!($n: (a.0) % (b.0) [0] -> [])) });
        )+
    };
}

#[cfg(not(target_feature = "avx2"))]
mod std_impl {
    use super::*;

    vec_ops_impl!(+ 1: [Vec<u8, 1>, Vec<u16, 1>, Vec<u32, 1>, Vec<u64, 1>, Vec<u128, 1>]);
    vec_ops_impl!(+ 1: [Vec<i8, 1>, Vec<i16, 1>, Vec<i32, 1>, Vec<i64, 1>, Vec<i128, 1>]);
    vec_ops_impl!(1: [Vec<f32, 1>, Vec<f64, 1>]);

    vec_ops_impl!(+ 2: [Vec<u8, 2>, Vec<u16, 2>, Vec<u32, 2>, Vec<u64, 2>, Vec<u128, 2>]);
    vec_ops_impl!(+ 2: [Vec<i8, 2>, Vec<i16, 2>, Vec<i32, 2>, Vec<i64, 2>, Vec<i128, 2>]);
    vec_ops_impl!(2: [Vec<f32, 2>, Vec<f64, 2>]);

    vec_ops_impl!(+ 3: [Vec<u8, 3>, Vec<u16, 3>, Vec<u32, 3>, Vec<u64, 3>, Vec<u128, 3>]);
    vec_ops_impl!(+ 3: [Vec<i8, 3>, Vec<i16, 3>, Vec<i32, 3>, Vec<i64, 3>, Vec<i128, 3>]);
    vec_ops_impl!(3: [Vec<f32, 3>, Vec<f64, 3>]);

    vec_ops_impl!(+ 4: [Vec<u8, 4>, Vec<u16, 4>, Vec<u32, 4>, Vec<u64, 4>, Vec<u128, 4>]);
    vec_ops_impl!(+ 4: [Vec<i8, 4>, Vec<i16, 4>, Vec<i32, 4>, Vec<i64, 4>, Vec<i128, 4>]);
    vec_ops_impl!(4: [Vec<f32, 4>, Vec<f64, 4>]);

    vec_ops_impl!(+ 5: [Vec<u8, 5>, Vec<u16, 5>, Vec<u32, 5>, Vec<u64, 5>, Vec<u128, 5>]);
    vec_ops_impl!(+ 5: [Vec<i8, 5>, Vec<i16, 5>, Vec<i32, 5>, Vec<i64, 5>, Vec<i128, 5>]);
    vec_ops_impl!(5: [Vec<f32, 5>, Vec<f64, 5>]);

    vec_ops_impl!(+ 6: [Vec<u8, 6>, Vec<u16, 6>, Vec<u32, 6>, Vec<u64, 6>, Vec<u128, 6>]);
    vec_ops_impl!(+ 6: [Vec<i8, 6>, Vec<i16, 6>, Vec<i32, 6>, Vec<i64, 6>, Vec<i128, 6>]);
    vec_ops_impl!(6: [Vec<f32, 6>, Vec<f64, 6>]);

    vec_ops_impl!(+ 7: [Vec<u8, 7>, Vec<u16, 7>, Vec<u32, 7>, Vec<u64, 7>, Vec<u128, 7>]);
    vec_ops_impl!(+ 7: [Vec<i8, 7>, Vec<i16, 7>, Vec<i32, 7>, Vec<i64, 7>, Vec<i128, 7>]);
    vec_ops_impl!(7: [Vec<f32, 7>, Vec<f64, 7>]);

    vec_ops_impl!(+ 8: [Vec<u8, 8>, Vec<u16, 8>, Vec<u32, 8>, Vec<u64, 8>, Vec<u128, 8>]);
    vec_ops_impl!(+ 8: [Vec<i8, 8>, Vec<i16, 8>, Vec<i32, 8>, Vec<i64, 8>, Vec<i128, 8>]);
    vec_ops_impl!(8: [Vec<f32, 8>, Vec<f64, 8>]);
}

#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    target_feature = "avx2"
))]
mod avx_impl {
    #[cfg(target_arch = "x86")] use std::arch::x86::*;
    #[cfg(target_arch = "x86_64")] use std::arch::x86_64::*;

    use super::*;

    vec_ops_impl!(+ 1: [Vec<u8, 1>, Vec<u16, 1>, Vec<u32, 1>, Vec<u64, 1>, Vec<u128, 1>]);
    vec_ops_impl!(+ 1: [Vec<i8, 1>, Vec<i16, 1>, Vec<i32, 1>, Vec<i64, 1>, Vec<i128, 1>]);
    vec_ops_impl!(1: [Vec<f32, 1>, Vec<f64, 1>]);

    vec_ops_impl!(+ 2: [Vec<u8, 2>, Vec<u16, 2>, Vec<u32, 2>, /* Vec<u64, 2>,*/ Vec<u128, 2>]);
    vec_ops_impl!(+ 2: [Vec<i8, 2>, Vec<i16, 2>, Vec<i32, 2>, /* Vec<i64, 2>,*/ Vec<i128, 2>]);
    vec_ops_impl!(2: [Vec<f32, 2>, Vec<f64, 2>]);

    vec_ops_impl!(+ 3: [Vec<u8, 3>, Vec<u16, 3>, Vec<u32, 3>, Vec<u64, 3>, Vec<u128, 3>]);
    vec_ops_impl!(+ 3: [Vec<i8, 3>, Vec<i16, 3>, Vec<i32, 3>, Vec<i64, 3>, Vec<i128, 3>]);
    vec_ops_impl!(3: [Vec<f32, 3>, Vec<f64, 3>]);

    vec_ops_impl!(+ 4: [Vec<u8, 4>, Vec<u16, 4>, Vec<u32, 4>, Vec<u64, 4>, Vec<u128, 4>]);
    vec_ops_impl!(+ 4: [Vec<i8, 4>, Vec<i16, 4>, Vec<i32, 4>, Vec<i64, 4>, Vec<i128, 4>]);
    vec_ops_impl!(4: [Vec<f32, 4>, Vec<f64, 4>]);

    vec_ops_impl!(+ 5: [Vec<u8, 5>, Vec<u16, 5>, Vec<u32, 5>, Vec<u64, 5>, Vec<u128, 5>]);
    vec_ops_impl!(+ 5: [Vec<i8, 5>, Vec<i16, 5>, Vec<i32, 5>, Vec<i64, 5>, Vec<i128, 5>]);
    vec_ops_impl!(5: [Vec<f32, 5>, Vec<f64, 5>]);

    vec_ops_impl!(+ 6: [Vec<u8, 6>, Vec<u16, 6>, Vec<u32, 6>, Vec<u64, 6>, Vec<u128, 6>]);
    vec_ops_impl!(+ 6: [Vec<i8, 6>, Vec<i16, 6>, Vec<i32, 6>, Vec<i64, 6>, Vec<i128, 6>]);
    vec_ops_impl!(6: [Vec<f32, 6>, Vec<f64, 6>]);

    vec_ops_impl!(+ 7: [Vec<u8, 7>, Vec<u16, 7>, Vec<u32, 7>, Vec<u64, 7>, Vec<u128, 7>]);
    vec_ops_impl!(+ 7: [Vec<i8, 7>, Vec<i16, 7>, Vec<i32, 7>, Vec<i64, 7>, Vec<i128, 7>]);
    vec_ops_impl!(7: [Vec<f32, 7>, Vec<f64, 7>]);

    vec_ops_impl!(+ 8: [Vec<u8, 8>, Vec<u16, 8>, Vec<u32, 8>, Vec<u64, 8>, Vec<u128, 8>]);
    vec_ops_impl!(+ 8: [Vec<i8, 8>, Vec<i16, 8>, Vec<i32, 8>, Vec<i64, 8>, Vec<i128, 8>]);
    vec_ops_impl!(8: [Vec<f32, 8>, Vec<f64, 8>]);

    ops_impl_bin!(|a: &Vec<u64, 2>, b: &Vec<u64, 2>| -> Vec<u64, 2>,
    + {
        unsafe {
            let a_vec = _mm_set_epi64x(a.0[0] as i64, a.0[1] as i64);
            let b_vec = _mm_set_epi64x(b.0[0] as i64, b.0[1] as i64);

            let vec = _mm_add_epi64(a_vec, b_vec);

            Vec::<u64, 2>([
                _mm_extract_epi64::<0>(vec) as u64,
                _mm_extract_epi64::<1>(vec) as u64,
            ])
        }
    }
    - {
        unsafe {
            let a_vec = _mm_set_epi64x(a.0[0] as i64, a.0[1] as i64);
            let b_vec = _mm_set_epi64x(b.0[0] as i64, b.0[1] as i64);

            let vec = _mm_sub_epi64(a_vec, b_vec);

            Vec::<u64, 2>([
                _mm_extract_epi64::<0>(vec) as u64,
                _mm_extract_epi64::<1>(vec) as u64,
            ])
        }
    }
    * {
        Vec::<u64, 2>([a.0[0] * b.0[0], a.0[1] * b.0[1]])
    }
    / {
        Vec::<u64, 2>([a.0[0] / b.0[0], a.0[1] / b.0[1]])
    }
    % {
        Vec::<u64, 2>([a.0[0] % b.0[0], a.0[1] % b.0[1]])
    });

    ops_impl_bin!(|a: &Vec<i64, 2>, b: &Vec<i64, 2>| -> Vec<i64, 2>,
    + {
        unsafe {
            let a_vec = _mm_set_epi64x(a.0[0], a.0[1]);
            let b_vec = _mm_set_epi64x(b.0[0], b.0[1]);

            let vec = _mm_add_epi64(a_vec, b_vec);

            Vec::<i64, 2>([
                _mm_extract_epi64::<0>(vec),
                _mm_extract_epi64::<1>(vec),
            ])
        }
    }
    - {
        unsafe {
            let a_vec = _mm_set_epi64x(a.0[0], a.0[1]);
            let b_vec = _mm_set_epi64x(b.0[0], b.0[1]);

            let vec = _mm_sub_epi64(a_vec, b_vec);

            Vec::<i64, 2>([
                _mm_extract_epi64::<0>(vec),
                _mm_extract_epi64::<1>(vec),
            ])
        }
    }
    * {
        Vec::<i64, 2>([a.0[0] * b.0[0], a.0[1] * b.0[1]])
    }
    / {
        Vec::<i64, 2>([a.0[0] / b.0[0], a.0[1] / b.0[1]])
    }
    % {
        Vec::<i64, 2>([a.0[0] % b.0[0], a.0[1] % b.0[1]])
    });
}

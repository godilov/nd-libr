use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ndlib::{
    num::*,
    ops::{Ops, OpsFrom},
    signed_fixed, unsigned_fixed,
};

const PRIMES: [u64; 5] = [
    29_996_224_275_833,
    29_996_224_275_821,
    29_996_224_275_791,
    29_996_224_275_781,
    15_485_863,
];

type S64 = signed_fixed!(64);
type U64 = unsigned_fixed!(64);

macro_rules! composite {
    ($type:ty, [$idx:expr, $($tail:expr),+]) => {
        (<$type>::from(PRIMES[$idx]) * composite!($type, [$($tail),+]))
    };
    ($type:ty, [$idx:expr]) => {
        <$type>::from(PRIMES[$idx])
    };
}

#[allow(unused)]
fn composite<T: From<u64> + Ops + OpsFrom>(arr: &[u64]) -> T {
    arr.iter().fold(T::from(1), |acc, &x| T::from(acc * T::from(x)))
}

macro_rules! impl_case {
    ($group:expr, $type:ty, $name:expr, [$($idx1:expr),+], [$($idx2:expr),+], [$op:tt]) => {
        let val1 = &composite!($type, [$($idx1),+]);
        let val2 = &composite!($type, [$($idx2),+]);

        $group.bench_function(format!("{} {}", stringify!($type), $name), |b| b.iter_with_large_drop(|| black_box(val1 $op val2)));
    };
    ($fn:ident, $name:literal, $group:literal, [$($type:ty: [$($idx1:expr),+], [$($idx2:expr),+]),+], [$op:tt]) => {
        fn $fn(c: &mut Criterion) {
            let mut group = c.benchmark_group($group);

            group.sample_size(256);

            $(impl_case!(group, $type, $name, [$($idx1),+], [$($idx2),+], [$op]);)+
        }
    };
}

impl_case!(add,     "Add", "Num", [SignedLong: [0, 1], [2, 3], UnsignedLong: [0, 1], [2, 3], S64: [0, 1], [2, 3], U64: [0, 1], [2, 3]], [+]);
impl_case!(sub,     "Sub", "Num", [SignedLong: [0, 1], [2, 3], UnsignedLong: [0, 1], [2, 3], S64: [0, 1], [2, 3], U64: [0, 1], [2, 3]], [-]);
impl_case!(mul,     "Mul", "Num", [SignedLong: [0, 1], [2, 3], UnsignedLong: [0, 1], [2, 3], S64: [0, 1], [2, 3], U64: [0, 1], [2, 3]], [*]);
impl_case!(div,     "Div", "Num", [SignedLong: [0, 1], [4, 4], UnsignedLong: [0, 1], [4, 4], S64: [0, 1], [4, 4], U64: [0, 1], [4, 4]], [/]);
impl_case!(bitor,   "Or",  "Num", [SignedLong: [0, 1], [2, 3], UnsignedLong: [0, 1], [2, 3], S64: [0, 1], [2, 3], U64: [0, 1], [2, 3]], [|]);
impl_case!(bitand,  "And", "Num", [SignedLong: [0, 1], [2, 3], UnsignedLong: [0, 1], [2, 3], S64: [0, 1], [2, 3], U64: [0, 1], [2, 3]], [&]);
impl_case!(bitxor,  "Xor", "Num", [SignedLong: [0, 1], [2, 3], UnsignedLong: [0, 1], [2, 3], S64: [0, 1], [2, 3], U64: [0, 1], [2, 3]], [^]);

criterion_group!(group, add, sub, mul, div, bitor, bitand, bitxor,);

criterion_main!(group);

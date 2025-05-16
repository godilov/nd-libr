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

fn composite<T: From<u64> + Ops + OpsFrom, Iter: IntoIterator<Item = u64>>(init: T, iter: Iter) -> T {
    iter.into_iter().fold(init, |acc, x| T::from(acc * T::from(x)))
}

macro_rules! impl_case {
    ($fn:ident, $name:literal, $group:literal, [$($type:ty),+], [$($idx1:expr),+], [$($idx2:expr),+], [$op:tt]) => {
        fn $fn(c: &mut Criterion) {
            let mut group = c.benchmark_group($group);

            group.sample_size(256);

            let primes1 = [$($idx1),+].into_iter().map(|idx| PRIMES[idx]);
            let primes2 = [$($idx2),+].into_iter().map(|idx| PRIMES[idx]);

            $({
                let val1 = &composite(<$type>::from(1u64), primes1.clone());
                let val2 = &composite(<$type>::from(1u64), primes2.clone());

                group.bench_function(format!("{} {}", stringify!($type), $name), |b| b.iter_with_large_drop(|| black_box(val1 $op val2)));
            })+
        }
    };
}

impl_case!(add,     "Add", "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [2, 3], [+]);
impl_case!(sub,     "Sub", "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [2, 3], [-]);
impl_case!(mul,     "Mul", "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [2, 3], [*]);
impl_case!(div,     "Div", "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [4, 4], [/]);
impl_case!(bitor,   "Or",  "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [2, 3], [|]);
impl_case!(bitand,  "And", "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [2, 3], [&]);
impl_case!(bitxor,  "Xor", "Num", [SignedLong, UnsignedLong, S64, U64], [0, 1], [2, 3], [^]);

criterion_group!(group, add, sub, mul, div, bitor, bitand, bitxor,);

criterion_main!(group);

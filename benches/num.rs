use criterion::{Criterion, black_box, criterion_group, criterion_main};
use ndlibr::{num::*, signed_fixed, unsigned_fixed};

const PRIMES: [u64; 5] = [
    29_996_224_275_833,
    29_996_224_275_821,
    29_996_224_275_791,
    29_996_224_275_781,
    15_485_863,
];

type S64 = signed_fixed!(64);
type U64 = unsigned_fixed!(64);

macro_rules! impl_case {
    ($fn:ident, $name:literal, $group:literal, $signed:ty, $unsigned:ty, [$i0:expr, $i1:expr, $i2:expr, $i3:expr], [$op:tt]) => {
        fn $fn(c: &mut Criterion) {
            let mut group = c.benchmark_group($group);

            group.sample_size(256);

            let signed_a = &(<$signed>::from(PRIMES[$i0]) * <$signed>::from(PRIMES[$i1]));
            let signed_b = &(<$signed>::from(PRIMES[$i2]) * <$signed>::from(PRIMES[$i3]));
            let unsigned_a = &(<$unsigned>::from(PRIMES[$i0]) * <$unsigned>::from(PRIMES[$i1]));
            let unsigned_b = &(<$unsigned>::from(PRIMES[$i2]) * <$unsigned>::from(PRIMES[$i3]));

            group.bench_function(format!("Signed {}", $name), |b| b.iter_with_large_drop(|| black_box(signed_a $op signed_b)));
            group.bench_function(format!("Unsigned {}", $name), |b| b.iter_with_large_drop(|| black_box(unsigned_a $op unsigned_b)));
        }
    };
}

impl_case!(add_long, "Add", "Longs", SignedLong, UnsignedLong, [0, 1, 2, 3], [+]);
impl_case!(sub_long, "Sub", "Longs", SignedLong, UnsignedLong, [0, 1, 2, 3], [-]);
impl_case!(mul_long, "Mul", "Longs", SignedLong, UnsignedLong, [0, 1, 2, 3], [*]);
impl_case!(div_long, "Div", "Longs", SignedLong, UnsignedLong, [0, 1, 4, 4], [/]);

impl_case!(add_fixed, "Add", "Fixed", S64, U64, [0, 1, 2, 3], [+]);
impl_case!(sub_fixed, "Sub", "Fixed", S64, U64, [0, 1, 2, 3], [-]);
impl_case!(mul_fixed, "Mul", "Fixed", S64, U64, [0, 1, 2, 3], [*]);
impl_case!(div_fixed, "Div", "Fixed", S64, U64, [0, 1, 4, 4], [/]);

criterion_group!(
    group, add_long, add_fixed, sub_long, sub_fixed, mul_long, mul_fixed, div_long, div_fixed
);

criterion_main!(group);

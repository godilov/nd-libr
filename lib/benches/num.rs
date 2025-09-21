use criterion::{Criterion, criterion_group, criterion_main};
use ndlib::{num::*, ops::*};
use std::{hint::black_box, time::Duration};

const PRIMES: [u64; 128] = [
    4292660621, 4292200421, 4274510453, 4273041679, 4268636153, 4199694749, 4187101291, 4172993729, 4132644721,
    4130742871, 4124827129, 4096342937, 4090601951, 4085747891, 4076510839, 4067541383, 4044350953, 3987288157,
    3985877521, 3984388871, 3977475763, 3974498197, 3974413831, 3962297863, 3941931089, 3931855493, 3930391987,
    3886837421, 3859565023, 3849536917, 3846256441, 3845038229, 3842529637, 3841579349, 3833893331, 3802103633,
    3799959671, 3779787749, 3720289933, 3697521383, 3633571897, 3627880951, 3627856019, 3593653249, 3560729231,
    3553488781, 3528270223, 3527446789, 3523236919, 3520342489, 3502411489, 3488032937, 3470411513, 3458207083,
    3457424039, 3445058833, 3431745271, 3392868547, 3368501743, 3363788501, 3351474677, 3345030697, 3330690373,
    3327423751, 3298061981, 3261870713, 3231209953, 3223797097, 3196733803, 3192230837, 3186501193, 3172273087,
    3113993567, 3112884391, 3093151403, 3063333907, 3062288627, 3050851061, 3038370737, 3034290521, 2993428673,
    2970970631, 2901039397, 2896187131, 2852510783, 2837908543, 2834220581, 2814481297, 2795544863, 2794499177,
    2789564599, 2784634477, 2770108139, 2763622949, 2744171039, 2711784941, 2694302099, 2671881827, 2661444397,
    2651203649, 2641091963, 2639870213, 2631062261, 2617453259, 2599949743, 2546088539, 2527921003, 2511921869,
    2494531129, 2479273411, 2475741131, 2435835313, 2417182837, 2399042783, 2382368081, 2374547509, 2360864237,
    2349724049, 2342014889, 2286167677, 2260374353, 2232170173, 2219637313, 2217298813, 2205500513, 2202423991,
    2179519291, 2179381573,
];

fn composite<T: From<u64> + Ops + OpsFrom, Iter: IntoIterator<Item = u64>>(init: T, iter: Iter) -> T {
    iter.into_iter().fold(init, |acc, x| T::from(acc * T::from(x)))
}

#[allow(unused_macros)]
macro_rules! fn_impl {
    ($fn:ident, $primes:expr, [$($type:ty),+], ($($args:tt)+)) => {
        fn $fn(c: &mut Criterion) {
            let mut group = c.benchmark_group(format!("num::{}", stringify!($fn)));

            group.sample_size(512);
            group.measurement_time(Duration::from_secs(10));
            group.warm_up_time(Duration::from_secs(5));

            $({
                group.bench_function(stringify!($type), |b| b.iter_with_large_drop(|| $type::$fn($($args)+)));
            })+
        }
    };
}

macro_rules! ops_impl {
    ($fn:ident, $primes1:expr, $primes2:expr, [$($type:ty),+], [$op:tt]) => {
        fn $fn(c: &mut Criterion) {
            let mut group = c.benchmark_group(format!("num::{}", stringify!($fn)));

            group.sample_size(512);
            group.measurement_time(Duration::from_secs(10));
            group.warm_up_time(Duration::from_secs(5));

            $({
                let op1 = composite(<$type>::from(1u64), $primes1);
                let op2 = composite(<$type>::from(1u64), $primes2);

                group.bench_function(stringify!($type), |b| b.iter_with_large_drop(|| black_box(&op1 $op &op2)));
            })+
        }
    };
}

macro_rules! ops_mut_impl {
    ($fn:ident, $primes1:expr, $primes2:expr, [$($type:ty),+], [$op:tt]) => {
        fn $fn(c: &mut Criterion) {
            let mut group = c.benchmark_group(format!("num::{}", stringify!($fn)));

            group.sample_size(512);
            group.measurement_time(Duration::from_secs(10));
            group.warm_up_time(Duration::from_secs(5));

            $({
                let mut val = composite(<$type>::from(1u64), $primes1);
                let operand = composite(<$type>::from(1u64), $primes2);

                group.bench_function(stringify!($type), |b| b.iter_with_large_drop(|| black_box(val $op &operand)));
            })+
        }
    };
}

ops_impl!(bitor,  PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [|]);
ops_impl!(bitand, PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [&]);
ops_impl!(bitxor, PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [^]);
ops_impl!(add,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [+]);
ops_impl!(sub,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [-]);
ops_impl!(mul,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S4096, U4096], [*]);
ops_impl!(div,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(4), [SignedLong, UnsignedLong, S2048, U2048], [/]);
ops_impl!(rem,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(4), [SignedLong, UnsignedLong, S2048, U2048], [%]);

ops_mut_impl!(bitor_mut,  PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [|=]);
ops_mut_impl!(bitand_mut, PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [&=]);
ops_mut_impl!(bitxor_mut, PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [^=]);
ops_mut_impl!(add_mut,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [+=]);
ops_mut_impl!(sub_mut,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S2048, U2048], [-=]);
ops_mut_impl!(mul_mut,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(2), [SignedLong, UnsignedLong, S4096, U4096], [*=]);
ops_mut_impl!(div_mut,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(4), [SignedLong, UnsignedLong, S2048, U2048], [/=]);
ops_mut_impl!(rem_mut,    PRIMES.iter().copied().step_by(2), PRIMES.iter().copied().skip(1).step_by(4), [SignedLong, UnsignedLong, S2048, U2048], [%=]);

criterion_group!(
    group, bitor, bitand, bitxor, add, sub, mul, div, rem, bitor_mut, bitand_mut, bitxor_mut, add_mut, sub_mut,
    mul_mut, div_mut, rem_mut,
);

criterion_main!(group);

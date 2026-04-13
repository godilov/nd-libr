//! # NdNumbers Long Benchmarks

use std::{str::FromStr, time::Duration};

use criterion::{
    BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main, measurement::WallTime,
};
use ndext::{convert::NdFrom, iter::IteratorExt};
use ndnum::{
    arch::Aligned,
    long::{
        ExpImpl, FromDigits, FromDigitsIter, IntoDigits, IntoDigitsIter, RadixImpl, ToDigits, ToDigitsIter,
        alias::{S4096, U4096},
    },
};
use rand::{RngExt, SeedableRng, rngs::StdRng};

const BITS: usize = std::mem::size_of::<U4096>() * 8;
const BYTES: usize = std::mem::size_of::<U4096>();
const PRIMES: [u64; 256] = [
    4291027133, 4288645421, 4286658479, 4286277323, 4284652657, 4283538983, 4282629761, 4279952009, 4274667043,
    4273974833, 4273382713, 4273199423, 4271705111, 4269969103, 4267926137, 4264085099, 4260878903, 4250977573,
    4250544959, 4246633649, 4246225493, 4241016077, 4240409711, 4237616501, 4234796389, 4232038339, 4230842009,
    4228079201, 4227614197, 4227213311, 4225275629, 4225014113, 4221426721, 4220500577, 4219434941, 4218877001,
    4217345917, 4214550283, 4211609429, 4211255369, 4203338233, 4202393023, 4199414509, 4198391947, 4197917419,
    4195822639, 4194402463, 4193518727, 4193157901, 4192159453, 4190809123, 4189681667, 4189520011, 4184333143,
    4179988061, 4177791907, 4176225421, 4174304191, 4169576387, 4167088327, 4164956267, 4163757461, 4162487471,
    4162433399, 4155280279, 4150850629, 4148495951, 4145409817, 4138918543, 4137629401, 4133472467, 4133143517,
    4127601791, 4127098379, 4125320897, 4119782671, 4119373777, 4116266897, 4114623391, 4114472227, 4113890243,
    4111216891, 4109928997, 4109554039, 4109437207, 4108660727, 4107543707, 4106668243, 4105198541, 4105145813,
    4104117547, 4099837199, 4098839399, 4090206881, 4082027251, 4079830631, 4076616491, 4074749527, 4073026987,
    4071996911, 4070606233, 4066189459, 4065919373, 4065869267, 4063186871, 4063001029, 4061437231, 4059829259,
    4057638779, 4057275149, 4056418217, 4053585509, 4052870243, 4052599567, 4051497707, 4047151763, 4043976113,
    4042149173, 4041819269, 4041425813, 4040864543, 4039822667, 4039596097, 4039371031, 4035933571, 4033269781,
    4030479209, 4028641571, 4027898323, 4020387907, 4020030439, 4016741693, 4015950373, 4010856151, 4010296321,
    4002768037, 4000083449, 3999337283, 3997631017, 3996904841, 3996239141, 3996231691, 3992282039, 3987042797,
    3985983493, 3984804251, 3981815993, 3980466067, 3979889761, 3977832437, 3976960177, 3974003959, 3973445087,
    3973437203, 3968773213, 3962255579, 3957508111, 3957446489, 3956151779, 3952554677, 3951771697, 3947962379,
    3947501713, 3945941407, 3945351733, 3938538553, 3937546231, 3931024621, 3928229521, 3926863777, 3925637923,
    3925630507, 3923116777, 3921916253, 3919193689, 3916272853, 3914476991, 3912733997, 3910894367, 3907467139,
    3905300699, 3903981637, 3903682789, 3903271391, 3902937593, 3902828141, 3900926717, 3899612911, 3898914809,
    3898690583, 3898266287, 3896687647, 3891151669, 3886099913, 3883701053, 3881347523, 3878793059, 3878626681,
    3876610021, 3875194231, 3870033113, 3864981817, 3859776643, 3858790703, 3853233091, 3851530411, 3850745009,
    3848951783, 3847673267, 3847541281, 3846909431, 3842810089, 3841784171, 3838278371, 3837915259, 3836192699,
    3834913189, 3834523711, 3831062129, 3829455317, 3827098747, 3826617997, 3825651871, 3822335971, 3822335071,
    3821576197, 3818361251, 3812111291, 3809103677, 3805474583, 3803465189, 3802681997, 3802458763, 3800685443,
    3800597261, 3800356489, 3789314803, 3788974997, 3785898461, 3780274999, 3778847507, 3775274857, 3773356493,
    3772649183, 3772244719, 3769968233, 3766850509, 3766527131, 3764376043, 3760497227, 3760053289, 3752964403,
    3751605971, 3750696997, 3742971191, 3742425377,
];

macro_rules! composite {
    ($long:ty, $primitive:ty, $skip:expr, $step:expr) => {
        PRIMES
            .iter()
            .copied()
            .skip($skip)
            .step_by($step)
            .fold(<$long>::from(1 as $primitive), |acc, x| <$long>::from(acc * x as $primitive))
    };
}

macro_rules! exec {
    ($group:expr => [$($id:expr, $args:expr, $fn:expr),* $(,)?]) => {
        $(exec!($group => $id, $args, $fn);)*
    };
    ($group:expr => $id:expr, $args:expr, $fn:expr $(,)?) => {
        $group.bench_with_input($id, $args, |b, args| {
            b.iter(|| ($fn)(args))
        });
    };
}

macro_rules! from_arr_impl {
    ($group:expr, $rng:expr, $shr:expr) => {
        let len = BYTES >> $shr;
        let bytes = $rng.random::<[u8; BYTES]>();
        let bytes = match <[u8; BYTES >> $shr]>::try_from(&bytes[..len]) {
            Ok(val) => val,
            Err(_) => return,
        };

        $group.throughput(Throughput::Bytes(len as u64));

        $group.bench_with_input(BenchmarkId::new("S4096::from_arr", 8 * len), &bytes, |b, bytes| {
            b.iter(|| Aligned(S4096::nd_from(bytes)))
        });

        $group.bench_with_input(BenchmarkId::new("U4096::from_arr", 8 * len), &bytes, |b, bytes| {
            b.iter(|| Aligned(U4096::nd_from(bytes)))
        });
    };
}

fn long_convert(c: &mut Criterion) {
    let mut group = c.benchmark_group("long::convert");
    let mut rng = StdRng::seed_from_u64(PRIMES[0] * PRIMES[1]);

    group.sample_size(128);
    group.measurement_time(Duration::from_secs(6));
    group.warm_up_time(Duration::from_secs(2));

    default(&mut group);
    from_primitive_const(&mut group);
    from_bytes_const(&mut group);
    from_primitive(&mut group, &mut rng);
    from_bytes(&mut group, &mut rng);
    from_arr(&mut group, &mut rng);
    from_slice(&mut group, &mut rng);
    from_iter(&mut group, &mut rng);
    from_digits(&mut group, &mut rng);
    from_digits_iter(&mut group, &mut rng);
    from_digits_radix(&mut group, &mut rng);
    from_digits_radix_iter(&mut group, &mut rng);
    to_digits(&mut group, &mut rng);
    to_digits_iter_count(&mut group, &mut rng);
    to_digits_iter_collect(&mut group, &mut rng);
    into_digits(&mut group, &mut rng);
    into_digits_iter_count(&mut group, &mut rng);
    into_digits_iter_collect(&mut group, &mut rng);
    from_str(&mut group, &mut rng);
    to_str(&mut group, &mut rng);
}

fn long_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("long::ops");

    group.sample_size(128);
    group.measurement_time(Duration::from_secs(6));
    group.warm_up_time(Duration::from_secs(2));

    ops(&mut group);
    ops_mut(&mut group);
    ops_single(&mut group);
    ops_single_mut(&mut group);
}

fn long_uops(c: &mut Criterion) {
    let mut group = c.benchmark_group("long::uops");

    group.sample_size(128);
    group.measurement_time(Duration::from_secs(6));
    group.warm_up_time(Duration::from_secs(2));

    uops(&mut group);
    uops_mut(&mut group);
}

fn default(group: &mut BenchmarkGroup<'_, WallTime>) {
    group.throughput(Throughput::Bits(BITS as u64));

    group.bench_function("S4096::default", |b| b.iter(|| Aligned(S4096::default())));
    group.bench_function("U4096::default", |b| b.iter(|| Aligned(U4096::default())));
}

fn from_primitive_const(group: &mut BenchmarkGroup<'_, WallTime>) {
    const I128: i128 = 116578228889707554089617590980330937198_i128;
    const U128: u128 = 121940457858715132528838202027877031762_u128;

    group.throughput(Throughput::Bits(128));

    group.bench_function("S4096::from_primitive_const", |b| {
        b.iter(|| const { Aligned(S4096::from_i128(I128)) })
    });

    group.bench_function("U4096::from_primitive_const", |b| {
        b.iter(|| const { Aligned(U4096::from_u128(U128)) })
    });
}

fn from_bytes_const(group: &mut BenchmarkGroup<'_, WallTime>) {
    const I128: [u8; 16] = 116578228889707554089617590980330937198_i128.to_le_bytes();
    const U128: [u8; 16] = 121940457858715132528838202027877031762_u128.to_le_bytes();

    group.throughput(Throughput::Bits(128));

    group.bench_function("S4096::from_bytes_const", |b| {
        b.iter(|| const { Aligned(S4096::from_bytes(&I128)) })
    });

    group.bench_function("U4096::from_bytes_const", |b| {
        b.iter(|| const { Aligned(U4096::from_bytes(&U128)) })
    });
}

fn from_primitive(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    group.throughput(Throughput::Bits(128));

    exec! { group => [
        BenchmarkId::new("S4096::from_primitive", i128::BITS), &rng.random::<i128>(), |&val: &i128| Aligned(S4096::from(val)),
        BenchmarkId::new("U4096::from_primitive", u128::BITS), &rng.random::<u128>(), |&val: &u128| Aligned(U4096::from(val)),
        BenchmarkId::new("S4096::from_primitive",  i64::BITS), &rng.random::<i64>(),  |&val:  &i64| Aligned(S4096::from(val)),
        BenchmarkId::new("U4096::from_primitive",  u64::BITS), &rng.random::<u64>(),  |&val:  &u64| Aligned(U4096::from(val)),
        BenchmarkId::new("S4096::from_primitive",  i32::BITS), &rng.random::<i32>(),  |&val:  &i32| Aligned(S4096::from(val)),
        BenchmarkId::new("U4096::from_primitive",  u32::BITS), &rng.random::<u32>(),  |&val:  &u32| Aligned(U4096::from(val)),
        BenchmarkId::new("S4096::from_primitive",  i16::BITS), &rng.random::<i16>(),  |&val:  &i16| Aligned(S4096::from(val)),
        BenchmarkId::new("U4096::from_primitive",  u16::BITS), &rng.random::<u16>(),  |&val:  &u16| Aligned(U4096::from(val)),
        BenchmarkId::new("S4096::from_primitive",   i8::BITS), &rng.random::<i8>(),   |&val:   &i8| Aligned(S4096::from(val)),
        BenchmarkId::new("U4096::from_primitive",   u8::BITS), &rng.random::<u8>(),   |&val:   &u8| Aligned(U4096::from(val)),
    ] };
}

fn from_bytes(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096::from_bytes", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(S4096::from_bytes(bytes)))
        });

        group.bench_with_input(BenchmarkId::new("U4096::from_bytes", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(U4096::from_bytes(bytes)))
        });
    }
}

fn from_arr(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    from_arr_impl!(group, rng, 4);
    from_arr_impl!(group, rng, 2);
    from_arr_impl!(group, rng, 0);
}

fn from_slice(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096::from_slice", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(S4096::nd_from(bytes)))
        });

        group.bench_with_input(BenchmarkId::new("U4096::from_slice", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(U4096::nd_from(bytes)))
        });
    }
}

fn from_iter(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::from_iter", 8 * len),
            &bytes[..len].iter().copied(),
            |b, iter| b.iter(|| iter.clone().collect::<Aligned<S4096>>()),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::from_iter", 8 * len),
            &bytes[..len].iter().copied(),
            |b, iter| b.iter(|| iter.clone().collect::<Aligned<U4096>>()),
        );
    }
}

fn from_digits(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;

        let exp = 7u8;
        let radix = 1u8 << exp;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::from_digits", 8 * len),
            &(&digits[..len], exp),
            |b, &(digits, exp)| b.iter(|| Aligned(S4096::from_digits(digits, ExpImpl { exp }))),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::from_digits", 8 * len),
            &(&digits[..len], exp),
            |b, &(digits, exp)| b.iter(|| Aligned(U4096::from_digits(digits, ExpImpl { exp }))),
        );
    }
}

fn from_digits_iter(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;

        let exp = 7u8;
        let radix = 1u8 << exp;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::from_digits_iter", 8 * len),
            &(&digits[..len].iter().copied(), exp),
            |b, &(iter, exp)| b.iter(|| Aligned(S4096::from_digits_iter(iter.clone(), ExpImpl { exp }))),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::from_digits_iter", 8 * len),
            &(&digits[..len].iter().copied(), exp),
            |b, &(iter, exp)| b.iter(|| Aligned(U4096::from_digits_iter(iter.clone(), ExpImpl { exp }))),
        );
    }
}

fn from_digits_radix(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;

        let radix = 251u8;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::from_digits_radix", 8 * len),
            &(&digits[..len], radix),
            |b, &(digits, radix)| b.iter(|| Aligned(S4096::from_digits(digits, RadixImpl { radix }))),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::from_digits_radix", 8 * len),
            &(&digits[..len], radix),
            |b, &(digits, radix)| b.iter(|| Aligned(U4096::from_digits(digits, RadixImpl { radix }))),
        );
    }
}

fn from_digits_radix_iter(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;

        let radix = 251u8;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::from_digits_radix_iter", 8 * len),
            &(&digits[..len].iter().copied(), radix),
            |b, &(iter, radix)| b.iter(|| S4096::from_digits_iter(iter.clone(), RadixImpl { radix })),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::from_digits_radix_iter", 8 * len),
            &(&digits[..len].iter().copied(), radix),
            |b, &(iter, radix)| b.iter(|| U4096::from_digits_iter(iter.clone(), RadixImpl { radix })),
        );
    }
}

fn to_digits(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for exp in [7u8, 4u8, 1u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let radix = 1u8 << exp;
        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::to_digits", radix),
            &(&signed, exp),
            |b, &(long, exp)| b.iter(|| long.to_digits(ExpImpl { exp })),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::to_digits", radix),
            &(&unsigned, exp),
            |b, &(long, exp)| b.iter(|| long.to_digits(ExpImpl { exp })),
        );
    }
}

fn to_digits_iter_count(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for exp in [7u8, 4u8, 1u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let radix = 1u8 << exp;
        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::to_digits::count", radix),
            &(&signed, exp),
            |b, &(long, exp)| b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.count())),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::to_digits::count", radix),
            &(&unsigned, exp),
            |b, &(long, exp)| b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.count())),
        );
    }
}

fn to_digits_iter_collect(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for exp in [7u8, 4u8, 1u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let radix = 1u8 << exp;
        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::to_digits::collect", radix),
            &(&signed, exp),
            |b, &(long, exp)| b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.collect::<Vec<u8>>())),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::to_digits::collect", radix),
            &(&unsigned, exp),
            |b, &(long, exp)| b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.collect::<Vec<u8>>())),
        );
    }
}

fn into_digits(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for radix in [255u8, 31u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::into_digits", radix),
            &(&signed, radix),
            |b, &(long, radix)| b.iter(|| long.into_digits(RadixImpl { radix })),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::into_digits", radix),
            &(&unsigned, radix),
            |b, &(long, radix)| b.iter(|| long.into_digits(RadixImpl { radix })),
        );
    }
}

fn into_digits_iter_count(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for radix in [255u8, 31u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::into_digits::count", radix),
            &(&signed, radix),
            |b, &(long, radix)| b.iter(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.count())),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::into_digits::count", radix),
            &(&unsigned, radix),
            |b, &(long, radix)| b.iter(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.count())),
        );
    }
}

fn into_digits_iter_collect(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for radix in [255u8, 31u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096::into_digits::collect", radix),
            &(&signed, radix),
            |b, &(long, radix)| {
                b.iter_with_large_drop(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.collect::<Vec<u8>>()))
            },
        );

        group.bench_with_input(
            BenchmarkId::new("U4096::into_digits::collect", radix),
            &(&unsigned, radix),
            |b, &(long, radix)| {
                b.iter_with_large_drop(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.collect::<Vec<u8>>()))
            },
        );
    }
}

fn from_str(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..len]);
        let unsigned = U4096::nd_from(&bytes[..len]);

        let dec_signed = format!("{:#}", &signed);
        let bin_signed = format!("{:#b}", &signed);
        let oct_signed = format!("{:#o}", &signed);
        let hex_signed = format!("{:#x}", &signed);

        let dec_unsigned = format!("{:#}", &unsigned);
        let bin_unsigned = format!("{:#b}", &unsigned);
        let oct_unsigned = format!("{:#o}", &unsigned);
        let hex_unsigned = format!("{:#x}", &unsigned);

        group.throughput(Throughput::Bytes(dec_signed.len() as u64));
        group.bench_with_input(BenchmarkId::new("S4096::from_str::dec", 8 * len), &dec_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(dec_unsigned.len() as u64));
        group.bench_with_input(BenchmarkId::new("U4096::from_str::dec", 8 * len), &dec_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(bin_signed.len() as u64));
        group.bench_with_input(BenchmarkId::new("S4096::from_str::bin", 8 * len), &bin_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(bin_unsigned.len() as u64));
        group.bench_with_input(BenchmarkId::new("U4096::from_str::bin", 8 * len), &bin_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(oct_signed.len() as u64));
        group.bench_with_input(BenchmarkId::new("S4096::from_str::oct", 8 * len), &oct_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(oct_unsigned.len() as u64));
        group.bench_with_input(BenchmarkId::new("U4096::from_str::oct", 8 * len), &oct_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(hex_signed.len() as u64));
        group.bench_with_input(BenchmarkId::new("S4096::from_str::hex", 8 * len), &hex_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(hex_unsigned.len() as u64));
        group.bench_with_input(BenchmarkId::new("U4096::from_str::hex", 8 * len), &hex_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });
    }
}

fn to_str(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
    for shift in [4, 2, 0] {
        let len = BYTES >> shift;
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..len]);
        let unsigned = U4096::nd_from(&bytes[..len]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096::to_str::dec", 8 * len), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096::to_str::dec", 8 * len), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#}", long))
        });

        group.bench_with_input(BenchmarkId::new("S4096::to_str::bin", 8 * len), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#b}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096::to_str::bin", 8 * len), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#b}", long))
        });

        group.bench_with_input(BenchmarkId::new("S4096::to_str::oct", 8 * len), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#o}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096::to_str::oct", 8 * len), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#o}", long))
        });

        group.bench_with_input(BenchmarkId::new("S4096::to_str::hex", 8 * len), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#x}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096::to_str::hex", 8 * len), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#x}", long))
        });
    }
}

fn ops(group: &mut BenchmarkGroup<'_, WallTime>) {
    let s4096 = [
        Aligned(composite!(S4096, i64, 0, 2)),
        Aligned(composite!(S4096, i64, 1, 2)),
        Aligned(composite!(S4096, i64, 1, 4)),
    ];

    let u4096 = [
        Aligned(composite!(U4096, u64, 0, 2)),
        Aligned(composite!(U4096, u64, 1, 2)),
        Aligned(composite!(U4096, u64, 1, 4)),
    ];

    group.throughput(Throughput::Bits(BITS as u64));

    exec! { group => [
        "S4096::add",     &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| lhs + rhs,
        "U4096::add",     &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| lhs + rhs,
        "S4096::sub",     &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| lhs - rhs,
        "U4096::sub",     &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| lhs - rhs,
        "S4096::mul",     &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| lhs * rhs,
        "U4096::mul",     &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| lhs * rhs,
        "S4096::div",     &s4096, |[lhs, _, rhs]: &[Aligned<S4096>; 3]| lhs / rhs,
        "U4096::div",     &u4096, |[lhs, _, rhs]: &[Aligned<U4096>; 3]| lhs / rhs,
        "S4096::rem",     &s4096, |[lhs, _, rhs]: &[Aligned<S4096>; 3]| lhs % rhs,
        "U4096::rem",     &u4096, |[lhs, _, rhs]: &[Aligned<U4096>; 3]| lhs % rhs,
        "S4096::bitor",   &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| lhs | rhs,
        "U4096::bitor",   &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| lhs | rhs,
        "S4096::bitxor",  &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| lhs & rhs,
        "U4096::bitxor",  &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| lhs & rhs,
        "S4096::bitand",  &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| lhs ^ rhs,
        "U4096::bitand",  &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| lhs ^ rhs,
    ] };

    exec! { group => [
        "S4096::shl", &s4096, |[val, _, _]: &[Aligned<S4096>; 3]| val << 7,
        "U4096::shl", &u4096, |[val, _, _]: &[Aligned<U4096>; 3]| val << 7,
        "S4096::shr", &s4096, |[val, _, _]: &[Aligned<S4096>; 3]| val >> 7,
        "U4096::shr", &u4096, |[val, _, _]: &[Aligned<U4096>; 3]| val >> 7,
    ] };
}

fn ops_mut(group: &mut BenchmarkGroup<'_, WallTime>) {
    let s4096 = [
        Aligned(composite!(S4096, i64, 0, 2)),
        Aligned(composite!(S4096, i64, 1, 2)),
        Aligned(composite!(S4096, i64, 1, 4)),
    ];

    let u4096 = [
        Aligned(composite!(U4096, u64, 0, 2)),
        Aligned(composite!(U4096, u64, 1, 2)),
        Aligned(composite!(U4096, u64, 1, 4)),
    ];

    group.throughput(Throughput::Bits(BITS as u64));

    exec! { group => [
        "S4096::add_mut",    &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val += rhs },
        "U4096::add_mut",    &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val += rhs },
        "S4096::sub_mut",    &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val -= rhs },
        "U4096::sub_mut",    &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val -= rhs },
        "S4096::mul_mut",    &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val *= rhs },
        "U4096::mul_mut",    &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val *= rhs },
        "S4096::div_mut",    &s4096, |[lhs, _, rhs]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val /= rhs },
        "U4096::div_mut",    &u4096, |[lhs, _, rhs]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val /= rhs },
        "S4096::rem_mut",    &s4096, |[lhs, _, rhs]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val %= rhs },
        "U4096::rem_mut",    &u4096, |[lhs, _, rhs]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val %= rhs },
        "S4096::bitor_mut",  &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val |= rhs },
        "U4096::bitor_mut",  &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val |= rhs },
        "S4096::bitxor_mut", &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val &= rhs },
        "U4096::bitxor_mut", &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val &= rhs },
        "S4096::bitand_mut", &s4096, |[lhs, rhs, _]: &[Aligned<S4096>; 3]| { let mut val = *lhs; val ^= rhs },
        "U4096::bitand_mut", &u4096, |[lhs, rhs, _]: &[Aligned<U4096>; 3]| { let mut val = *lhs; val ^= rhs },
    ] };

    exec! { group => [
        "S4096::shl_mut", &s4096, |[val, _, _]: &[Aligned<S4096>; 3]| { let mut val = *val; val <<= 7 },
        "U4096::shl_mut", &u4096, |[val, _, _]: &[Aligned<U4096>; 3]| { let mut val = *val; val <<= 7 },
        "S4096::shr_mut", &s4096, |[val, _, _]: &[Aligned<S4096>; 3]| { let mut val = *val; val >>= 7 },
        "U4096::shr_mut", &u4096, |[val, _, _]: &[Aligned<U4096>; 3]| { let mut val = *val; val >>= 7 },
    ] };
}

#[allow(clippy::unnecessary_cast)]
fn ops_single(group: &mut BenchmarkGroup<'_, WallTime>) {
    let s4096 = (Aligned(composite!(S4096, i64, 0, 2)), Aligned((PRIMES[1] * PRIMES[3]) as i64));
    let u4096 = (Aligned(composite!(U4096, u64, 0, 2)), Aligned((PRIMES[1] * PRIMES[3]) as u64));

    group.throughput(Throughput::Bits(BITS as u64));

    exec! { group => [
        "S4096::add_single",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs + rhs,
        "U4096::add_single",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs + rhs,
        "S4096::sub_single",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs - rhs,
        "U4096::sub_single",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs - rhs,
        "S4096::mul_single",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs * rhs,
        "U4096::mul_single",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs * rhs,
        "S4096::div_single",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs / rhs,
        "U4096::div_single",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs / rhs,
        "S4096::rem_single",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs % rhs,
        "U4096::rem_single",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs % rhs,
        "S4096::bitor_single",  &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs | rhs,
        "U4096::bitor_single",  &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs | rhs,
        "S4096::bitxor_single", &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs & rhs,
        "U4096::bitxor_single", &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs & rhs,
        "S4096::bitand_single", &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| lhs ^ rhs,
        "U4096::bitand_single", &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| lhs ^ rhs,
    ] };
}

#[allow(clippy::unnecessary_cast)]
fn ops_single_mut(group: &mut BenchmarkGroup<'_, WallTime>) {
    let s4096 = (Aligned(composite!(S4096, i64, 0, 2)), Aligned((PRIMES[1] * PRIMES[3]) as i64));
    let u4096 = (Aligned(composite!(U4096, u64, 0, 2)), Aligned((PRIMES[1] * PRIMES[3]) as u64));

    group.throughput(Throughput::Bits(BITS as u64));

    exec! { group => [
        "S4096::add_single_mut",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val += rhs },
        "U4096::add_single_mut",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val += rhs },
        "S4096::sub_single_mut",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val -= rhs },
        "U4096::sub_single_mut",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val -= rhs },
        "S4096::mul_single_mut",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val *= rhs },
        "U4096::mul_single_mut",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val *= rhs },
        "S4096::div_single_mut",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val /= rhs },
        "U4096::div_single_mut",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val /= rhs },
        "S4096::rem_single_mut",    &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val %= rhs },
        "U4096::rem_single_mut",    &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val %= rhs },
        "S4096::bitor_single_mut",  &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val |= rhs },
        "U4096::bitor_single_mut",  &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val |= rhs },
        "S4096::bitxor_single_mut", &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val &= rhs },
        "U4096::bitxor_single_mut", &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val &= rhs },
        "S4096::bitand_single_mut", &s4096, |(lhs, rhs): &(Aligned<S4096>, Aligned<i64>)| { let mut val = *lhs; val ^= rhs },
        "U4096::bitand_single_mut", &u4096, |(lhs, rhs): &(Aligned<U4096>, Aligned<u64>)| { let mut val = *lhs; val ^= rhs },
    ] };
}

fn uops(_group: &mut BenchmarkGroup<'_, WallTime>) {}

fn uops_mut(_group: &mut BenchmarkGroup<'_, WallTime>) {}

criterion_group!(group, long_convert, long_ops, long_uops);

criterion_main!(group);

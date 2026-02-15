use std::{str::FromStr, time::Duration};

use criterion::{
    BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main, measurement::WallTime,
};
use ndlib::{
    IteratorExt, NdFrom,
    arch::Aligned,
    long::{
        ExpImpl, FromDigits, FromDigitsIter, IntoDigits, IntoDigitsIter, RadixImpl, S4096, ToDigits, ToDigitsIter,
        U4096,
    },
};
use rand::{RngExt, SeedableRng, rngs::StdRng};

const BYTES: usize = 512;
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

macro_rules! from_arr_impl {
    ($group:expr, $rng:expr, $shr:expr) => {
        let len = BYTES >> $shr;
        let bytes = $rng.random::<[u8; BYTES]>();
        let bytes = match <[u8; BYTES >> $shr]>::try_from(&bytes[..len]) {
            Ok(val) => val,
            Err(_) => return,
        };

        $group.throughput(Throughput::Bytes(len as u64));

        $group.bench_with_input(BenchmarkId::new("S4096", 8 * len), &bytes, |b, bytes| {
            b.iter(|| Aligned(S4096::nd_from(bytes)))
        });

        $group.bench_with_input(BenchmarkId::new("U4096", 8 * len), &bytes, |b, bytes| {
            b.iter(|| Aligned(U4096::nd_from(bytes)))
        });
    };
}

macro_rules! ops_impl {
    ($criterion:expr, [$($fn:literal ($len0:expr, $len1:expr): $fns:expr, $fnu:expr),+ $(,)?]) => {{
        $({
            let s4096 = [
                Aligned(composite!(S4096, i64, 0, 2 * 4096 / $len0)),
                Aligned(composite!(S4096, i64, 1, 2 * 4096 / $len1)),
            ];

            let u4096 = [
                Aligned(composite!(U4096, u64, 0, 2 * 4096 / $len0)),
                Aligned(composite!(U4096, u64, 1, 2 * 4096 / $len1)),
            ];

            let mut group = get_group($criterion, $fn);

            group.throughput(Throughput::Bytes(BYTES as u64));

            group.bench_with_input("S4096", &s4096, |b, longs| {
                b.iter(|| ($fns)(&longs[0], &longs[1]))
            });

            group.bench_with_input("U4096", &u4096, |b, longs| {
                b.iter(|| ($fnu)(&longs[0], &longs[1]))
            });
        })+
    }};
}

macro_rules! ops_single_impl {
    ($criterion:expr, [$($fn:literal: $fns:expr, $fnu:expr),+ $(,)?]) => {{
        $({
            let s4096 = Aligned(composite!(S4096, i64, 0, 2));
            let u4096 = Aligned(composite!(U4096, u64, 0, 2));

            let mut group = get_group($criterion, $fn);

            group.throughput(Throughput::Bytes(BYTES as u64));

            group.bench_with_input("S4096", &(s4096, PRIMES[1] as i64), |b, &(long, single)| {
                b.iter(|| ($fns)(&long, single))
            });

            group.bench_with_input("U4096", &(u4096, PRIMES[1] as u64), |b, &(long, single)| {
                b.iter(|| ($fnu)(&long, single))
            });
        })+
    }};
}

macro_rules! ops_shift_impl {
    ($criterion:expr, [$($fn:literal: $fns:expr, $fnu:expr),+ $(,)?]) => {{
        $({
            let s4096 = Aligned(composite!(S4096, i64, 0, 2));
            let u4096 = Aligned(composite!(U4096, u64, 0, 2));

            let mut group = get_group($criterion, $fn);

            group.throughput(Throughput::Bytes(BYTES as u64));

            group.bench_with_input("S4096", &s4096, |b, &long| {
                b.iter(|| ($fns)(&long))
            });

            group.bench_with_input("U4096", &u4096, |b, &long| {
                b.iter(|| ($fnu)(&long))
            });
        })+
    }};
}

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

fn get_group<'c>(c: &'c mut Criterion, name: &'static str) -> BenchmarkGroup<'c, WallTime> {
    let mut group = c.benchmark_group(name);

    group.sample_size(128);
    group.measurement_time(Duration::from_secs(4));
    group.warm_up_time(Duration::from_secs(2));
    group
}

fn get_rng() -> StdRng {
    StdRng::seed_from_u64(PRIMES[0] * PRIMES[1])
}

fn default(c: &mut Criterion) {
    let mut group = get_group(c, "long::default");

    group.throughput(Throughput::Bits(4096));
    group.bench_function(BenchmarkId::new("S4096", 4096), |b| b.iter(|| Aligned(S4096::default())));
    group.bench_function(BenchmarkId::new("U4096", 4096), |b| b.iter(|| Aligned(U4096::default())));
}

fn from_bytes_const(c: &mut Criterion) {
    const SVAL: Aligned<S4096> =
        Aligned(S4096::from_bytes(&116578228889707554089617590980330937198_i128.to_le_bytes()));

    const UVAL: Aligned<U4096> =
        Aligned(U4096::from_bytes(&121940457858715132528838202027877031762_u128.to_le_bytes()));

    let mut group = get_group(c, "long::from_bytes::const");

    group.throughput(Throughput::Bits(128));
    group.bench_function(BenchmarkId::new("S4096", 128), |b| b.iter(|| SVAL));
    group.bench_function(BenchmarkId::new("U4096", 128), |b| b.iter(|| UVAL));
}

fn from_primitive_const(c: &mut Criterion) {
    const SVAL: Aligned<S4096> =
        Aligned(S4096::from_bytes(&116578228889707554089617590980330937198_i128.to_le_bytes()));

    const UVAL: Aligned<U4096> =
        Aligned(U4096::from_bytes(&121940457858715132528838202027877031762_u128.to_le_bytes()));

    let mut group = get_group(c, "long::from_primitive::const");

    group.throughput(Throughput::Bits(128));
    group.bench_function(BenchmarkId::new("S4096", 128), |b| b.iter(|| SVAL));
    group.bench_function(BenchmarkId::new("U4096", 128), |b| b.iter(|| UVAL));
}

fn from_bytes(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_bytes");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(S4096::from_bytes(bytes)))
        });

        group.bench_with_input(BenchmarkId::new("U4096", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(U4096::from_bytes(bytes)))
        });
    }
}

fn from_primitive(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_primitive");
    let mut rng = get_rng();

    let s128 = rng.random::<i128>();
    let u128 = rng.random::<u128>();

    group.throughput(Throughput::Bits(128));

    group.bench_with_input(BenchmarkId::new("S4096", 128), &s128, |b, &val| {
        b.iter(|| Aligned(S4096::from(val)))
    });

    group.bench_with_input(BenchmarkId::new("U4096", 128), &u128, |b, &val| {
        b.iter(|| Aligned(U4096::from(val)))
    });
}

fn from_arr(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_arr");
    let mut rng = get_rng();

    from_arr_impl!(group, rng, 4);
    from_arr_impl!(group, rng, 2);
    from_arr_impl!(group, rng, 0);
}

fn from_slice(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_slice");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(S4096::nd_from(bytes)))
        });

        group.bench_with_input(BenchmarkId::new("U4096", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| Aligned(U4096::nd_from(bytes)))
        });
    }
}

fn from_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_iter");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096", 8 * len), &bytes[..len].iter().copied(), |b, iter| {
            b.iter(|| iter.clone().collect::<Aligned<S4096>>())
        });

        group.bench_with_input(BenchmarkId::new("U4096", 8 * len), &bytes[..len].iter().copied(), |b, iter| {
            b.iter(|| iter.clone().collect::<Aligned<U4096>>())
        });
    }
}

fn from_digits(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;

        let exp = 7u8;
        let radix = 1u8 << exp;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len], exp),
            |b, &(digits, exp)| b.iter(|| Aligned(S4096::from_digits(digits, ExpImpl { exp }))),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len], exp),
            |b, &(digits, exp)| b.iter(|| Aligned(U4096::from_digits(digits, ExpImpl { exp }))),
        );
    }
}

fn from_digits_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits_iter");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;

        let exp = 7u8;
        let radix = 1u8 << exp;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len].iter().copied(), exp),
            |b, &(iter, exp)| b.iter(|| Aligned(S4096::from_digits_iter(iter.clone(), ExpImpl { exp }))),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len].iter().copied(), exp),
            |b, &(iter, exp)| b.iter(|| Aligned(U4096::from_digits_iter(iter.clone(), ExpImpl { exp }))),
        );
    }
}

fn from_digits_radix(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits_radix");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;

        let radix = 251u8;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len], radix),
            |b, &(digits, radix)| b.iter(|| Aligned(S4096::from_digits(digits, RadixImpl { radix }))),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len], radix),
            |b, &(digits, radix)| b.iter(|| Aligned(U4096::from_digits(digits, RadixImpl { radix }))),
        );
    }
}

fn from_digits_radix_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits_radix_iter");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;

        let radix = 251u8;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len].iter().copied(), radix),
            |b, &(iter, radix)| b.iter(|| S4096::from_digits_iter(iter.clone(), RadixImpl { radix })),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len].iter().copied(), radix),
            |b, &(iter, radix)| b.iter(|| U4096::from_digits_iter(iter.clone(), RadixImpl { radix })),
        );
    }
}

fn to_digits(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_digits");
    let mut rng = get_rng();

    for exp in [7u8, 4u8, 1u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let radix = 1u8 << exp;
        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits(ExpImpl { exp }))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits(ExpImpl { exp }))
        });
    }
}

fn to_digits_iter_count(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_digits_iter::count");
    let mut rng = get_rng();

    for exp in [7u8, 4u8, 1u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let radix = 1u8 << exp;
        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.count()))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.count()))
        });
    }
}

fn to_digits_iter_collect(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_digits_iter::collect");
    let mut rng = get_rng();

    for exp in [7u8, 4u8, 1u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let radix = 1u8 << exp;
        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.collect::<Vec<u8>>()))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_iter(ExpImpl { exp }).map(|it| it.collect::<Vec<u8>>()))
        });
    }
}

fn into_digits(c: &mut Criterion) {
    let mut group = get_group(c, "long::into_digits");
    let mut rng = get_rng();

    for radix in [255u8, 31u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits(RadixImpl { radix }))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits(RadixImpl { radix }))
        });
    }
}

fn into_digits_iter_count(c: &mut Criterion) {
    let mut group = get_group(c, "long::into_digits_iter::count");
    let mut rng = get_rng();

    for radix in [255u8, 31u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.count()))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.count()))
        });
    }
}

fn into_digits_iter_collect(c: &mut Criterion) {
    let mut group = get_group(c, "long::into_digits_iter::collect");
    let mut rng = get_rng();

    for radix in [255u8, 31u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..]);
        let unsigned = U4096::nd_from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, radix), |b, &(long, radix)| {
            b.iter_with_large_drop(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.collect::<Vec<u8>>()))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, radix), |b, &(long, radix)| {
            b.iter_with_large_drop(|| long.into_digits_iter(RadixImpl { radix }).map(|it| it.collect::<Vec<u8>>()))
        });
    }
}

fn from_str(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_str");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;
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

        group.bench_with_input(BenchmarkId::new("S4096", format!("dec/{}", 8 * len)), &dec_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(dec_unsigned.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("U4096", format!("dec/{}", 8 * len)),
            &dec_unsigned,
            |b, str| b.iter(|| U4096::from_str(str)),
        );

        group.throughput(Throughput::Bytes(bin_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", format!("bin/{}", 8 * len)), &bin_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(bin_unsigned.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("U4096", format!("bin/{}", 8 * len)),
            &bin_unsigned,
            |b, str| b.iter(|| U4096::from_str(str)),
        );

        group.throughput(Throughput::Bytes(oct_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", format!("oct/{}", 8 * len)), &oct_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(oct_unsigned.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("U4096", format!("oct/{}", 8 * len)),
            &oct_unsigned,
            |b, str| b.iter(|| U4096::from_str(str)),
        );

        group.throughput(Throughput::Bytes(hex_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", format!("hex/{}", 8 * len)), &hex_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(hex_unsigned.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("U4096", format!("hex/{}", 8 * len)),
            &hex_unsigned,
            |b, str| b.iter(|| U4096::from_str(str)),
        );
    }
}

fn to_str(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_str");
    let mut rng = get_rng();

    for shr in [4, 2, 0] {
        let len = BYTES >> shr;
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::nd_from(&bytes[..len]);
        let unsigned = U4096::nd_from(&bytes[..len]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096", format!("dec/{}", 8 * len)), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096", format!("dec/{}", 8 * len)), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#}", long))
        });

        group.bench_with_input(BenchmarkId::new("S4096", format!("bin/{}", 8 * len)), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#b}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096", format!("bin/{}", 8 * len)), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#b}", long))
        });

        group.bench_with_input(BenchmarkId::new("S4096", format!("oct/{}", 8 * len)), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#o}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096", format!("oct/{}", 8 * len)), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#o}", long))
        });

        group.bench_with_input(BenchmarkId::new("S4096", format!("hex/{}", 8 * len)), &signed, |b, long| {
            b.iter_with_large_drop(|| format!("{:#x}", long))
        });

        group.bench_with_input(BenchmarkId::new("U4096", format!("hex/{}", 8 * len)), &unsigned, |b, long| {
            b.iter_with_large_drop(|| format!("{:#x}", long))
        });
    }
}

fn ops(c: &mut Criterion) {
    ops_impl!(c, [
        "long::ops::add"    (4096, 4096): |lhs: &S4096, rhs: &S4096| lhs + rhs, |lhs: &U4096, rhs: &U4096| lhs + rhs,
        "long::ops::sub"    (4096, 4096): |lhs: &S4096, rhs: &S4096| lhs - rhs, |lhs: &U4096, rhs: &U4096| lhs - rhs,
        "long::ops::mul"    (4096, 4096): |lhs: &S4096, rhs: &S4096| lhs * rhs, |lhs: &U4096, rhs: &U4096| lhs * rhs,
        "long::ops::div"    (4096, 2048): |lhs: &S4096, rhs: &S4096| lhs / rhs, |lhs: &U4096, rhs: &U4096| lhs / rhs,
        "long::ops::rem"    (4096, 2048): |lhs: &S4096, rhs: &S4096| lhs % rhs, |lhs: &U4096, rhs: &U4096| lhs % rhs,
        "long::ops::bitor"  (4096, 4096): |lhs: &S4096, rhs: &S4096| lhs | rhs, |lhs: &U4096, rhs: &U4096| lhs | rhs,
        "long::ops::bitand" (4096, 4096): |lhs: &S4096, rhs: &S4096| lhs & rhs, |lhs: &U4096, rhs: &U4096| lhs & rhs,
        "long::ops::bitxor" (4096, 4096): |lhs: &S4096, rhs: &S4096| lhs ^ rhs, |lhs: &U4096, rhs: &U4096| lhs ^ rhs,
    ]);
}

fn ops_assign(c: &mut Criterion) {
    ops_impl!(c, [
        "long::ops::assign::add"    (4096, 4096): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs += rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs += rhs },
        "long::ops::assign::sub"    (4096, 4096): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs -= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs -= rhs },
        "long::ops::assign::mul"    (4096, 4096): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs *= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs *= rhs },
        "long::ops::assign::div"    (4096, 2048): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs /= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs /= rhs },
        "long::ops::assign::rem"    (4096, 2048): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs %= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs %= rhs },
        "long::ops::assign::bitor"  (4096, 4096): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs |= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs |= rhs },
        "long::ops::assign::bitand" (4096, 4096): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs &= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs &= rhs },
        "long::ops::assign::bitxor" (4096, 4096): |lhs: &S4096, rhs: &S4096| { let mut lhs = *lhs; lhs ^= rhs }, |lhs: &U4096, rhs: &U4096| { let mut lhs = *lhs; lhs ^= rhs },
    ]);
}

fn ops_single(c: &mut Criterion) {
    ops_single_impl!(c, [
        "long::ops::single::add":    |lhs: &S4096, rhs: i64| lhs + rhs, |lhs: &U4096, rhs: u64| lhs + rhs,
        "long::ops::single::sub":    |lhs: &S4096, rhs: i64| lhs - rhs, |lhs: &U4096, rhs: u64| lhs - rhs,
        "long::ops::single::mul":    |lhs: &S4096, rhs: i64| lhs * rhs, |lhs: &U4096, rhs: u64| lhs * rhs,
        "long::ops::single::div":    |lhs: &S4096, rhs: i64| lhs / rhs, |lhs: &U4096, rhs: u64| lhs / rhs,
        "long::ops::single::rem":    |lhs: &S4096, rhs: i64| lhs % rhs, |lhs: &U4096, rhs: u64| lhs % rhs,
        "long::ops::single::bitor":  |lhs: &S4096, rhs: i64| lhs | rhs, |lhs: &U4096, rhs: u64| lhs | rhs,
        "long::ops::single::bitand": |lhs: &S4096, rhs: i64| lhs & rhs, |lhs: &U4096, rhs: u64| lhs & rhs,
        "long::ops::single::bitxor": |lhs: &S4096, rhs: i64| lhs ^ rhs, |lhs: &U4096, rhs: u64| lhs ^ rhs,
    ]);
}

fn ops_single_assign(c: &mut Criterion) {
    ops_single_impl!(c, [
        "long::ops::single::assign::add":    |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs += rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs += rhs },
        "long::ops::single::assign::sub":    |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs -= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs -= rhs },
        "long::ops::single::assign::mul":    |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs *= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs *= rhs },
        "long::ops::single::assign::div":    |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs /= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs /= rhs },
        "long::ops::single::assign::rem":    |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs %= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs %= rhs },
        "long::ops::single::assign::bitor":  |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs |= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs |= rhs },
        "long::ops::single::assign::bitand": |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs &= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs &= rhs },
        "long::ops::single::assign::bitxor": |lhs: &S4096, rhs: i64| { let mut lhs = *lhs; lhs ^= rhs }, |lhs: &U4096, rhs: u64| { let mut lhs = *lhs; lhs ^= rhs },
    ]);
}

fn ops_shift(c: &mut Criterion) {
    ops_shift_impl!(c, [
        "long::ops::shl": |value: &S4096| value << 1021, |value: &U4096| value << 1021,
        "long::ops::shr": |value: &S4096| value >> 1021, |value: &U4096| value >> 1021,
    ]);
}

fn ops_shift_assign(c: &mut Criterion) {
    ops_shift_impl!(c, [
        "long::ops::assign::shl": |value: &S4096| { let mut value = *value; value <<= 1021 }, |value: &U4096| { let mut value = *value; value <<= 1021 },
        "long::ops::assign::shr": |value: &S4096| { let mut value = *value; value >>= 1021 }, |value: &U4096| { let mut value = *value; value >>= 1021 },
    ]);
}

criterion_group!(
    group,
    default,
    from_bytes_const,
    from_primitive_const,
    from_bytes,
    from_primitive,
    from_arr,
    from_slice,
    from_iter,
    from_digits,
    from_digits_iter,
    from_digits_radix,
    from_digits_radix_iter,
    to_digits,
    to_digits_iter_count,
    to_digits_iter_collect,
    into_digits,
    into_digits_iter_count,
    into_digits_iter_collect,
    from_str,
    to_str,
    ops,
    ops_assign,
    ops_single,
    ops_single_assign,
    ops_shift,
    ops_shift_assign,
);

criterion_main!(group);

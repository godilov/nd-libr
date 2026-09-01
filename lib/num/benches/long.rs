//! # NdNumbers Long Benchmarks

use std::time::Duration;

use criterion::{Criterion, criterion_group, criterion_main};
use rand::{SeedableRng, rngs::StdRng};

type SxWord = <ndnum::arch::word::Single as ndnum::NumExt>::Signed;
type UxWord = <ndnum::arch::word::Single as ndnum::NumExt>::Unsigned;

type Sx64 = ndnum::long::Signed<64>;
type Ux64 = ndnum::long::Unsigned<64>;

const BITS: usize = std::mem::size_of::<Ux64>() * 8;
const BYTES: usize = std::mem::size_of::<Ux64>();
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

macro_rules! state {
    ($criterion:expr, $group:literal) => {{
        let mut group = $criterion.benchmark_group($group);

        group.measurement_time(Duration::from_secs(4));
        group.warm_up_time(Duration::from_secs(1));

        (group, StdRng::seed_from_u64(PRIMES[0] * PRIMES[1]))
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

macro_rules! exec {
    ($group:expr => [$($id:expr, $args:expr, $fn:expr),* $(,)?]) => {
        $(exec!($group => $id, $args, $fn);)*
    };
    ($group:expr => $id:expr, $args:expr, $fn:expr $(,)?) => {
        $group.bench_with_input($id, $args, |b, args| {
            b.iter(|| std::hint::black_box(($fn)(std::hint::black_box(args))))
        });
    };
}

fn init_fn(c: &mut Criterion) {
    let (mut group, mut rng) = state!(c, "init");

    init::default(&mut group);
    init::primitive_const(&mut group);
    init::bytes_const(&mut group);
    init::primitive(&mut group, &mut rng);
    init::bytes(&mut group, &mut rng);
    init::array(&mut group, &mut rng);
    init::slice(&mut group, &mut rng);
    init::iter(&mut group, &mut rng);
}

fn str_fn(c: &mut Criterion) {
    let (mut group, mut rng) = state!(c, "str");

    str::from(&mut group, &mut rng);
    str::to(&mut group, &mut rng);
}

fn radix_fn(c: &mut Criterion) {
    let (mut group, mut rng) = state!(c, "radix");

    radix::from_exp(&mut group, &mut rng);
    radix::from_radix(&mut group, &mut rng);
    radix::into_count(&mut group, &mut rng);
    radix::into_collect(&mut group, &mut rng);
    radix::to_count(&mut group, &mut rng);
    radix::to_collect(&mut group, &mut rng);
}

fn ops_fn(c: &mut Criterion) {
    let (mut group, _) = state!(c, "ops");

    ops::long(&mut group);
    ops::single(&mut group);
    ops::shift(&mut group);
}

fn uops_fn(c: &mut Criterion) {
    let (mut group, _) = state!(c, "uops");

    uops::long(&mut group);
    uops::single(&mut group);
    uops::signed(&mut group);
    uops::shift(&mut group);
}

mod init {
    use criterion::{BenchmarkGroup, BenchmarkId, Throughput, measurement::WallTime};
    use ndext::convert::NdFrom;
    use ndnum::arch::Aligned;
    use rand::{RngExt, rngs::StdRng};

    use super::{BITS, BYTES, Sx64, Ux64};

    macro_rules! array_impl {
        ($group:expr, $rng:expr, $shr:expr) => {
            let len = BYTES >> $shr;
            let bytes = $rng.random::<[u8; BYTES]>();
            let bytes = match <[u8; BYTES >> $shr]>::try_from(&bytes[..len]) {
                Ok(val) => val,
                Err(_) => return,
            };

            $group.throughput(Throughput::Bytes(len as u64));

            $group.bench_with_input(BenchmarkId::new("array::sx64", 8 * len), &bytes, |b, bytes| {
                b.iter(|| Aligned(Sx64::nd_from(bytes, ())))
            });

            $group.bench_with_input(BenchmarkId::new("array::ux64", 8 * len), &bytes, |b, bytes| {
                b.iter(|| Aligned(Ux64::nd_from(bytes, ())))
            });
        };
    }

    pub(super) fn default(group: &mut BenchmarkGroup<'_, WallTime>) {
        group.throughput(Throughput::Bits(BITS as u64));

        group.bench_function("default::sx64", |b| b.iter(|| Aligned(Sx64::default())));
        group.bench_function("default::ux64", |b| b.iter(|| Aligned(Ux64::default())));
    }

    pub(super) fn primitive_const(group: &mut BenchmarkGroup<'_, WallTime>) {
        const S128: i128 = 116578228889707554089617590980330937198_i128;
        const U128: u128 = 121940457858715132528838202027877031762_u128;

        group.throughput(Throughput::Bits(128));

        group.bench_function("primitive_const::sx64", |b| b.iter(|| const { Aligned(Sx64::from_i128(S128)) }));
        group.bench_function("primitive_const::ux64", |b| b.iter(|| const { Aligned(Ux64::from_u128(U128)) }));
    }

    pub(super) fn bytes_const(group: &mut BenchmarkGroup<'_, WallTime>) {
        const S128: [u8; 16] = 116578228889707554089617590980330937198_i128.to_le_bytes();
        const U128: [u8; 16] = 121940457858715132528838202027877031762_u128.to_le_bytes();

        group.throughput(Throughput::Bits(128));

        group.bench_function("bytes_const::sx64", |b| b.iter(|| const { Aligned(Sx64::from_bytes(&S128)) }));
        group.bench_function("bytes_const::ux64", |b| b.iter(|| const { Aligned(Ux64::from_bytes(&U128)) }));
    }

    pub(super) fn primitive(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        group.throughput(Throughput::Bits(128));

        exec! { group => [
            BenchmarkId::new("primitive::sx64", i128::BITS), &rng.random::<i128>(), |&val: &i128| Aligned(Sx64::from(val)),
            BenchmarkId::new("primitive::ux64", u128::BITS), &rng.random::<u128>(), |&val: &u128| Aligned(Ux64::from(val)),
            BenchmarkId::new("primitive::sx64",  i64::BITS), &rng.random:: <i64>(), |&val:  &i64| Aligned(Sx64::from(val)),
            BenchmarkId::new("primitive::ux64",  u64::BITS), &rng.random:: <u64>(), |&val:  &u64| Aligned(Ux64::from(val)),
            BenchmarkId::new("primitive::sx64",  i32::BITS), &rng.random:: <i32>(), |&val:  &i32| Aligned(Sx64::from(val)),
            BenchmarkId::new("primitive::ux64",  u32::BITS), &rng.random:: <u32>(), |&val:  &u32| Aligned(Ux64::from(val)),
            BenchmarkId::new("primitive::sx64",  i16::BITS), &rng.random:: <i16>(), |&val:  &i16| Aligned(Sx64::from(val)),
            BenchmarkId::new("primitive::ux64",  u16::BITS), &rng.random:: <u16>(), |&val:  &u16| Aligned(Ux64::from(val)),
            BenchmarkId::new("primitive::sx64",   i8::BITS), &rng.random::  <i8>(), |&val:   &i8| Aligned(Sx64::from(val)),
            BenchmarkId::new("primitive::ux64",   u8::BITS), &rng.random::  <u8>(), |&val:   &u8| Aligned(Ux64::from(val)),
        ] };
    }

    pub(super) fn bytes(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;
            let bytes = rng.random::<[u8; BYTES]>();

            group.throughput(Throughput::Bytes(len as u64));

            group.bench_with_input(BenchmarkId::new("bytes::sx64", 8 * len), &bytes[..len], |b, bytes| {
                b.iter(|| Aligned(Sx64::from_bytes(bytes)))
            });

            group.bench_with_input(BenchmarkId::new("bytes::ux64", 8 * len), &bytes[..len], |b, bytes| {
                b.iter(|| Aligned(Ux64::from_bytes(bytes)))
            });
        }
    }

    pub(super) fn array(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        array_impl!(group, rng, 4);
        array_impl!(group, rng, 2);
        array_impl!(group, rng, 0);
    }

    pub(super) fn slice(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;
            let bytes = rng.random::<[u8; BYTES]>();

            group.throughput(Throughput::Bytes(len as u64));

            group.bench_with_input(BenchmarkId::new("slice::sx64", 8 * len), &bytes[..len], |b, bytes| {
                b.iter(|| Aligned(Sx64::nd_from(bytes, ())))
            });

            group.bench_with_input(BenchmarkId::new("slice::ux64", 8 * len), &bytes[..len], |b, bytes| {
                b.iter(|| Aligned(Ux64::nd_from(bytes, ())))
            });
        }
    }

    pub(super) fn iter(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;
            let bytes = rng.random::<[u8; BYTES]>();

            group.throughput(Throughput::Bytes(len as u64));

            group.bench_with_input(
                BenchmarkId::new("iter::sx64", 8 * len),
                &bytes[..len].iter().copied(),
                |b, iter| b.iter(|| iter.clone().collect::<Aligned<Sx64>>()),
            );

            group.bench_with_input(
                BenchmarkId::new("iter::ux64", 8 * len),
                &bytes[..len].iter().copied(),
                |b, iter| b.iter(|| iter.clone().collect::<Aligned<Ux64>>()),
            );
        }
    }
}

mod str {
    use std::str::FromStr;

    use criterion::{BenchmarkGroup, BenchmarkId, Throughput, measurement::WallTime};
    use ndext::convert::NdFrom;
    use ndnum::arch::Aligned;
    use rand::{RngExt, rngs::StdRng};

    use super::{BYTES, Sx64, Ux64};

    pub(super) fn from(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;
            let bytes = rng.random::<[u8; BYTES]>();

            let signed = Sx64::nd_from(&bytes[..len], ());
            let unsigned = Ux64::nd_from(&bytes[..len], ());

            let dec_signed = format!("{:#}", signed);
            let bin_signed = format!("{:#b}", signed);
            let oct_signed = format!("{:#o}", signed);
            let hex_signed = format!("{:#x}", signed);

            let dec_unsigned = format!("{:#}", unsigned);
            let bin_unsigned = format!("{:#b}", unsigned);
            let oct_unsigned = format!("{:#o}", unsigned);
            let hex_unsigned = format!("{:#x}", unsigned);

            group.throughput(Throughput::Bytes(dec_signed.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::dec::sx64", 8 * len), &dec_signed, |b, str| {
                b.iter(|| Sx64::from_str(str))
            });

            group.throughput(Throughput::Bytes(dec_unsigned.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::dec::ux64", 8 * len), &dec_unsigned, |b, str| {
                b.iter(|| Ux64::from_str(str))
            });

            group.throughput(Throughput::Bytes(bin_signed.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::bin::sx64", 8 * len), &bin_signed, |b, str| {
                b.iter(|| Sx64::from_str(str))
            });

            group.throughput(Throughput::Bytes(bin_unsigned.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::bin::ux64", 8 * len), &bin_unsigned, |b, str| {
                b.iter(|| Ux64::from_str(str))
            });

            group.throughput(Throughput::Bytes(oct_signed.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::oct::sx64", 8 * len), &oct_signed, |b, str| {
                b.iter(|| Sx64::from_str(str))
            });

            group.throughput(Throughput::Bytes(oct_unsigned.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::oct::ux64", 8 * len), &oct_unsigned, |b, str| {
                b.iter(|| Ux64::from_str(str))
            });

            group.throughput(Throughput::Bytes(hex_signed.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::hex::sx64", 8 * len), &hex_signed, |b, str| {
                b.iter(|| Sx64::from_str(str))
            });

            group.throughput(Throughput::Bytes(hex_unsigned.len() as u64));
            group.bench_with_input(BenchmarkId::new("from::hex::ux64", 8 * len), &hex_unsigned, |b, str| {
                b.iter(|| Ux64::from_str(str))
            });
        }
    }

    pub(super) fn to(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;
            let bytes = rng.random::<[u8; BYTES]>();

            let signed = Aligned(Sx64::nd_from(&bytes[..len], ()));
            let unsigned = Aligned(Ux64::nd_from(&bytes[..len], ()));

            group.throughput(Throughput::Bytes(len as u64));

            group.bench_with_input(BenchmarkId::new("to::dec::sx64", 8 * len), &signed, |b, long| {
                b.iter_with_large_drop(|| format!("{:#}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::dec::ux64", 8 * len), &unsigned, |b, long| {
                b.iter_with_large_drop(|| format!("{:#}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::bin::sx64", 8 * len), &signed, |b, long| {
                b.iter_with_large_drop(|| format!("{:#b}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::bin::ux64", 8 * len), &unsigned, |b, long| {
                b.iter_with_large_drop(|| format!("{:#b}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::oct::sx64", 8 * len), &signed, |b, long| {
                b.iter_with_large_drop(|| format!("{:#o}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::oct::ux64", 8 * len), &unsigned, |b, long| {
                b.iter_with_large_drop(|| format!("{:#o}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::hex::sx64", 8 * len), &signed, |b, long| {
                b.iter_with_large_drop(|| format!("{:#x}", long))
            });

            group.bench_with_input(BenchmarkId::new("to::hex::ux64", 8 * len), &unsigned, |b, long| {
                b.iter_with_large_drop(|| format!("{:#x}", long))
            });
        }
    }
}

mod radix {

    use criterion::{BenchmarkGroup, BenchmarkId, Throughput, measurement::WallTime};
    use ndext::{
        convert::{NdFrom, NdTryFrom},
        iter::IteratorExt,
    };
    use ndnum::{
        arch::{Aligned, word::Single},
        long::radix::*,
    };
    use rand::{RngExt, rngs::StdRng};

    use super::{BYTES, Sx64, Ux64};

    pub(super) fn from_exp(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;

            let exp = 7u8;
            let radix = 1u8 << exp;
            let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

            group.throughput(Throughput::Bytes(len as u64));

            group.bench_with_input(
                BenchmarkId::new("from_exp::sx64", 8 * len),
                &(&digits[..len], exp),
                |b, &(digits, exp)| b.iter(|| Aligned(Sx64::nd_try_from(digits.iter().copied(), ExpImpl { exp }))),
            );

            group.bench_with_input(
                BenchmarkId::new("from_exp::ux64", 8 * len),
                &(&digits[..len], exp),
                |b, &(digits, exp)| b.iter(|| Aligned(Ux64::nd_try_from(digits.iter().copied(), ExpImpl { exp }))),
            );
        }
    }

    pub(super) fn from_radix(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for shift in [4, 2, 0] {
            let len = BYTES >> shift;

            let radix = 251u8;
            let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

            group.throughput(Throughput::Bytes(len as u64));

            group.bench_with_input(
                BenchmarkId::new("from_radix::sx64", 8 * len),
                &(&digits[..len], radix),
                |b, &(digits, radix)| {
                    b.iter(|| Aligned(Sx64::nd_try_from(digits.iter().copied(), RadixImpl { radix })))
                },
            );

            group.bench_with_input(
                BenchmarkId::new("from_radix::ux64", 8 * len),
                &(&digits[..len], radix),
                |b, &(digits, radix)| {
                    b.iter(|| Aligned(Ux64::nd_try_from(digits.iter().copied(), RadixImpl { radix })))
                },
            );
        }
    }

    pub(super) fn into_count(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for radix in [255u8, 31u8, 3u8] {
            let bytes = rng.random::<[u8; BYTES]>();

            let signed = Sx64::nd_from(&bytes[..], ());
            let unsigned = Ux64::nd_from(&bytes[..], ());

            group.throughput(Throughput::Bytes(bytes.len() as u64));

            group.bench_with_input(
                BenchmarkId::new("into::sx64", radix),
                &(&signed, radix as Single),
                |b, &(long, radix)| b.iter(|| long.into_digits(RadixImpl { radix }).count()),
            );

            group.bench_with_input(
                BenchmarkId::new("into::ux64", radix),
                &(&unsigned, radix as Single),
                |b, &(long, radix)| b.iter(|| long.into_digits(RadixImpl { radix }).count()),
            );
        }
    }

    pub(super) fn into_collect(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for radix in [255u8, 31u8, 3u8] {
            let bytes = rng.random::<[u8; BYTES]>();

            let signed = Sx64::nd_from(&bytes[..], ());
            let unsigned = Ux64::nd_from(&bytes[..], ());

            group.throughput(Throughput::Bytes(bytes.len() as u64));

            group.bench_with_input(
                BenchmarkId::new("into::sx64::collect", radix),
                &(&signed, radix as Single),
                |b, &(long, radix)| {
                    b.iter_with_large_drop(|| long.into_digits(RadixImpl { radix }).collect::<Vec<Single>>())
                },
            );

            group.bench_with_input(
                BenchmarkId::new("into::ux64::collect", radix),
                &(&unsigned, radix as Single),
                |b, &(long, radix)| {
                    b.iter_with_large_drop(|| long.into_digits(RadixImpl { radix }).collect::<Vec<Single>>())
                },
            );
        }
    }

    pub(super) fn to_count(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for exp in [7u8, 4u8, 1u8] {
            let bytes = rng.random::<[u8; BYTES]>();

            let radix = 1u8 << exp;
            let signed = Sx64::nd_from(&bytes[..], ());
            let unsigned = Ux64::nd_from(&bytes[..], ());

            group.throughput(Throughput::Bytes(bytes.len() as u64));

            group.bench_with_input(BenchmarkId::new("to::sx64", radix), &(&signed, exp), |b, &(long, exp)| {
                b.iter(|| long.to_digits(ExpImpl { exp }).count())
            });

            group.bench_with_input(BenchmarkId::new("to::ux64", radix), &(&unsigned, exp), |b, &(long, exp)| {
                b.iter(|| long.to_digits(ExpImpl { exp }).count())
            });
        }
    }

    pub(super) fn to_collect(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut StdRng) {
        for exp in [7u8, 4u8, 1u8] {
            let bytes = rng.random::<[u8; BYTES]>();

            let radix = 1u8 << exp;
            let signed = Sx64::nd_from(&bytes[..], ());
            let unsigned = Ux64::nd_from(&bytes[..], ());

            group.throughput(Throughput::Bytes(bytes.len() as u64));

            group.bench_with_input(
                BenchmarkId::new("to::sx64::collect", radix),
                &(&signed, exp),
                |b, &(long, exp)| b.iter_with_large_drop(|| long.to_digits(ExpImpl { exp }).collect::<Vec<u8>>()),
            );

            group.bench_with_input(
                BenchmarkId::new("to::ux64::collect", radix),
                &(&unsigned, exp),
                |b, &(long, exp)| b.iter_with_large_drop(|| long.to_digits(ExpImpl { exp }).collect::<Vec<u8>>()),
            );
        }
    }
}

mod ops {
    use criterion::{BenchmarkGroup, Throughput, measurement::WallTime};
    use ndext::ops::{Mut, Ref, Relaxed};
    use ndnum::arch::Aligned;

    use crate::{BITS, PRIMES, SxWord, UxWord};

    use super::{Sx64, Ux64};

    pub(super) fn long(group: &mut BenchmarkGroup<'_, WallTime>) {
        let s4096 = Aligned([
            composite!(Sx64, i64, 0, 2),
            composite!(Sx64, i64, 1, 2),
            composite!(Sx64, i64, 1, 4),
        ]);

        let u4096 = Aligned([
            composite!(Ux64, u64, 0, 2),
            composite!(Ux64, u64, 1, 2),
            composite!(Ux64, u64, 1, 4),
        ]);

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "add::sx64",        &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| Relaxed(Ref(lhs)) + Relaxed(Ref(rhs)),
            "add::ux64",        &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| Relaxed(Ref(lhs)) + Relaxed(Ref(rhs)),
            "sub::sx64",        &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| Relaxed(Ref(lhs)) - Relaxed(Ref(rhs)),
            "sub::ux64",        &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| Relaxed(Ref(lhs)) - Relaxed(Ref(rhs)),
            "mul::sx64",        &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| Relaxed(Ref(lhs)) * Relaxed(Ref(rhs)),
            "mul::ux64",        &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| Relaxed(Ref(lhs)) * Relaxed(Ref(rhs)),
            "div::sx64",        &s4096.0, |[lhs, _, rhs]: &[Sx64; 3]| Relaxed(Ref(lhs)) / Relaxed(Ref(rhs)),
            "div::ux64",        &u4096.0, |[lhs, _, rhs]: &[Ux64; 3]| Relaxed(Ref(lhs)) / Relaxed(Ref(rhs)),
            "rem::sx64",        &s4096.0, |[lhs, _, rhs]: &[Sx64; 3]| Relaxed(Ref(lhs)) % Relaxed(Ref(rhs)),
            "rem::ux64",        &u4096.0, |[lhs, _, rhs]: &[Ux64; 3]| Relaxed(Ref(lhs)) % Relaxed(Ref(rhs)),
            "bitor::sx64",      &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| Relaxed(Ref(lhs)) | Relaxed(Ref(rhs)),
            "bitor::ux64",      &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| Relaxed(Ref(lhs)) | Relaxed(Ref(rhs)),
            "bitand::sx64",     &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| Relaxed(Ref(lhs)) & Relaxed(Ref(rhs)),
            "bitand::ux64",     &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| Relaxed(Ref(lhs)) & Relaxed(Ref(rhs)),
            "bitxor::sx64",     &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| Relaxed(Ref(lhs)) ^ Relaxed(Ref(rhs)),
            "bitxor::ux64",     &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| Relaxed(Ref(lhs)) ^ Relaxed(Ref(rhs)),

            "add_mut::sx64",    &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp += Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "add_mut::ux64",    &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp += Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "sub_mut::sx64",    &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp -= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "sub_mut::ux64",    &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp -= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "mul_mut::sx64",    &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp *= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "mul_mut::ux64",    &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp *= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "div_mut::sx64",    &s4096.0, |[lhs, _, rhs]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp /= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "div_mut::ux64",    &u4096.0, |[lhs, _, rhs]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp /= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "rem_mut::sx64",    &s4096.0, |[lhs, _, rhs]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp %= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "rem_mut::ux64",    &u4096.0, |[lhs, _, rhs]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp %= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitor_mut::sx64",  &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp |= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitor_mut::ux64",  &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp |= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitand_mut::sx64", &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp &= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitand_mut::ux64", &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp &= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitxor_mut::sx64", &s4096.0, |[lhs, rhs, _]: &[Sx64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp ^= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitxor_mut::ux64", &u4096.0, |[lhs, rhs, _]: &[Ux64; 3]| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp ^= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
        ] };
    }

    pub(super) fn single(group: &mut BenchmarkGroup<'_, WallTime>) {
        let s4096 = Aligned((composite!(Sx64, i64, 0, 2), (PRIMES[1] * PRIMES[3]) as SxWord));
        let u4096 = Aligned((composite!(Ux64, u64, 0, 2), (PRIMES[1] * PRIMES[3]) as UxWord));

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "add_single::sx64",        &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) + Relaxed(Ref(rhs)),
            "add_single::ux64",        &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) + Relaxed(Ref(rhs)),
            "sub_single::sx64",        &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) - Relaxed(Ref(rhs)),
            "sub_single::ux64",        &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) - Relaxed(Ref(rhs)),
            "mul_single::sx64",        &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) * Relaxed(Ref(rhs)),
            "mul_single::ux64",        &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) * Relaxed(Ref(rhs)),
            "div_single::sx64",        &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) / Relaxed(Ref(rhs)),
            "div_single::ux64",        &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) / Relaxed(Ref(rhs)),
            "rem_single::sx64",        &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) % Relaxed(Ref(rhs)),
            "rem_single::ux64",        &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) % Relaxed(Ref(rhs)),
            "bitor_single::sx64",      &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) | Relaxed(Ref(rhs)),
            "bitor_single::ux64",      &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) | Relaxed(Ref(rhs)),
            "bitand_single::sx64",     &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) & Relaxed(Ref(rhs)),
            "bitand_single::ux64",     &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) & Relaxed(Ref(rhs)),
            "bitxor_single::sx64",     &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| Relaxed(Ref(lhs)) ^ Relaxed(Ref(rhs)),
            "bitxor_single::ux64",     &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| Relaxed(Ref(lhs)) ^ Relaxed(Ref(rhs)),

            "add_single_mut::sx64",    &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp += Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "add_single_mut::ux64",    &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp += Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "sub_single_mut::sx64",    &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp -= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "sub_single_mut::ux64",    &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp -= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "mul_single_mut::sx64",    &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp *= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "mul_single_mut::ux64",    &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp *= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "div_single_mut::sx64",    &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp /= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "div_single_mut::ux64",    &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp /= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "rem_single_mut::sx64",    &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp %= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "rem_single_mut::ux64",    &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp %= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitor_single_mut::sx64",  &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp |= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitor_single_mut::ux64",  &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp |= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitand_single_mut::sx64", &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp &= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitand_single_mut::ux64", &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp &= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitxor_single_mut::sx64", &s4096.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp ^= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
            "bitxor_single_mut::ux64", &u4096.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; let mut tmp = Relaxed(Mut(&mut val)); tmp ^= Relaxed(Ref(rhs)); std::hint::black_box(&val); },
        ] };
    }

    pub(super) fn shift(group: &mut BenchmarkGroup<'_, WallTime>) {
        let s4096 = Aligned([
            composite!(Sx64, i64, 0, 2),
            composite!(Sx64, i64, 1, 2),
            composite!(Sx64, i64, 1, 4),
        ]);

        let u4096 = Aligned([
            composite!(Ux64, u64, 0, 2),
            composite!(Ux64, u64, 1, 2),
            composite!(Ux64, u64, 1, 4),
        ]);

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "shl::sx64", &s4096.0, |[val, _, _]: &[Sx64; 3]| Relaxed(Ref(val)) << 7,
            "shl::ux64", &u4096.0, |[val, _, _]: &[Ux64; 3]| Relaxed(Ref(val)) << 7,
            "shr::sx64", &s4096.0, |[val, _, _]: &[Sx64; 3]| Relaxed(Ref(val)) >> 7,
            "shr::ux64", &u4096.0, |[val, _, _]: &[Ux64; 3]| Relaxed(Ref(val)) >> 7,

            "shl_mut::sx64", &s4096.0, |[val, _, _]: &[Sx64; 3]| { let mut val = *val; let mut tmp = Relaxed(Mut(&mut val)); tmp <<= 7; std::hint::black_box(&val); },
            "shl_mut::ux64", &u4096.0, |[val, _, _]: &[Ux64; 3]| { let mut val = *val; let mut tmp = Relaxed(Mut(&mut val)); tmp <<= 7; std::hint::black_box(&val); },
            "shr_mut::sx64", &s4096.0, |[val, _, _]: &[Sx64; 3]| { let mut val = *val; let mut tmp = Relaxed(Mut(&mut val)); tmp >>= 7; std::hint::black_box(&val); },
            "shr_mut::ux64", &u4096.0, |[val, _, _]: &[Ux64; 3]| { let mut val = *val; let mut tmp = Relaxed(Mut(&mut val)); tmp >>= 7; std::hint::black_box(&val); },
        ] };
    }
}

mod uops {
    use criterion::{BenchmarkGroup, Throughput, measurement::WallTime};
    use ndnum::{
        Dir,
        arch::Aligned,
        long::uops::{self, Expr, ExprMut},
    };

    use crate::{BITS, PRIMES, SxWord, UxWord};

    use super::{Sx64, Ux64};

    pub(super) fn long(group: &mut BenchmarkGroup<'_, WallTime>) {
        let args = Aligned([composite!(Ux64, u64, 0, 2), composite!(Ux64, u64, 1, 2)]);

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "posx",        &args.0, |[lhs,   _]: &[Ux64; 2]| uops::dirx(&lhs.0, Dir::POS).iter().count(),
            "negx",        &args.0, |[lhs,   _]: &[Ux64; 2]| uops::dirx(&lhs.0, Dir::NEG).iter().count(),

            "not",         &args.0, |[lhs,   _]: &[Ux64; 2]| uops::not(&lhs.0,       ).iter().count(),
            "pos",         &args.0, |[lhs,   _]: &[Ux64; 2]| uops::pos(&lhs.0,       ).iter().count(),
            "neg",         &args.0, |[lhs,   _]: &[Ux64; 2]| uops::neg(&lhs.0,       ).iter().count(),
            "add",         &args.0, |[lhs, rhs]: &[Ux64; 2]| uops::add(&lhs.0, &rhs.0).iter().count(),
            "sub",         &args.0, |[lhs, rhs]: &[Ux64; 2]| uops::sub(&lhs.0, &rhs.0).iter().count(),

            "bitor",       &args.0, |[lhs, rhs]: &[Ux64; 2]| uops::bitor (&lhs.0, &rhs.0).iter().count(),
            "bitand",      &args.0, |[lhs, rhs]: &[Ux64; 2]| uops::bitand(&lhs.0, &rhs.0).iter().count(),
            "bitxor",      &args.0, |[lhs, rhs]: &[Ux64; 2]| uops::bitxor(&lhs.0, &rhs.0).iter().count(),

            "posx_mut",    &args.0, |[lhs,   _]: &[Ux64; 2]| { let mut val = *lhs; uops::dirx(&mut val.0, Dir::POS).iter_mut().count(); },
            "negx_mut",    &args.0, |[lhs,   _]: &[Ux64; 2]| { let mut val = *lhs; uops::dirx(&mut val.0, Dir::NEG).iter_mut().count(); },

            "not_mut",     &args.0, |[lhs,   _]: &[Ux64; 2]| { let mut val = *lhs; uops::not(&mut val.0,       ).iter_mut().count(); },
            "pos_mut",     &args.0, |[lhs,   _]: &[Ux64; 2]| { let mut val = *lhs; uops::pos(&mut val.0,       ).iter_mut().count(); },
            "neg_mut",     &args.0, |[lhs,   _]: &[Ux64; 2]| { let mut val = *lhs; uops::neg(&mut val.0,       ).iter_mut().count(); },
            "add_mut",     &args.0, |[lhs, rhs]: &[Ux64; 2]| { let mut val = *lhs; uops::add(&mut val.0, &rhs.0).iter_mut().count(); },
            "sub_mut",     &args.0, |[lhs, rhs]: &[Ux64; 2]| { let mut val = *lhs; uops::sub(&mut val.0, &rhs.0).iter_mut().count(); },

            "bitor_mut",   &args.0, |[lhs, rhs]: &[Ux64; 2]| { let mut val = *lhs; uops::bitor (&mut val.0, &rhs.0).iter_mut().count(); },
            "bitand_mut",  &args.0, |[lhs, rhs]: &[Ux64; 2]| { let mut val = *lhs; uops::bitand(&mut val.0, &rhs.0).iter_mut().count(); },
            "bitxor_mut",  &args.0, |[lhs, rhs]: &[Ux64; 2]| { let mut val = *lhs; uops::bitxor(&mut val.0, &rhs.0).iter_mut().count(); },
        ] };
    }

    pub(super) fn single(group: &mut BenchmarkGroup<'_, WallTime>) {
        let args = Aligned((composite!(Ux64, u64, 0, 2), (PRIMES[1] * PRIMES[3]) as UxWord));

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "add_single", &args.0, |(lhs, rhs): &(Ux64, UxWord)| uops::add(&lhs.0, *rhs).iter().count(),
            "sub_single", &args.0, |(lhs, rhs): &(Ux64, UxWord)| uops::sub(&lhs.0, *rhs).iter().count(),

            "bitor_single",  &args.0, |(lhs, rhs): &(Ux64, UxWord)| uops::bitor (&lhs.0, *rhs).iter().count(),
            "bitand_single", &args.0, |(lhs, rhs): &(Ux64, UxWord)| uops::bitand(&lhs.0, *rhs).iter().count(),
            "bitxor_single", &args.0, |(lhs, rhs): &(Ux64, UxWord)| uops::bitxor(&lhs.0, *rhs).iter().count(),

            "add_single_mut", &args.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; uops::add(&mut val.0, *rhs).iter_mut().count() },
            "sub_single_mut", &args.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; uops::sub(&mut val.0, *rhs).iter_mut().count() },

            "bitor_single_mut",  &args.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; uops::bitor (&mut val.0, *rhs).iter_mut().count() },
            "bitand_single_mut", &args.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; uops::bitand(&mut val.0, *rhs).iter_mut().count() },
            "bitxor_single_mut", &args.0, |(lhs, rhs): &(Ux64, UxWord)| { let mut val = *lhs; uops::bitxor(&mut val.0, *rhs).iter_mut().count() },
        ] };
    }

    pub(super) fn signed(group: &mut BenchmarkGroup<'_, WallTime>) {
        let args = Aligned((composite!(Sx64, i64, 0, 2), (PRIMES[1] * PRIMES[3]) as SxWord));

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "add_signed", &args.0, |(lhs, rhs): &(Sx64, SxWord)| uops::add(&lhs.0, *rhs).signed().iter().count(),
            "sub_signed", &args.0, |(lhs, rhs): &(Sx64, SxWord)| uops::sub(&lhs.0, *rhs).signed().iter().count(),

            "bitor_signed",  &args.0, |(lhs, rhs): &(Sx64, SxWord)| uops::bitor (&lhs.0, *rhs).iter().count(),
            "bitand_signed", &args.0, |(lhs, rhs): &(Sx64, SxWord)| uops::bitand(&lhs.0, *rhs).iter().count(),
            "bitxor_signed", &args.0, |(lhs, rhs): &(Sx64, SxWord)| uops::bitxor(&lhs.0, *rhs).iter().count(),

            "add_signed_mut", &args.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; uops::add(&mut val.0, *rhs).signed().iter_mut().count() },
            "sub_signed_mut", &args.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; uops::sub(&mut val.0, *rhs).signed().iter_mut().count() },

            "bitor_signed_mut",  &args.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; uops::bitor (&mut val.0, *rhs).iter_mut().count() },
            "bitand_signed_mut", &args.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; uops::bitand(&mut val.0, *rhs).iter_mut().count() },
            "bitxor_signed_mut", &args.0, |(lhs, rhs): &(Sx64, SxWord)| { let mut val = *lhs; uops::bitxor(&mut val.0, *rhs).iter_mut().count() },
        ] };
    }

    pub(super) fn shift(group: &mut BenchmarkGroup<'_, WallTime>) {
        let args = Aligned([composite!(Ux64, u64, 0, 2), composite!(Ux64, u64, 1, 2)]);

        group.throughput(Throughput::Bits(BITS as u64));

        exec! { group => [
            "shl", &args.0, |[val, _]: &[Ux64; 2]| uops::shl(&val.0, 7).eval(),
            "shr", &args.0, |[val, _]: &[Ux64; 2]| uops::shr(&val.0, 7).eval(),

            "shl_mut", &args.0, |[val, _]: &[Ux64; 2]| { let mut val = *val; uops::shl(&mut val.0, 7).eval_mut(); },
            "shr_mut", &args.0, |[val, _]: &[Ux64; 2]| { let mut val = *val; uops::shr(&mut val.0, 7).eval_mut(); },
        ] };
    }
}

criterion_group!(group, init_fn, str_fn, radix_fn, ops_fn, uops_fn);

criterion_main!(group);

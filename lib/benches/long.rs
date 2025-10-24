use std::{str::FromStr, time::Duration};

use criterion::{
    BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main, measurement::WallTime,
};
use ndlib::{
    num::long::{S4096, U4096},
    ops::IteratorExt,
};
use rand::{Rng, SeedableRng, rngs::StdRng};

const BYTES: usize = 512;
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

fn get_group<'c>(c: &'c mut Criterion, name: &'static str) -> BenchmarkGroup<'c, WallTime> {
    let mut group = c.benchmark_group(name);

    group.sample_size(256);
    group.measurement_time(Duration::from_secs(6));
    group.warm_up_time(Duration::from_secs(2));
    group
}

fn get_rng() -> StdRng {
    StdRng::seed_from_u64(PRIMES[0] * PRIMES[1])
}

fn from_std_const(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_std::const");

    group.throughput(Throughput::Bits(128));

    group.bench_function(BenchmarkId::new("S4096", 128), |b| {
        b.iter(|| S4096::from_i128(116578228889707554089617590980330937198_i128))
    });

    group.bench_function(BenchmarkId::new("U4096", 128), |b| {
        b.iter(|| U4096::from_u128(121940457858715132528838202027877031762_u128))
    });
}

fn from_std(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_std");
    let mut rng = get_rng();

    let s128 = rng.random::<i128>();
    let u128 = rng.random::<u128>();

    group.throughput(Throughput::Bits(128));
    group.bench_with_input(BenchmarkId::new("S4096", 128), &s128, |b, &val| b.iter(|| S4096::from(val)));
    group.bench_with_input(BenchmarkId::new("U4096", 128), &u128, |b, &val| b.iter(|| U4096::from(val)));
}

fn from_slice(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_slice");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| S4096::from(bytes))
        });

        group.bench_with_input(BenchmarkId::new("U4096", 8 * len), &bytes[..len], |b, bytes| {
            b.iter(|| U4096::from(bytes))
        });
    }
}

fn from_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_iter");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;
        let bytes = rng.random::<[u8; BYTES]>();

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("S4096", 8 * len), &bytes[..len].iter().copied(), |b, iter| {
            b.iter(|| iter.clone().collect::<S4096>())
        });

        group.bench_with_input(BenchmarkId::new("U4096", 8 * len), &bytes[..len].iter().copied(), |b, iter| {
            b.iter(|| iter.clone().collect::<U4096>())
        });
    }
}

fn from_digits(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;

        let radix = 251u8;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len], radix),
            |b, &(digits, radix)| b.iter(|| S4096::from_digits(digits, radix)),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len], radix),
            |b, &(digits, radix)| b.iter(|| U4096::from_digits(digits, radix)),
        );
    }
}

fn from_digits_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits_iter");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;

        let radix = 251u8;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len].iter().copied(), radix),
            |b, &(iter, radix)| b.iter(|| S4096::from_digits_iter(iter.clone(), radix)),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len].iter().copied(), radix),
            |b, &(iter, radix)| b.iter(|| U4096::from_digits_iter(iter.clone(), radix)),
        );
    }
}

fn from_digits_bin(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits_bin");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;

        let exp = 7;
        let radix = 1 << exp;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len], exp),
            |b, &(digits, exp)| b.iter(|| S4096::from_digits_bin(digits, exp)),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len], exp),
            |b, &(digits, exp)| b.iter(|| U4096::from_digits_bin(digits, exp)),
        );
    }
}

fn from_digits_bin_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_digits_bin_iter");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;

        let exp = 7;
        let radix = 1 << exp;
        let digits = (0..len).map(|_| rng.random_range(..radix)).collect_with([0; BYTES]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(
            BenchmarkId::new("S4096", 8 * len),
            &(&digits[..len].iter().copied(), exp),
            |b, &(iter, exp)| b.iter(|| S4096::from_digits_bin_iter(iter.clone(), exp)),
        );

        group.bench_with_input(
            BenchmarkId::new("U4096", 8 * len),
            &(&digits[..len].iter().copied(), exp),
            |b, &(iter, exp)| b.iter(|| U4096::from_digits_bin_iter(iter.clone(), exp)),
        );
    }
}

fn into_digits(c: &mut Criterion) {
    let mut group = get_group(c, "long::into_digits");
    let mut rng = get_rng();

    for radix in [255u8, 127u8, 63u8, 31u8, 15u8, 7u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::from(&bytes[..]);
        let unsigned = U4096::from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits(radix))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits(radix))
        });
    }
}

fn into_digits_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::into_digits_iter");
    let mut rng = get_rng();

    for radix in [255u8, 127u8, 63u8, 31u8, 15u8, 7u8, 3u8] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::from(&bytes[..]);
        let unsigned = U4096::from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", radix), &(&signed, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits_iter(radix).map(|it| it.count()))
        });

        group.bench_with_input(BenchmarkId::new("U4096", radix), &(&unsigned, radix), |b, &(long, radix)| {
            b.iter(|| long.into_digits_iter(radix).map(|it| it.count()))
        });
    }
}

fn to_digits_bin(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_digits_bin");
    let mut rng = get_rng();

    for exp in [7, 6, 5, 4, 3, 2, 1] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::from(&bytes[..]);
        let unsigned = U4096::from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", exp), &(&signed, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_bin::<u8>(exp))
        });

        group.bench_with_input(BenchmarkId::new("U4096", exp), &(&unsigned, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_bin::<u8>(exp))
        });
    }
}

fn to_digits_bin_iter(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_digits_bin_iter");
    let mut rng = get_rng();

    for exp in [7, 6, 5, 4, 3, 2, 1] {
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::from(&bytes[..]);
        let unsigned = U4096::from(&bytes[..]);

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(BenchmarkId::new("S4096", exp), &(&signed, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_bin_iter::<u8>(exp).map(|it| it.count()))
        });

        group.bench_with_input(BenchmarkId::new("U4096", exp), &(&unsigned, exp), |b, &(long, exp)| {
            b.iter(|| long.to_digits_bin_iter::<u8>(exp).map(|it| it.count()))
        });
    }
}

fn from_str(c: &mut Criterion) {
    let mut group = get_group(c, "long::from_str");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::from(&bytes[..len]);
        let unsigned = U4096::from(&bytes[..len]);

        let dec_signed = format!("{:#}", &signed);
        let bin_signed = format!("{:#b}", &signed);
        let oct_signed = format!("{:#o}", &signed);
        let hex_signed = format!("{:#x}", &signed);

        let dec_unsigned = format!("{:#}", &unsigned);
        let bin_unsigned = format!("{:#b}", &unsigned);
        let oct_unsigned = format!("{:#o}", &unsigned);
        let hex_unsigned = format!("{:#x}", &unsigned);

        group.throughput(Throughput::Bytes(dec_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("dec::S4096", 8 * len), &dec_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(dec_unsigned.len() as u64));

        group.bench_with_input(BenchmarkId::new("dec::U4096", 8 * len), &dec_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(bin_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("bin::S4096", 8 * len), &bin_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(bin_unsigned.len() as u64));

        group.bench_with_input(BenchmarkId::new("bin::U4096", 8 * len), &bin_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(oct_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("oct::S4096", 8 * len), &oct_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(oct_unsigned.len() as u64));

        group.bench_with_input(BenchmarkId::new("oct::U4096", 8 * len), &oct_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(hex_signed.len() as u64));

        group.bench_with_input(BenchmarkId::new("hex::S4096", 8 * len), &hex_signed, |b, str| {
            b.iter(|| S4096::from_str(str))
        });

        group.throughput(Throughput::Bytes(hex_unsigned.len() as u64));

        group.bench_with_input(BenchmarkId::new("hex::U4096", 8 * len), &hex_unsigned, |b, str| {
            b.iter(|| U4096::from_str(str))
        });
    }
}

fn to_str(c: &mut Criterion) {
    let mut group = get_group(c, "long::to_str");
    let mut rng = get_rng();

    for div in (0..6).rev().map(|exp| 1usize << exp) {
        let len = BYTES / div;
        let bytes = rng.random::<[u8; BYTES]>();

        let signed = S4096::from(&bytes[..len]);
        let unsigned = U4096::from(&bytes[..len]);

        group.throughput(Throughput::Bytes(len as u64));

        group.bench_with_input(BenchmarkId::new("dec::S4096", 8 * len), &signed, |b, long| {
            b.iter(|| format!("{:#}", long))
        });

        group.bench_with_input(BenchmarkId::new("dec::U4096", 8 * len), &unsigned, |b, long| {
            b.iter(|| format!("{:#}", long))
        });

        group.bench_with_input(BenchmarkId::new("bin::S4096", 8 * len), &signed, |b, long| {
            b.iter(|| format!("{:#b}", long))
        });

        group.bench_with_input(BenchmarkId::new("bin::U4096", 8 * len), &unsigned, |b, long| {
            b.iter(|| format!("{:#b}", long))
        });

        group.bench_with_input(BenchmarkId::new("oct::S4096", 8 * len), &signed, |b, long| {
            b.iter(|| format!("{:#o}", long))
        });

        group.bench_with_input(BenchmarkId::new("oct::U4096", 8 * len), &unsigned, |b, long| {
            b.iter(|| format!("{:#o}", long))
        });

        group.bench_with_input(BenchmarkId::new("hex::S4096", 8 * len), &signed, |b, long| {
            b.iter(|| format!("{:#x}", long))
        });

        group.bench_with_input(BenchmarkId::new("hex::U4096", 8 * len), &unsigned, |b, long| {
            b.iter(|| format!("{:#x}", long))
        });
    }
}

criterion_group!(
    group,
    from_std_const,
    from_std,
    from_slice,
    from_iter,
    from_digits,
    from_digits_iter,
    from_digits_bin,
    from_digits_bin_iter,
    into_digits,
    into_digits_iter,
    to_digits_bin,
    to_digits_bin_iter,
    from_str,
    to_str
);

criterion_main!(group);

extern crate criterion;
extern crate fraction;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fraction::generic;
use fraction::{prelude::Decimal, GenericDecimal, GenericFraction};
#[cfg(all(feature = "with-bigint", feature = "with-dynaint"))]
use fraction::{DynaFraction, DynaInt, Num};
use std::str::FromStr;

#[allow(clippy::missing_panics_doc)]
pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("Decimal u128/u16 init", |b| {
        b.iter(|| GenericDecimal::<u128, u16>::from(black_box(15978.649)));
    });

    c.bench_function("Decimal i64/u16 init", |b| {
        b.iter(|| {
            let a = GenericDecimal::<i64, u16>::from(black_box(15978.649));
            let b = GenericDecimal::<i64, u16>::from(black_box(-15978.649));

            (a, b)
        });
    });

    c.bench_function("Convert int like from str", |b| {
        b.iter(|| {
            let a = GenericFraction::<u8>::from_str(black_box("1"));
            let b = GenericFraction::<u8>::from_str(black_box("100"));

            (a, b)
        });
    });

    c.bench_function("Convert float like from str", |b| {
        b.iter(|| {
            let a = GenericFraction::<u8>::from_str(black_box("1.0"));
            let b = GenericFraction::<u8>::from_str(black_box("100.001"));

            (a, b)
        });
    });

    c.bench_function("Convert fraction like from str", |b| {
        b.iter(|| {
            let a = GenericFraction::<u8>::from_str(black_box("1/1"));
            let b = GenericFraction::<u8>::from_str(black_box("255/255"));
            (a, b)
        });
    });

    #[cfg(all(feature = "with-bigint", feature = "with-dynaint"))]
    {
        // Round-five reference (CPU 0; 2 s warm-up / 8 s measurement; median of three):
        // Parser f7c4917 -> f774a72: small 4.4264 -> 4.2729 ns (-3.47%); promoted
        // 12.627 -> 12.710 ns (+0.66%); DynaFraction 50.565 -> 50.491 ns (-0.15%).
        // Absolute values are layout-sensitive and comparable only when this benchmark body/order is unchanged.
        c.bench_function("DynaInt small from_str_radix", |b| {
            b.iter(|| {
                let value: Result<DynaInt<u8, u16>, _> = Num::from_str_radix(black_box("42"), 10);
                black_box(value)
            });
        });

        c.bench_function("DynaInt promoted from_str_radix", |b| {
            b.iter(|| {
                let value: Result<DynaInt<u8, u16>, _> = Num::from_str_radix(black_box("4096"), 10);
                black_box(value)
            });
        });

        c.bench_function("DynaFraction from_str_radix", |b| {
            b.iter(|| {
                let value: Result<DynaFraction<u8>, _> = Num::from_str_radix(black_box("1/2"), 10);
                black_box(value)
            });
        });
    }

    c.bench_function("Decimal cmp integer early exit", |b| {
        let left = Decimal::from_str("123456").unwrap();
        let right = Decimal::from_str("999999").unwrap();

        b.iter(|| black_box(left).cmp(&black_box(right)));
    });

    c.bench_function("Decimal cmp reported equal pair", |b| {
        let left = Decimal::from_str("0.5").unwrap() / Decimal::from_str("0.3").unwrap();
        let right = Decimal::from_str("1.6").unwrap();

        b.iter(|| black_box(left).cmp(&black_box(right)));
    });

    c.bench_function(
        "Decimal cmp exact fraction same value different precision",
        |b| {
            let left = GenericDecimal::<u64, u8>::from_fraction_with_precision(
                GenericFraction::new(5u64, 3u64),
                1,
            );
            let right = GenericDecimal::<u64, u8>::from_fraction_with_precision(
                GenericFraction::new(5u64, 3u64),
                2,
            );

            b.iter(|| black_box(left).cmp(&black_box(right)));
        },
    );

    c.bench_function("Decimal cmp negative canonical zero", |b| {
        let left = Decimal::from_str("-0.9").unwrap().set_precision(0);
        let right = Decimal::from_str("-0.04").unwrap().set_precision(1);

        b.iter(|| black_box(left).cmp(&black_box(right)));
    });

    c.bench_function("Decimal cmp long common prefix p1", |b| {
        let left = Decimal::from_str("1.4").unwrap();
        let right = Decimal::from_str("1.5").unwrap();

        b.iter(|| black_box(left).cmp(&black_box(right)));
    });

    c.bench_function("Decimal cmp long common prefix p16", |b| {
        let left = Decimal::from_str("0.3141592653589793").unwrap();
        let right = Decimal::from_str("0.3141592653589794").unwrap();

        b.iter(|| black_box(left).cmp(&black_box(right)));
    });

    c.bench_function("Decimal cmp long common prefix p255", |b| {
        let left = GenericDecimal::<u64, u8>::from_fraction_with_precision(
            GenericFraction::new(1u64, 3u64),
            255,
        );
        let right = GenericDecimal::<u64, u8>::from_fraction_with_precision(
            GenericFraction::new(1u64, 3u64),
            254,
        );

        b.iter(|| black_box(left).cmp(&black_box(right)));
    });

    c.bench_function("generic::read_generic_integer / i8 to u8", |b| {
        b.iter(|| generic::read_generic_integer::<u8, i8>(black_box(14i8)).unwrap());
    });

    c.bench_function("generic::read_generic_integer / u8 to u8", |b| {
        b.iter(|| generic::read_generic_integer::<u8, u8>(black_box(14u8)).unwrap());
    });

    c.bench_function("From couple", |b| {
        b.iter(|| GenericFraction::<u8>::from(black_box((3u8, 4u8))));
    });

    #[cfg(feature = "with-approx")]
    {
        let num2 = GenericFraction::<u8>::from(2);
        let small_num = fraction::BigFraction::new(1_u8, u128::MAX) / u128::MAX;
        let big_num = fraction::BigFraction::new(u128::MAX, 1_u8) * u128::MAX;

        let mut bench_dp = |n: u32| {
            let mut group = c.benchmark_group(format!("Sqrt {n}dp raw"));

            group.bench_function("2", |b| {
                b.iter(|| num2.sqrt_raw(n));
            });

            group.bench_function("Small", |b| {
                b.iter(|| small_num.sqrt_raw(n));
            });

            group.bench_function("Big", |b| {
                b.iter(|| big_num.sqrt_raw(n));
            });

            group.finish();
        };

        bench_dp(10_000);
        bench_dp(1_000);
        bench_dp(100);
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

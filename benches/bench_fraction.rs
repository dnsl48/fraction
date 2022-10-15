extern crate criterion;
extern crate fraction;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fraction::generic;
use fraction::{GenericDecimal, GenericFraction};
use std::str::FromStr;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("Decimal u128/u16 init", |b| {
        b.iter(|| GenericDecimal::<u128, u16>::from(black_box(15978.649)))
    });

    c.bench_function("Decimal i64/u16 init", |b| {
        b.iter(|| {
            let a = GenericDecimal::<i64, u16>::from(black_box(15978.649));
            let b = GenericDecimal::<i64, u16>::from(black_box(-15978.649));

            (a, b)
        })
    });

    c.bench_function("Convert int like from str", |b| {
        b.iter(|| {
            let a = GenericFraction::<u8>::from_str(black_box("1"));
            let b = GenericFraction::<u8>::from_str(black_box("100"));

            (a, b)
        })
    });

    c.bench_function("Convert float like from str", |b| {
        b.iter(|| {
            let a = GenericFraction::<u8>::from_str(black_box("1.0"));
            let b = GenericFraction::<u8>::from_str(black_box("100.001"));

            (a, b)
        })
    });

    c.bench_function("Convert fraction like from str", |b| {
        b.iter(|| {
            let a = GenericFraction::<u8>::from_str(black_box("1/1"));
            let b = GenericFraction::<u8>::from_str(black_box("255/255"));
            (a, b)
        })
    });

    c.bench_function("generic::read_generic_integer / i8 to u8", |b| {
        b.iter(|| generic::read_generic_integer::<u8, i8>(black_box(14i8)).unwrap())
    });

    c.bench_function("generic::read_generic_integer / u8 to u8", |b| {
        b.iter(|| generic::read_generic_integer::<u8, u8>(black_box(14u8)).unwrap())
    });

    c.bench_function("From couple", |b| {
        b.iter(|| GenericFraction::<u8>::from(black_box((3u8, 4u8))))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

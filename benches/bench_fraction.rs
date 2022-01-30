extern crate criterion;
extern crate fraction;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fraction::{GenericDecimal, GenericFraction};
use std::str::FromStr;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("Decimal u128/u16 init", |b| {
        b.iter(|| {
            GenericDecimal::<u128, u16>::from(black_box(15978.649));
        })
    });

    c.bench_function("Decimal i64/u16 init", |b| {
        b.iter(|| {
            GenericDecimal::<i64, u16>::from(black_box(15978.649));
            GenericDecimal::<i64, u16>::from(black_box(-15978.649));
        })
    });

    c.bench_function("Convert int like from str", |b| {
        b.iter(|| {
            GenericFraction::<u8>::from_str(black_box("1"));
            GenericFraction::<u8>::from_str(black_box("100"));
        })
    });

    c.bench_function("Convert float like from str", |b| {
        b.iter(|| {
            GenericFraction::<u8>::from_str(black_box("1.0"));
            GenericFraction::<u8>::from_str(black_box("100.001"));
        })
    });

    c.bench_function("Convert fraction like from str", |b| {
        b.iter(|| {
            GenericFraction::<u8>::from_str(black_box("1/1"));
            GenericFraction::<u8>::from_str(black_box("255/255"));
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

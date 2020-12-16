extern crate criterion;
extern crate fraction;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fraction::GenericDecimal;

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
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

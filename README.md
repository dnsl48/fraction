# Fraction

Lossless fractions and decimals for Rust; an aspirational drop-in replacement for floating-point types.

[![GitHub Actions](https://github.com/dnsl48/fraction/actions/workflows/main.yml/badge.svg?branch=master)](https://github.com/dnsl48/fraction/actions/workflows/main.yml?query=branch%3Amaster)
[![Documentation](https://docs.rs/fraction/badge.svg)](https://docs.rs/fraction/)
[![Current Version on crates.io](https://img.shields.io/crates/v/fraction.svg)](https://crates.io/crates/fraction/)
[![MSRV](https://img.shields.io/badge/MSRV-1.70-blue.svg)](#features)
[![Licence](https://img.shields.io/badge/licence-MIT%20/%20Apache%202.0-blue.svg)](#licence)

## Overview

`fraction` provides:

- `Fraction`, a rational type designed for float-like arithmetic with exact values
- `Decimal`, a lossless decimal representation with explicit precision
- `DynaInt`, a dynamically growing integer for checked maths
- hashable and orderable fractions, including deterministic ordering for `NaN`
- PostgreSQL, Juniper, Serde, Unicode, and approximate maths support via features

## Install

```toml
[dependencies]
fraction = "0.15.4"
```

Enable optional integrations explicitly:

```toml
[dependencies]
fraction = { version = "0.15.4", features = ["with-postgres-support", "with-serde-support"] }
```

## Features

The `default` feature set enables the features marked **Yes** below.

| Feature                 | Default? | Overview                                                                                                             |
|-------------------------|----------|----------------------------------------------------------------------------------------------------------------------|
| `with-bigint`           | Yes      | Adds `num::BigInt`/`BigUint` support, re-exports those types, and enables aliases such as `BigFraction`.             |
| `with-decimal`          | Yes      | Adds `GenericDecimal` and decimal aliases such as `Decimal`, with precision retained for formatting and comparison.  |
| `with-dynaint`          | Yes      | Adds `DynaInt`, which keeps small integers inline and promotes them to a larger backing type on overflow.            |
| `with-approx`           | No       | Enables `with-bigint` and adds accuracy-controlled square-root helpers for fractions and, when enabled, decimals.    |
| `with-juniper-support`  | No       | Adds Juniper GraphQL scalar, input, and output implementations for the enabled fraction and decimal types.           |
| `with-postgres-support` | No       | Adds PostgreSQL `NUMERIC` `ToSql`/`FromSql` conversions for the enabled fraction and decimal types.                  |
| `with-serde-support`    | No       | Adds Serde `Serialize`/`Deserialize` implementations for enabled fraction, decimal, sign, and dynamic-integer types. |
| `with-unicode`          | No       | Adds Unicode fraction formatting and parsing helpers for `GenericFraction`.                                          |

MSRV note: Rust 1.70 is the declared minimum and is CI-tested for the `with-bigint`/`with-approx` surface exercised by
the MSRV smoke harness. Latest stable is tested with all features enabled. Optional integration dependency graphs,
including `with-juniper-support` and `with-postgres-support`, may require a newer compiler under fresh dependency
resolution.

Unlike primitive floats, `Fraction` treats `NaN` as equal to itself and orders it below negative infinity. That makes
fractions usable in sets, hash maps, and B-trees.

## Examples

### Fraction

```rust
use std::str::FromStr;
use fraction::{Fraction, One, Zero, Sign};

let f = Fraction::new(1u8, 2u8);
assert_eq!(f, Fraction::new_generic(Sign::Plus, 1i32, 2u8).unwrap());
assert_eq!(f, Fraction::from(0.5));
assert_eq!(f, Fraction::from_str("0.5").unwrap());
assert_eq!(f, Fraction::from_str("1/2").unwrap());
assert_eq!(Fraction::from_str("1/0").unwrap(), Fraction::infinity());
assert_eq!(Fraction::from_str("-1/0").unwrap(), Fraction::neg_infinity());
assert_eq!(Fraction::from_str("0/0").unwrap(), Fraction::nan());
assert_eq!(f * 2, Fraction::one());
assert_eq!(f - f, Fraction::zero());
```

### Decimal

```rust
use std::str::FromStr;
use fraction::{Decimal, Fraction};

let d = Decimal::from(1);
assert_eq!(d, Decimal::from_fraction(Fraction::from(1)));

let d = Decimal::from(1.3);
assert_eq!(d, Decimal::from_str("1.3").unwrap());

let d = Decimal::from(0.5);
// Decimal fraction notation inherits the same zero-denominator mapping as Fraction::from_str.
assert_eq!(d, Decimal::from_str("1/2").unwrap());
assert_eq!(Decimal::from_str("1/0").unwrap(), Decimal::infinity());
assert_eq!(Decimal::from_str("-1/0").unwrap(), Decimal::neg_infinity());
assert_eq!(Decimal::from_str("0/0").unwrap(), Decimal::nan());

let one_third = Fraction::new(1u8, 3u8);
assert_eq!(
    Decimal::from_fraction_with_precision(one_third, 4).to_string(),
    "0.3333"
);
```

### Formatting

```rust
type F = fraction::Fraction;

let result = F::from(0.7) / F::from(0.4);
assert_eq!(format!("{}", result), "7/4");
assert_eq!(format!("{:.2}", result), "1.75");
assert_eq!(format!("{:#.3}", result), "1.750");
```

### Unicode

When `with-unicode` is enabled, Unicode display helpers are available.

```rust
#[cfg(feature = "with-unicode")]
{
    type F = fraction::Fraction;

    let res = F::from(0.7) / F::from(0.4);
    assert_eq!("7⁄4", format!("{}", res.get_unicode_display()));
    assert_eq!("⁷/₄", format!("{}", res.get_unicode_display().supsub()));
}
```

## PostgreSQL notes

Use `Decimal` rather than `Fraction` for PostgreSQL work where possible. PostgreSQL’s binary protocol uses `i16`, so the
base type for `GenericFraction` or `GenericDecimal` should be at least `u16`.

For very large or repeating values such as `1/3` or `1/7`, `Fraction` can grow to 16383 digits after the decimal point,
which is slower than an explicitly precision-bound `Decimal`. If you need dynamic growth, `DynaInt<u8, _>` or
`DynaInt<usize, BigUint>` can help.

## Documentation

- [crate docs on docs.rs](https://docs.rs/fraction/)
- [changelog](CHANGELOG.md)

## Licence

Licensed under either of:

- [MIT](LICENSE-MIT)
- [Apache License, Version 2.0](LICENSE-APACHE)

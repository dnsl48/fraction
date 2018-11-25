# Fraction

Lossless fractions and decimals; drop-in float replacement
------

[![Current Version on crates.io](https://img.shields.io/crates/v/fraction.svg)](https://crates.io/crates/fraction/) [![MIT / Apache2 License](https://img.shields.io/badge/license-MIT%20/%20Apache2-blue.svg)]() [![Build Status](https://travis-ci.org/dnsl48/fraction.svg?branch=master)](https://travis-ci.org/dnsl48/fraction) [![Documentation](https://docs.rs/fraction/badge.svg)](https://docs.rs/fraction/)
------

# Features
 - Drop in replacement for floats with the exception for NaN == NaN so that it's hashable
 - It's hashable, so may be used as values in Sets and keys in dictionaries and hash maps
 - Fraction type, representing floats as fractions
 - Decimal type, based on Fraction type, represents floats as decimals
 - DynaInt implements dinamically growing integer type that perfarms checked math and avoids stack overflows
 - PostgreSQL integration for Numeric/Decimal type (with no extra memory allocations)
 - Juniper integration for both fractions and decimals
 - Generic integer conversions, such as `i8 -> u8`, `usize -> u8` and so on
 - Lossless division with no allocations and infinite precision

# Examples

## Simple arithmetic
```rust
use fraction::Fraction;

fn main () {
  let mut fr = Fraction::zero ();

  fr = fr + Fraction::from (2);   // 0 + 2   = 2
  fr = fr / Fraction::from (0.5); // 2 / 0.5 = 4

  assert_eq! (fr, Fraction::from (4));
  assert_eq! (4.0f64, fr.to_f64 ());
}
```

## Decimal
```rust
type D = fraction::Decimal;

let result = D::from(0.5) / D::from(0.3);
assert_eq!(format!("{:.4}", result), "1.6666");
```

## Using as keys for a HashMap
```rust
use std::collections::HashMap;
use fraction::Fraction;

fn main () {
  let f = Fraction::from (0.75);

  let mut map: HashMap<Fraction, ()> = HashMap::new ();

  map.insert (f, ());

  assert! (map.contains_key (&Fraction::new (3u64, 4u64)));   // 0.75 == 3/4
  assert! (map.contains_key (&Fraction::new (6u64, 8u64)));   // 0.75 == 6/8
  assert! (map.contains_key (&Fraction::new (12u64, 16u64))); // 0.75 == 12/16
  assert! (! map.contains_key (&Fraction::from (0.5))); // 0.75 != 1/2
}
```

### Generic integer conversion
```rust
use fraction::{Sign, GenericFraction};

type F = GenericFraction<u32>;

let fra = F::new_generic(Sign::Plus, 1i8, 42usize).unwrap();
assert_eq!(fra, F::new(1u32, 42u32));
```

## Comparison
```rust
use fraction::Fraction;

fn main () {
  let f14 = Fraction::new (1u64, 4u64); // 1/4 == 0.25
  let f12 = Fraction::new (1u64, 2u64); // 1/2 == 0.50
  let f24 = Fraction::new (2u64, 4u64); // 2/4 == 0.50
  let f34 = Fraction::new (3u64, 4u64); // 3/4 == 0.75

  assert_eq! (f12, f24);                   // 1/2 == 2/4
  assert_eq! (f34, f12 + f14);             // 3/4 == 1/2 + 1/4
  assert_eq! (f14, Fraction::from (0.25)); // 1/4 == 0.25
}
```


# Change Log

Look into the [CHANGELOG.md](CHANGELOG.md) file for details

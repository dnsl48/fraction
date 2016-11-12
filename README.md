# Fraction
Lossless float that may be used in matching, ordering and hashing
------

[![Current Version on crates.io](https://img.shields.io/crates/v/fraction.svg)](https://crates.io/crates/fraction/) [![MIT / Apache2 License](https://img.shields.io/badge/license-MIT%20/%20Apache2-blue.svg)]() [![Build Status](https://travis-ci.org/dnsl48/fraction.svg?branch=master)](https://travis-ci.org/dnsl48/fraction)
------
 * The main goal of Fraction is to keep precision that floats cannot do
 * Fractions can be used for matching and comparisons and thus for hashing
 * Base arithmetic implemented upon [`num`](http://rust-num.github.io/num/num/index.html) crate (`rational` module)
 * `Fraction` struct implementation uses two `u64` numbers and arithmetic on stack
 * `BigFraction` struct implementation uses two limitless `BigUint` numbers and arithmetic on heap

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


## Upcoming release
### Refactoring
- More efficient implementation of `From<[unsigned ints]>`
- More generic implementation of `From<BigInt>`


## [0.3.2] - 2016-11-13
### Refactoring
- `Zero::is_zero` to be used everywhere in math, rather than making new zero vals + comparing with them

### Added
- `fn new_nan` constructor
- `fn new_inf` constructor
- `fn new_inf_neg` constructor


## [0.3.1] - 2016-11-12
### Added
- `fn format_as_float` implementation for GenericFraction<T> (it was only available for BigFraction before)

### Changed
- `Into<T>` to be used in bounds rather than `From<N>`, since it's more flexible (thanks to Alexander Altman for the patch)
- number of bug fixes within `fn format_as_float` + test coverage


## [0.3.0] - 2016-11-08
### Added
- From<(N, D)> generic implementation (through std::fmt::Display)

### Changed
- GenericFraction<T> copy semantic to be applied only when `T: Clone`
- GenericFraction impl, constructors refactoring (new, new_raw)
- `num` upgraded up to `0.1.36` (from `0.1.34`)

### Removed
- `fn new` does not perform type casting through fmt::Display anymore (that functionality moved out as `From<(N, D)>`)


## [0.2.2] - 2016-09-17
### Added
- `impl From<num::BigInt> for BigFraction`
- `impl From<num::BigUint> for BigFraction`


## [0.2.1] - 2016-08-28
### Changed
- Package description has been changed


## [0.2.0] - 2016-08-28
### Added
- [num crate](https://crates.io/crates/num) is a dependency now
- `GenericFraction<T>` implemented upon `num::Ratio<T>`
- `BigFraction` implementation based on `num::BigRational` (using heap)
- `num::traits::Bounded` trait implemented
- `fn min_positive_value` implemented
- `num::traits::ToPrimitive` trait implemented
- `num::traits::Signed` trait implemented
- `From<f64>` trait implementation now relies on `format!` macro instead of `f64::fract`
- `BigFraction` struct using `num::BigUint`
- `fn format_as_float` for BigFraction has been implemented

### Changed
- The codebase has been rewritten and the license has been changed from `LGPL-3` to `MIT/Apache2` dual
- no more convertions into INFINITY on arithmetic overflows
- `fn to_f64` now returns `Option<f64>` instead of `f64` (`num::trait::ToPrimitive` implementation)
- `From` trait implementation uses `fmt::Display` from now on

### Removed
- `fn unpack` removed
- `std::cmp::Ord` implementation removed in regard to `NaN` values


## [0.1.0] - 2016-01-24
### Added
- Basic implementation

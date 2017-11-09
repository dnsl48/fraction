# Fraction
Lossless float that may be used in matching, ordering and hashing
------

[![Current Version on crates.io](https://img.shields.io/crates/v/fraction.svg)](https://crates.io/crates/fraction/) [![MIT / Apache2 License](https://img.shields.io/badge/license-MIT%20/%20Apache2-blue.svg)]() [![Build Status](https://travis-ci.org/dnsl48/fraction.svg?branch=master)](https://travis-ci.org/dnsl48/fraction) [![Documentation](https://docs.rs/fraction/badge.svg)](https://docs.rs/fraction/)
------

More documentation available on [docs.rs](https://docs.rs/fraction/).

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

Look into the [CHANGELOG.md](CHANGELOG.md) file for details
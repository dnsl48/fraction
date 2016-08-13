# Fraction
------
WARNING: The lib is deprecated. Use [num-rational](https://crates.io/crates/num-rational) instead.
Also, you may find the whole [num](https://crates.io/crates/num) crate quite useful.
If you need to keep the values like INF, -INF and NaN, you probably might go with a simple enum like this one:
```rust
pub enum FloatValue {
    Ratio (BigRational),
    Inf,
    NegInf,
    NaN
}
```
------
[!['LGPLv3 License'](http://img.shields.io/badge/license-LGPLv3-blue.svg)](https://www.gnu.org/licenses/lgpl.html) [![Build Status](https://travis-ci.org/dnsl48/fraction.svg?branch=master)](https://travis-ci.org/dnsl48/fraction)
------
* Fraction data type with lossless arithmetic that is more precise than float and can be used for hashing.
* The main goal of Fraction is keeping precision that floats cannot do.
* Fractions do not lose information about numbers and thus can be used for matching, comparisons and hashing (key values for HashMaps).
* Base arithmetic operators are also available (+ - / *), even though they work slower than for native numbers.
* Overflow checks are being performed for every arithmetic operation, so that Fraction becomes infinite, negative_infinite or NaN.

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

  assert! (map.contains_key (&Fraction::new (3, 4)));   // 0.75 == 3/4
  assert! (map.contains_key (&Fraction::new (6, 8)));   // 0.75 == 6/8
  assert! (map.contains_key (&Fraction::new (12, 16))); // 0.75 == 12/16
  assert! (! map.contains_key (&Fraction::from (0.5))); // 0.75 != 1/2
}
```

## Comparison
```rust
use fraction::Fraction;

fn main () {
  let f14 = Fraction::new (1, 4); // 1/4 == 0.25
  let f12 = Fraction::new (1, 2); // 1/2 == 0.50
  let f24 = Fraction::new (2, 4); // 2/4 == 0.50
  let f34 = Fraction::new (3, 4); // 3/4 == 0.75

  assert_eq! (f12, f24);                   // 1/2 == 2/4
  assert_eq! (f34, f12 + f14);             // 3/4 == 1/2 + 1/4
  assert_eq! (f14, Fraction::from (0.25)); // 1/4 == 0.25
}
```

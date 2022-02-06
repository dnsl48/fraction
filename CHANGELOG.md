# Change Log

## [0.10.0]

### Added
 - `std::str::FromStr` trait implementation for GenericFraction and GenericDecimal
  Special thanks to Scott Wilson for the contribution
 - Deprecated `GenericFraction::from_decimal_str` and `GenericDecimal::from_decimal_str` in favour of of `std::str::FromStr`


## [0.9.0] - 2021-08-22

### Added
 - Default trait implementation for GenericFraction and GenericDecimal
 - `postgres-types: ^0.2` and `bytes: 1` are new optional dependencies (feature: with-postgres-support)
 - `GenericFraction::new_raw_signed` constructor

### Changed
 - Juniper supported version upgraded from 0.11 to 0.15
 - Postgres supported version upgraded from 0.15 to 0.19 (might be down to 0.16, but untested).

### Removed
 - `postgres` crate is not a dependency any longer
 - Deprecated fn `GenericFraction::format_as_decimal` is removed

## [0.8.0] - 2020-12-17
### Changed
 - More efficient f32/f64 conversion to Fractions and Decimals (up to 10 times faster and not using memory allocation anymore)
   Special thanks to Christopher Rabotin for the contribution!

## [0.7.0] - 2020-12-05
### Added
 - fraction::display::Format implements Clone trait (becomes cloneable)
 - fraction::Sign implements PartialOrd and Ord traits (becomes orderable)
 - GenericDecimal::calc_precision max_precision optional argument to limit the calculation

### Changed
 - Decimal::from_fraction now limits precision calculation to 255
 - rustfmt for the whole codebase
 - small readability refactoring for some methods

## [0.6.3] - 2020-05-07
### Added
 - std::iter::{Sum, Product} implemented for GenericFraction and GenericDecimal

## [0.6.2] - 2019-05-20
### Addad
 - std::error::Error implemented for error::ParseError

## [0.6.1] - 2019-03-29
### Added
 - dynaint, `Into<BigUint>` implementation
 - fraction, `GenericFraction::into_fraction<I>` method implementation

## [0.6.0] - 2019-02-05
### Added
- division::divide_to_callback implementation. Some other functions refactored to be using it internally
- fraction::display module implementation, Fraction ::std::fmt::Display implementation supporting all the features of the std::fmt::Formatter
- Decimal ::std::fmt::Display implementation supporting all the features of the std::fmt::Formatter

### Changed
- Juniper updated to 0.11
- GenericFraction::format_as_decimal is now deprecated. Use format! macro instead, or division module if you need more control
- division module functions signatures now have flags for trailing zeroes

### Removed
- Deprecated functions

## [0.5.0] - 2018-11-26
### Changed
- Division module API; functions to return division state for later reuse (remainder and divisor)


## [0.4.1] - 2018-10-19
### Added
 - `DynaInt`, initial `std::fmt::Display` implementation


## [0.4.0] - 2018-10-10
### Bugs
 - `Hash` implementation for `GenericFraction` now returns equal hashes for negative and positive zeroes

### Added
- Lossless division, fraction decimal representation with infinite precision
- Decimal type, built on top of Fraction
- PostgreSQL integration
- Juniper integration
- Types with dynamic growth into heap on overflow
- Generic integer conversions (usize -> i8, i8 -> u8, etc)
- Examples and documentation for new features
- Re-exporting the bunch of `num` traits so that the library can be used without explicit dependency on `num`

### Refactoring
- The lib has been split into modules with separate features

### Modules
- `convert` module with traits for optimistic convesion
- `decimal` module with `GenericDecimal` implementation, `Juniper` and `PostgreSQL` integration for it
- `division` module with lossless infinite division implementation without memory allocation
- `dynaint` module with `DynaInt` type implementation (dynamically growing integer)
- `error` module with shared library error types
- `fraction` module with `GenericFraction` implementation, `Juniper` and `PostgreSQL` integration for it
- `generic` module with `GenericInteger` trait implementation, generic integer types conversion
- `prelude` module with some predefined type aliases such as `Fraction` and `Decimal`
- `tests` module with some tests

### Features
- `with-bigint` (default), integration with `num::{BigInt, BigUint}` types
- `with-decimal` (default), `GenericDecimal` type implementation
- `with-dynaint` (default), `DynaInt` type implementation
- `with-juniper-support`, `Juniper 0.10` integration
- `with-postgres-support`, `Postgres 0.15` integration

### Changes
- `GenericFraction` redundant methods deprecated: `new_nan`, `new_inf`, `new_inf_neg`, `into_big`, `format_as_float`


## [0.3.7] - 2017-11-10
### Bugs
 - Fix comparisons with negative numbers


## [0.3.6] - 2017-07-27
### Bugs
- `T in GenericFraction<T>` is `Clone + Integer` from now onwards (thanks to Taryn Hill aka Phrohdoh)


## [0.3.5] - 2017-04-17
### Changed
 - `num` package dependency version updated from "0.1.36" to "0.1.37"


## [0.3.4] - 2016-12-11
### Bugs
- `fn _new` now returns NaN for 0/0 (was Infinity before)
- `fn sign` now returns values for GenericFraction::Infinite values too
- `fn neg_zero` now returns zero with negative sign (was positive before)
- `fn recip` now handles zero values gracefully (does not panic, returns Infinity)

### Added
- Lots of documentation


## [0.3.3] - 2016-11-18
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
- `fn format_as_float` implemented for `GenericFraction<T>` (it was only available for BigFraction before)

### Changed
- `Into<T>` to be used in bounds rather than `From<N>`, since it's more flexible (thanks to Alexander Altman for the patch)
- number of bug fixes within `fn format_as_float` + test coverage


## [0.3.0] - 2016-11-08
### Added
- `From<(N, D)>` generic implementation (through std::fmt::Display)

### Changed
- `GenericFraction<T>` copy semantic to be applied only when `T: Clone`
- `GenericFraction` impl, constructors refactoring (new, new_raw)
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

#![doc(test(attr(deny(warnings), allow(deprecated))))]

//! Fraction is designed to be a precise lossless drop-in replacement for floating types (f32, f64).
//!
//! It comes with a number of predefined type aliases covering the most common use cases such as
//! [Fraction], [Decimal], [BigFraction], [DynaDecimal] and so on (see [prelude] module for more examples).
//!
//! The public API provides you with the generic types that you may use straightforwardly to build your
//! own types, suiting your needs best (see [prelude] module for the examples).
//!
//! # Library features
//!
//! - Drop in replacement for floats with the exception for NaN == NaN so that it's hashable
//! - It's hashable, so may be used as values in Sets and keys in dictionaries and hash maps
//! - [Display](fraction::display) implementation for fractions and decimals
//! - [Fraction](GenericFraction) type, representing fractions
//! - [Decimal](GenericDecimal) type, based on [Fraction](GenericFraction) type represents floats as lossless decimals
//! - [DynaInt](dynaint) implements dinamically growing integer type that perfarms checked math and avoids stack overflows
//! - PostgreSQL binary protocol integration for both fractions and decimals
//! - Juniper support for both fractions and decimals
//! - [Generic integer conversions](generic), such as `i8 -> u8`, `usize -> u8` and so on
//! - [Lossless division](division) with no allocations and infinite precision
//!
//! # Disclaimer
//! Even though we do our best to keep it well covered with tests, there may be bugs out there.
//! The library API is still in flux. When it gets stable we will release the version 1.0.0.
//! You may find more info about Semantic Versioning on [https://semver.org/](https://semver.org/).
//! Bug reports and contributions are appreciated.
//!
//! # Crate features
//! - `with-bigint` (default) integration with [num::BigInt] and [num::BigUint] data types
//! - `with-decimal` (default) [Decimal] type implemented upon [GenericFraction]
//! - `with-dynaint` (default) dynamically growing integer avoiding stack overflows
//! - `with-juniper-support` [Juniper](https://crates.io/crates/juniper) integration
//! - `with-postgres-support` [PostgreSQL](https://crates.io/crates/postgres) integration; Numeric/Decimal type
//! - `with-serde-support` [Serde](https://crates.io/crates/serde) traits implementation
//!
//! # Implementation
//! Basic math implemented upon the [num] crate (in particular the [num::rational] module).
//! The utilised traits from the [num] crate are re-exported, so you don't have to explicitly depend on that crate however,
//! you may import them from either of crates if necessary.
//!
//! # Usage
//! To start using types see the [Prelude](self::prelude) module.
//!
//! # Examples
//!
//! ## Simple use:
//!
//! ```
//! type F = fraction::Fraction; // choose the type accordingly to your needs (see prelude module docs)
//!
//! let two = F::from(0) + F::from(2);   // 0 + 2 = 2
//! let two_third = two / F::from(3);    // 2/3 = 0.666666[...]
//!
//! assert_eq!(F::from(2), two);
//! assert_eq!(F::new(2u64, 3u64), two_third);
//!
//! assert_eq!("2/3", format!("{}", two_third));  // print as Fraction (by default)
//! assert_eq!("0.6666", format!("{:.4}", two_third));  // format as decimal and print up to 4 digits after floating point
//! ```
//!
//! Decimal is implemented as a representation layer on top of Fraction.
//! Thus, it is also lossless and may require explicit control over "precision"
//! for comparison and formatting operations.
//! ```
//! type D = fraction::Decimal;
//!
//! let result = D::from(0.5) / D::from(0.3);
//!
//! assert_eq!(format!("{}", result), "1.6"); // calculation result uses precision of the operands
//! assert_eq!(format!("{:.4}", result), "1.6666");  // explicitly passing precision to format
//!
//! assert_eq!("1.6666", format!("{}", result.set_precision(4))); // the other way to set precision explicitly on Decimal
//! ```
//!
//! ## Construct:
//!
//! Fraction:
//! ```
//! use std::str::FromStr;
//! use fraction::{Fraction, Sign};  // choose the type accordingly with your needs (see prelude module docs)
//!
//! fn main() {
//!     // There are several ways to construct a fraction, depending on your use case
//!
//!     let f = Fraction::new(1u8, 2u8);  // constructs with numerator/denominator and normalizes the fraction (finds least common denominator)
//!     assert_eq!(f, Fraction::new_generic(Sign::Plus, 1i32, 2u8).unwrap());  // with numerator/denominator of different integer types
//!     assert_eq!(f, Fraction::from(0.5));  // convert from float (f32, f64)
//!     assert_eq!(f, Fraction::from_str("0.5").unwrap());  // parse a string
//!
//!     // Raw construct with no extra calculations.
//!     // Most performant, but does not look for common denominator and may lead to unexpected results
//!     // in following calculations. Only use if you are sure numerator/denominator are already normalized.
//!     assert_eq!(f, Fraction::new_raw(1u64, 2u64));
//! }
//! ```
//!
//! Decimal:
//! ```
//! use std::str::FromStr;
//! use fraction::{Decimal, Fraction};  // choose the type accordingly with your needs (see prelude module docs)
//!
//! fn main() {
//!     // There are similar ways to construct Decimal. Underneath it is always represented as Fraction.
//!     // When constructed, Decimal preserves its precision (number of digits after floating point).
//!     // When two decimals are calculated, the result takes the biggest precision of both.
//!     // The precision is used for visual representation (formatting and printing) and for comparison of two decimals.
//!     // Precision is NOT used in any calculations. All calculations are lossless and implemented through Fraction.
//!     // To override the precision use Decimal::set_precision.
//!
//!     let d = Decimal::from(1);  // from integer, precision = 0
//!     assert_eq!(d, Decimal::from_fraction(Fraction::from(1))); // from fraction, precision is calculated from fraction
//!
//!     let d = Decimal::from(1.3);  // from float (f32, f64)
//!     assert_eq!(d, Decimal::from_str("1.3").unwrap());
//! }
//! ```
//!
//! ## Format (convert to string)
//! Formatting works similar for both Decimal and Fraction (Decimal uses Fraction internally).
//! The format implementation closely follows the rust Format trait documentation.
//!
//! ```
//! type F = fraction::Fraction;
//!
//! let result = F::from(0.7) / F::from(0.4);
//! assert_eq!(format!("{}", result), "7/4");  // Printed as fraction by default
//! assert_eq!(format!("{:.2}", result), "1.75"); // if precision is defined, printed as decimal
//! assert_eq!(format!("{:#.3}", result), "1.750"); // to print leading zeroes, pass hash to the format
//! ```
//!
//! ### Generic integer conversion
//! ```
//! use fraction::{Sign, GenericFraction};
//!
//! type F = GenericFraction<u32>;
//!
//! let fra = F::new_generic(Sign::Plus, 1i8, 42usize).unwrap();
//! assert_eq!(fra, F::new(1u32, 42u32));
//! ```
//!
//! ### Postgres usage
//! Postgres uses i16 for its binary protocol, so you'll have to use at least u16
//! as the base type for fractions/decimals.
//! Otherwise you may workaround with DynaInt<u8, _something_more_than_u8_>.
//! The safest way to go with would be DynaInt based types
//! such as DynaFraction or DynaDecimal as they would prevent
//! stack overflows for high values.
//!
//! Beware bad numbers such as 1/3, 1/7.
//! Fraction keeps the highest achievable precision (up to 16383 digits after floating point).
//! Decimal uses its own precision.
//! So, if you may end up with bad numbers, it may be preferable to go with Decimals over Fractions.
//!
//! Both types (fractions and decimals) should work transparently
//! in accordance with Postgres crate documentation

extern crate num;

#[cfg(feature = "with-bigint")]
#[macro_use]
extern crate lazy_static;

#[cfg(feature = "with-bigint")]
pub use num::bigint::{BigInt, BigUint};

pub use num::rational::{ParseRatioError, Ratio};

pub use num::{
    Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, FromPrimitive, Integer, Num, One,
    Signed, ToPrimitive, Zero,
};

#[cfg(test)]
#[macro_use]
mod tests;

pub mod convert;

pub mod division;

pub mod error;

mod fraction;
pub use fraction::*;

pub mod generic;

pub mod prelude;
pub use self::prelude::*;

// ====================================== FEATURES ======================================

#[cfg(feature = "with-juniper-support")]
extern crate juniper;
#[cfg(feature = "with-postgres-support")]
#[macro_use]
extern crate postgres_types;

#[cfg(feature = "with-serde-support")]
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "with-serde-support")]
extern crate serde;

#[cfg(feature = "with-decimal")]
mod decimal;
#[cfg(feature = "with-dynaint")]
pub mod dynaint;

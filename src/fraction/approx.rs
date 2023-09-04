//! Approximate mathematical operations.
//!
//! This module implements operations that cannot guarantee lossless results, but which are
//! nonetheless useful. Using any functionality from within this module requires a compromise to be
//! made between performance and accuracy.

use crate::{generic::GenericInteger, GenericFraction, Sign};
use num::{
    bigint::{ToBigInt, ToBigUint},
    rational::Ratio,
    BigUint, Integer, ToPrimitive, Zero,
};

/// The level of accuracy to which a square root will be computed.
#[derive(Clone, Debug)]
pub struct SqrtAccuracy {
    /// The value by which we multiply and divide in order to truncate values.
    ///
    /// Truncation is implemented here by shifting the decimal place by multiplying by some power
    /// of 10, removing the fractional part of the result, then shifting the decimal place back by
    /// dividing by the same power of 10. This value is that power of 10.
    multiplier: BigUint,
}

impl SqrtAccuracy {
    /// Creates a new `SqrtAccuracy` with `tail` digits after the decimal point.
    pub fn new(tail: u32) -> SqrtAccuracy {
        SqrtAccuracy {
            multiplier: BigUint::from(10u8).pow(tail),
        }
    }

    /// Truncates the ratio formed by `numer` and `denom` so that its decimal equivalent has only
    /// the level of accuracy specified when `self` was created. This method takes ownership of
    /// `numer` by necessity, but `denom` does not need to be mutated and thus only a reference to
    /// it is required.
    ///
    /// This does **not** simplify the return value (hence `_raw`).
    fn truncate_ratio_raw(&self, mut numer: BigUint, denom: &BigUint) -> Ratio<BigUint> {
        numer *= &self.multiplier;

        // Integer division gets rid of any digits we don't want.
        numer /= denom;

        // We now have an integer, so we can 'divide' by just giving a denominator other than 1 -
        // in this case, we need to divide by the multiplier again.
        Ratio::new_raw(numer, self.multiplier.clone())
    }
}

/// An approximation of a square root.
pub enum SqrtApprox {
    /// A rational (i.e. fractional) approximation.
    ///
    /// Depending on the accuracy used, these numbers can be *very* large to store (>100 KB with
    /// excessive accuracy), so cloning is likely to be expensive. This size also means that
    /// computations can take a long time.
    Rational(Ratio<BigUint>),

    /// Positive infinity. This is returned when the square root of positive infinity is requested.
    PlusInf,

    /// Zero. This only occurs when the input is zero.
    Zero,

    /// An invalid number. This can only result from NaN input.
    NaN,
}

struct SqrtSetup {
    /// The initial estimate for the square root, used as a 'seed' for generating a more accurate
    /// approximation.
    estimate: SqrtApprox,

    /// The input value converted to a `Ratio`. This is merely a byproduct of the setup step, but
    /// since we need it later on it's efficient to keep it around.
    ///
    /// This isn't necessary if `estimate` isn't `Rational`.
    value_as_ratio: Option<Ratio<BigUint>>,
}

/// Generates the setup values for finding the square root of `value`.
///
/// The `value_as_ratio` field of the returned `SqrtSetup` will not be `None` if the `estimate`
/// field is `SqrtApprox::Rational`.
///
/// # Panics
/// This function will panic if `value` is negative.
fn sqrt_setup<Nd>(value: &GenericFraction<Nd>) -> SqrtSetup
where
    Nd: Clone + GenericInteger + ToBigInt + ToBigUint,
{
    match value {
        GenericFraction::Rational(Sign::Plus, ratio) => {
            // If we can convert the components of `ratio` into `f64`s, we can approximate the
            // square root using `f64::sqrt`. This gives an excellent starting point.
            let float_estimate = ratio
                .to_f64()
                .map(f64::sqrt)
                // `from_float` will give `None` if the result of `sqrt` is not finite (incl. NaN),
                // so we'll automatically fall back to the alternative method if `sqrt` fails here.
                .and_then(|float| {
                    let (n, d) = Ratio::<num::BigInt>::from_float(float)?.into();

                    // Why is `to_biguint` not `into_biguint`? `to_biguint` takes a reference only
                    // and clones the underlying data, and there's nothing we can do about it :/
                    Some(Ratio::new_raw(
                        n.to_biguint().unwrap(),
                        d.to_biguint().unwrap(),
                    ))
                });

            // Safety: `to_bigint` is guaranteed not to fail for any integer type, and we know that
            // `Nd` is an integer type.
            let ratio = Ratio::new_raw(
                ratio.numer().to_biguint().unwrap(),
                ratio.denom().to_biguint().unwrap(),
            );

            if let Some(estimate) = float_estimate {
                return SqrtSetup {
                    estimate: SqrtApprox::Rational(estimate),
                    value_as_ratio: Some(ratio),
                };
            }

            // If we couldn't use floats, we fall back to a crude estimate using truncated integer
            // square roots. This still isn't too bad.
            let estimate = Ratio::new(ratio.numer().sqrt(), ratio.denom().sqrt());

            SqrtSetup {
                estimate: SqrtApprox::Rational(estimate),
                value_as_ratio: Some(ratio),
            }
        }

        GenericFraction::Infinity(Sign::Plus) => SqrtSetup {
            estimate: SqrtApprox::PlusInf,
            value_as_ratio: None,
        },

        GenericFraction::NaN => SqrtSetup {
            estimate: SqrtApprox::NaN,
            value_as_ratio: None,
        },

        something_negative => panic!(
            "cannot take the square root of a negative number ({})",
            something_negative
        ),
    }
}

/// Halves `value` in-place while keeping it in simplest form. This is faster than standard
/// division.
fn halve_in_place_pos_rational(ratio: &mut Ratio<BigUint>) {
    // To mutate the numerator and denominator of the ratio we'll take ownership of both and then
    // put them back when we're done.
    let (mut numer, mut denom) = std::mem::take(ratio).into();

    if numer.is_even() {
        numer /= 2_u32;
    } else {
        denom *= 2_u32;
    }

    *ratio = Ratio::new_raw(numer, denom);
}

/// Adds two `Ratio`s together without reducing the result to simplest form. This is significantly
/// faster than using the standard addition operator provided by `num`, and may be used as long as
/// the result does not need to be in simplest form (e.g. within an algorithm which reduces the
/// output ratio before returning).
fn add_ratios_raw(lhs: Ratio<BigUint>, rhs: Ratio<BigUint>) -> Ratio<BigUint> {
    // Don't bother comparing the denominators because it's highly unlikely that they're equal.
    // Instead, we just go straight to giving the fractions equal denominators.
    let (mut lhs_numer, lhs_denom) = lhs.into();
    let (mut rhs_numer, rhs_denom) = rhs.into();

    let common_denom = lhs_denom.lcm(&rhs_denom);

    let lhs_multiplier = &common_denom / &lhs_denom;
    let rhs_multiplier = &common_denom / &rhs_denom;

    lhs_numer *= lhs_multiplier;
    rhs_numer *= rhs_multiplier;

    Ratio::new_raw(lhs_numer + rhs_numer, common_denom)
}

/// Converts a `SqrtApprox` into a `DynaFraction`.
fn convert_sqrt_output(approx: SqrtApprox, reduce: bool) -> GenericFraction<BigUint> {
    match approx {
        SqrtApprox::Rational(ratio) => GenericFraction::Rational(Sign::Plus, {
            if reduce {
                let (numer, denom) = ratio.into();

                // `Ratio::new` always returns the simplest form, so we don't need to explicitly
                // reduce the ratio. We could achieve the same thing just by returning
                // `ratio.reduced()`, but that would clone the numerator and denominator for...
                // idk, `num` reasons. `new` uses a private `reduce` method which does it all
                // in-place.
                Ratio::new(numer, denom)
            } else {
                ratio
            }
        }),

        SqrtApprox::PlusInf => GenericFraction::infinity(),
        SqrtApprox::Zero => GenericFraction::zero(),
        SqrtApprox::NaN => GenericFraction::nan(),
    }
}

/// Various square root operations for `GenericFraction`.
impl<T: Clone + Integer + ToBigUint + ToBigInt + GenericInteger> GenericFraction<T> {
    /// Returns an unsimplified rational approximation of the square root of `self`.
    ///
    /// If you need the result to be simplified, use `sqrt_with_accuracy` instead.
    ///
    /// The square of the resulting value is guaranteed to be equal to `self` to the number of
    /// decimal places specified by `accuracy`.
    ///
    /// # Panics
    /// This method will panic if `self` is negative.
    pub fn sqrt_with_accuracy_raw(&self, accuracy: &SqrtAccuracy) -> SqrtApprox {
        let SqrtSetup {
            estimate: initial_estimate,
            value_as_ratio,
        } = sqrt_setup(self);

        // If the initial estimate isn't rational, it must be something weird (inf, NaN, zero), so
        // we can return immediately.
        let SqrtApprox::Rational(estimate) = initial_estimate else {
            return initial_estimate;
        };

        // Take ownership of the two parts of the target ratio. This allows us to treat them
        // separately. For example, we must clone the numerator for the next step, but only a
        // reference to the denominator is needed. Therefore, we can avoid needlessly cloning both
        // halves.
        let (target_numer, target_denom) = {
            // Safety: `sqrt_setup` guarantees that `value_as_ratio` won't be `None` if
            // `initial_estimate` is `Rational`, which is what we matched above.
            value_as_ratio.unwrap().into()
        };

        // Truncate the target square so we can check against it to determine when to finish.
        let truncated_target = accuracy.truncate_ratio_raw(target_numer.clone(), &target_denom);

        let mut current_approx = estimate;

        loop {
            // We're using a highly optimised version of Newton's method here, broken into three
            // steps. Mathematically we would write
            //      r1 = 0.5(r0 + A/r0)
            // where r0 is the current guess, r1 is the next guess, and A is the value we're
            // finding the square root of.

            // One of the key optimisations is to avoid using the `Ratio` type's `std::ops`
            // implementations, as they ensure that the resulting `Ratio` is always in simplest
            // form. That's normally a useful property, but here we need to be able to perform many
            // iterations very quickly, and the process of reducing a fraction to simplest form is
            // really quite slow. This is especially true when dealing with the size of numbers
            // that we'll be dealing with after only a couple of iterations - as the approximation
            // gets more accurate, the numerator and denominator become larger. To get around this,
            // we use a lot of `new_raw` and explicit manipulation of the numerators and
            // denominators of fractions.

            // A/r0
            let divided = Ratio::new_raw(
                &target_numer * current_approx.denom(),
                &target_denom * current_approx.numer(),
            );

            // r0 + A/r0
            current_approx = add_ratios_raw(current_approx, divided);

            // 0.5(r0 + A/r0)
            halve_in_place_pos_rational(&mut current_approx);

            // For checking the approximation, we square it to see how close the result is to the
            // original input value.
            let squared_and_truncated = accuracy.truncate_ratio_raw(
                current_approx.numer() * current_approx.numer(),
                &(current_approx.denom() * current_approx.denom()),
            );

            // Stop and yield the current guess if it's close enough to the true value.
            if squared_and_truncated == truncated_target {
                // This is `_raw`, so we don't reduce.
                break SqrtApprox::Rational(current_approx);
            }
        }
    }

    pub fn sqrt_with_accuracy(&self, accuracy: &SqrtAccuracy) -> GenericFraction<BigUint> {
        convert_sqrt_output(self.sqrt_with_accuracy_raw(accuracy), true)
    }

    pub fn sqrt_raw(&self, decimal_places: u32) -> SqrtApprox {
        self.sqrt_with_accuracy_raw(&SqrtAccuracy::new(decimal_places))
    }

    pub fn sqrt(&self, decimal_places: u32) -> GenericFraction<BigUint> {
        convert_sqrt_output(self.sqrt_raw(decimal_places), true)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    #[test]
    fn test_simple() {
        // This test actually works because of our delegation to `f64::sqrt` for an initial
        // estimate. For square numbers `f64::sqrt` is able to give precise results, which we can
        // just verify and return. Newton's method would get close to these precise answers but
        // we'd never quite get there.

        let u8_25: crate::GenericFraction<u8> = crate::GenericFraction::from(25_f64);
        let x = u8_25.sqrt(10);

        assert_eq!(x, 5.into());
    }

    #[test]
    fn test_perf_10k() {
        let _ = crate::GenericFraction::<u8>::from(2_u8).sqrt_raw(10_000);
    }

    #[test]
    fn test_perf_100k() {
        let _ = crate::GenericFraction::<u8>::from(2_u8).sqrt_raw(100_000);
    }

    #[test]
    fn test_big_numbers() {
        let big_fraction = crate::DynaFraction::<u8>::from_str("5735874745115151552958367280658028638020529468164964850251033802750727314244020586751748892724760644/4789532131435371284839616979453671799246590610930954499621009334289181266216833845985099376094324166").unwrap();
        let sqrt = big_fraction.sqrt(1_000);

        let s = format!("{sqrt:.100}");
        assert_eq!(s, "1.0943425455728974838600903859180783076888376493725431295813967125637781050743787384965051763360943812");
    }
}

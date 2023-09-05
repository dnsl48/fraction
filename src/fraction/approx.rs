//! Approximate mathematical operations.
//!
//! This module implements operations that cannot guarantee lossless results, but which are
//! nonetheless useful. Using any functionality from within this module requires a compromise to be
//! made between performance and accuracy.

use crate::{generic::GenericInteger, BigFraction, GenericFraction, Sign};
use num::{
    bigint::{ToBigInt, ToBigUint},
    rational::Ratio,
    traits::Pow,
    BigUint, Integer, ToPrimitive, Zero,
};
use std::borrow::Borrow;

/// Levels of accuracy for an approximation, in terms of correct digits.
#[derive(Clone, Debug)]
pub enum Accuracy {
    /// At least 20 digits correct after the decimal point.
    #[cfg(feature = "lazy_static")]
    Dp20,

    /// At least 100 digits correct after the decimal point.
    #[cfg(feature = "lazy_static")]
    Dp100,

    /// At least 500 digits correct after the decimal point.
    #[cfg(feature = "lazy_static")]
    Dp500,

    /// An arbitrary number of correct digits.
    Custom {
        /// The multiplier used to check values for equality to the desired accuracy. **You
        /// probably want this to be `10^{n}`, where `n` is the number of decimal places of
        /// accuracy you need.**
        ///
        /// Normally this will have the form `10^n` where `n` is the number of correct decimal
        /// places, but this also holds for other bases. For instance, a value of `2^n` here has
        /// little meaning when the result is printed as decimal, but if the result was represented
        /// as a binary string in the form `a.b`, `b` would be correct to `n` digits (and `a` would
        /// be completely correct).
        multiplier: BigUint,
    },
}

impl Accuracy {
    /// Returns an `Accuracy` of `n` decimal places.
    #[must_use]
    pub fn decimal_places<N: GenericInteger>(n: N) -> Self
    where
        BigUint: Pow<N>,
        <BigUint as Pow<N>>::Output: Into<BigUint>,
    {
        #[cfg(feature = "lazy_static")]
        {
            // If we have access to pre-allocated `Accuracy` values, use them instead of allocating
            // a new multiplier.
            match n.to_u16() {
                Some(20) => return Self::Dp20,
                Some(100) => return Self::Dp100,
                Some(500) => return Self::Dp500,
                _ => (),
            }
        }

        Self::Custom {
            multiplier: Pow::pow(BigUint::from(10_u8), n).into(),
        }
    }

    /// Returns an [`Accuracy`] of `n` digits after the point (`.`) in the representation of the
    /// result in the given `base`.
    ///
    /// For example, `base_places(2, 5)` means "correct to at least 5 digits after the `.` when
    /// printed as binary".
    ///
    /// Prefer using [`Accuracy::decimal_places`] when `base == 10`.
    pub fn base_places<B: GenericInteger, N: GenericInteger>(base: B, n: N) -> Self
    where
        // Assuming `n` is anything other than really small, `base^n` will likely be pretty big, so
        // we calculate the multiplier using `BigUint`.
        B: Into<BigUint>,

        // We need to be able to raise `BigUint(base)` to the power of `n`...
        BigUint: Pow<N>,

        // ...and get back something that we can convert straight to `BigUint`.
        <BigUint as Pow<N>>::Output: Into<BigUint>,
    {
        Self::Custom {
            multiplier: Pow::pow(base.into(), n).into(),
        }
    }

    /// Returns a [`BigFraction`] which is equal to `fraction` according to this `Accuracy` by
    /// "chopping off" any irrelevant digits.
    ///
    /// The result will be equal to `(fraction * self.multiplier()).floor() / self.multiplier()`.
    ///
    /// This method propagates infinity and NaN values.
    pub fn chop<T>(&self, fraction: &GenericFraction<T>) -> BigFraction
    where
        T: Clone + Integer,
        BigUint: for<'a> From<&'a T>,
    {
        match fraction {
            GenericFraction::Rational(sign, ratio) => BigFraction::Rational(
                *sign,
                self.chop_ratio(&Ratio::new_raw(ratio.numer().into(), ratio.denom().into())),
            ),

            GenericFraction::Infinity(sign) => BigFraction::Infinity(*sign),
            GenericFraction::NaN => BigFraction::NaN,
        }
    }

    /// Returns a chopped and simplified version of `ratio`.
    #[must_use]
    fn chop_ratio(&self, ratio: &Ratio<BigUint>) -> Ratio<BigUint> {
        Ratio::new(
            self.chopped_numerator_raw(ratio.numer(), ratio.denom()),
            self.multiplier().clone(),
        )
    }

    /// Returns the numerator of the chopped but unsimplified version of `numer / denom`, where the
    /// implied denominator is `self.multiplier()`.
    fn chopped_numerator_raw(&self, numer: &BigUint, denom: &BigUint) -> BigUint {
        (numer * self.multiplier()) / denom
    }

    /// Returns a reference to the multiplier used by `self` to chop off irrelevant digits.
    #[must_use]
    pub fn multiplier(&self) -> &BigUint {
        #[cfg(feature = "lazy_static")]
        {
            lazy_static! {
                static ref DP20_MUL: BigUint = BigUint::from(10_u8).pow(20_u32);
                static ref DP100_MUL: BigUint = BigUint::from(10_u8).pow(100_u32);
                static ref DP500_MUL: BigUint = BigUint::from(10_u8).pow(500_u32);
            };

            return match self {
                Accuracy::Dp20 => &DP20_MUL,
                Accuracy::Dp100 => &DP100_MUL,
                Accuracy::Dp500 => &DP500_MUL,
                Accuracy::Custom { multiplier } => multiplier,
            };
        }

        // When `lazy_static` is enabled, this gets flagged as unreachable which it technically is,
        // but *only* when `lazy_static` is on.
        #[allow(unreachable_code)]
        {
            let Accuracy::Custom { multiplier } = self else {
                // `Custom` is the only available variant when `lazy_static` is off.
                unreachable!()
            };

            multiplier
        }
    }
}

impl Default for Accuracy {
    fn default() -> Self {
        Self::Dp100
    }
}

/// An approximation of a square root.
#[allow(clippy::module_name_repetitions)]
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

impl SqrtApprox {
    /// Returns `self` in the simplest form. This only modifies `Rational` values.
    #[must_use]
    pub fn simplified(self) -> Self {
        match self {
            SqrtApprox::Rational(ratio) => {
                // We could call `ratio.reduced()`, but that would clone the numerator and
                // denominator. If we take ownership of them and recreate the ratio using `new`,
                // we can reduce it without the clone.

                let (n, d) = ratio.into();
                SqrtApprox::Rational(Ratio::new(n, d))
            }
            other => other,
        }
    }
}

impl From<SqrtApprox> for GenericFraction<BigUint> {
    fn from(v: SqrtApprox) -> Self {
        match v {
            SqrtApprox::Rational(ratio) => GenericFraction::Rational(Sign::Plus, ratio),
            SqrtApprox::PlusInf => GenericFraction::infinity(),
            SqrtApprox::Zero => GenericFraction::zero(),
            SqrtApprox::NaN => GenericFraction::nan(),
        }
    }
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

impl SqrtSetup {
    /// Generates the setup values for finding the square root of `value`.
    ///
    /// The `value_as_ratio` field of the returned [`SqrtSetup`] will not be `None` if the
    /// `estimate` field is [`SqrtApprox::Rational`].
    ///
    /// # Panics
    /// This function will panic if `value` is negative.
    fn for_value<Nd>(value: &GenericFraction<Nd>) -> SqrtSetup
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

                        // Using `into_parts` allows us to avoid having to clone the underlying
                        // `BigUint` data within the two values.
                        Some(Ratio::new_raw(n.into_parts().1, d.into_parts().1))
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

/// Various square root operations for `GenericFraction`.
impl<T: Clone + Integer + ToBigUint + ToBigInt + GenericInteger> GenericFraction<T> {
    /// Returns an unsimplified rational approximation of the square root of `self`.
    ///
    /// If you need the result to be simplified, use `sqrt_with_accuracy` instead.
    ///
    /// The square of the resulting value is guaranteed to be equal to `self` within the bounds of
    /// `accuracy`. See [`Accuracy`] for more details.
    ///
    /// # Panics
    /// This method will panic if `self` is negative.
    pub fn sqrt_with_accuracy_raw(&self, accuracy: impl Borrow<Accuracy>) -> SqrtApprox {
        let accuracy = accuracy.borrow();

        let SqrtSetup {
            estimate: initial_estimate,
            value_as_ratio,
        } = SqrtSetup::for_value(self);

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

        // Truncate the target square so we can check against it to determine when to finish. The
        // implied denominator for the numerator returned by the chop operation ("choperation"?) is
        // `accuracy.multiplier()`, so we don't need to store it.
        let truncated_target_numerator =
            accuracy.chopped_numerator_raw(&target_numer, &target_denom);

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
            // original input value. Again, the implied denominator is `accuracy.multiplier()`.
            // This is the same as for `truncated_target_numerator`, so we just need to compare the
            // numerators.
            let squared_and_truncated_numerator = accuracy.chopped_numerator_raw(
                &(current_approx.numer() * current_approx.numer()),
                &(current_approx.denom() * current_approx.denom()),
            );

            // Stop and yield the current guess if it's close enough to the true value.
            if squared_and_truncated_numerator == truncated_target_numerator {
                // This is `_raw`, so we don't reduce.
                break SqrtApprox::Rational(current_approx);
            }
        }
    }

    pub fn sqrt_with_accuracy(&self, accuracy: impl Borrow<Accuracy>) -> GenericFraction<BigUint> {
        self.sqrt_with_accuracy_raw(accuracy).simplified().into()
    }

    pub fn sqrt_raw(&self, decimal_places: u32) -> SqrtApprox {
        self.sqrt_with_accuracy_raw(Accuracy::decimal_places(decimal_places))
    }

    pub fn sqrt(&self, decimal_places: u32) -> GenericFraction<BigUint> {
        self.sqrt_raw(decimal_places).simplified().into()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BigFraction, GenericFraction};
    use std::str::FromStr;

    #[test]
    fn test_simple() {
        // This test actually works because of our delegation to `f64::sqrt` for an initial
        // estimate. For square numbers `f64::sqrt` is able to give precise results, which we can
        // just verify and return. Newton's method would get close to these precise answers but
        // we'd never quite get there.

        let u8_25: GenericFraction<u8> = GenericFraction::from(25_f64);
        let x = u8_25.sqrt(20);

        assert_eq!(x, 5.into());
    }

    #[test]
    fn test_perf_10k() {
        let _ = GenericFraction::<u8>::from(2_u8).sqrt_raw(10_000);
    }

    #[test]
    fn test_perf_100k() {
        let _ = GenericFraction::<u8>::from(2_u8).sqrt_raw(100_000);
    }

    #[test]
    fn test_big_numbers() {
        let big_fraction = BigFraction::from_str("5735874745115151552958367280658028638020529468164964850251033802750727314244020586751748892724760644/4789532131435371284839616979453671799246590610930954499621009334289181266216833845985099376094324166").unwrap();
        let sqrt = big_fraction.sqrt(1_000);

        let s = format!("{sqrt:.100}");
        assert_eq!(s, "1.0943425455728974838600903859180783076888376493725431295813967125637781050743787384965051763360943812");
    }
}

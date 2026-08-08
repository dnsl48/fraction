//! Approximate mathematical operations.
//!
//! This module implements operations that do not guarantee lossless results, but which are
//! nonetheless useful. Using any functionality from within this module requires a compromise to be
//! made between performance and accuracy.
//!
//! Approximations are grouped into modules; for information on a particular approximation or group
//! of approximations, consult the relevant module's documentation.

use crate::{generic::GenericInteger, BigFraction, GenericFraction};
use num::{rational::Ratio, traits::Pow, BigUint, Integer};

pub mod sqrt;

/// Levels of accuracy for an approximation.
#[derive(Clone, Debug, Default)]
pub enum Accuracy {
    /// At least 20 digits correct after the decimal point.
    #[cfg(feature = "with-bigint")]
    Dp20,

    /// At least 100 digits correct after the decimal point.
    #[cfg(feature = "with-bigint")]
    #[default]
    Dp100,

    /// At least 500 digits correct after the decimal point.
    #[cfg(feature = "with-bigint")]
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
    /// Returns an [`Accuracy`] of `n` decimal places.
    #[must_use]
    pub fn decimal_places<N: GenericInteger>(n: N) -> Self
    where
        BigUint: Pow<N>,
        <BigUint as Pow<N>>::Output: Into<BigUint>,
    {
        #[cfg(feature = "with-bigint")]
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
    pub fn base_places<B, N: GenericInteger>(base: B, n: N) -> Self
    where
        // Assuming `n` is anything other than really small, `base^n` will likely be pretty big, so
        // we calculate the multiplier using `BigUint`.
        B: Into<BigUint> + GenericInteger,

        // We need to be able to raise `BigUint(base)` to the power of `n`...
        BigUint: Pow<N>,

        // ...and get back something that we can convert straight to `BigUint`.
        <BigUint as Pow<N>>::Output: Into<BigUint>,
    {
        Self::Custom {
            multiplier: Pow::pow(base.into(), n).into(),
        }
    }

    /// Returns a [`BigFraction`] which is equal to `fraction` according to this [`Accuracy`] by
    /// "chopping off" any irrelevant digits.
    ///
    /// The result will be equal to `(fraction * self.multiplier()).floor() / self.multiplier()`.
    ///
    /// This method propagates infinity and NaN values.
    pub fn chop<T>(&self, fraction: &GenericFraction<T>) -> BigFraction
    where
        T: Clone + Integer,
        BigUint: From<T>,
    {
        match fraction {
            GenericFraction::Rational(sign, ratio) => BigFraction::Rational(*sign, {
                self.chop_ratio(&Ratio::new_raw(
                    ratio.numer().clone().into(),
                    ratio.denom().clone().into(),
                ))
            }),

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
        match self {
            #[cfg(feature = "with-bigint")]
            Accuracy::Dp20 => {
                static DP20_MUL: std::sync::OnceLock<BigUint> = std::sync::OnceLock::new();
                DP20_MUL.get_or_init(|| BigUint::from(10_u8).pow(20_u32))
            }
            #[cfg(feature = "with-bigint")]
            Accuracy::Dp100 => {
                static DP100_MUL: std::sync::OnceLock<BigUint> = std::sync::OnceLock::new();
                DP100_MUL.get_or_init(|| BigUint::from(10_u8).pow(100_u32))
            }
            #[cfg(feature = "with-bigint")]
            Accuracy::Dp500 => {
                static DP500_MUL: std::sync::OnceLock<BigUint> = std::sync::OnceLock::new();
                DP500_MUL.get_or_init(|| BigUint::from(10_u8).pow(500_u32))
            }
            Accuracy::Custom { multiplier } => multiplier,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Accuracy;
    use num::BigUint;

    #[test]
    fn decimal_places_uses_precomputed_multipliers() {
        assert_eq!(
            Accuracy::decimal_places(20_u8).multiplier(),
            &BigUint::from(10_u8).pow(20_u32)
        );
        assert_eq!(
            Accuracy::decimal_places(100_u8).multiplier(),
            &BigUint::from(10_u8).pow(100_u32)
        );
        assert_eq!(
            Accuracy::decimal_places(500_u16).multiplier(),
            &BigUint::from(10_u8).pow(500_u32)
        );
    }

    #[test]
    fn decimal_places_reuses_precomputed_multiplier_references() {
        assert!(std::ptr::eq(
            Accuracy::decimal_places(20_u8).multiplier(),
            Accuracy::decimal_places(20_u8).multiplier()
        ));
        assert!(std::ptr::eq(
            Accuracy::decimal_places(100_u8).multiplier(),
            Accuracy::decimal_places(100_u8).multiplier()
        ));
        assert!(std::ptr::eq(
            Accuracy::decimal_places(500_u16).multiplier(),
            Accuracy::decimal_places(500_u16).multiplier()
        ));
    }
}

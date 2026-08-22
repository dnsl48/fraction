use crate::fraction::GenericFraction;
use crate::{error::ParseError, Sign};
use num::rational::Ratio;
use num::{CheckedAdd, CheckedMul, Zero};
use std::{fmt, str};
use Integer;

pub struct UnicodeDisplay<'a, T: Clone + Integer>(&'a GenericFraction<T>);
pub struct SupSubDisplay<'a, T: Clone + Integer>(&'a UnicodeDisplay<'a, T>);

fn checked_mixed_numerator<T>(trunc: &T, numer: &T, denom: &T) -> Result<T, ParseError>
where
    T: Clone + CheckedAdd + CheckedMul,
{
    let scaled_trunc = trunc.checked_mul(denom).ok_or(ParseError::ParseIntError)?;
    scaled_trunc
        .checked_add(numer)
        .ok_or(ParseError::ParseIntError)
}

impl<'a, T> fmt::Display for UnicodeDisplay<'a, T>
where
    T: Clone + Integer + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            GenericFraction::NaN => write!(f, "NaN"),
            GenericFraction::Infinity(s) => {
                write!(f, "{}∞", s)
            }
            GenericFraction::Rational(s, r) => {
                write!(f, "{}{}", s, r.numer())?;
                if !r.denom().is_one() {
                    write!(f, "⁄{}", r.denom())?;
                }
                Ok(())
            }
        }
    }
}

impl<'a, T: Clone + Integer + fmt::Display> UnicodeDisplay<'a, T> {
    /// Display the fraction using FRACTION SLASH '\u{2044}' '⁄' as a mixed fraction e.g. "1⁤1⁄2"
    /// Will put INVISIBLE PLUS '\u{2064}' as a separator '⁤'
    /// If you have font support, this is the way Unicode wants to display fractions
    /// ```
    /// use fraction::Fraction;
    /// assert_eq!(
    ///   format!("{}", Fraction::new(1u8,2u8).get_unicode_display().mixed()),
    ///   "1⁄2"
    /// );
    /// assert_eq!(
    ///   format!("{}", Fraction::new(3u8,2u8).get_unicode_display().mixed()),
    ///   "1⁤1⁄2"
    /// );
    /// ```
    pub fn mixed(&self) -> impl fmt::Display + '_ {
        struct D<'a, T: Clone + Integer + fmt::Display>(&'a UnicodeDisplay<'a, T>);
        impl<'a, T: Clone + Integer + fmt::Display> fmt::Display for D<'a, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match &self.0 .0 {
                    GenericFraction::Rational(s, r) if r.fract() != *r && !r.denom().is_one() => {
                        write!(
                            f,
                            "{}{}\u{2064}{}⁄{}",
                            s,
                            r.trunc().numer(),
                            r.fract().numer(),
                            r.fract().denom()
                        )
                    }
                    _ => write!(f, "{}", self.0),
                }
            }
        }
        D(self)
    }

    /// Display the fraction using super/subscript
    /// This will look OK without font support
    /// ```
    /// use fraction::Fraction;
    /// assert_eq!(
    ///   format!("{}", Fraction::new(1u8,2u8).get_unicode_display().supsub()),
    ///   "¹/₂"
    /// );
    /// assert_eq!(
    ///   format!("{}", Fraction::new(3u8,2u8).get_unicode_display().supsub()),
    ///   "³/₂"
    /// );
    /// ```
    pub fn supsub(&'a self) -> SupSubDisplay<'a, T> {
        SupSubDisplay(self)
    }
}

impl<'a, T: Clone + Integer + fmt::Display> SupSubDisplay<'a, T> {
    /// Display the fraction as a mixed fraction using super/subscript e.g. "1¹/₂"
    /// This will look OK without font support
    /// ```
    /// use fraction::Fraction;
    /// assert_eq!(
    ///   format!("{}", Fraction::new(1u8,2u8).get_unicode_display().supsub().mixed()),
    ///   "¹/₂"
    /// );
    /// assert_eq!(
    ///   format!("{}", Fraction::new(3u8,2u8).get_unicode_display().supsub().mixed()),
    ///   "1¹/₂"
    /// );
    /// ```
    pub fn mixed(&self) -> impl fmt::Display + '_ {
        struct D<'a, T: Clone + Integer + fmt::Display>(&'a SupSubDisplay<'a, T>);
        impl<'a, T: Clone + Integer + fmt::Display> fmt::Display for D<'a, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match &self.0 .0 .0 {
                    GenericFraction::Rational(s, r) if r.fract() != *r && !r.denom().is_one() => {
                        write!(
                            f,
                            "{}{}{}",
                            s,
                            r.trunc().numer(),
                            GenericFraction::Rational(Sign::Plus, r.fract().clone())
                                .get_unicode_display()
                                .supsub()
                        )
                    }
                    _ => write!(f, "{}", self.0),
                }
            }
        }
        D(self)
    }
}

impl<'a, T: Clone + Integer + fmt::Display> fmt::Display for SupSubDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 .0 {
            GenericFraction::Rational(s, r) => {
                write!(
                    f,
                    "{}{}/{}",
                    s,
                    r.numer()
                        .to_string()
                        .chars()
                        .map(|c| match c {
                            '1' => '¹',
                            '2' => '²',
                            '3' => '³',
                            '4' => '⁴',
                            '5' => '⁵',
                            '6' => '⁶',
                            '7' => '⁷',
                            '8' => '⁸',
                            '9' => '⁹',
                            '0' => '⁰',
                            _ => '?',
                        })
                        .collect::<String>(),
                    r.denom()
                        .to_string()
                        .chars()
                        .map(|c| match c {
                            '1' => '₁',
                            '2' => '₂',
                            '3' => '₃',
                            '4' => '₄',
                            '5' => '₅',
                            '6' => '₆',
                            '7' => '₇',
                            '8' => '₈',
                            '9' => '₉',
                            '0' => '₀',
                            c => c,
                        })
                        .collect::<String>(),
                )
            }
            _ => write!(f, "{}", self.0),
        }
    }
}

impl<T: Clone + Integer + fmt::Display> GenericFraction<T> {
    /// Display the fraction using FRACTION SLASH '\u{2044}' '⁄'
    /// If you have font support, this is the way Unicode wants to display fractions
    /// ```
    /// use fraction::Fraction;
    /// assert_eq!(
    ///   format!("{}", Fraction::new(1u8,2u8).get_unicode_display()),
    ///   "1⁄2"
    /// );
    /// assert_eq!(
    ///   format!("{}", Fraction::new(3u8,2u8).get_unicode_display()),
    ///   "3⁄2"
    /// );
    /// ```
    pub fn get_unicode_display(&self) -> UnicodeDisplay<'_, T> {
        UnicodeDisplay(self)
    }
}

impl<T: Clone + Integer + From<u8>> GenericFraction<T> {
    /// Parse a unicode string
    /// The string can be:
    /// - A normal fraction e.g. "1/2"
    /// - A vulgar fraction e.g. '½'
    /// - ~A mixed vulgar fraction "1½"~
    /// - A unicode fraction e.g. "1⁄2" where '⁄' can be any of:
    ///   - '/' ASCII SOLIDUS
    ///   - '⁄' FRACTION SLASH
    ///   - '∕' DIVISION SLASH
    ///   - '÷' DIVISION SIGN
    /// - A mixed unicode fraction: "1\u{2063}1⁄2": 1⁤1⁄2
    ///   - '\u{2064}' INVISIBLE PLUS
    ///   - '\u{2063}' INVISIBLE SEPARATOR
    ///   - NOT ~'\u{2062}' INVISIBLE TIMES~
    /// - A super-subscript fraction "¹/₂"
    /// - A mixed super-subscript fraction  "1¹/₂"
    ///
    /// Focus is on being lenient towards input rather than being fast.
    ///
    /// Mixed-number components are combined with checked arithmetic. If the
    /// raw combined numerator does not fit in `T`, parsing returns
    /// [`ParseError::ParseIntError`].
    ///
    /// ```
    /// use fraction::Fraction;
    /// let v = vec![
    ///  ("1/2", Fraction::new(1u8,2u8)),
    ///  ("-1/2", Fraction::new_neg(1u8,2u8)),
    ///  ("½", Fraction::new(1u8,2u8)),
    ///  // ("1½", Fraction::new(3u8,2u8)),       // mixed vulgar fractions
    ///  // ("-1½", Fraction::new_neg(3u8,2u8)),  // currently not supported
    ///  ("1⁄2", Fraction::new(1u8,2u8)),
    ///  ("-1⁄2", Fraction::new_neg(1u8,2u8)),
    ///  ("1⁤1⁄2", Fraction::new(3u8,2u8)),
    ///  ("-1⁤1⁄2", Fraction::new_neg(3u8,2u8)),
    ///  ("¹/₂", Fraction::new(1u8,2u8)),
    ///  ("-¹/₂", Fraction::new_neg(1u8,2u8)),
    ///  ("1¹/₂", Fraction::new(3u8,2u8)),
    ///  ("-1¹/₂", Fraction::new_neg(3u8,2u8)),
    /// ];
    /// for (f_str, f) in v {
    ///   assert_eq!(Fraction::from_unicode_str(f_str), Ok(f))
    /// }
    /// ```
    /// Slash and fraction-slash inputs keep the same zero-denominator semantics:
    /// `1⁄0` yields positive infinity, `-1⁄0` yields negative infinity, and `0⁄0` yields NaN.
    /// ```
    /// use fraction::Fraction;
    ///
    /// assert_eq!(Fraction::from_unicode_str("1⁄0"), Ok(Fraction::infinity()));
    /// assert_eq!(Fraction::from_unicode_str("-1⁄0"), Ok(Fraction::neg_infinity()));
    /// assert_eq!(Fraction::from_unicode_str("0⁄0"), Ok(Fraction::nan()));
    /// ```
    pub fn from_unicode_str(input: &str) -> Result<Self, ParseError>
    where
        T: CheckedAdd + CheckedMul,
    {
        let s: &str;
        let sign = if input.starts_with('-') {
            s = input.strip_prefix('-').unwrap();
            Sign::Minus
        } else if input.starts_with('+') {
            s = input.strip_prefix('+').unwrap();
            Sign::Plus
        } else {
            s = input;
            Sign::Plus
        };
        if s.to_lowercase().starts_with("nan") {
            Ok(GenericFraction::nan())
        } else if s.starts_with('∞') || s.starts_with("inf") || s.starts_with("infty") {
            Ok(GenericFraction::Infinity(sign))
        // vulgar fractions
        } else if s.starts_with('½') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 2.into()),
            ))
        } else if s.starts_with('¼') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 4.into()),
            ))
        } else if s.starts_with('¾') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(3.into(), 4.into()),
            ))
        } else if s.starts_with('⅐') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 7.into()),
            ))
        } else if s.starts_with('⅑') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 9.into()),
            ))
        } else if s.starts_with('⅒') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 10.into()),
            ))
        } else if s.starts_with('⅓') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 3.into()),
            ))
        } else if s.starts_with('⅔') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(2.into(), 3.into()),
            ))
        } else if s.starts_with('⅕') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 5.into()),
            ))
        } else if s.starts_with('⅖') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(2.into(), 5.into()),
            ))
        } else if s.starts_with('⅗') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(3.into(), 5.into()),
            ))
        } else if s.starts_with('⅘') {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(4.into(), 5.into()),
            ))
        } else if let Some((first, denom_str)) = s.split_once(&['/', '⁄', '∕', '÷'][..]) {
            // allow for mixed fractions of the shape 1²/₃
            if let Some(idx) =
                first.find(&['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', '⁰'][..])
            {
                let trunc = if idx.is_zero() {
                    T::zero()
                } else {
                    let Ok(t) = T::from_str_radix(&first[..idx], 10) else {
                        return Err(ParseError::ParseIntError);
                    };
                    t
                };

                let Ok(numer) = T::from_str_radix(
                    &first[idx..]
                        .chars()
                        .map(|c| match c {
                            '¹' => '1',
                            '²' => '2',
                            '³' => '3',
                            '⁴' => '4',
                            '⁵' => '5',
                            '⁶' => '6',
                            '⁷' => '7',
                            '⁸' => '8',
                            '⁹' => '9',
                            '⁰' => '0',
                            _ => '?',
                        })
                        .collect::<String>(),
                    10,
                ) else {
                    return Err(ParseError::ParseIntError);
                };
                let Ok(denom) = T::from_str_radix(
                    // let n =
                    &denom_str
                        .chars()
                        .map(|c| match c {
                            '₁' => '1',
                            '₂' => '2',
                            '₃' => '3',
                            '₄' => '4',
                            '₅' => '5',
                            '₆' => '6',
                            '₇' => '7',
                            '₈' => '8',
                            '₉' => '9',
                            '₀' => '0',
                            c => c,
                        })
                        .collect::<String>(),
                    10,
                ) else {
                    return Err(ParseError::ParseIntError);
                };
                let numer = checked_mixed_numerator(&trunc, &numer, &denom)?;
                Ok(Self::new_signed(sign, numer, denom))
            } else if let Some((trunc_str, numer_str)) =
                // also allow for mixed fractions to be parsed: `1⁤1⁄2`
                // allowed invisible separators: \u{2064} \u{2063}
                // '+' is disallowed, bc it would be confusing with -1+1/2
                first.split_once(&['\u{2064}', '\u{2063}'][..])
            {
                let Ok(numer) = T::from_str_radix(numer_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                let Ok(trunc) = T::from_str_radix(trunc_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                let Ok(denom) = T::from_str_radix(denom_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                let numer = checked_mixed_numerator(&trunc, &numer, &denom)?;
                Ok(Self::new_signed(sign, numer, denom))
            } else {
                let Ok(numer) = T::from_str_radix(first, 10) else {
                    return Err(ParseError::ParseIntError);
                };

                let Ok(denom) = T::from_str_radix(denom_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };

                Ok(Self::new_signed(sign, numer, denom))
            }
        } else {
            let Ok(val) = T::from_str_radix(s, 10) else {
                return Err(ParseError::ParseIntError);
            };
            Ok(GenericFraction::Rational(sign, Ratio::new(val, T::one())))
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::{error::ParseError, Fraction, GenericFraction};
    use num::{One, Zero};
    #[cfg(feature = "with-bigint")]
    use std::str::FromStr;

    #[test]
    fn from_unicode_str_mixed_rejects_reported_overflow() {
        let inputs = ["18446744073709551615¹/₂", "18446744073709551615\u{2064}1⁄2"];

        for input in inputs {
            assert_eq!(
                GenericFraction::<u64>::from_unicode_str(input),
                Err(ParseError::ParseIntError)
            );
        }
    }

    #[test]
    fn from_unicode_str_mixed_rejects_component_overflow() {
        let multiplication_overflow = ["128¹/₂", "128\u{2064}1/2"];
        let addition_overflow = ["255¹/₁", "255\u{2064}1/1"];

        for input in multiplication_overflow
            .iter()
            .chain(addition_overflow.iter())
        {
            assert_eq!(
                GenericFraction::<u8>::from_unicode_str(input),
                Err(ParseError::ParseIntError)
            );
        }
    }

    #[test]
    fn from_unicode_str_mixed_accepts_fitting_signed_values() {
        assert_eq!(
            GenericFraction::<u8>::from_unicode_str("127¹/₂"),
            Ok(GenericFraction::<u8>::new(255, 2))
        );
        assert_eq!(
            GenericFraction::<u8>::from_unicode_str("+127\u{2064}1/2"),
            Ok(GenericFraction::<u8>::new(255, 2))
        );
        assert_eq!(
            GenericFraction::<u8>::from_unicode_str("-127¹/₂"),
            Ok(GenericFraction::<u8>::new_neg(255, 2))
        );
    }

    #[test]
    fn from_unicode_str_mixed_rejects_raw_overflow_before_reduction() {
        for input in ["127²/₂", "127\u{2064}2/2"] {
            assert_eq!(
                GenericFraction::<u8>::from_unicode_str(input),
                Err(ParseError::ParseIntError)
            );
        }
    }

    #[test]
    fn from_unicode_str_mixed_preserves_zero_denominator_semantics() {
        assert_eq!(
            Fraction::from_unicode_str("1\u{2064}1/0"),
            Ok(Fraction::infinity())
        );
        assert_eq!(Fraction::from_unicode_str("1¹/₀"), Ok(Fraction::infinity()));
        assert_eq!(
            Fraction::from_unicode_str("0\u{2064}0/0"),
            Ok(Fraction::nan())
        );
    }

    #[cfg(feature = "with-bigint")]
    #[test]
    fn from_unicode_str_mixed_preserves_big_fraction_capacity() {
        use crate::BigFraction;

        let expected = BigFraction::from_str("36893488147419103231/2").unwrap();
        for input in ["18446744073709551615¹/₂", "18446744073709551615\u{2064}1⁄2"] {
            assert_eq!(BigFraction::from_unicode_str(input), Ok(expected.clone()));
        }
    }

    #[cfg(all(feature = "with-bigint", feature = "with-dynaint"))]
    #[test]
    fn from_unicode_str_mixed_preserves_dyna_fraction_capacity() {
        use crate::DynaFraction;

        let expected = DynaFraction::<u64>::from_str("36893488147419103231/2").unwrap();
        for input in ["18446744073709551615¹/₂", "18446744073709551615\u{2064}1⁄2"] {
            assert_eq!(
                DynaFraction::<u64>::from_unicode_str(input),
                Ok(expected.clone())
            );
        }
    }

    #[test]
    fn test_fromto_str() {
        let test_vec = vec![
            ("NaN", Fraction::nan()),
            ("∞", Fraction::infinity()),
            ("-∞", Fraction::neg_infinity()),
            ("0", Fraction::zero()),
            ("1", Fraction::one()),
            ("-1", -Fraction::one()),
            ("5", Fraction::from(5)),
            ("1⁄2", Fraction::new(1u8, 2u8)),
            ("-1⁄2", Fraction::new_neg(1u8, 2u8)),
            ("3⁄2", Fraction::new(3u8, 2u8)),
            ("-3⁄2", Fraction::new_neg(3u8, 2u8)),
            ("12⁄23", Fraction::new(12u8, 23u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::from_unicode_str(string), Ok(frac));
            println!("{} ?= {}", string, frac);
            assert_eq!(format!("{}", frac.get_unicode_display()), string);
        }
    }

    #[test]
    fn test_alternate_parse() {
        let test_vec = vec![
            ("nan", Fraction::nan()),
            ("+∞", Fraction::infinity()),
            ("+1", Fraction::one()),
            ("+5", Fraction::from(5)),
            // vulgar fractions
            ("½", Fraction::new(1u8, 2u8)),
            ("-½", Fraction::new_neg(1u8, 2u8)),
            ("+½", Fraction::new(1u8, 2u8)),
            ("¼", Fraction::new(1u8, 4u8)),
            ("-¼", Fraction::new_neg(1u8, 4u8)),
            ("+¼", Fraction::new(1u8, 4u8)),
            ("¾", Fraction::new(3u8, 4u8)),
            ("-¾", Fraction::new_neg(3u8, 4u8)),
            ("+¾", Fraction::new(3u8, 4u8)),
            ("⅐", Fraction::new(1u8, 7u8)),
            ("-⅐", Fraction::new_neg(1u8, 7u8)),
            ("+⅐", Fraction::new(1u8, 7u8)),
            ("⅑", Fraction::new(1u8, 9u8)),
            ("-⅑", Fraction::new_neg(1u8, 9u8)),
            ("+⅑", Fraction::new(1u8, 9u8)),
            ("⅒", Fraction::new(1u8, 10u8)),
            ("-⅒", Fraction::new_neg(1u8, 10u8)),
            ("+⅒", Fraction::new(1u8, 10u8)),
            ("⅓", Fraction::new(1u8, 3u8)),
            ("-⅓", Fraction::new_neg(1u8, 3u8)),
            ("+⅓", Fraction::new(1u8, 3u8)),
            ("⅔", Fraction::new(2u8, 3u8)),
            ("-⅔", Fraction::new_neg(2u8, 3u8)),
            ("+⅔", Fraction::new(2u8, 3u8)),
            ("⅕", Fraction::new(1u8, 5u8)),
            ("-⅕", Fraction::new_neg(1u8, 5u8)),
            ("+⅕", Fraction::new(1u8, 5u8)),
            ("⅖", Fraction::new(2u8, 5u8)),
            ("-⅖", Fraction::new_neg(2u8, 5u8)),
            ("+⅖", Fraction::new(2u8, 5u8)),
            ("⅗", Fraction::new(3u8, 5u8)),
            ("-⅗", Fraction::new_neg(3u8, 5u8)),
            ("+⅗", Fraction::new(3u8, 5u8)),
            ("⅘", Fraction::new(4u8, 5u8)),
            ("-⅘", Fraction::new_neg(4u8, 5u8)),
            ("+⅘", Fraction::new(4u8, 5u8)),
            // supsub with other delim
            ("¹⁄₃", Fraction::new(1u8, 3u8)),
            ("1¹⁄₃", Fraction::new(4u8, 3u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::from_unicode_str(string), Ok(frac));
        }
    }

    #[test]
    fn test_fromto_supsub() {
        let test_vec = vec![
            // super/subscript
            ("¹²/₂₃", Fraction::new(12u8, 23u8)),
            ("¹²³⁴⁵⁶⁷⁸⁹⁰/₂₃", Fraction::new(1234567890u64, 23u8)),
            ("²³/₁₂₃₄₅₆₇₈₉₀", Fraction::new(23u8, 1234567890u64)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::from_unicode_str(string), Ok(frac));
            println!("{} ?= {}", string, frac);
            assert_eq!(format!("{}", frac.get_unicode_display().supsub()), string);
        }
    }

    #[test]
    fn test_fromto_supsub_mixed() {
        let test_vec = vec![
            // super/subscript mixed
            ("1¹/₂", Fraction::new(3u8, 2u8)),
            ("¹/₂", Fraction::new(1u8, 2u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::from_unicode_str(string), Ok(frac));
            println!("{} ?= {}", string, frac);
            assert_eq!(
                format!("{}", frac.get_unicode_display().supsub().mixed()),
                string
            );
        }
    }

    #[test]
    fn test_fromto_mixed() {
        let test_vec = vec![
            ("NaN", Fraction::nan()),
            ("∞", Fraction::infinity()),
            ("-∞", Fraction::neg_infinity()),
            ("0", Fraction::zero()),
            ("1", Fraction::one()),
            ("-1", -Fraction::one()),
            ("5", Fraction::from(5)),
            ("1\u{2064}1⁄2", Fraction::new(3u8, 2u8)),
            ("-1\u{2064}1⁄2", Fraction::new_neg(3u8, 2u8)),
            ("1⁄2", Fraction::new(1u8, 2u8)),
            ("-1⁄2", Fraction::new_neg(1u8, 2u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            let f_test = Fraction::from_unicode_str(string);
            assert_eq!(f_test, Ok(frac));
            assert_eq!(format!("{}", frac.get_unicode_display().mixed()), string);
        }
    }

    #[test]
    fn from_unicode_str_zero_denominator() {
        let test_vec = vec![
            ("1\u{2064}1/0", Fraction::infinity()),
            ("1/0", Fraction::infinity()),
            ("0/0", Fraction::nan()),
            ("²/₀", Fraction::infinity()),
            ("⁰/₀", Fraction::nan()),
            ("1⁄0", Fraction::infinity()),
            ("5⁄0", Fraction::infinity()),
            ("-1⁄0", Fraction::neg_infinity()),
            ("1\u{2064}0/0", Fraction::nan()),
            ("1⁰/₀", Fraction::nan()),
        ];
        for (string, fraction) in test_vec {
            assert_eq!(Fraction::from_unicode_str(string), Ok(fraction));
        }
    }

    #[test]
    fn test_from_fail() {
        // TODO: "nanBOGUS" and "∞BOGUS" will parse.
        // Either make that everything with BOGUS
        // after will parse, or make ^those fail.
        let test_vec = vec![
            "asdf",
            "+1BOGUS",
            "+5BOGUS",
            "1⁤1⁄2BOGUS",
            "1⁣1⁄2BOGUS",
            "-1⁤1⁄2BOGUS",
            "1⁢1⁄2", // uses INVISIBLE_TIMES
        ];
        for s in test_vec {
            println!("{}", s);
            assert_eq!(
                Fraction::from_unicode_str(s),
                Err(ParseError::ParseIntError)
            )
        }
    }

    #[test]
    fn test_fromstr_fraction_ops() {
        let test_vec = vec!["1", "1/2", "3/2"];
        for s in test_vec {
            let f = Fraction::from_unicode_str(s).unwrap();
            assert_eq!(f * Fraction::one(), f);
            assert_eq!(f + Fraction::zero(), f);
        }
    }
}

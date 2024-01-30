use std::fmt::Display;

use crate::fraction::GenericFraction;
use std::{fmt, str};
use crate::{error::ParseError, Sign};
use num::rational::Ratio;
use Integer;

impl<T: Clone + Integer + Display> GenericFraction<T> {
    pub fn unicode_display(&self) -> impl fmt::Display + '_ {
        struct UnicodeDisplay<'a, T: Clone + Integer>(&'a GenericFraction<T>);
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
        UnicodeDisplay(self)
    }

    pub fn unicode_display_mixed(&self) -> impl Display + '_ {
        struct S<'a, T: Clone + Integer + fmt::Display>(&'a GenericFraction<T>);
        impl<'a, T> fmt::Display for S<'a, T>
        where
            T: Clone + Integer + fmt::Display,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match &self.0 {
                    GenericFraction::Rational(s, r) if r.fract() != *r  && !r.denom().is_one() => {
                        write!(f, "{}{}\u{2064}{}⁄{}", s, r.trunc().numer(), r.fract().numer(), r.fract().denom())
                    }
                    _ => write!(f, "{}", self.0.unicode_display())
                }
            }
        }
        S(self)
    }

    pub fn unicode_parse(input: &str) -> Result<Self, ParseError> {
        let s: &str;
        let sign = if input.starts_with('-') {
            s = &input[1..];
            Sign::Minus
            
        } else if input.starts_with('+') {
            s = &input[1..];
            Sign::Plus
        } else {
            s = input;
            Sign::Plus
        };
        if s.to_lowercase().starts_with("nan") {
            Ok(GenericFraction::nan())
        } else if s.starts_with("∞")
            || s.starts_with("inf")
            || s.starts_with("infty")
        {
            Ok(GenericFraction::Infinity(sign))
        } else if let Some((first, denom_str)) = s.split_once(&['/', '⁄', '∕', '÷'][..]) {
            // also allow for mixed fractions to be parsed: `1⁤1⁄2`
            // allowed invisible separators: \u{2064} \u{2063}
            // '+' is disallowed, bc it would be confusing with -1+1/2
            let mut numer: T;
            let denom: T;
            if let Some((trunc_str, numer_str)) =
                first.split_once(&['\u{2064}', '\u{2063}'][..])
            {
                let Ok(n) = T::from_str_radix(numer_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                numer = n;
                let Ok(t) = T::from_str_radix(trunc_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                let trunc = t;
                let Ok(d) = T::from_str_radix(denom_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                denom = d;
                numer = numer + trunc * denom.clone();
            } else {
                let Ok(n) = T::from_str_radix(&first, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                numer = n;
                let Ok(d) = T::from_str_radix(denom_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                denom = d;
            }
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new(numer, denom),
            ))
        } else {
            let Ok(val) = T::from_str_radix(&s, 10) else {
                return Err(ParseError::ParseIntError);
            };
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new(val, T::one()),
            ))
        }
    }
}

#[cfg(test)]
mod tests {

    use num::{One, Zero};

    use crate::{
        error::ParseError, Fraction,
    };

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
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::unicode_parse(string), Ok(frac));
            println!("{} ?= {}", string, frac);
            assert_eq!(format!("{}", frac.unicode_display()), string);
        }
    }

    #[test]
    fn test_fromto_str_mixed() {
        let test_vec = vec![
            ("NaN", Fraction::nan()),
            ("∞", Fraction::infinity()),
            ("-∞", Fraction::neg_infinity()),
            ("0", Fraction::zero()),
            ("1", Fraction::one()),
            ("-1", -Fraction::one()),
            ("5", Fraction::from(5)),
            // ("nan", Fraction::nan()),
            // ("+∞", Fraction::infinity()),
            // ("+1", Fraction::one()),
            // ("+5", Fraction::from(5)),
            ("1\u{2064}1⁄2", Fraction::new(3u8, 2u8)),
            // ("1⁣1⁄2", Fraction::new(3u8, 2u8)),
            ("-1\u{2064}1⁄2", Fraction::new_neg(3u8, 2u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            let f_test = Fraction::unicode_parse(string);
            assert_eq!(f_test, Ok(frac));
            assert_eq!(format!("{}", frac.unicode_display_mixed()), string);
        }
    }

    #[test]
    fn test_from_fail() {
        let test_vec = vec![
            "asdf",
            // "NanBOGUS",
            // "nanBOGUS",
            // "+∞BOGUS",
            "+1BOGUS",
            "+5BOGUS",
            "1⁤1⁄2BOGUS",
            "1⁣1⁄2BOGUS",
            "-1⁤1⁄2BOGUS",
            "1⁢1⁄2" // uses INVISIBLE_TIMES
        ];
        for s in test_vec {
            println!("{}", s);
            assert_eq!(
                Fraction::unicode_parse(s),
                Err(ParseError::ParseIntError)
            )
        }
    }

    #[test]
    fn test_fromstr_fraction_ops() {
        let test_vec = vec![
            "1",
            "1/2",
            "3/2",
        ];
        for s in test_vec {
            let f = Fraction::unicode_parse(s).unwrap();
            assert_eq!(f*Fraction::one(), f);
            assert_eq!(f+Fraction::zero(), f);
        }
    }
}

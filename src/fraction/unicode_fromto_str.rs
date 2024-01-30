use crate::fraction::GenericFraction;
extern crate core;
use self::core::{fmt, str};
use crate::{error::ParseError, Sign};
use num::rational::Ratio;
use Integer;

#[derive(Debug, PartialEq)]
pub struct UnicodeFromToStr<T: Clone + Integer>(GenericFraction<T>);

impl<T> fmt::Display for UnicodeFromToStr<T>
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

impl<T> str::FromStr for UnicodeFromToStr<T>
where
    T: Clone + Integer + fmt::Display,
{
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (sign, start) = if s.starts_with('-') {
            (Sign::Minus, 1)
        } else if s.starts_with('+') {
            (Sign::Plus, 1)
        } else {
            (Sign::Plus, 0)
        };
        if s[start..].to_lowercase().starts_with("nan") {
            Ok(Self(GenericFraction::nan()))
        } else if s[start..].starts_with("∞")
            || s[start..].starts_with("inf")
            || s[start..].starts_with("infty")
        {
            Ok(Self(GenericFraction::Infinity(sign)))
        } else if let Some((first, denom_str)) = s.split_once(&['/', '⁄', '∕', '÷'][..]) {
            // also allow for mixed fractions to be parsed: `1+1/2` or `1⁤1⁄2`
            // allowed invisible separators: \u{2064} \u{2063}
            // '+' is disallowed, bc it would be confusing with -1+1/2
            let mut numer: T;
            let denom: T;
            if let Some((trunc_str, numer_str)) =
                first[start..].split_once(&['\u{2064}', '\u{2063}'][..])
            {
                // let Ok(nu)
                println!("mixed!");
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
                let Ok(n) = T::from_str_radix(&first[start..], 10) else {
                    return Err(ParseError::ParseIntError);
                };
                numer = n;
                let Ok(d) = T::from_str_radix(denom_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                denom = d;
            }
            Ok(Self(GenericFraction::Rational(
                sign,
                Ratio::new(numer, denom),
            )))
        } else {
            let Ok(val) = T::from_str_radix(&s[start..], 10) else {
                return Err(ParseError::ParseIntError);
            };
            Ok(Self(GenericFraction::Rational(
                sign,
                Ratio::new(val, T::one()),
            )))
        }
    }
}

impl<T: Clone + Integer> From<UnicodeFromToStr<T>> for GenericFraction<T> {
    fn from(value: UnicodeFromToStr<T>) -> Self {
        value.0
    }
}

impl<T: Clone + Integer> From<GenericFraction<T>> for UnicodeFromToStr<T> {
    fn from(value: GenericFraction<T>) -> Self {
        Self(value)
    }
}

#[cfg(test)]
mod tests {
    use std::{num::ParseIntError, str::FromStr};

    use num::{One, Zero};

    use crate::{
        error::ParseError, unicode_fromto_str::UnicodeFromToStr, Fraction, GenericFraction,
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
            assert_eq!(UnicodeFromToStr::from_str(string).unwrap().0, frac);
            println!("{} ?= {}", string, frac);
            assert_eq!(format!("{}", UnicodeFromToStr(frac)), string);
        }
    }

    #[test]
    fn test_from_str() {
        let test_vec = vec![
            ("Nan", Fraction::nan()),
            ("nan", Fraction::nan()),
            ("+∞", Fraction::infinity()),
            ("+1", Fraction::one()),
            ("+5", Fraction::from(5)),
            ("1⁤1⁄2", Fraction::new(3u8, 2u8)),
            ("1⁣1⁄2", Fraction::new(3u8, 2u8)),
            ("-1⁤1⁄2", Fraction::new_neg(3u8, 2u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            let f_test = UnicodeFromToStr::from_str(string).unwrap().0;
            assert_eq!(f_test, frac);
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
        ];
        for s in test_vec {
            println!("{}", s);
            assert_eq!(
                UnicodeFromToStr::<u64>::from_str(s).err(),
                Some(ParseError::ParseIntError)
            )
        }
    }
}

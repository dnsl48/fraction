use std::fmt::Display;

use crate::fraction::GenericFraction;
use crate::{error::ParseError, Sign};
use num::rational::Ratio;
use num::Zero;
use std::{fmt, str};
use Integer;

impl<T: Clone + Integer + Display + From<u8>> GenericFraction<T> {
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
            T: Clone + Integer + fmt::Display + From<u8>,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match &self.0 {
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
                    _ => write!(f, "{}", self.0.unicode_display()),
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
        } else if s.starts_with("∞") || s.starts_with("inf") || s.starts_with("infty") {
            Ok(GenericFraction::Infinity(sign))
        // vulgar fractions
        } else if s.starts_with("½") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 2.into()),
            ))
        } else if s.starts_with("¼") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 4.into()),
            ))
        } else if s.starts_with("¾") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(3.into(), 4.into()),
            ))
        } else if s.starts_with("⅐") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 7.into()),
            ))
        } else if s.starts_with("⅑") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 9.into()),
            ))
        } else if s.starts_with("⅒") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 10.into()),
            ))
        } else if s.starts_with("⅓") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 3.into()),
            ))
        } else if s.starts_with("⅔") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(2.into(), 3.into()),
            ))
        } else if s.starts_with("⅕") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(1.into(), 5.into()),
            ))
        } else if s.starts_with("⅖") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(2.into(), 5.into()),
            ))
        } else if s.starts_with("⅗") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(3.into(), 5.into()),
            ))
        } else if s.starts_with("⅘") {
            Ok(GenericFraction::Rational(
                sign,
                Ratio::new_raw(4.into(), 5.into()),
            ))
        } else if let Some((first, denom_str)) = s.split_once(&['/', '⁄', '∕', '÷'][..]) {
            let mut numer: T;
            let denom: T;
            // allow for mixed fractions of the shape 1²/₃
            if let Some(idx) =
                first.find(&['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', '⁰'][..])
            {
                println!("Supsub! {}", first);
                let trunc = if idx.is_zero() {
                    T::zero()
                } else {
                    let Ok(t) = T::from_str_radix(&first[..idx], 10) else {
                        return Err(ParseError::ParseIntError);
                    };
                    t
                };

                let Ok(n) = T::from_str_radix(
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
                numer = n;
                println!("numer: {}", &numer);
                let Ok(d) = T::from_str_radix(
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
                println!("denom: {}", d);
                denom = d;
                numer = numer + trunc * denom.clone();
            } else
            // also allow for mixed fractions to be parsed: `1⁤1⁄2`
            // allowed invisible separators: \u{2064} \u{2063}
            // '+' is disallowed, bc it would be confusing with -1+1/2
            if let Some((trunc_str, numer_str)) =
                first.split_once(&['\u{2064}', '\u{2063}'][..])
            {
                let Ok(n) = T::from_str_radix(numer_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
                numer = n;
                let Ok(trunc) = T::from_str_radix(trunc_str, 10) else {
                    return Err(ParseError::ParseIntError);
                };
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
            Ok(GenericFraction::Rational(sign, Ratio::new(numer, denom)))
        } else {
            let Ok(val) = T::from_str_radix(&s, 10) else {
                return Err(ParseError::ParseIntError);
            };
            Ok(GenericFraction::Rational(sign, Ratio::new(val, T::one())))
        }
    }
}

#[cfg(test)]
mod tests {

    use num::{One, Zero};

    use crate::{error::ParseError, Fraction};

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
            assert_eq!(Fraction::unicode_parse(string), Ok(frac));
            println!("{} ?= {}", string, frac);
            assert_eq!(format!("{}", frac.unicode_display()), string);
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
            // ("¹⁄₃", Fraction::new(1u8, 3u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::unicode_parse(string), Ok(frac));
            // println!("{} ?= {}", string, frac);
            // assert_eq!(format!("{}", frac.unicode_display()), string);
        }
    }

    #[test]
    fn test_fromto_supsub() {
        let test_vec = vec![
            // super/subscript
            ("¹²/₂₃", Fraction::new(12u8, 23u8)),
            ("¹²³⁴⁵⁶⁷⁸⁹⁰/₂₃", Fraction::new(1234567890u64, 23u8)),
            ("¹²/₁₂₃₄₅₆₇₈₉₀", Fraction::new(12u8, 1234567890u64)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::unicode_parse(string), Ok(frac));
            // println!("{} ?= {}", string, frac);
            // assert_eq!(format!("{}", frac.unicode_display()), string);
        }
    }

    #[test]
    fn test_fromto_supsub_mixed() {
        let test_vec = vec![
            // super/subscript mixed
            ("1¹/₂", Fraction::new(3u8, 2u8)),
        ];
        for (string, frac) in test_vec {
            println!("{} ?= {}", string, frac);
            assert_eq!(Fraction::unicode_parse(string), Ok(frac));
            // println!("{} ?= {}", string, frac);
            // assert_eq!(format!("{}", frac.unicode_display()), string);
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
            "1⁢1⁄2", // uses INVISIBLE_TIMES
        ];
        for s in test_vec {
            println!("{}", s);
            assert_eq!(Fraction::unicode_parse(s), Err(ParseError::ParseIntError))
        }
    }

    #[test]
    fn test_fromstr_fraction_ops() {
        let test_vec = vec!["1", "1/2", "3/2"];
        for s in test_vec {
            let f = Fraction::unicode_parse(s).unwrap();
            assert_eq!(f * Fraction::one(), f);
            assert_eq!(f + Fraction::zero(), f);
        }
    }
}

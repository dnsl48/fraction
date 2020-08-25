//! Juniper values conversion for GenericFraction
//! The format is case sensitive text representation of the sign and numbers.
//! Those are:
//! * Special cases: `NaN`, `+inf`, `-inf`
//! * Zero: `+0`, `-0`
//! * Whole numbers: `+1`, `-2`
//! * Fractions: `+1/2`, `-3/4`

use generic::GenericInteger;

use juniper::{
    meta::MetaType, parser::ScalarToken, Executor, FromInputValue, GraphQLType, InputValue,
    ParseScalarResult, ParseScalarValue, Registry, ScalarRefValue, ScalarValue, Selection,
    ToInputValue, Value,
};

use super::{CheckedAdd, CheckedMul, CheckedSub, Integer, Num, One};
use std::fmt::Display;

use super::{GenericFraction, Sign};

impl<S, T> ParseScalarValue<S> for GenericFraction<T>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + Integer + CheckedAdd + CheckedMul + CheckedSub + Display,
{
    fn from_str<'a>(value: ScalarToken<'a>) -> ParseScalarResult<'a, S> {
        match value {
            ScalarToken::String(val) | ScalarToken::Int(val) | ScalarToken::Float(val) => {
                Ok(S::from(val.to_owned()))
            }
        }
    }
}

impl<S, T> GraphQLType<S> for GenericFraction<T>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + GenericInteger + Display + 'static,
{
    type Context = ();
    type TypeInfo = ();

    fn name(_: &()) -> Option<&str> {
        Some("Fraction")
    }

    fn meta<'r>(info: &(), registry: &mut Registry<'r, S>) -> MetaType<'r, S>
    where
        S: 'r,
    {
        registry
            .build_scalar_type::<Self>(info)
            .description("Fraction")
            .into_meta()
    }

    fn resolve(
        &self,
        _: &(),
        _: Option<&[Selection<S>]>,
        _: &Executor<Self::Context, S>,
    ) -> Value<S> {
        Value::scalar(S::from(self.to_string()))
    }
}

impl<S, T> ToInputValue<S> for GenericFraction<T>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + GenericInteger,
{
    fn to_input_value(&self) -> InputValue<S> {
        ToInputValue::to_input_value(&format!("{:+}", self))
    }
}

impl<S, T> FromInputValue<S> for GenericFraction<T>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + Integer + CheckedAdd + CheckedMul + CheckedSub + Num + One,
{
    fn from_input_value(value: &InputValue<S>) -> Option<Self> {
        let val = match value.as_scalar() {
            None => return None,
            Some(scalar) => {
                let s: Option<&String> = scalar.into();
                match s {
                    Some(v) => v,
                    _ => return None,
                }
            }
        };

        if val.len() < 2 {
            None
        } else if val == "NaN" {
            Some(GenericFraction::nan())
        } else if val == "-inf" {
            Some(GenericFraction::neg_infinity())
        } else if val == "+inf" {
            Some(GenericFraction::infinity())
        } else {
            let sign = match val.as_bytes()[0] {
                43 => Sign::Plus,
                45 => Sign::Minus,
                _ => return None,
            };

            let (denom, split): (T, usize) = if let Some(idx) = val.find('/') {
                let (_, denom) = val.split_at(idx + 1);

                match T::from_str_radix(denom, 10) {
                    Ok(val) => (val, idx),
                    Err(_) => return None,
                }
            } else {
                (T::one(), val.len())
            };

            let (snum, _) = val.split_at(split);
            let (_, num) = snum.split_at(1);

            match T::from_str_radix(num, 10) {
                Ok(num) => match sign {
                    Sign::Plus => Some(GenericFraction::new(num, denom)),
                    Sign::Minus => Some(GenericFraction::new_neg(num, denom)),
                },
                Err(_) => None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type F = GenericFraction<u8>;
    fn get_tests() -> Vec<(&'static str, F)> {
        vec![
            ("NaN", F::nan()),
            ("-inf", F::neg_infinity()),
            ("+inf", F::infinity()),
            ("+0", F::new(0u8, 1u8)),
            ("-0", F::new_neg(0u8, 1u8)),
            ("+2", F::new(2u8, 1u8)),
            ("-2", F::new_neg(2u8, 1u8)),
            ("+1/2", F::new(1u8, 2u8)),
            ("-1/2", F::new_neg(1u8, 2u8)),
            ("+5/6", F::new(10u8, 12u8)),
            ("-1/255", F::new_neg(1u8, 255u8)),
        ]
    }

    #[cfg(features = "with-bigint")]
    fn get_big_tests() -> Vec<(&'static str, BigFraction)> {
        vec![
            ("NaN", BigFraction::nan()),
            ("-inf", BigFraction::neg_infinity()),
            ("+inf", BigFraction::infinity()),
            ("+0", BigFraction::new(0u8, 1u8)),
            ("-0", BigFraction::new_neg(0u8, 1u8)),
            ("+2", BigFraction::new(2u8, 1u8)),
            ("-2", BigFraction::new_neg(2u8, 1u8)),
            ("+1/2", BigFraction::new(1u8, 2u8)),
            ("-1/2", BigFraction::new_neg(1u8, 2u8)),
            ("+5/6", BigFraction::new(10u8, 12u8)),
            ("-1/255", BigFraction::new_neg(1u8, 255u8)),
            (
                "+42090291092428642826240949012091044820/42090291092428642826240949012091044821",
                BigFraction::from_str_radix(
                    "42090291092428642826240949012091044820/42090291092428642826240949012091044821",
                    10,
                )
                .unwrap(),
            ),
        ]
    }

    #[test]
    fn to_input_value() {
        for (s, v) in get_tests() {
            let value = <F as ToInputValue>::to_input_value(&v);
            let str_value = value.as_scalar_value::<String>();

            assert!(str_value.is_some());
            assert_eq!(s, str_value.unwrap());
        }

        #[cfg(features = "with-bigint")]
        {
            for (s, v) in get_big_tests() {
                let value = <BigFraction as ToInputValue>::to_input_value(&v);
                let str_value = value.as_string_value();

                assert!(str_value.is_some());
                assert_eq!(s, str_value.unwrap());
            }
        }
    }

    #[test]
    fn from_input_value() {
        for (s, v) in get_tests() {
            let value = <F as FromInputValue>::from_input_value(&InputValue::scalar(s.to_owned()));
            assert_eq!(value, Some(v));
        }

        #[cfg(features = "with-bigint")]
        {
            for (s, v) in get_big_tests() {
                let value =
                    <BigFraction as FromInputValue>::from_input_value(&InputValue::string(s));
                assert_eq!(value, Some(v));
            }
        }
    }
}

use juniper::{
    meta::MetaType, parser::ScalarToken, Executor, FromInputValue, GraphQLType, InputValue,
    ParseScalarResult, ParseScalarValue, Registry, ScalarRefValue, ScalarValue, Selection,
    ToInputValue, Value,
};

use generic::GenericInteger;
use num::Integer;
use std::fmt;

use super::GenericDecimal;

impl<S, T, P> ParseScalarValue<S> for GenericDecimal<T, P>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + GenericInteger + From<u8> + fmt::Display,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
{
    fn from_str<'a>(value: ScalarToken<'a>) -> ParseScalarResult<'a, S> {
        match value {
            ScalarToken::String(val) | ScalarToken::Int(val) | ScalarToken::Float(val) => {
                Ok(S::from(val.to_owned()))
            }
        }
    }
}

impl<S, T, P> GraphQLType<S> for GenericDecimal<T, P>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + GenericInteger + From<u8> + fmt::Display,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
{
    type Context = ();
    type TypeInfo = ();

    fn name(_: &()) -> Option<&str> {
        Some("Decimal")
    }

    fn meta<'r>(info: &(), registry: &mut Registry<'r, S>) -> MetaType<'r, S>
    where
        S: 'r,
    {
        registry
            .build_scalar_type::<Self>(info)
            .description("Decimal")
            .into_meta()
    }

    fn resolve(
        &self,
        _: &(),
        _: Option<&[Selection<S>]>,
        _: &Executor<Self::Context, S>,
    ) -> Value<S> {
        Value::scalar(S::from(format!("{}", self)))
    }
}

impl<S, T, P> ToInputValue<S> for GenericDecimal<T, P>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + GenericInteger + fmt::Display + From<u8>,
    P: Copy + Integer + Into<usize>,
{
    fn to_input_value(&self) -> InputValue<S> {
        ToInputValue::to_input_value(&format!("{}", self))
    }
}

impl<S, T, P> FromInputValue<S> for GenericDecimal<T, P>
where
    S: ScalarValue,
    for<'a> &'a S: ScalarRefValue<'a>,
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
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

        Some(GenericDecimal::from_decimal_str(val).ok())?
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fraction::GenericFraction;

    type D = GenericDecimal<u64, u8>;
    type F = GenericFraction<u64>;
    fn get_tests() -> Vec<(&'static str, D)> {
        vec![
            ("NaN", D::nan()),
            ("-inf", D::neg_infinity()),
            ("inf", D::infinity()),
            ("0", D::from_fraction(F::new(0u64, 1u64))),
            ("2", D::from_fraction(F::new(2u64, 1u64))),
            ("-2", D::from_fraction(F::new_neg(2u64, 1u64))),
            ("0.5", D::from_fraction(F::new(1u64, 2u64))),
            ("-0.5", D::from_fraction(F::new_neg(1u64, 2u64))),
            ("0.625", D::from_fraction(F::new(5u64, 8u64))),
            (
                "246.5856420264",
                D::from_fraction(F::new(308232052533u64, 1250000000u64)),
            ),
        ]
    }

    #[test]
    fn to_input_value() {
        for (s, v) in get_tests() {
            let value = <D as ToInputValue>::to_input_value(&v);
            let str_value = value.as_scalar_value::<String>();

            assert!(str_value.is_some());
            assert_eq!(s, str_value.unwrap());
        }
    }

    #[test]
    fn from_input_value() {
        for (s, v) in get_tests() {
            let value = <D as FromInputValue>::from_input_value(&InputValue::scalar(s.to_owned()));

            assert_eq!(value, Some(v));
            assert_eq!(value.unwrap().get_precision(), v.get_precision())
        }
    }
}

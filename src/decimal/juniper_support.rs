use juniper::{
    meta::MetaType, Executor, FromInputValue, GraphQLType, InputValue, Registry, Selection,
    ToInputValue, Value,
};

use generic::GenericInteger;
use num::Integer;
use std::fmt;

use super::GenericDecimal;

impl<T, P> GraphQLType for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + From<u8> + fmt::Display,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
{
    type Context = ();
    type TypeInfo = ();

    fn name(_: &()) -> Option<&str> {
        Some("Decimal")
    }

    fn meta<'r>(info: &(), registry: &mut Registry<'r>) -> MetaType<'r> {
        registry
            .build_scalar_type::<Self>(info)
            .description("Fraction")
            .into_meta()
    }

    fn resolve(&self, _: &(), _: Option<&[Selection]>, _: &Executor<Self::Context>) -> Value {
        Value::string(format!("{}", self))
    }
}

impl<T, P> ToInputValue for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + fmt::Display + From<u8>,
    P: Copy + Integer + Into<usize>,
{
    fn to_input_value(&self) -> InputValue {
        ToInputValue::to_input_value(&format!("{}", self))
    }
}

impl<T, P> FromInputValue for GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize> + From<u8>
{
    fn from_input_value(value: &InputValue) -> Option<Self> {
        let val = if let Some(v) = value.as_string_value() {
            v
        } else {
            return None;
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
            let str_value = value.as_string_value();

            assert!(str_value.is_some());
            assert_eq!(s, str_value.unwrap());
        }
    }

    #[test]
    fn from_input_value() {
        for (s, v) in get_tests() {
            let value = <D as FromInputValue>::from_input_value(&InputValue::string(s));
            assert_eq!(value, Some(v));
            assert_eq!(value.unwrap().get_precision(), v.get_precision())
        }
    }
}

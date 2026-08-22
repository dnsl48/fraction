use fraction::approx::Accuracy;
use fraction::dynaint::DynaInt;
use fraction::error::ParseError;
use fraction::generic::GenericInteger;
use fraction::BigInt;
use fraction::BigUint;
use fraction::Fraction;
use fraction::{GenericFraction, Num, Sign};
use std::str::FromStr;

#[test]
fn msrv_accuracy_multipliers_are_cached() {
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

#[test]
fn msrv_generic_integer_accessors_are_usable() {
    assert_eq!(BigUint::_0(), BigUint::ZERO);
    assert_eq!(BigUint::_1(), BigUint::ONE);
    assert_eq!(BigUint::_10(), BigUint::from(10_u8));

    let bu0_a = BigUint::_0r().expect("BigUint::_0r should be present");
    let bu0_b = BigUint::_0r().expect("BigUint::_0r should be present");
    assert_eq!(*bu0_a, BigUint::ZERO);
    assert!(std::ptr::eq(bu0_a, bu0_b));

    let bu1_a = BigUint::_1r().expect("BigUint::_1r should be present");
    let bu1_b = BigUint::_1r().expect("BigUint::_1r should be present");
    assert_eq!(*bu1_a, BigUint::ONE);
    assert!(std::ptr::eq(bu1_a, bu1_b));

    let bu10_a = BigUint::_10r().expect("BigUint::_10r should be present");
    let bu10_b = BigUint::_10r().expect("BigUint::_10r should be present");
    assert_eq!(*bu10_a, BigUint::from(10_u8));
    assert!(std::ptr::eq(bu10_a, bu10_b));

    assert_eq!(BigInt::_0(), BigInt::ZERO);
    assert_eq!(BigInt::_1(), BigInt::ONE);
    assert_eq!(BigInt::_10(), BigInt::from(10_i8));
    assert!(BigInt::_10() > BigInt::ZERO);

    let bi0_a = BigInt::_0r().expect("BigInt::_0r should be present");
    let bi0_b = BigInt::_0r().expect("BigInt::_0r should be present");
    assert_eq!(*bi0_a, BigInt::ZERO);
    assert!(std::ptr::eq(bi0_a, bi0_b));

    let bi1_a = BigInt::_1r().expect("BigInt::_1r should be present");
    let bi1_b = BigInt::_1r().expect("BigInt::_1r should be present");
    assert_eq!(*bi1_a, BigInt::ONE);
    assert!(std::ptr::eq(bi1_a, bi1_b));

    let bi10_a = BigInt::_10r().expect("BigInt::_10r should be present");
    let bi10_b = BigInt::_10r().expect("BigInt::_10r should be present");
    assert_eq!(*bi10_a, BigInt::from(10_i8));
    assert!(std::ptr::eq(bi10_a, bi10_b));
}

#[test]
fn msrv_unicode_mixed_overflow_is_reported() {
    for input in ["18446744073709551615¹/₂", "18446744073709551615\u{2064}1⁄2"] {
        assert_eq!(
            Fraction::from_unicode_str(input),
            Err(ParseError::ParseIntError)
        );
    }
}

#[test]
fn msrv_parser_component_sign_contract_is_stable() {
    let parsed = GenericFraction::<i16>::from_str("-1/2").unwrap();
    assert_eq!(parsed.sign(), Some(Sign::Minus));
    assert_eq!(parsed.numer(), Some(&1i16));
    assert_eq!(parsed.denom(), Some(&2i16));

    for input in ["1/-2", "1/+2", "--1/2", "-32768"] {
        assert_eq!(
            GenericFraction::<i16>::from_str(input),
            Err(ParseError::ParseIntError)
        );
    }

    assert_eq!(
        GenericFraction::<i16>::from_str_radix("-1/2", 10),
        Ok(GenericFraction::new_neg(1i16, 2i16))
    );
    assert_eq!(
        GenericFraction::<i16>::from_str_radix("1/0", 10),
        Err(ParseError::ZeroDenominator)
    );
    for radix in [1, 37] {
        assert_eq!(
            GenericFraction::<i16>::from_str_radix("1/2", radix),
            Err(ParseError::UnsupportedBase)
        );
    }
    assert_eq!(
        GenericFraction::<i16>::from_str_radix("10/10", 2),
        Ok(GenericFraction::new(1i16, 1i16))
    );
    assert_eq!(
        GenericFraction::<i16>::from_str_radix("z/z", 36),
        Ok(GenericFraction::new(1i16, 1i16))
    );

    type Dynamic = DynaInt<u8, u16>;
    let parsed: Result<Dynamic, ParseError> = Dynamic::from_str_radix("256", 10);
    assert_eq!(parsed, Ok(Dynamic::from(256u16)));
    assert_eq!(
        Dynamic::from_str_radix("1", 0),
        Err(ParseError::UnsupportedBase)
    );
}

use convert::TryToConvertFrom;
use error;

use num::integer::Integer;
use num::traits::{
    Bounded, CheckedAdd, CheckedMul, CheckedSub, FromPrimitive, Num, One, Signed, ToPrimitive, Zero,
};

use std::cmp::{self, Eq, Ordering, PartialEq, PartialOrd};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::{Product, Sum};
use std::num::FpCategory;
use std::ops::{Add, DivAssign, Mul, MulAssign, Neg, SubAssign};
use std::str::FromStr;

use super::{GenericFraction, Sign};
use division;
use fraction::display;
use generic::GenericInteger;

#[cfg(feature = "with-bigint")]
use super::{BigInt, BigUint};

#[cfg(feature = "with-postgres-support")]
mod postgres_support;

#[cfg(feature = "with-juniper-support")]
mod juniper_support;

#[cfg(feature = "with-approx")]
mod approx;

mod ops;
mod try_from;

/// Decimal type implementation
///
/// T is the type for data
/// P is the type for precision
///
/// Uses [GenericFraction] internally to represent the data.
/// Precision is used for display, ordering and hashing.
/// Calculations are exact and ignore precision; comparisons and hashes use each
/// value’s stored precision and truncate fractional digits accordingly.
///
/// # Examples
///
/// ```
/// use fraction::GenericDecimal;
///
/// type Decimal = GenericDecimal<u64, u8>;
///
/// let d1 = Decimal::from(12);
/// let d2 = Decimal::from(0.5);
///
/// let mul = d1 * d2;
/// let div = d1 / d2;
/// let add = d1 + d2;
///
/// assert_eq!(mul, 6.into());
/// assert_eq!(div, Decimal::from("24.00"));
/// assert_eq!(add, Decimal::from(12.5));
/// ```
#[derive(Clone)]
#[cfg_attr(feature = "with-serde-support", derive(Serialize, Deserialize))]
pub struct GenericDecimal<T, P>(pub(crate) GenericFraction<T>, pub(crate) P)
where
    T: Clone + Integer,
    P: Copy + Integer + Into<usize>;

impl<T, P> Copy for GenericDecimal<T, P>
where
    T: Copy + Integer,
    P: Copy + Integer + Into<usize>,
{
}

impl<T, P> Default for GenericDecimal<T, P>
where
    T: Clone + Integer,
    P: Copy + Integer + Into<usize>,
{
    fn default() -> Self {
        Self(GenericFraction::default(), P::zero())
    }
}

impl<T, P> fmt::Display for GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + Integer + Into<usize>,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            GenericDecimal(ref fraction, precision) => {
                let format = display::Format::new(formatter).set_precision(Some(
                    formatter.precision().unwrap_or_else(|| precision.into()),
                ));
                display::format_fraction(fraction, formatter, &format)
            }
        }
    }
}

impl<T, P> fmt::Debug for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + From<u8> + ToPrimitive + fmt::Debug,
    P: Copy + Integer + Into<usize>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            GenericDecimal(ref fraction, precision) => {
                let prec = precision.into();
                let debug_prec = f.precision().unwrap_or(32);
                let value = format!("{:.1$}", fraction, prec);
                let debug_value = format!("{:.1$}", fraction, debug_prec);

                write!(
                    f,
                    "GenericDecimal({} | prec={}; {:?}; {})",
                    value, prec, fraction, debug_value
                )
            }
        }
    }
}

impl<T, P> FromStr for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + CheckedAdd + CheckedMul + CheckedSub,
    P: Copy + GenericInteger + Into<usize> + From<u8> + CheckedAdd,
{
    type Err = error::ParseError;

    fn from_str(val: &str) -> Result<Self, Self::Err> {
        if val == "NaN" {
            Ok(Self::nan())
        } else if val == "-inf" {
            Ok(Self::neg_infinity())
        } else if val == "+inf" || val == "inf" {
            Ok(Self::infinity())
        } else {
            // Check if the number is float like (1.0, 123.456, etc).
            if let Some(split_idx) = val.find('.') {
                let mut prec_iter = val.len() - split_idx - 1;
                let mut precision: P = P::zero();

                loop {
                    if prec_iter == 0 {
                        break;
                    }
                    prec_iter -= 1;

                    if let Some(p) = precision.checked_add(&P::one()) {
                        precision = p;
                    } else {
                        break;
                    }
                }

                Ok(GenericDecimal::from_str_radix(val, 10)?.set_precision(precision))
            // Check if the number is fraction like (1/1, 123/456, etc).
            } else if val.find('/').is_some() {
                Ok(GenericDecimal(GenericFraction::from_str(val)?, 16u8.into()))
            // Check if the number is int like (1, 123, etc).
            } else {
                Ok(GenericDecimal::from_str_radix(val, 10)?.set_precision(P::zero()))
            }
        }
    }
}

macro_rules! dec_impl {
    (impl_trait_math_unary; $trait:ident, $fn:ident) => {
        impl<T, P> $trait for GenericDecimal<T, P>
        where
            T: Clone + GenericInteger,
            P: Copy + Integer + Into<usize>
        {
            type Output = Self;

            fn $fn(self) -> Self::Output {
                match self {
                    GenericDecimal(sf, sp) => GenericDecimal($trait::$fn(sf), sp)
                }
            }
        }


        impl<'a, T, P> $trait for &'a GenericDecimal<T, P>
        where
            T: Clone + GenericInteger,
            P: Copy + Integer + Into<usize>,
            &'a T: $trait<Output=T>
        {
            type Output = GenericDecimal<T, P>;

            fn $fn(self) -> Self::Output {
                match self {
                    GenericDecimal(sf, sp) => GenericDecimal($trait::$fn(sf), *sp)
                }
            }
        }
    };

    (impl_trait_proxy; $trait:ident; $(($fn:ident ; $self:tt ; ; $return:ty)),*) => {
        impl<T, P> $trait for GenericDecimal<T, P>
        where
            T: Clone + GenericInteger + $trait,
            P: Copy + GenericInteger + Into<usize>
        {$(
            dec_impl!(_impl_trait_proxy_fn; $trait; $self; $fn; ; $return);
        )*}
    };

    (_impl_trait_proxy_fn; $trait:ident; rself; $fn:ident ; ; $return:ty) => {
        fn $fn(&self) -> $return {
            match self {
                GenericDecimal(f, _) => {
                    <GenericFraction<T> as $trait>::$fn(f)
                }
            }
        }
    };

    (impl_trait_from_int; $($t:ty),*) => {$(
        impl<T, P> From<$t> for GenericDecimal<T, P>
        where
            T: Clone + GenericInteger,
            P: Copy + GenericInteger + Into<usize>
        {
            fn from(value: $t) -> Self {
                GenericDecimal(GenericFraction::from(value), P::zero())
            }
        }
    )*};

    (impl_trait_from_float; $($t:ty),*) => {$(
        impl<T, P> From<$t> for GenericDecimal<T, P>
        where
            T: Clone + GenericInteger + FromPrimitive,
            P: Copy + GenericInteger + Into<usize> + From<u8> + Bounded
        {
            fn from(value: $t) -> Self {
                if value.is_nan () { return GenericDecimal::nan() };
                if value.is_infinite () { return if value.is_sign_negative () { GenericDecimal::neg_infinity() } else { GenericDecimal::infinity() } };

                GenericDecimal(GenericFraction::from(value), P::zero()).calc_precision(None)
            }
        }
    )*}
}

dec_impl!(impl_trait_from_float; f32, f64);
dec_impl!(impl_trait_from_int; u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

impl<'a, T, P> From<&'a str> for GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
{
    fn from(value: &'a str) -> Self {
        GenericDecimal::from_str(value).unwrap_or_else(|_| GenericDecimal::nan())
    }
}

#[cfg(feature = "with-bigint")]
dec_impl!(impl_trait_from_int; BigUint, BigInt);

dec_impl!(impl_trait_math_unary; Neg, neg);

dec_impl!(impl_trait_proxy;
    ToPrimitive;
        (to_i64; rself;; Option<i64>),
        (to_u64; rself;; Option<u64>),
        (to_f64; rself;; Option<f64>)
);

impl<T, P> Sum for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialEq,
    P: Copy + GenericInteger + Into<usize>,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(GenericDecimal::<T, P>::zero(), Add::add)
    }
}
impl<'a, T, P> Sum<&'a GenericDecimal<T, P>> for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialEq,
    P: Copy + GenericInteger + Into<usize>,
{
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        let mut sum = Self::zero();

        for x in iter {
            sum += x;
        }

        sum
    }
}

impl<T, P> Product for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialEq,
    P: Copy + GenericInteger + Into<usize>,
{
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(GenericDecimal::<T, P>::one(), Mul::mul)
    }
}
impl<'a, T, P> Product<&'a GenericDecimal<T, P>> for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialEq,
    P: Copy + GenericInteger + Into<usize>,
{
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        let mut sum = Self::one();

        for x in iter {
            sum *= x;
        }

        sum
    }
}

fn decimal_fraction_next_digit<T>(state_slot: &mut Option<division::DivisionState<T>>) -> Option<u8>
where
    T: Clone + GenericInteger,
{
    let state = match state_slot.take() {
        None => return Some(0),
        Some(state) => state,
    };

    if state.remainder.is_zero() {
        *state_slot = Some(state);
        return Some(0);
    }

    let mut digit = 0u8;
    match division::divide_rem_resume(state, |s, d| {
        digit = d;
        Ok(Err(s))
    }) {
        Ok(next_state) => {
            *state_slot = Some(next_state);
            Some(digit)
        }
        Err(_) => None,
    }
}

fn decimal_is_canonical_zero<T>(numer: &T, denom: &T, precision: usize) -> bool
where
    T: Clone + GenericInteger,
{
    let (integral, remainder) = numer.div_rem(denom);
    if !integral.is_zero() {
        return false;
    }

    if precision == 0 {
        return true;
    }

    let mut state = if remainder.is_zero() {
        None
    } else {
        Some(division::DivisionState::new(remainder, denom.clone()))
    };

    for _ in 0..precision {
        let digit = match decimal_fraction_next_digit(&mut state) {
            Some(digit) => digit,
            None => return false,
        };
        if digit != 0 {
            return false;
        }
    }

    true
}

fn decimal_fraction_cmp<T>(
    lhs_num: &T,
    lhs_den: &T,
    lhs_precision: usize,
    rhs_num: &T,
    rhs_den: &T,
    rhs_precision: usize,
) -> Ordering
where
    T: Clone + GenericInteger,
{
    let (lhs_int, lhs_rem) = lhs_num.div_rem(lhs_den);
    let (rhs_int, rhs_rem) = rhs_num.div_rem(rhs_den);

    if lhs_int != rhs_int {
        return lhs_int.cmp(&rhs_int);
    }

    let max_precision = if lhs_precision > rhs_precision {
        lhs_precision
    } else {
        rhs_precision
    };

    let mut lhs_state = if lhs_rem.is_zero() {
        None
    } else {
        Some(division::DivisionState::new(lhs_rem, lhs_den.clone()))
    };
    let mut rhs_state = if rhs_rem.is_zero() {
        None
    } else {
        Some(division::DivisionState::new(rhs_rem, rhs_den.clone()))
    };

    for digit in 0..max_precision {
        let lhs_digit = if digit >= lhs_precision {
            0
        } else {
            decimal_fraction_next_digit(&mut lhs_state).unwrap_or(0)
        };

        let rhs_digit = if digit >= rhs_precision {
            0
        } else {
            decimal_fraction_next_digit(&mut rhs_state).unwrap_or(0)
        };

        if lhs_digit != rhs_digit {
            return lhs_digit.cmp(&rhs_digit);
        }
    }

    Ordering::Equal
}

impl<T, P> Ord for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + Ord,
    P: Copy + GenericInteger + Into<usize>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            GenericDecimal(sf, sp) => match other {
                GenericDecimal(of, op) => match (sf, of) {
                    (GenericFraction::NaN, GenericFraction::NaN) => Ordering::Equal,
                    (GenericFraction::NaN, _) => Ordering::Less,
                    (_, GenericFraction::NaN) => Ordering::Greater,
                    (GenericFraction::Infinity(sign), GenericFraction::Infinity(other_sign)) => {
                        sign.cmp(other_sign)
                    }
                    (GenericFraction::Infinity(Sign::Plus), GenericFraction::Rational(_, _)) => {
                        Ordering::Greater
                    }
                    (GenericFraction::Infinity(Sign::Minus), GenericFraction::Rational(_, _)) => {
                        Ordering::Less
                    }
                    (GenericFraction::Rational(_, _), GenericFraction::Infinity(Sign::Plus)) => {
                        Ordering::Less
                    }
                    (GenericFraction::Rational(_, _), GenericFraction::Infinity(Sign::Minus)) => {
                        Ordering::Greater
                    }
                    (
                        GenericFraction::Rational(s_sign, s_ratio),
                        GenericFraction::Rational(o_sign, o_ratio),
                    ) => {
                        let lhs_precision = (*sp).into();
                        let rhs_precision = (*op).into();

                        let lhs_zero = decimal_is_canonical_zero(
                            s_ratio.numer(),
                            s_ratio.denom(),
                            lhs_precision,
                        );
                        let rhs_zero = decimal_is_canonical_zero(
                            o_ratio.numer(),
                            o_ratio.denom(),
                            rhs_precision,
                        );

                        if lhs_zero && rhs_zero {
                            return Ordering::Equal;
                        }

                        if s_sign != o_sign {
                            return if *s_sign == Sign::Minus {
                                Ordering::Less
                            } else {
                                Ordering::Greater
                            };
                        }

                        let abs_cmp = decimal_fraction_cmp(
                            s_ratio.numer(),
                            s_ratio.denom(),
                            lhs_precision,
                            o_ratio.numer(),
                            o_ratio.denom(),
                            rhs_precision,
                        );

                        if *s_sign == Sign::Minus {
                            abs_cmp.reverse()
                        } else {
                            abs_cmp
                        }
                    }
                },
            },
        }
    }
}

impl<T, P> PartialOrd for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialOrd,
    P: Copy + GenericInteger + Into<usize>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T, P> PartialEq for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialEq,
    P: Copy + GenericInteger + Into<usize>,
{
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<T, P> Hash for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + PartialEq,
    P: Copy + GenericInteger + Into<usize>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            GenericDecimal(fraction, precision) => match fraction {
                GenericFraction::NaN => state.write_u8(0u8),
                GenericFraction::Infinity(sign) => {
                    if let Sign::Plus = sign {
                        state.write_u8(1u8)
                    } else {
                        state.write_u8(2u8)
                    }
                }
                GenericFraction::Rational(sign, ratio) => {
                    let num = ratio.numer();
                    let den = ratio.denom();
                    let precision = (*precision).into();
                    let canonical_zero = decimal_is_canonical_zero(num, den, precision);

                    if *sign == Sign::Plus || canonical_zero {
                        state.write_u8(3u8);
                    } else {
                        state.write_u8(4u8);
                    }

                    let mut hasher_state =
                        division::divide_integral(num.clone(), den.clone(), |digit: u8| {
                            state.write_u8(digit);
                            Ok(true)
                        })
                        .ok()
                        .filter(|hash_state| !hash_state.remainder.is_zero());

                    if precision != 0 {
                        let mut dot = false;
                        let mut trailing_zeroes: usize = 0;

                        for _ in 0..precision {
                            let digit = decimal_fraction_next_digit(&mut hasher_state).unwrap_or(0);

                            if digit == 0 {
                                trailing_zeroes += 1;
                                continue;
                            }

                            if !dot {
                                dot = true;
                                state.write_u8(10u8);
                            }

                            if trailing_zeroes > 0 {
                                state.write_usize(trailing_zeroes);
                                trailing_zeroes = 0;
                            }

                            state.write_u8(digit);
                        }
                    }
                }
            },
        };
    }
}

impl<T, P> Eq for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + Eq,
    P: Copy + GenericInteger + Into<usize>,
{
}

impl<T, P> Bounded for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + Bounded,
    P: Copy + GenericInteger + Into<usize> + Bounded,
{
    fn min_value() -> Self {
        GenericDecimal(GenericFraction::min_value(), P::max_value())
    }

    fn max_value() -> Self {
        GenericDecimal(GenericFraction::max_value(), P::max_value())
    }
}

impl<T, P> Zero for GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize> + Zero,
{
    fn zero() -> Self {
        GenericDecimal(GenericFraction::zero(), P::zero())
    }

    fn is_zero(&self) -> bool {
        match self {
            GenericDecimal(fra, _) => fra.is_zero(),
        }
    }
}

impl<T, P> One for GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize>,
{
    fn one() -> Self {
        GenericDecimal(GenericFraction::one(), P::zero())
    }
}

impl<T, P> Num for GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
{
    type FromStrRadixErr = error::ParseError;

    fn from_str_radix(value: &str, base: u32) -> Result<Self, error::ParseError> {
        if base != 10 {
            return Err(error::ParseError::UnsupportedBase);
        }

        Ok(GenericDecimal(
            GenericFraction::from_str(value)?,
            16u8.into(),
        ))
    }
}

impl<T, P> Signed for GenericDecimal<T, P>
where
    T: Clone + GenericInteger + Neg,
    P: Copy + GenericInteger + Into<usize> + From<u8>,
{
    fn abs(&self) -> Self {
        match self {
            GenericDecimal(fra, pres) => GenericDecimal(fra.abs(), *pres),
        }
    }

    fn abs_sub(&self, other: &Self) -> Self {
        match self {
            GenericDecimal(sf, sp) => match other {
                GenericDecimal(of, op) => GenericDecimal(sf.abs_sub(of), cmp::max(*sp, *op)),
            },
        }
    }

    fn signum(&self) -> Self {
        match self {
            GenericDecimal(fra, pres) => GenericDecimal(fra.signum(), *pres),
        }
    }

    fn is_positive(&self) -> bool {
        match self {
            GenericDecimal(f, _) => f.is_positive(),
        }
    }

    fn is_negative(&self) -> bool {
        match self {
            GenericDecimal(f, _) => f.is_negative(),
        }
    }
}

impl<T, P> GenericDecimal<T, P>
where
    T: Clone + GenericInteger,
    P: Copy + GenericInteger + Into<usize>,
{
    /// Returns Some(Sign) of the decimal, or None if NaN is the value
    pub const fn sign(&self) -> Option<Sign>
    where
        T: CheckedAdd + CheckedMul + CheckedSub,
    {
        self.0.sign()
    }

    /// Sets representational precision for the Decimal.
    ///
    /// Precision controls truncation for comparison and hashing.
    /// `set_precision(0)` drops all fractional digits.
    ///
    /// Canonical zero values (for example `-0`, `-0.9@p0`, and
    /// `-0.04@p1`) compare and hash as positive zero.
    ///
    /// Use this method when you know the precision you want to work with.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericDecimal;
    ///
    /// type D = GenericDecimal<u32, u8>;
    ///
    /// let first = D::from("0.004")  // initial precision is 4
    ///             .set_precision(2);  // but we want to work with 2
    /// let second = D::from("0.006").set_precision(2);
    ///
    /// // Even though "first" and "second" both have precision 2
    /// // the actual calculations are still performed with their
    /// // exact initial precision
    /// assert_eq!(first + second, D::from("0.01"));
    ///
    /// // The comparison, on the other hand, takes each value’s own precision first.
    /// // The comparison then pads the shorter representation with zeroes so both
    /// // operands can be compared in the same precision grid.
    /// assert_ne!(  // compares "0.010" with "0.011"
    ///     D::from("0.01"),  // has precision 2
    ///     D::from("0.011")  // has precision 3
    /// );
    ///
    /// assert_eq!(  // compares "0.01" with "0.01"
    ///     D::from("0.01").set_precision(2),
    ///     D::from("0.011").set_precision(2)
    /// );
    /// ```
    pub fn set_precision(self, precision: P) -> Self {
        match self {
            GenericDecimal(fraction, _) => GenericDecimal(fraction, precision),
        }
    }

    /// Returns the current representational precision for the Decimal
    pub const fn get_precision(&self) -> P {
        match self {
            GenericDecimal(_, precision) => *precision,
        }
    }

    /// Try to recalculate the representational precision
    /// depending on the internal Fraction, which is the actual value.
    ///
    /// Performs the actual division until the exact decimal value is calculated,
    /// the precision type (P) capacity is reached (e.g. 255 for u8) or max_precision
    /// is reached, if it is given.
    ///
    /// # WARNING
    /// You only need this method if you want to find the max available
    /// precision for the current decimal value.
    /// However, keep in mind that irrational values (such as 1/3) do not have finite precision,
    /// so if this method returns P::MAX (or max_precision), most likely you have
    /// an irrational value.
    /// Be careful with max numbers for `usize` - that can take very long time to
    /// compute (more than a minute)
    pub fn calc_precision(self, max_precision: Option<P>) -> Self
    where
        T: CheckedMul + DivAssign + MulAssign + SubAssign + ToPrimitive + GenericInteger,
        P: Bounded + CheckedAdd,
    {
        match self {
            GenericDecimal(fraction, _) => {
                let precision = match fraction {
                    GenericFraction::NaN => P::zero(),
                    GenericFraction::Infinity(_) => P::zero(),
                    GenericFraction::Rational(_, ref ratio) => {
                        let mut precision: P = P::zero();
                        let max_precision: P = max_precision.unwrap_or_else(P::max_value);

                        let num = ratio.numer();
                        let den = ratio.denom();

                        if let Ok(div_state) =
                            division::divide_integral(num.clone(), den.clone(), |_| Ok(true))
                        {
                            if !div_state.remainder.is_zero() {
                                let one = P::one();

                                let _result = division::divide_rem(
                                    div_state.remainder,
                                    div_state.divisor,
                                    |s, _| {
                                        if precision >= max_precision {
                                            // stop here, we have reached the limit
                                            return Ok(Err(s));
                                        }

                                        precision = if let Some(p) = precision.checked_add(&one) {
                                            p
                                        } else {
                                            return Ok(Err(s));
                                        };
                                        Ok(Ok(s))
                                    },
                                );
                            }
                        }

                        precision
                    }
                };

                GenericDecimal(fraction, precision)
            }
        }
    }

    #[inline]
    pub fn nan() -> Self {
        GenericDecimal(GenericFraction::nan(), P::zero())
    }

    #[inline]
    pub fn infinity() -> Self {
        GenericDecimal(GenericFraction::infinity(), P::zero())
    }

    #[inline]
    pub fn neg_infinity() -> Self {
        GenericDecimal(GenericFraction::neg_infinity(), P::zero())
    }

    #[inline]
    pub fn neg_zero() -> Self {
        GenericDecimal(GenericFraction::neg_zero(), P::zero())
    }

    pub fn min_positive_value() -> Self
    where
        T: Bounded,
        P: Bounded,
    {
        GenericDecimal(GenericFraction::min_positive_value(), P::max_value())
    }

    pub const fn is_nan(&self) -> bool {
        self.0.is_nan()
    }

    pub const fn is_infinite(&self) -> bool {
        self.0.is_infinite()
    }

    pub const fn is_finite(&self) -> bool {
        self.0.is_finite()
    }

    pub fn is_normal(&self) -> bool {
        self.0.is_normal()
    }

    pub fn classify(&self) -> FpCategory {
        self.0.classify()
    }

    pub fn floor(&self) -> Self {
        match self {
            GenericDecimal(f, _) => GenericDecimal(f.floor(), P::zero()),
        }
    }

    pub fn ceil(&self) -> Self {
        match self {
            GenericDecimal(f, _) => GenericDecimal(f.ceil(), P::zero()),
        }
    }

    pub fn round(&self) -> Self {
        match self {
            GenericDecimal(f, _) => GenericDecimal(f.round(), P::zero()),
        }
    }

    pub fn trunc(&self) -> Self {
        match self {
            GenericDecimal(f, _) => GenericDecimal(f.trunc(), P::zero()),
        }
    }

    pub fn fract(&self) -> Self {
        self.map_ref(|f| f.fract())
    }

    pub fn abs(&self) -> Self {
        self.map_ref(|f| f.abs())
    }

    pub fn signum(&self) -> Self {
        self.map_ref(|f| f.signum())
    }

    pub const fn is_sign_positive(&self) -> bool {
        self.0.is_sign_positive()
    }

    pub const fn is_sign_negative(&self) -> bool {
        self.0.is_sign_negative()
    }

    pub fn mul_add(&self, a: Self, b: Self) -> Self {
        self.clone() * a + b
    }

    pub fn recip(&self) -> Self {
        self.map_ref(|f| f.recip())
    }

    pub fn map(self, fun: impl FnOnce(GenericFraction<T>) -> GenericFraction<T>) -> Self {
        match self {
            GenericDecimal(fra, pres) => GenericDecimal(fun(fra), pres),
        }
    }

    pub fn map_mut(&mut self, fun: impl FnOnce(&mut GenericFraction<T>)) {
        match self {
            GenericDecimal(fra, _) => fun(fra),
        }
    }

    pub fn map_ref(&self, fun: impl FnOnce(&GenericFraction<T>) -> GenericFraction<T>) -> Self {
        match self {
            GenericDecimal(fra, pres) => GenericDecimal(fun(fra), *pres),
        }
    }

    #[deprecated(note = "Use `match decimal {GenericDecimal(fraction, precision) => ... }`")]
    pub fn apply_ref<R>(&self, fun: impl FnOnce(&GenericFraction<T>, P) -> R) -> R {
        match self {
            GenericDecimal(fra, pres) => fun(fra, *pres),
        }
    }

    /// Convert from a GenericFraction
    ///
    /// Automatically calculates precision, so for "bad" numbers
    /// may take a lot of CPU cycles, especially if precision
    /// represented by big types (e.g. usize)
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::{Fraction, Decimal};
    ///
    /// let from_fraction = Decimal::from_fraction(Fraction::new(1u64, 3u64));
    /// let from_division = Decimal::from(1) / Decimal::from(3);
    ///
    /// let d1 = Decimal::from(4) / from_fraction;
    /// let d2 = Decimal::from(4) / from_division;
    ///
    /// assert_eq!(d1, d2);
    /// assert_eq!(d1, Decimal::from(12));
    /// ```
    #[inline]
    pub fn from_fraction(fraction: GenericFraction<T>) -> Self
    where
        T: GenericInteger + ToPrimitive,
        P: Bounded + CheckedAdd,
    {
        let two = P::one() + P::one();
        let hun = P::_10() * P::_10();
        let max_precision = two * hun + hun / two + P::_10() / two; // 255

        GenericDecimal(fraction, P::zero()).calc_precision(Some(max_precision))
    }

    #[inline]
    pub fn from_fraction_with_precision(fraction: GenericFraction<T>, precision: P) -> Self
    where
        T: GenericInteger + ToPrimitive,
        P: Bounded + CheckedAdd,
    {
        GenericDecimal(fraction, precision)
    }
}

impl<T, F, P1, P2> TryToConvertFrom<GenericDecimal<F, P1>> for GenericDecimal<T, P2>
where
    T: Copy + Integer + TryToConvertFrom<F>,
    F: Copy + Integer,
    P2: Copy + Integer + Into<usize> + TryToConvertFrom<P1>,
    P1: Copy + Integer + Into<usize>,
{
    fn try_to_convert_from(src: GenericDecimal<F, P1>) -> Option<Self> {
        Some(match src {
            GenericDecimal(fraction, precision) => GenericDecimal(
                GenericFraction::try_to_convert_from(fraction)?,
                P2::try_to_convert_from(precision)?,
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::error::ParseError;
    use std::cmp::Ordering;
    use std::collections::{BTreeSet, HashSet};
    use {CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};

    use super::{GenericDecimal, One};
    use fraction::GenericFraction;
    use prelude::Decimal;
    use std::hash::{Hash, Hasher};
    use std::str::FromStr;

    type D = GenericDecimal<u8, u8>;

    fn hash_it(target: &impl Hash) -> u64 {
        use std::collections::hash_map::DefaultHasher;

        let mut h = DefaultHasher::new();
        target.hash(&mut h);
        h.finish()
    }

    generate_ops_tests! (
        NaN => {D::nan()};
        NegInf => {D::neg_infinity()};
        PosInf => {D::infinity()};
        Zero => {D::from(0)};
        Half => {D::from(0.5)};
        One => {D::from(1)};
        Two => {D::from(2)};
        Three => {D::from(3)};
        Four => {D::from(4)};
    );

    #[test]
    fn hash_and_partial_eq() {
        {
            let one = Decimal::from(152.568);
            let two = Decimal::from(328.76842);

            let div = two / one.set_precision(16);
            let red = Decimal::from("2.1548976194221592");

            assert_eq!(div.get_precision(), 16);
            assert_eq!(div, red);
            assert_eq!(hash_it(&div), hash_it(&red));
        }

        {
            let one = Decimal::from(152.568);
            let two = Decimal::from(328.76842);

            let mul = one * two;

            assert_eq!(mul.get_precision(), 5);
            assert_eq!(mul, Decimal::from("50159.5403"));
            assert_eq!(hash_it(&mul), hash_it(&Decimal::from("50159.5403")));
            assert_eq!(mul.set_precision(6), Decimal::from("50159.540302"));
            assert_eq!(
                hash_it(&mul.set_precision(6)),
                hash_it(&Decimal::from("50159.540302"))
            );
        }
    }

    #[test]
    fn comparison_reported_bug_pair() {
        let a = Decimal::from_str("0.5").unwrap() / Decimal::from_str("0.3").unwrap();
        let b = Decimal::from_str("1.6").unwrap();

        assert_eq!(a, b);
        assert_eq!(Some(Ordering::Equal), a.partial_cmp(&b));
        assert_eq!(Ordering::Equal, a.cmp(&b));
        assert!(!(a < b));
        assert!(!(a > b));
        assert!(a <= b);
        assert!(a >= b);

        let mut set = BTreeSet::new();
        set.insert(a);
        set.insert(b);
        assert_eq!(set.len(), 1);

        let mut hash = HashSet::new();
        hash.insert(a);
        hash.insert(b);
        assert_eq!(hash.len(), 1);
        assert_eq!(hash_it(&a), hash_it(&b));

        assert_eq!(vec![a].binary_search(&b), Ok(0));
    }

    #[test]
    fn comparison_trailing_zeroes_and_precision() {
        let one = Decimal::from_str("1.0").unwrap();
        let one_with_more_zeroes = Decimal::from_str("1.000").unwrap();

        assert_eq!(one, one_with_more_zeroes);
        assert_eq!(hash_it(&one), hash_it(&one_with_more_zeroes));

        let mut set = BTreeSet::new();
        set.insert(one);
        set.insert(one_with_more_zeroes);
        assert_eq!(set.len(), 1);

        let mut hash = HashSet::new();
        hash.insert(one);
        hash.insert(one_with_more_zeroes);
        assert_eq!(hash.len(), 1);

        assert_eq!(vec![one].binary_search(&one_with_more_zeroes), Ok(0));
    }

    #[test]
    fn comparison_same_exact_fraction_different_precision() {
        type D = GenericDecimal<u64, u8>;

        let five_thirds_p1: D =
            GenericDecimal::from_fraction_with_precision(GenericFraction::new(5u64, 3u64), 1u8);
        let five_thirds_p2: D =
            GenericDecimal::from_fraction_with_precision(GenericFraction::new(5u64, 3u64), 2u8);

        assert!(five_thirds_p1 < five_thirds_p2);
        assert_eq!(five_thirds_p1, five_thirds_p1.set_precision(1));
        assert_eq!(five_thirds_p2, five_thirds_p2.set_precision(2));
    }

    #[test]
    fn comparison_truncation_p0() {
        let positive_one = Decimal::from_str("1.99").unwrap().set_precision(0);
        let positive_other = Decimal::from_str("1.01").unwrap().set_precision(0);
        let negative_one = Decimal::from_str("-1.99").unwrap().set_precision(0);
        let negative_other = Decimal::from_str("-1.01").unwrap().set_precision(0);

        assert_eq!(positive_one, positive_other);
        assert_eq!(negative_one, negative_other);
        assert!(!(positive_one < positive_other));
        assert!(!(negative_one < negative_other));
    }

    #[test]
    fn comparison_negative_and_zero() {
        use num::traits::Zero;

        let negative_zero = -Decimal::zero();
        let negative_zero_p0 = -Decimal::from_str("0.9").unwrap().set_precision(0);
        let negative_zero_p1 = -Decimal::from_str("0.04").unwrap().set_precision(1);

        assert_eq!(negative_zero, Decimal::from(0));
        assert_eq!(negative_zero_p0, Decimal::from(0));
        assert_eq!(negative_zero_p1, Decimal::from(0));
        assert_eq!(negative_zero, negative_zero_p0);
        assert_eq!(negative_zero, negative_zero_p1);
        assert_eq!(negative_zero_p0, negative_zero_p1);
        assert_eq!(hash_it(&negative_zero), hash_it(&negative_zero_p1));

        let mut set = BTreeSet::new();
        set.insert(negative_zero);
        set.insert(negative_zero_p0);
        set.insert(negative_zero_p1);
        assert_eq!(set.len(), 1);

        let mut set = HashSet::new();
        set.insert(negative_zero);
        set.insert(negative_zero_p0);
        set.insert(negative_zero_p1);
        assert_eq!(set.len(), 1);
        assert_eq!(hash_it(&negative_zero), hash_it(&negative_zero_p1));

        assert_eq!(vec![negative_zero].binary_search(&negative_zero_p1), Ok(0));
    }

    #[test]
    fn comparison_special_value_order() {
        let nan = Decimal::nan();
        let neg_inf = Decimal::neg_infinity();
        let finite = Decimal::from_str("1.6").unwrap();
        let inf = Decimal::infinity();

        assert_eq!(nan.cmp(&nan), Ordering::Equal);
        assert_eq!(nan.cmp(&neg_inf), Ordering::Less);
        assert_eq!(nan.cmp(&finite), Ordering::Less);
        assert_eq!(nan.cmp(&inf), Ordering::Less);

        assert_eq!(neg_inf.cmp(&finite), Ordering::Less);
        assert_eq!(neg_inf.cmp(&inf), Ordering::Less);

        assert_eq!(finite.cmp(&inf), Ordering::Less);
    }

    #[test]
    fn comparison_pairwise_eq_iff_cmp_equal() {
        let values = vec![
            Decimal::nan(),
            Decimal::neg_infinity(),
            (-Decimal::from_str("1").unwrap()),
            Decimal::from_str("-0.5").unwrap(),
            Decimal::from(0),
            Decimal::from_str("0.5").unwrap(),
            Decimal::from_str("1.6").unwrap(),
            Decimal::infinity(),
        ];

        for left in &values {
            for right in &values {
                let cmp = left.cmp(right);
                assert_eq!(left.eq(right), cmp == Ordering::Equal);
                assert_eq!(left.partial_cmp(right), Some(cmp));
            }
        }
    }

    #[test]
    fn comparison_reverse_antisymmetry() {
        let values = vec![
            Decimal::nan(),
            Decimal::neg_infinity(),
            (-Decimal::from_str("1").unwrap()),
            Decimal::from_str("-0.5").unwrap(),
            Decimal::from(0),
            Decimal::from_str("0.5").unwrap(),
            Decimal::from_str("1.6").unwrap(),
            Decimal::infinity(),
        ];

        for left in &values {
            for right in &values {
                let forward = left.cmp(right);
                let reverse = right.cmp(left);

                assert_eq!(forward, reverse.reverse());
            }
        }
    }

    #[test]
    fn comparison_transitivity_5_thirds_chain() {
        let five_thirds_p1 =
            Decimal::from_fraction_with_precision(GenericFraction::new(5u64, 3u64), 1);
        let one_dot_six = Decimal::from_str("1.6").unwrap();
        let one_dot_sixty_five = Decimal::from_str("1.65").unwrap();
        let negative_five_thirds_p1 = -five_thirds_p1;
        let negative_one_dot_six = -Decimal::from_str("1.6").unwrap();

        assert_eq!(five_thirds_p1, one_dot_six);
        assert_eq!(
            Some(Ordering::Equal),
            five_thirds_p1.partial_cmp(&one_dot_six)
        );
        assert!(one_dot_six < one_dot_sixty_five);
        assert!(five_thirds_p1 < one_dot_sixty_five);

        assert_eq!(negative_five_thirds_p1, negative_one_dot_six);
        assert_eq!(
            Some(Ordering::Equal),
            negative_five_thirds_p1.partial_cmp(&negative_one_dot_six)
        );
        assert_eq!(
            Ordering::Equal,
            negative_five_thirds_p1.cmp(&negative_one_dot_six)
        );
        assert!(!(negative_five_thirds_p1 < negative_one_dot_six));
        assert!(!(negative_five_thirds_p1 > negative_one_dot_six));
        assert!(negative_five_thirds_p1 <= negative_one_dot_six);
        assert!(negative_five_thirds_p1 >= negative_one_dot_six);
    }

    #[test]
    fn fmt_debug() {
        type F = GenericFraction<u64>;
        assert_eq!(
            format!("{:?}", Decimal::one()),
            format!("GenericDecimal(1 | prec=0; {:?}; 1)", F::one())
        );
    }

    #[test]
    fn summing_iterator() {
        let values = vec![Decimal::from(152.568), Decimal::from(328.76842)];
        let sum: Decimal = values.iter().sum();
        assert_eq!(sum, values[0] + values[1])
    }

    #[test]
    fn product_iterator() {
        let values = vec![Decimal::from(152.568), Decimal::from(328.76842)];
        let product: Decimal = values.iter().product();
        assert_eq!(product, values[0] * values[1])
    }

    #[test]
    fn calc_precision() {
        use super::BigUint;
        type BigDecimal = GenericDecimal<BigUint, usize>;

        let one = BigDecimal::from(1);
        let two = BigDecimal::from(2);
        let three = BigDecimal::from(3);
        let half = BigDecimal::from(1) / BigDecimal::from(2);
        let onethird = BigDecimal::from(1) / BigDecimal::from(3);

        assert_eq!(0, one.get_precision());
        assert_eq!(0, two.get_precision());
        assert_eq!(0, three.get_precision());
        assert_eq!(0, half.get_precision());
        assert_eq!(0, onethird.get_precision());
        assert_eq!(1, half.clone().calc_precision(None).get_precision());
        assert_eq!(0, half.clone().calc_precision(Some(0)).get_precision());
        assert_eq!(1, half.clone().calc_precision(Some(1)).get_precision());
        assert_eq!(1, half.clone().calc_precision(Some(255)).get_precision());

        assert_eq!(0, onethird.clone().calc_precision(Some(0)).get_precision());
        assert_eq!(1, onethird.clone().calc_precision(Some(1)).get_precision());
        assert_eq!(
            255,
            onethird.clone().calc_precision(Some(255)).get_precision()
        );
        assert_eq!(
            2056,
            onethird.clone().calc_precision(Some(2056)).get_precision()
        );

        type D = GenericDecimal<u64, u8>;
        let one = D::from(1);
        let two = D::from(2);
        let three = D::from(3);
        let half = one / two;
        let onethird = one / three;

        assert_eq!(0, one.get_precision());
        assert_eq!(0, two.get_precision());
        assert_eq!(0, three.get_precision());
        assert_eq!(0, half.get_precision());
        assert_eq!(0, onethird.get_precision());
        assert_eq!(1, half.calc_precision(None).get_precision());
        assert_eq!(255, onethird.calc_precision(None).get_precision());
    }

    #[test]
    fn decimal_test_default() {
        let dec = D::default();
        assert_eq!("0", format!("{}", dec));
        assert_eq!(0, dec.get_precision());

        #[cfg(feature = "with-bigint")]
        {
            use crate::BigDecimal;
            let dec = BigDecimal::default();
            assert_eq!("0", format!("{}", dec));
            assert_eq!(0, dec.get_precision());
        }
    }

    #[test]
    fn from_fraction_with_precision() {
        let one_third: GenericFraction<u64> = GenericFraction::new(1u64, 3u64);

        assert_eq!(
            GenericDecimal::<u64, u8>::from_fraction_with_precision(one_third, 18).get_precision(),
            18
        );
    }

    #[test]
    fn from_str_zero_denominator() {
        assert_eq!(Ok(Decimal::infinity()), Decimal::from_str("1/0"));
        assert_eq!(Ok(Decimal::infinity()), Decimal::from_str("+1/0"));
        assert_eq!(Ok(Decimal::neg_infinity()), Decimal::from_str("-1/0"));
        assert_eq!(Ok(Decimal::nan()), Decimal::from_str("0/0"));

        assert_eq!(
            Ok(GenericDecimal::<u8, u8>::infinity()),
            GenericDecimal::<u8, u8>::from_str("1/0")
        );
        assert_eq!(
            Ok(GenericDecimal::<u8, u8>::neg_infinity()),
            GenericDecimal::<u8, u8>::from_str("-1/0")
        );
        assert_eq!(
            Ok(GenericDecimal::<u8, u8>::nan()),
            GenericDecimal::<u8, u8>::from_str("0/0")
        );

        assert_eq!(Decimal::from("1/0"), Decimal::infinity());
    }

    #[test]
    fn from_str_infallible_conversion_rejects_component_signs_as_nan() {
        assert!(Decimal::from("1/+2").is_nan());
        assert!(Decimal::from("1.+5").is_nan());
    }

    #[test]
    fn from_str_component_sign_rejected_for_signed_storage() {
        type SignedDecimal = GenericDecimal<i16, u8>;

        assert_eq!(
            SignedDecimal::from_str("-1/2").unwrap(),
            SignedDecimal::from_fraction_with_precision(GenericFraction::new_neg(1i16, 2i16), 16)
        );
        for input in ["1/-2", "1/+2", "--1/2", "1.-2", "-32768", "1/-32768"] {
            assert_eq!(
                Err(ParseError::ParseIntError),
                SignedDecimal::from_str(input),
                "input should not place a sign inside a decimal component: {input}"
            );
        }
    }

    // TODO: more tests
}

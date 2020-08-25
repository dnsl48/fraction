#[cfg(feature = "with-bigint")]
use super::{BigInt, BigUint};

use error::ParseError;
use std::iter::{Product, Sum};

use super::{
    /*Float, */ Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Integer, Num, One,
    ParseRatioError, Ratio, Signed, ToPrimitive, Zero,
};

use generic::{read_generic_integer, GenericInteger};

use std::cmp::{Eq, Ordering, PartialEq, PartialOrd};
use std::hash::{Hash, Hasher};
use std::num::FpCategory;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

use std::f64;
use std::fmt;
use std::mem;

pub mod display;

#[cfg(feature = "with-juniper-support")]
pub mod juniper_support;

#[cfg(feature = "with-postgres-support")]
pub mod postgres_support;

/// Sign representation
///
/// Fractions keep the sign represented by this enum,
/// so that we can use unsigned ints as base data types.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "with-serde-support", derive(Serialize, Deserialize))]
pub enum Sign {
    Plus,
    Minus,
}

impl Sign {
    pub fn is_positive(self) -> bool {
        match self {
            Sign::Plus => true,
            _ => false,
        }
    }

    pub fn is_negative(self) -> bool {
        match self {
            Sign::Minus => true,
            _ => false,
        }
    }
}

impl Mul for Sign {
    type Output = Self;

    fn mul(self, oth: Sign) -> Self::Output {
        if self == oth {
            Sign::Plus
        } else {
            Sign::Minus
        }
    }
}

impl Neg for Sign {
    type Output = Self;

    fn neg(self) -> Sign {
        match self {
            Sign::Plus => Sign::Minus,
            Sign::Minus => Sign::Plus,
        }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let format = display::Format::new(f);
        display::format_sign(*self, f, &format)
    }
}

impl From<Sign> for char {
    fn from(sign: Sign) -> char {
        match sign {
            Sign::Plus => '+',
            Sign::Minus => '-',
        }
    }
}

/// Generic implementation of the fraction type
///
/// # Examples
///
/// ```
/// use fraction::GenericFraction;
///
/// type F = GenericFraction<u8>;
///
/// let first = F::new (1u8, 2u8);
/// let second = F::new (2u8, 8u8);
///
/// assert_eq! (first + second, F::new (3u8, 4u8));
/// ```
///
///
/// Since GenericFraction keeps its sign explicitly and independently of the numerics,
/// it is not recommended to use signed types, although it's completely valid with the cost of target type capacity.
///
/// ```
/// use fraction::GenericFraction;
///
/// type F = GenericFraction<i8>;
///
/// let first = F::new (1, 2);
/// let second = F::new (2, 8);
///
/// assert_eq! (first + second, F::new (3, 4));
/// ```
#[derive(Clone, Debug)]
#[cfg_attr(feature = "with-serde-support", derive(Serialize, Deserialize))]
pub enum GenericFraction<T>
where
    T: Clone + Integer,
{
    Rational(Sign, Ratio<T>),
    Infinity(Sign),
    NaN,
}

/// Copy semantics to be applied for the target type, but only if T also has it.
impl<T> Copy for GenericFraction<T> where T: Copy + Integer {}

impl<T> GenericFraction<T>
where
    T: Clone + Integer,
{
    /// Constructs a new fraction with the specified numerator and denominator
    /// Handles gracefully signed integers even if the storage type is unsigned and vise versa
    /// The arguments can be of any integer types imlementing the necessary traits
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::{GenericFraction, Sign};
    /// type F = GenericFraction<u16>;
    ///
    /// let f12 = F::new_generic(Sign::Plus, 1i8, 2u8).unwrap();
    /// let f34 = F::new_generic(Sign::Plus, 3i16, 4u32).unwrap();
    /// let f56 = F::new_generic(Sign::Plus, 5i64, 6u128).unwrap();
    /// let f78 = F::new_generic(Sign::Plus, 7usize, 8isize).unwrap();
    ///
    /// assert_eq! ((*f12.numer().unwrap(), *f12.denom().unwrap()), (1u16, 2u16));
    /// assert_eq! ((*f34.numer().unwrap(), *f34.denom().unwrap()), (3u16, 4u16));
    /// assert_eq! ((*f56.numer().unwrap(), *f56.denom().unwrap()), (5u16, 6u16));
    /// assert_eq! ((*f78.numer().unwrap(), *f78.denom().unwrap()), (7u16, 8u16));
    /// ````
    pub fn new_generic<N, D>(sign: Sign, num: N, den: D) -> Option<GenericFraction<T>>
    where
        N: GenericInteger + PartialOrd,
        D: GenericInteger + PartialOrd,
        T: GenericInteger,
    {
        let (ns, num): (Sign, T) = read_generic_integer(num)?;
        let (ds, den): (Sign, T) = read_generic_integer(den)?;

        let sign = ns * ds * sign;

        Some(Self::_new(sign, num, den))
    }

    fn _new<N, D>(sign: Sign, num: N, den: D) -> GenericFraction<T>
    where
        N: Into<T>,
        D: Into<T>,
    {
        let num: T = num.into();
        let den: T = den.into();

        if den.is_zero() {
            if num.is_zero() {
                GenericFraction::NaN
            } else {
                GenericFraction::Infinity(sign)
            }
        } else {
            GenericFraction::Rational(sign, Ratio::new(num, den))
        }
    }

    /// Constructs a new fraction with the specified numerator and denominator
    ///
    /// The arguments must me either of `T` type, or implement `Into<T>` trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u16>;
    ///
    /// let _f = F::new(1u8, 2u16);
    /// ```
    pub fn new<N, D>(num: N, den: D) -> GenericFraction<T>
    where
        N: Into<T>,
        D: Into<T>,
    {
        Self::_new(Sign::Plus, num, den)
    }

    /// Constructs a new negative fraction with the specified numerator and denominator
    ///
    /// The arguments must be either of `T` type, or implement `Into<T>` trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u16>;
    ///
    /// let _f = F::new_neg (1u8, 2u16);
    /// ```
    pub fn new_neg<N, D>(num: N, den: D) -> GenericFraction<T>
    where
        N: Into<T>,
        D: Into<T>,
    {
        Self::_new(Sign::Minus, num, den)
    }

    /// Constructs a new fraction without types casting, checking for denom == 0 and reducing numbers.
    ///
    /// You must be careful with this function because all the other functionality parts rely on the
    /// numbers to be reduced. That said, in the normal case 2/4 has to be reduced to 1/2, but it will not
    /// happen with new_raw.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let _f = F::new_raw (1u8, 2u8);
    /// ```
    pub fn new_raw(num: T, den: T) -> GenericFraction<T> {
        GenericFraction::Rational(Sign::Plus, Ratio::new_raw(num, den))
    }

    /// The same as [fn new_raw](enum.GenericFraction.html#method.new_raw), but produces negative fractions.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let _f = F::new_raw_neg (1u8, 2u8);
    /// ```
    pub fn new_raw_neg(num: T, den: T) -> GenericFraction<T> {
        GenericFraction::Rational(Sign::Minus, Ratio::new_raw(num, den))
    }

    /// Returns a reference to the numerator value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let fra = F::new (5u8, 6u8);
    /// assert_eq! (5, *fra.numer ().unwrap ());
    /// ```
    pub fn numer(&self) -> Option<&T> {
        match *self {
            GenericFraction::Rational(_, ref r) => Some(r.numer()),
            _ => None,
        }
    }

    /// Returns a reference to the denominator value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let fra = F::new (5u8, 6u8);
    /// assert_eq! (6, *fra.denom ().unwrap ());
    /// ```
    pub fn denom(&self) -> Option<&T> {
        match *self {
            GenericFraction::Rational(_, ref r) => Some(r.denom()),
            _ => None,
        }
    }

    /// Returns a reference to the sign value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::{ GenericFraction, Sign };
    /// type F = GenericFraction<u8>;
    ///
    ///
    /// let fra = F::new (5u8, 6u8);
    /// assert_eq! (Sign::Plus, fra.sign ().unwrap ());
    ///
    /// let fra = F::new_neg (5u8, 6u8);
    /// assert_eq! (Sign::Minus, fra.sign ().unwrap ());
    ///
    ///
    /// let fra = F::infinity ();
    /// assert_eq! (Sign::Plus, fra.sign ().unwrap ());
    ///
    /// let fra = F::neg_infinity ();
    /// assert_eq! (Sign::Minus, fra.sign ().unwrap ());
    ///
    ///
    /// let fra = F::nan ();
    /// assert_eq! (None, fra.sign ());
    /// ```
    pub fn sign(&self) -> Option<Sign> {
        match self {
            GenericFraction::Rational(s, _) => Some(*s),
            GenericFraction::Infinity(s) => Some(*s),
            _ => None,
        }
    }

    /// Generates a GenericFraction<T> from GenericFraction<F>
    /// where T: From<F>
    ///
    /// ```
    /// use fraction::{ Fraction, GenericFraction };
    /// type F8 = GenericFraction<u8>;
    ///
    /// let fra8 = F8::new (5u8, 6u8);
    /// assert_eq! (Fraction::new (5u64, 6u64), Fraction::from_fraction(fra8));
    /// ```
    pub fn from_fraction<F>(from: GenericFraction<F>) -> GenericFraction<T>
    where
        T: From<F>,
        F: Clone + Integer,
    {
        match from {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(sign) => GenericFraction::Infinity(sign),
            GenericFraction::Rational(sign, ratio) => {
                let (num, den): (F, F) = ratio.into();
                GenericFraction::Rational(sign, Ratio::new_raw(T::from(num), T::from(den)))
            }
        }
    }

    /// Generates a GenericFraction<I> from GenericFraction<T>
    /// where T: Into<I>
    ///
    /// ```
    /// use fraction::{ Fraction, GenericFraction };
    /// type F8 = GenericFraction<u8>;
    ///
    /// let fra8 = F8::new (5u8, 6u8);
    /// assert_eq! (Fraction::new (5u64, 6u64), fra8.into_fraction());
    /// ```
    pub fn into_fraction<I>(self) -> GenericFraction<I>
    where
        T: Into<I>,
        I: Clone + Integer,
    {
        match self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(sign) => GenericFraction::Infinity(sign),
            GenericFraction::Rational(sign, ratio) => {
                let (num, den): (T, T) = ratio.into();
                GenericFraction::Rational(sign, Ratio::new_raw(num.into(), den.into()))
            }
        }
    }

    /// Returns a decimal representation of the fraction
    ///
    /// DEPRECATED! Use `format!("{:.1$}", fraction, precision)` instead
    ///
    /// If you have a fraction "1/2", in decimal it should be "0.5".
    ///
    /// Returns None in case we couldn't write the result into a string,
    /// e.g. not enough RAM.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! ("0.5", &F::new (1u8, 2u8).format_as_decimal (1).unwrap ());
    /// assert_eq! ("0.8", &F::new (8u8, 10u8).format_as_decimal (2).unwrap ());
    /// assert_eq! (&F::new (1u8, 3u8).format_as_decimal(32).unwrap(), "0.33333333333333333333333333333333");
    /// ```
    #[deprecated(note = "Use `format!(\"{:.1$}\", fraction, precision)`")]
    pub fn format_as_decimal(&self, precision: usize) -> Option<String>
    where
        T: Clone + GenericInteger,
    {
        return Some(format!("{:.1$}", &self, precision));
    }

    /// Parse a decimal string into a fraction and return the result.
    /// Returns ParseError::OverflowError if there's not enough space in T to represent the decimal (use BigFraction in such a case)
    /// Returns ParseError::ParseIntError if the string contains incorrect junk data (e.g. non-numeric characters).
    /// May return ParseIntError if there is not enough volume in T to read whole part of the number into it.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    ///
    /// let f = Fraction::from_decimal_str ("1.5");
    /// assert_eq! (f, Ok (Fraction::new(3u8, 2u8)));
    /// ```
    pub fn from_decimal_str(src: &str) -> Result<Self, ParseError>
    where
        T: CheckedAdd + CheckedMul,
    {
        let (sign, start) = if src.starts_with('-') {
            (Sign::Minus, 1)
        } else if src.starts_with('+') {
            (Sign::Plus, 1)
        } else {
            (Sign::Plus, 0)
        };

        let dot = src.find('.');
        let who = if dot.is_some() {
            &src[start..dot.unwrap()]
        } else {
            &src[start..]
        };

        let mut num = match T::from_str_radix(who, 10) {
            Err(_) => return Err(ParseError::ParseIntError),
            Ok(value) => value,
        };

        let (fra, len) = if let Some(dot) = dot {
            (T::from_str_radix(&src[dot + 1..], 10), src.len() - dot - 1)
        } else {
            (Ok(T::zero()), 0)
        };

        let fra = match fra {
            Err(_) => return Err(ParseError::ParseIntError),
            Ok(value) => value,
        };

        let mut den = T::one();

        if len > 0 {
            let mut t10 = T::one();
            for _ in 0..9 {
                t10 = if let Some(t10) = t10.checked_add(&den) {
                    t10
                } else {
                    return Err(ParseError::OverflowError);
                };
            }

            for _ in 0..len {
                num = if let Some(num) = num.checked_mul(&t10) {
                    num
                } else {
                    return Err(ParseError::OverflowError);
                };
                den = if let Some(den) = den.checked_mul(&t10) {
                    den
                } else {
                    return Err(ParseError::OverflowError);
                };
            }
        }

        let num = if let Some(num) = num.checked_add(&fra) {
            num
        } else {
            return Err(ParseError::OverflowError);
        };

        Ok(GenericFraction::Rational(sign, Ratio::new(num, den)))
    }
}

impl<T: Bounded + Clone + Integer> Bounded for GenericFraction<T> {
    fn min_value() -> Self {
        let one = T::one();
        let max = T::max_value();

        GenericFraction::Rational(Sign::Minus, Ratio::new(max, one))
    }

    fn max_value() -> Self {
        let one = T::one();
        let max = T::max_value();

        GenericFraction::Rational(Sign::Plus, Ratio::new(max, one))
    }
}

impl<T: Clone + Integer> PartialEq for GenericFraction<T> {
    fn eq(&self, other: &Self) -> bool {
        match *self {
            GenericFraction::NaN => match *other {
                GenericFraction::NaN => true,
                _ => false,
            },
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::Infinity(osign) => sign == osign,
                _ => false,
            },
            GenericFraction::Rational(ref ls, ref l) => match *other {
                GenericFraction::Rational(ref rs, ref r) => {
                    if ls == rs {
                        l.eq(r)
                    } else {
                        l.is_zero() && r.is_zero()
                    }
                }
                _ => false,
            },
        }
    }
}

impl<T: Clone + Integer + Hash> Hash for GenericFraction<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            GenericFraction::NaN => state.write_u8(0u8),
            GenericFraction::Infinity(sign) => {
                if let Sign::Plus = sign {
                    state.write_u8(1u8)
                } else {
                    state.write_u8(2u8)
                }
            }
            GenericFraction::Rational(sign, ratio) => {
                if ratio.is_zero() {
                    state.write_u8(3u8);
                } else if let Sign::Plus = sign {
                    state.write_u8(3u8);
                } else {
                    state.write_u8(4u8);
                }

                ratio.hash(state);
            }
        }
    }
}

impl<T: Clone + Integer> Eq for GenericFraction<T> {}

impl<T: Clone + Integer> PartialOrd for GenericFraction<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match *self {
            GenericFraction::NaN => None,
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => None,
                GenericFraction::Infinity(osign) => {
                    if sign == osign {
                        Some(Ordering::Equal)
                    } else if sign == Sign::Minus {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    }
                }
                GenericFraction::Rational(_, _) => {
                    if sign == Sign::Plus {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Less)
                    }
                }
            },
            GenericFraction::Rational(ref ls, ref l) => match *other {
                GenericFraction::NaN => None,
                GenericFraction::Infinity(rs) => {
                    if rs == Sign::Plus {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    }
                }
                GenericFraction::Rational(ref rs, ref r) => {
                    if ls == rs {
                        match *ls {
                            Sign::Plus => l.partial_cmp(r),
                            Sign::Minus => r.partial_cmp(l),
                        }
                    } else if l.is_zero() && r.is_zero() {
                        Some(Ordering::Equal)
                    } else if *ls == Sign::Minus {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    }
                }
            },
        }
    }
}

impl<T: Clone + Integer> Neg for GenericFraction<T> {
    type Output = GenericFraction<T>;

    fn neg(self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity(sign) => GenericFraction::Infinity(-sign),
            GenericFraction::Rational(s, r) => {
                if r.is_zero() {
                    GenericFraction::Rational(Sign::Plus, r)
                } else {
                    GenericFraction::Rational(s.neg(), r)
                }
            }
        }
    }
}

impl<'a, T: Clone + Integer> Neg for &'a GenericFraction<T> {
    type Output = GenericFraction<T>;

    fn neg(self) -> Self::Output {
        match *self {
            GenericFraction::NaN => GenericFraction::nan(),
            GenericFraction::Infinity(sign) => GenericFraction::Infinity(-sign),
            GenericFraction::Rational(s, ref r) => {
                if r.is_zero() {
                    GenericFraction::Rational(Sign::Plus, r.clone())
                } else {
                    GenericFraction::Rational(-s, r.clone())
                }
            }
        }
    }
}

impl<T: Clone + Integer> Add for GenericFraction<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity(sign) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Rational(_, _) => self,
                GenericFraction::Infinity(osign) => {
                    if sign != osign {
                        GenericFraction::NaN
                    } else {
                        self
                    }
                }
            },
            GenericFraction::Rational(ls, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(_) => other,
                GenericFraction::Rational(rs, r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l.add(r))
                    } else if ls == Sign::Plus {
                        if l < r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l.sub(r))
                        }
                    } else if rs == Sign::Plus {
                        if r < l {
                            GenericFraction::Rational(Sign::Minus, l.sub(r))
                        } else {
                            GenericFraction::Rational(Sign::Plus, r.sub(l))
                        }
                    } else {
                        GenericFraction::Rational(Sign::Minus, l.add(r))
                    }
                }
            },
        }
    }
}

impl<'a, T> Add for &'a GenericFraction<T>
where
    T: Clone + Integer,
{
    type Output = GenericFraction<T>;

    fn add(self, other: Self) -> GenericFraction<T> {
        match *self {
            GenericFraction::NaN => self.clone(),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Rational(_, _) => self.clone(),
                GenericFraction::Infinity(osign) => {
                    if sign != osign {
                        GenericFraction::NaN
                    } else {
                        self.clone()
                    }
                }
            },
            GenericFraction::Rational(ls, ref l) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(_) => other.clone(),
                GenericFraction::Rational(rs, ref r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l.add(r))
                    } else if ls == Sign::Plus {
                        if l < r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l.sub(r))
                        }
                    } else if rs == Sign::Plus {
                        if r < l {
                            GenericFraction::Rational(Sign::Minus, l.sub(r))
                        } else {
                            GenericFraction::Rational(Sign::Plus, r.sub(l))
                        }
                    } else {
                        GenericFraction::Rational(Sign::Minus, l.add(r))
                    }
                }
            },
        }
    }
}

impl<T> CheckedAdd for GenericFraction<T>
where
    T: Clone + Integer + CheckedAdd + CheckedSub + CheckedMul,
{
    fn checked_add(&self, other: &Self) -> Option<GenericFraction<T>> {
        match *self {
            GenericFraction::NaN => Some(self.clone()),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Rational(_, _) => Some(self.clone()),
                GenericFraction::Infinity(osign) => {
                    if sign != osign {
                        Some(GenericFraction::NaN)
                    } else {
                        Some(self.clone())
                    }
                }
            },
            GenericFraction::Rational(ls, ref l) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(_) => Some(other.clone()),
                GenericFraction::Rational(rs, ref r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        l.checked_add(r)
                            .map(|value| GenericFraction::Rational(Sign::Plus, value))
                    } else if ls == Sign::Plus {
                        if l < r {
                            r.checked_sub(l)
                                .map(|value| GenericFraction::Rational(Sign::Minus, value))
                        } else {
                            l.checked_sub(r)
                                .map(|value| GenericFraction::Rational(Sign::Plus, value))
                        }
                    } else if rs == Sign::Plus {
                        if r < l {
                            l.checked_sub(r)
                                .map(|value| GenericFraction::Rational(Sign::Minus, value))
                        } else {
                            r.checked_sub(l)
                                .map(|value| GenericFraction::Rational(Sign::Plus, value))
                        }
                    } else {
                        l.checked_add(r)
                            .map(|value| GenericFraction::Rational(Sign::Minus, value))
                    }
                }
            },
        }
    }
}

impl<T: Clone + Integer> AddAssign for GenericFraction<T> {
    fn add_assign(&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Rational(_, _) => GenericFraction::Infinity(ls),
                GenericFraction::Infinity(rs) => {
                    if ls != rs {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(ls)
                    }
                }
            },
            GenericFraction::Rational(ls, ref mut l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(_) => other,
                GenericFraction::Rational(rs, r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if ls == Sign::Plus && rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l_.add(r))
                    } else if ls == Sign::Plus {
                        if l_ < r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l_))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l_.sub(r))
                        }
                    } else if rs == Sign::Plus {
                        if r < l_ {
                            GenericFraction::Rational(Sign::Minus, l_.sub(r))
                        } else {
                            GenericFraction::Rational(Sign::Plus, r.sub(l_))
                        }
                    } else {
                        GenericFraction::Rational(Sign::Minus, l_.add(r))
                    }
                }
            },
        };
    }
}

impl<'a, T> AddAssign<&'a GenericFraction<T>> for GenericFraction<T>
where
    T: Clone + Integer,
{
    fn add_assign(&mut self, other: &'a Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Rational(_, _) => GenericFraction::Infinity(ls),
                GenericFraction::Infinity(rs) => {
                    if ls != rs {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(ls)
                    }
                }
            },
            GenericFraction::Rational(ls, ref mut l) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(_) => other.clone(),
                GenericFraction::Rational(rs, ref r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if ls == Sign::Plus && rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l_.add(r))
                    } else if ls == Sign::Plus {
                        if l_ < *r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l_))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l_.sub(r))
                        }
                    } else if rs == Sign::Plus {
                        if *r < l_ {
                            GenericFraction::Rational(Sign::Minus, l_.sub(r))
                        } else {
                            GenericFraction::Rational(Sign::Plus, r.sub(l_))
                        }
                    } else {
                        GenericFraction::Rational(Sign::Minus, l_.add(r))
                    }
                }
            },
        };
    }
}

impl<T: Clone + Integer> Sub for GenericFraction<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity(sign) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(osign) => {
                    if sign == osign {
                        GenericFraction::NaN
                    } else {
                        self
                    }
                }
                GenericFraction::Rational(_, _) => self,
            },
            GenericFraction::Rational(ls, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(sign) => GenericFraction::Infinity(-sign),
                GenericFraction::Rational(rs, r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l < r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l.sub(r))
                        }
                    } else if ls == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l.add(r))
                    } else if rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Minus, l.add(r))
                    } else {
                        if l < r {
                            GenericFraction::Rational(Sign::Plus, r.sub(l))
                        } else {
                            GenericFraction::Rational(Sign::Minus, l.sub(r))
                        }
                    }
                }
            },
        }
    }
}

impl<'a, T> Sub for &'a GenericFraction<T>
where
    T: Clone + Integer,
{
    type Output = GenericFraction<T>;

    fn sub(self, other: Self) -> GenericFraction<T> {
        match *self {
            GenericFraction::NaN => self.clone(),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(osign) => {
                    if sign == osign {
                        GenericFraction::NaN
                    } else {
                        self.clone()
                    }
                }
                GenericFraction::Rational(_, _) => self.clone(),
            },
            GenericFraction::Rational(ls, ref l) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(sign) => GenericFraction::Infinity(-sign),
                GenericFraction::Rational(rs, ref r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l < r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l.sub(r))
                        }
                    } else if ls == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l.add(r))
                    } else if rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Minus, l.add(r))
                    } else {
                        if l < r {
                            GenericFraction::Rational(Sign::Plus, r.sub(l))
                        } else {
                            GenericFraction::Rational(Sign::Minus, l.sub(r))
                        }
                    }
                }
            },
        }
    }
}

impl<T> CheckedSub for GenericFraction<T>
where
    T: Clone + Integer + CheckedAdd + CheckedSub + CheckedMul,
{
    fn checked_sub(&self, other: &Self) -> Option<GenericFraction<T>> {
        match *self {
            GenericFraction::NaN => Some(self.clone()),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(osign) => {
                    if sign == osign {
                        Some(GenericFraction::NaN)
                    } else {
                        Some(self.clone())
                    }
                }
                GenericFraction::Rational(_, _) => Some(self.clone()),
            },
            GenericFraction::Rational(ls, ref l) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(sign) => Some(GenericFraction::Infinity(-sign)),
                GenericFraction::Rational(rs, ref r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l < r {
                            r.checked_sub(l)
                                .map(|value| GenericFraction::Rational(Sign::Minus, value))
                        } else {
                            l.checked_sub(r)
                                .map(|value| GenericFraction::Rational(Sign::Plus, value))
                        }
                    } else if ls == Sign::Plus {
                        l.checked_add(r)
                            .map(|value| GenericFraction::Rational(Sign::Plus, value))
                    } else if rs == Sign::Plus {
                        l.checked_add(r)
                            .map(|value| GenericFraction::Rational(Sign::Minus, value))
                    } else {
                        if l < r {
                            r.checked_sub(l)
                                .map(|value| GenericFraction::Rational(Sign::Plus, value))
                        } else {
                            l.checked_sub(r)
                                .map(|value| GenericFraction::Rational(Sign::Minus, value))
                        }
                    }
                }
            },
        }
    }
}

impl<T: Clone + Integer> SubAssign for GenericFraction<T> {
    fn sub_assign(&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(rs) => {
                    if ls == rs {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(ls)
                    }
                }
                GenericFraction::Rational(_, _) => GenericFraction::Infinity(ls),
            },
            GenericFraction::Rational(ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(s) => GenericFraction::Infinity(-s),
                GenericFraction::Rational(rs, r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l_ < r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l_))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l_.sub(r))
                        }
                    } else if ls == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l_.add(r))
                    } else if rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Minus, l_.add(r))
                    } else {
                        if l_ < r {
                            GenericFraction::Rational(Sign::Plus, r.sub(l_))
                        } else {
                            GenericFraction::Rational(Sign::Minus, l_.sub(r))
                        }
                    }
                }
            },
        };
    }
}

impl<'a, T> SubAssign<&'a GenericFraction<T>> for GenericFraction<T>
where
    T: Clone + Integer,
{
    fn sub_assign(&mut self, other: &'a Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(rs) => {
                    if ls == rs {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(ls)
                    }
                }
                GenericFraction::Rational(_, _) => GenericFraction::Infinity(ls),
            },
            GenericFraction::Rational(ls, ref mut l) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(s) => GenericFraction::Infinity(-s),
                GenericFraction::Rational(rs, ref r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l_ < *r {
                            GenericFraction::Rational(Sign::Minus, r.sub(l_))
                        } else {
                            GenericFraction::Rational(Sign::Plus, l_.sub(r))
                        }
                    } else if ls == Sign::Plus {
                        GenericFraction::Rational(Sign::Plus, l_.add(r))
                    } else if rs == Sign::Plus {
                        GenericFraction::Rational(Sign::Minus, l_.add(r))
                    } else {
                        if l_ < *r {
                            GenericFraction::Rational(Sign::Plus, r.sub(l_))
                        } else {
                            GenericFraction::Rational(Sign::Minus, l_.sub(r))
                        }
                    }
                }
            },
        };
    }
}

impl<T: Clone + Integer> Mul for GenericFraction<T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity(sign) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(osign) => GenericFraction::Infinity(if sign == osign {
                    Sign::Plus
                } else {
                    Sign::Minus
                }),
                GenericFraction::Rational(osign, l) => {
                    if l.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        })
                    }
                }
            },
            GenericFraction::Rational(sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(osign) => {
                    if l.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        })
                    }
                }
                GenericFraction::Rational(osign, r) => {
                    let s = if l.is_zero() || r.is_zero() {
                        Sign::Plus
                    } else if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };
                    GenericFraction::Rational(s, l.mul(r))
                }
            },
        }
    }
}

impl<'a, T> Mul for &'a GenericFraction<T>
where
    T: Clone + Integer,
{
    type Output = GenericFraction<T>;

    fn mul(self, other: Self) -> GenericFraction<T> {
        match *self {
            GenericFraction::NaN => self.clone(),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(osign) => GenericFraction::Infinity(if sign == osign {
                    Sign::Plus
                } else {
                    Sign::Minus
                }),
                GenericFraction::Rational(osign, ref l) => {
                    if l.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        })
                    }
                }
            },
            GenericFraction::Rational(sign, ref l) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(osign) => {
                    if l.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        })
                    }
                }
                GenericFraction::Rational(osign, ref r) => {
                    let s = if l.is_zero() || r.is_zero() {
                        Sign::Plus
                    } else if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };
                    GenericFraction::Rational(s, l.mul(r))
                }
            },
        }
    }
}

impl<T> CheckedMul for GenericFraction<T>
where
    T: Clone + Integer + CheckedMul,
{
    fn checked_mul(&self, other: &Self) -> Option<GenericFraction<T>> {
        match *self {
            GenericFraction::NaN => Some(self.clone()),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(osign) => {
                    Some(GenericFraction::Infinity(if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    }))
                }
                GenericFraction::Rational(osign, ref l) => {
                    if l.is_zero() {
                        Some(GenericFraction::NaN)
                    } else {
                        Some(GenericFraction::Infinity(if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        }))
                    }
                }
            },
            GenericFraction::Rational(sign, ref l) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(osign) => {
                    if l.is_zero() {
                        Some(GenericFraction::NaN)
                    } else {
                        Some(GenericFraction::Infinity(if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        }))
                    }
                }
                GenericFraction::Rational(osign, ref r) => l.checked_mul(r).map(|value| {
                    GenericFraction::Rational(
                        if l.is_zero() || r.is_zero() {
                            Sign::Plus
                        } else if sign == osign {
                            Sign::Plus
                        } else {
                            Sign::Minus
                        },
                        value,
                    )
                }),
            },
        }
    }
}

impl<T: Clone + Integer> MulAssign for GenericFraction<T> {
    fn mul_assign(&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(rs) => {
                    GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                }
                GenericFraction::Rational(rs, r) => {
                    if r.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
            },
            GenericFraction::Rational(ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(rs) => {
                    if l.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
                GenericFraction::Rational(rs, r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    let s = if l_.is_zero() || r.is_zero() {
                        Sign::Plus
                    } else if ls == rs {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };

                    GenericFraction::Rational(s, l_.mul(r))
                }
            },
        };
    }
}

impl<'a, T> MulAssign<&'a GenericFraction<T>> for GenericFraction<T>
where
    T: Clone + Integer,
{
    fn mul_assign(&mut self, other: &'a Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(rs) => {
                    GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                }
                GenericFraction::Rational(rs, ref r) => {
                    if r.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
            },
            GenericFraction::Rational(ls, ref mut l) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(rs) => {
                    if l.is_zero() {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
                GenericFraction::Rational(rs, ref r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    let s = if l_.is_zero() || r.is_zero() {
                        Sign::Plus
                    } else if ls == rs {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };

                    GenericFraction::Rational(s, l_.mul(r))
                }
            },
        };
    }
}

impl<T: Clone + Integer> Div for GenericFraction<T> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity(sign) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(osign, _) => {
                    GenericFraction::Infinity(if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    })
                }
            },
            GenericFraction::Rational(sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(_) => {
                    GenericFraction::Rational(Sign::Plus, Ratio::zero())
                }
                GenericFraction::Rational(osign, r) => {
                    if l.is_zero() && r.is_zero() {
                        GenericFraction::NaN
                    } else if r.is_zero() {
                        GenericFraction::Infinity(sign)
                    } else if l.is_zero() {
                        GenericFraction::Rational(Sign::Plus, l)
                    } else {
                        GenericFraction::Rational(
                            if sign == osign {
                                Sign::Plus
                            } else {
                                Sign::Minus
                            },
                            l.div(r),
                        )
                    }
                }
            },
        }
    }
}

impl<'a, T> Div for &'a GenericFraction<T>
where
    T: Clone + Integer,
{
    type Output = GenericFraction<T>;

    fn div(self, other: Self) -> GenericFraction<T> {
        match *self {
            GenericFraction::NaN => self.clone(),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(osign, _) => {
                    GenericFraction::Infinity(if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    })
                }
            },
            GenericFraction::Rational(sign, ref l) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(_) => {
                    GenericFraction::Rational(Sign::Plus, Ratio::zero())
                }
                GenericFraction::Rational(osign, ref r) => {
                    if l.is_zero() && r.is_zero() {
                        GenericFraction::NaN
                    } else if r.is_zero() {
                        GenericFraction::Infinity(sign)
                    } else if l.is_zero() {
                        GenericFraction::Rational(Sign::Plus, l.clone())
                    } else {
                        GenericFraction::Rational(
                            if sign == osign {
                                Sign::Plus
                            } else {
                                Sign::Minus
                            },
                            l.div(r),
                        )
                    }
                }
            },
        }
    }
}

impl<T> CheckedDiv for GenericFraction<T>
where
    T: Clone + Integer + CheckedDiv + CheckedMul,
{
    fn checked_div(&self, other: &Self) -> Option<GenericFraction<T>> {
        match *self {
            GenericFraction::NaN => Some(self.clone()),
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(_) => Some(GenericFraction::NaN),
                GenericFraction::Rational(osign, _) => {
                    Some(GenericFraction::Infinity(if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    }))
                }
            },
            GenericFraction::Rational(sign, ref l) => match *other {
                GenericFraction::NaN => Some(other.clone()),
                GenericFraction::Infinity(_) => {
                    Some(GenericFraction::Rational(Sign::Plus, Ratio::zero()))
                }
                GenericFraction::Rational(osign, ref r) => {
                    if l.is_zero() && r.is_zero() {
                        Some(GenericFraction::NaN)
                    } else if r.is_zero() {
                        Some(GenericFraction::Infinity(sign))
                    } else if l.is_zero() {
                        Some(GenericFraction::Rational(Sign::Plus, l.clone()))
                    } else {
                        l.checked_div(r).map(|value| {
                            GenericFraction::Rational(
                                if sign == osign {
                                    Sign::Plus
                                } else {
                                    Sign::Minus
                                },
                                value,
                            )
                        })
                    }
                }
            },
        }
    }
}

impl<T: Clone + Integer> DivAssign for GenericFraction<T> {
    fn div_assign(&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(rs, _) => {
                    GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                }
            },
            GenericFraction::Rational(ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => {
                    GenericFraction::Rational(Sign::Plus, Ratio::zero())
                }
                GenericFraction::Rational(rs, r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if l_.is_zero() && r.is_zero() {
                        GenericFraction::NaN
                    } else if r.is_zero() {
                        GenericFraction::Infinity(ls)
                    } else if l_.is_zero() {
                        GenericFraction::Rational(Sign::Plus, l_)
                    } else {
                        GenericFraction::Rational(
                            if ls == rs { Sign::Plus } else { Sign::Minus },
                            l_.div(r),
                        )
                    }
                }
            },
        };
    }
}

impl<'a, T> DivAssign<&'a GenericFraction<T>> for GenericFraction<T>
where
    T: Clone + Integer,
{
    fn div_assign(&mut self, other: &'a Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(ls) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(rs, _) => {
                    GenericFraction::Infinity(if ls == rs { Sign::Plus } else { Sign::Minus })
                }
            },
            GenericFraction::Rational(ls, ref mut l) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => {
                    GenericFraction::Rational(Sign::Plus, Ratio::zero())
                }
                GenericFraction::Rational(rs, ref r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if l_.is_zero() && r.is_zero() {
                        GenericFraction::NaN
                    } else if r.is_zero() {
                        GenericFraction::Infinity(ls)
                    } else if l_.is_zero() {
                        GenericFraction::Rational(Sign::Plus, l_)
                    } else {
                        GenericFraction::Rational(
                            if ls == rs { Sign::Plus } else { Sign::Minus },
                            l_.div(r),
                        )
                    }
                }
            },
        };
    }
}

impl<T: Clone + Integer> Rem for GenericFraction<T> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity(_) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(_, _) => GenericFraction::NaN,
            },
            GenericFraction::Rational(sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity(_) => GenericFraction::Rational(sign, l),
                GenericFraction::Rational(_, r) => {
                    if r.is_zero() {
                        GenericFraction::NaN
                    } else if l == r {
                        GenericFraction::Rational(Sign::Plus, Ratio::zero())
                    } else {
                        GenericFraction::Rational(sign, l % r)
                    }
                }
            },
        }
    }
}

impl<'a, T> Rem for &'a GenericFraction<T>
where
    T: Clone + Integer,
{
    type Output = GenericFraction<T>;

    fn rem(self, other: Self) -> GenericFraction<T> {
        match *self {
            GenericFraction::NaN => self.clone(),
            GenericFraction::Infinity(_) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(_, _) => GenericFraction::NaN,
            },
            GenericFraction::Rational(sign, ref l) => match *other {
                GenericFraction::NaN => other.clone(),
                GenericFraction::Infinity(_) => GenericFraction::Rational(sign, l.clone()),
                GenericFraction::Rational(_, ref r) => {
                    if r.is_zero() {
                        GenericFraction::NaN
                    } else if l == r {
                        GenericFraction::Rational(Sign::Plus, Ratio::zero())
                    } else {
                        GenericFraction::Rational(sign, l.rem(r))
                    }
                }
            },
        }
    }
}

impl<T: Clone + Integer> RemAssign for GenericFraction<T> {
    fn rem_assign(&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(_) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(_, _) => GenericFraction::NaN,
            },
            GenericFraction::Rational(ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => GenericFraction::Rational(
                    ls,
                    mem::replace(l, Ratio::new_raw(T::zero(), T::zero())),
                ),
                GenericFraction::Rational(_, r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if r.is_zero() {
                        GenericFraction::NaN
                    } else if l_ == r {
                        GenericFraction::Rational(Sign::Plus, Ratio::zero())
                    } else {
                        GenericFraction::Rational(ls, l_.rem(r))
                    }
                }
            },
        };
    }
}

impl<'a, T> RemAssign<&'a GenericFraction<T>> for GenericFraction<T>
where
    T: Clone + Integer,
{
    fn rem_assign(&mut self, other: &'a Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(_) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => GenericFraction::NaN,
                GenericFraction::Rational(_, _) => GenericFraction::NaN,
            },
            GenericFraction::Rational(ls, ref mut l) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(_) => GenericFraction::Rational(
                    ls,
                    mem::replace(l, Ratio::new_raw(T::zero(), T::zero())),
                ),
                GenericFraction::Rational(_, ref r) => {
                    let l_ = mem::replace(l, Ratio::new_raw(T::zero(), T::zero()));

                    if r.is_zero() {
                        GenericFraction::NaN
                    } else if l_ == *r {
                        GenericFraction::Rational(Sign::Plus, Ratio::zero())
                    } else {
                        GenericFraction::Rational(ls, l_.rem(r))
                    }
                }
            },
        };
    }
}

impl<T: Clone + Integer> Sum for GenericFraction<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(GenericFraction::<T>::zero(), Add::add)
    }
}

impl<'a, T: 'a + Clone + Integer> Sum<&'a GenericFraction<T>> for GenericFraction<T> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(GenericFraction::<T>::zero(), |ref s, x| Add::add(s, x))
    }
}

impl<T: Clone + Integer> Product for GenericFraction<T> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(GenericFraction::<T>::one(), Mul::mul)
    }
}

impl<'a, T: 'a + Clone + Integer> Product<&'a GenericFraction<T>> for GenericFraction<T> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(GenericFraction::<T>::one(), |ref s, x| Mul::mul(s, x))
    }
}

impl<T: Clone + Integer> Zero for GenericFraction<T> {
    fn zero() -> Self {
        GenericFraction::Rational(Sign::Plus, Ratio::zero())
    }

    fn is_zero(&self) -> bool {
        match *self {
            GenericFraction::Rational(_, ref r) => r.is_zero(),
            _ => false,
        }
    }
}

impl<T: Clone + Integer> One for GenericFraction<T> {
    fn one() -> Self {
        GenericFraction::Rational(Sign::Plus, Ratio::one())
    }
}

impl<T: Clone + Integer> Num for GenericFraction<T> {
    type FromStrRadixErr = ParseRatioError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        if str.starts_with('-') {
            Ratio::from_str_radix(&str[1..], radix)
                .and_then(|ratio| Ok(GenericFraction::Rational(Sign::Minus, ratio)))
        } else if str.starts_with('+') {
            Ratio::from_str_radix(&str[1..], radix)
                .and_then(|ratio| Ok(GenericFraction::Rational(Sign::Plus, ratio)))
        } else {
            Ratio::from_str_radix(str, radix)
                .and_then(|ratio| Ok(GenericFraction::Rational(Sign::Plus, ratio)))
        }
    }
}

impl<T: Clone + Integer> Signed for GenericFraction<T> {
    fn abs(&self) -> Self {
        GenericFraction::abs(self)
    }

    fn abs_sub(&self, other: &Self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(sign) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(osign) => {
                    if sign == Sign::Minus {
                        GenericFraction::zero()
                    } else {
                        if osign == Sign::Plus {
                            GenericFraction::zero()
                        } else {
                            GenericFraction::Infinity(Sign::Plus)
                        }
                    }
                }
                GenericFraction::Rational(_, _) => {
                    if sign == Sign::Plus {
                        GenericFraction::Infinity(sign)
                    } else {
                        GenericFraction::zero()
                    }
                }
            },
            GenericFraction::Rational(sign, ref l) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity(osign) => {
                    if osign == Sign::Plus {
                        GenericFraction::zero()
                    } else {
                        if sign == Sign::Minus {
                            GenericFraction::Infinity(Sign::Minus)
                        } else {
                            GenericFraction::Infinity(Sign::Plus)
                        }
                    }
                }
                GenericFraction::Rational(_, ref r) => {
                    if l < r {
                        GenericFraction::Rational(Sign::Plus, r - l)
                    } else {
                        GenericFraction::Rational(Sign::Plus, l - r)
                    }
                }
            },
        }
    }

    fn signum(&self) -> Self {
        GenericFraction::signum(self)
    }

    fn is_positive(&self) -> bool {
        GenericFraction::is_sign_positive(self)
    }

    fn is_negative(&self) -> bool {
        GenericFraction::is_sign_negative(self)
    }
}

impl<T: Clone + Integer + PartialEq + ToPrimitive> ToPrimitive for GenericFraction<T> {
    fn to_i64(&self) -> Option<i64> {
        match *self {
            GenericFraction::NaN => None,
            GenericFraction::Infinity(_) => None,
            GenericFraction::Rational(sign, ref r) if *r.denom() == T::one() => {
                if let Some(n) = r.numer().to_i64() {
                    if sign == Sign::Minus {
                        Some(-n)
                    } else {
                        Some(n)
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_u64(&self) -> Option<u64> {
        match *self {
            GenericFraction::NaN => None,
            GenericFraction::Infinity(_) => None,
            GenericFraction::Rational(sign, ref r) if *r.denom() == T::one() => {
                if sign == Sign::Minus {
                    None
                } else {
                    r.numer().to_u64()
                }
            }
            _ => None,
        }
    }

    fn to_f64(&self) -> Option<f64> {
        match *self {
            GenericFraction::NaN => Some(f64::NAN),
            GenericFraction::Infinity(sign) => Some(if sign == Sign::Minus {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            }),
            GenericFraction::Rational(sign, ref r) => r
                .numer()
                .to_f64()
                .and_then(|n| r.denom().to_f64().map(|d| n / d))
                .map(|x| if sign == Sign::Minus { -x } else { x }),
        }
    }
}

impl<T: Clone + Integer> GenericFraction<T> {
    /// Returns NaN value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::nan (), F::new (0, 0));
    /// ```
    pub fn nan() -> Self {
        GenericFraction::NaN
    }

    /// Returns positive Infinity value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::infinity (), F::new (1, 0));
    /// ```
    pub fn infinity() -> Self {
        GenericFraction::Infinity(Sign::Plus)
    }

    /// Returns negative Infinity value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::neg_infinity (), F::new_neg (1, 0));
    /// ```
    pub fn neg_infinity() -> Self {
        GenericFraction::Infinity(Sign::Minus)
    }

    /// Returns zero with negative sign
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::neg_zero (), F::new_neg (0, 1));
    /// ```
    pub fn neg_zero() -> Self {
        GenericFraction::Rational(Sign::Minus, Ratio::zero())
    }

    /// Returns minimal value greater than zero
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F8 = GenericFraction<u8>;
    /// type F16 = GenericFraction<u16>;
    ///
    /// assert_eq! (F8::min_positive_value (), F8::new (1u8, 255u8));
    /// assert_eq! (F16::min_positive_value (), F16::new (1u16, 65535u16));
    /// ```
    pub fn min_positive_value() -> Self
    where
        T: Bounded,
    {
        GenericFraction::Rational(Sign::Plus, Ratio::new(T::one(), T::max_value()))
    }

    /// Returns true if the value is NaN
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert! (F::nan ().is_nan ());
    /// assert! (F::new (0, 0).is_nan ());
    /// ```
    pub fn is_nan(&self) -> bool {
        match *self {
            GenericFraction::NaN => true,
            _ => false,
        }
    }

    /// Returns true if the value is Infinity (does not matter positive or negative)
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert! (F::infinity ().is_infinite ());
    /// assert! (F::new (1u8, 0).is_infinite ());
    /// assert! (F::new_neg (1u8, 0).is_infinite ());
    /// ```
    pub fn is_infinite(&self) -> bool {
        match *self {
            GenericFraction::Infinity(_) => true,
            _ => false,
        }
    }

    /// Returns true if the value is not Infinity (does not matter positive or negative)
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert! (! F::infinity ().is_finite ());
    /// assert! (! F::new (1u8, 0).is_finite ());
    /// assert! (! F::new_neg (1u8, 0).is_finite ());
    /// ```
    pub fn is_finite(&self) -> bool {
        match *self {
            GenericFraction::Infinity(_) => false,
            _ => true,
        }
    }

    /// Returns true if the number is neither zero, Infinity or NaN
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert! (! F::nan ().is_normal ());
    /// assert! (! F::infinity ().is_normal ());
    /// assert! (! F::neg_infinity ().is_normal ());
    /// assert! (! F::new (0, 1u8).is_normal ());
    /// assert! (! F::neg_zero ().is_normal ());
    /// ```
    pub fn is_normal(&self) -> bool {
        match *self {
            GenericFraction::Rational(_, ref v) => !v.is_zero(),
            _ => false,
        }
    }

    /// Returns the floating point category of the number
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::FpCategory;
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::nan ().classify (), FpCategory::Nan);
    /// assert_eq! (F::infinity ().classify (), FpCategory::Infinite);
    /// assert_eq! (F::new (0, 1u8).classify (), FpCategory::Zero);
    /// assert_eq! (F::new (1u8, 1u8).classify (), FpCategory::Normal);
    /// ```
    pub fn classify(&self) -> FpCategory {
        match *self {
            GenericFraction::NaN => FpCategory::Nan,
            GenericFraction::Infinity(_) => FpCategory::Infinite,
            GenericFraction::Rational(_, ref v) if v.is_zero() => FpCategory::Zero,
            _ => FpCategory::Normal,
        }
    }

    /// Returns the largest integer less than or equal to the value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (7u8, 5u8).floor (), F::new (5u8, 5u8));
    /// ```
    pub fn floor(&self) -> Self {
        match *self {
            GenericFraction::Rational(s, ref r) => GenericFraction::Rational(s, r.floor()),
            _ => self.clone(),
        }
    }

    /// Returns the smallest integer greater than or equal to the value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (7u8, 5u8).ceil (), F::new (10u8, 5u8));
    /// ```
    pub fn ceil(&self) -> Self {
        match *self {
            GenericFraction::Rational(s, ref r) => GenericFraction::Rational(s, r.ceil()),
            _ => self.clone(),
        }
    }

    /// Returns the nearest integer to the value (.5 goes up)
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (7u8, 5u8).round (), F::new (5u8, 5u8));
    /// assert_eq! (F::new (8u8, 5u8).round (), F::new (10u8, 5u8));
    /// assert_eq! (F::new (3u8, 2u8).round (), F::new (4u8, 2u8));
    /// assert_eq! (F::new (1u8, 2u8).round (), F::new (2u8, 2u8));
    /// ```
    pub fn round(&self) -> Self {
        match *self {
            GenericFraction::Rational(s, ref r) => GenericFraction::Rational(s, r.round()),
            _ => self.clone(),
        }
    }

    /// Returns the integer part of the value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (7u8, 5u8).trunc (), F::new (5u8, 5u8));
    /// assert_eq! (F::new (8u8, 5u8).trunc (), F::new (5u8, 5u8));
    /// ```
    pub fn trunc(&self) -> Self {
        match *self {
            GenericFraction::Rational(s, ref r) => GenericFraction::Rational(s, r.trunc()),
            _ => self.clone(),
        }
    }

    /// Returns the fractional part of a number
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (7u8, 5u8).fract (), F::new (2u8, 5u8));
    /// assert_eq! (F::new (8u8, 5u8).fract (), F::new (3u8, 5u8));
    /// ```
    pub fn fract(&self) -> Self {
        match *self {
            GenericFraction::Rational(s, ref r) => GenericFraction::Rational(s, r.fract()),
            _ => GenericFraction::NaN,
        }
    }

    /// Returns the absolute value of self
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::nan ().abs (), F::nan ());
    /// assert_eq! (F::infinity ().abs (), F::infinity ());
    /// assert_eq! (F::neg_infinity ().abs (), F::infinity ());
    /// assert_eq! (F::new (1u8, 2u8).abs (), F::new (1u8, 2u8));
    /// assert_eq! (F::new_neg (1u8, 2u8).abs (), F::new (1u8, 2u8));
    /// ```
    pub fn abs(&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(_) => GenericFraction::Infinity(Sign::Plus),
            GenericFraction::Rational(_, ref r) => GenericFraction::Rational(Sign::Plus, r.clone()),
        }
    }

    /// Returns a number that represents the sign of self
    ///
    ///  * 1.0 if the number is positive, +0.0 or INFINITY
    ///  * -1.0 if the number is negative, -0.0 or NEG_INFINITY
    ///  * NAN if the number is NAN
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (1u8, 2u8).signum (), F::new (1u8, 1u8));
    /// assert_eq! (F::new (0u8, 1u8).signum (), F::new (1u8, 1u8));
    /// assert_eq! (F::infinity ().signum (), F::new (1u8, 1u8));
    /// assert_eq! (F::new_neg (1u8, 2u8).signum (), F::new_neg (1u8, 1u8));
    /// assert_eq! (F::neg_zero ().signum (), F::new_neg (1u8, 1u8));
    /// assert_eq! (F::neg_infinity ().signum (), F::new_neg (1u8, 1u8));
    /// assert_eq! (F::nan ().signum (), F::nan ());
    /// ```
    pub fn signum(&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(s) => {
                if s == Sign::Plus {
                    GenericFraction::Rational(Sign::Plus, Ratio::new(T::one(), T::one()))
                } else {
                    GenericFraction::Rational(Sign::Minus, Ratio::new(T::one(), T::one()))
                }
            }
            GenericFraction::Rational(s, _) => {
                if s == Sign::Plus {
                    GenericFraction::Rational(Sign::Plus, Ratio::new(T::one(), T::one()))
                } else {
                    GenericFraction::Rational(Sign::Minus, Ratio::new(T::one(), T::one()))
                }
            }
        }
    }

    /// Returns true if the sign is positive
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert! (F::new (1u8, 2u8).is_sign_positive ());
    /// assert! (F::infinity ().is_sign_positive ());
    /// assert! (! F::nan ().is_sign_positive ());
    /// ```
    pub fn is_sign_positive(&self) -> bool {
        match *self {
            GenericFraction::NaN => false,
            GenericFraction::Infinity(sign) => sign == Sign::Plus,
            GenericFraction::Rational(sign, _) => sign == Sign::Plus,
        }
    }

    /// Returns true if the sign is negative
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert! (F::new_neg (1u8, 2u8).is_sign_negative ());
    /// assert! (F::neg_zero ().is_sign_negative ());
    /// assert! (F::neg_infinity ().is_sign_negative ());
    /// assert! (! F::nan ().is_sign_negative ());
    /// ```
    pub fn is_sign_negative(&self) -> bool {
        match *self {
            GenericFraction::NaN => false,
            GenericFraction::Infinity(sign) => sign == Sign::Minus,
            GenericFraction::Rational(sign, _) => sign == Sign::Minus,
        }
    }

    /// self.clone () * a + b
    ///
    /// Added for interface compatibility with float types
    pub fn mul_add(&self, a: Self, b: Self) -> Self {
        self.clone() * a + b
    }

    /// Takes the reciprocal (inverse) of the value (1/x)
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! (F::new (1u8, 2u8).recip (), F::new (2u8, 1u8));
    /// assert_eq! (F::new (0u8, 1u8).recip (), F::infinity ());
    /// assert_eq! (F::infinity ().recip (), F::new (0u8, 1u8));
    /// assert_eq! (F::nan ().recip (), F::nan ());
    /// ```
    pub fn recip(&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity(_) => {
                GenericFraction::Rational(Sign::Plus, Ratio::new(T::zero(), T::one()))
            }
            GenericFraction::Rational(s, ref r) if r.is_zero() => GenericFraction::Infinity(s),
            GenericFraction::Rational(s, ref r) => GenericFraction::Rational(s, r.recip()),
        }
    }

    /* ... Some stuff here that has not been implemented for Ratio<T> ... */
}

impl<T: Clone + GenericInteger> fmt::Display for GenericFraction<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let format = display::Format::new(formatter);
        display::format_fraction(self, formatter, &format)
    }
}

macro_rules! fraction_from_generic_int {
    ( $($F:ty),* ) => {
        $(
        impl<T> From<$F> for GenericFraction<T>
        where
            T: Clone + Integer + GenericInteger + CheckedAdd + CheckedMul + CheckedSub,
            $F: GenericInteger + CheckedAdd + CheckedDiv + CheckedMul + CheckedSub + PartialOrd
        {
            fn from (val: $F) -> GenericFraction<T> {
                if let Some((sign, value)) = read_generic_integer::<T, $F>(val) {
                    GenericFraction::Rational(sign, Ratio::new (value, T::one()))
                } else {
                    GenericFraction::nan()
                }
            }
        }
        )*
    };
}

#[cfg(feature = "with-bigint")]
fraction_from_generic_int!(BigUint, BigInt);

fraction_from_generic_int!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

macro_rules! generic_fraction_from_float {
    ( $($from:ty),*) => {
        $(
        impl<T: Clone + Integer + CheckedAdd + CheckedMul + CheckedSub> From<$from> for GenericFraction<T> {
            fn from (val: $from) -> GenericFraction<T> {
                if val.is_nan () { return GenericFraction::NaN };
                if val.is_infinite () { return GenericFraction::Infinity (if val.is_sign_negative () { Sign::Minus } else { Sign::Plus }) };

                /* TODO: without the String conversion (probably through .to_bits) */
                let src = format! ("{:+}", val);

                Self::from_decimal_str(&src).unwrap_or(GenericFraction::nan())
            }
        }
        )*
    };
}

generic_fraction_from_float!(f32, f64);

impl<T, N, D> From<(N, D)> for GenericFraction<T>
where
    T: Clone + Integer,
    N: fmt::Display,
    D: fmt::Display,
{
    fn from(pair: (N, D)) -> GenericFraction<T> {
        let (num, den) = pair;

        let num = format!("{:+}", num);

        let n_sign = if num.starts_with('-') {
            Sign::Minus
        } else if num.starts_with('+') {
            Sign::Plus
        } else {
            return GenericFraction::NaN;
        };

        let n: Result<T, T::FromStrRadixErr> = T::from_str_radix(&num[1..], 10);

        if n.is_err() {
            return GenericFraction::NaN;
        }

        let den = format!("{:+}", den);

        let d_sign = if den.starts_with('-') {
            Sign::Minus
        } else if den.starts_with('+') {
            Sign::Plus
        } else {
            return GenericFraction::NaN;
        };

        let d: Result<T, T::FromStrRadixErr> = T::from_str_radix(&den[1..], 10);

        if d.is_err() {
            return GenericFraction::NaN;
        }

        GenericFraction::Rational(
            if n_sign == d_sign {
                Sign::Plus
            } else {
                Sign::Minus
            },
            Ratio::new(n.ok().unwrap(), d.ok().unwrap()),
        )
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "with-bigint")]
    use prelude::BigFraction;

    #[cfg(feature = "with-bigint")]
    use super::{BigInt, BigUint};

    use super::{
        super::Fraction, Bounded, FpCategory, GenericFraction, Num, One, ParseError, Sign, Signed,
        ToPrimitive, Zero,
    };

    use super::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};

    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};

    type Frac = GenericFraction<u8>;

    fn hash_it(target: &impl Hash) -> u64 {
        use std::collections::hash_map::DefaultHasher;

        let mut h = DefaultHasher::new();
        target.hash(&mut h);
        h.finish()
    }

    generate_ops_tests! (
        NaN => {Frac::nan()};
        NegInf => {Frac::neg_infinity()};
        PosInf => {Frac::infinity()};
        Zero => {Frac::new(0, 1)};
        Half => {Frac::new(1, 2)};
        One => {Frac::new(1, 1)};
        Two => {Frac::new(2, 1)};
        Three => {Frac::new(3, 1)};
        Four => {Frac::new(4, 1)};
    );

    #[test]
    fn op_ord() {
        let pin = Frac::infinity();
        let nin = Frac::neg_infinity();
        let nil = Frac::zero();

        let a = Frac::new(3, 4);
        let b = Frac::new(5, 7);

        assert!(a > b);
        assert!(a > nil);
        assert!(b > nil);
        assert!(nin < nil);
        assert!(nil < pin);
    }

    #[test]
    fn from_i8() {
        let f = Fraction::from(-2i8);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0i8);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2i8);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_u8() {
        let f = Fraction::from(0u8);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2u8);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(u8::max_value());
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(u8::max_value() as u64, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_i16() {
        let f = Fraction::from(-2i16);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0i16);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2i16);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_u16() {
        let f = Fraction::from(0u16);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2u16);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_i32() {
        let f = Fraction::from(-2i32);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0i32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2i32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_u32() {
        let f = Fraction::from(0u32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2u32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_i64() {
        let f = Fraction::from(-2i64);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0i64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2i64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_u64() {
        let f = Fraction::from(0u64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2u64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_i128() {
        let f = Fraction::from(0i128);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2i128);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(-2i128);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(22460602606i128);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(22460602606, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_u128() {
        let f = Fraction::from(0u128);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2u128);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_isize() {
        let f = Fraction::from(-2isize);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0isize);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2isize);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_usize() {
        let f = Fraction::from(0usize);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(2usize);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(2, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_f32() {
        let f = Fraction::from(0f32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0.01f32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(1, *f.numer().unwrap());
        assert_eq!(100, *f.denom().unwrap());

        let f = Fraction::from(-0.01f32);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(1, *f.numer().unwrap());
        assert_eq!(100, *f.denom().unwrap());

        let f = Fraction::from(16584253f32);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(16584253u64, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn from_f64() {
        let f = Fraction::from(0f64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(0, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());

        let f = Fraction::from(0.01f64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(1, *f.numer().unwrap());
        assert_eq!(100, *f.denom().unwrap());

        let f = Fraction::from(-0.01f64);
        assert_eq!(Sign::Minus, f.sign().unwrap());
        assert_eq!(1, *f.numer().unwrap());
        assert_eq!(100, *f.denom().unwrap());

        let f = Fraction::from(1658425342060f64);
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(1658425342060u64, *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    #[cfg(feature = "with-bigint")]
    fn from_insanity() {
        let number = "2062065394209534095362056240654064520645230645230645230645230645206452064520645203642530940959212130935957";
        let fraction = format!("{}/1", number);
        let f = BigFraction::from_str_radix(&fraction, 10);
        assert!(f.is_ok());
        let f = f.ok().unwrap();
        assert_eq!(
            BigUint::from_str_radix(&number, 10).ok().unwrap(),
            *f.numer().unwrap()
        );
        assert_eq!(BigUint::from(1u8), *f.denom().unwrap());
    }

    #[test]
    #[cfg(feature = "with-bigint")]
    fn from_bigint() {
        let number = BigInt::from(42);
        let frac = BigFraction::from(number);

        assert_eq!(frac, BigFraction::from((42, 1)));

        let number = BigInt::from(-44);
        let frac = BigFraction::from(number);

        assert_eq!(frac, -BigFraction::from((44, 1)));
    }

    #[test]
    #[cfg(feature = "with-bigint")]
    fn from_biguint() {
        let number = BigUint::from(42u32);
        let frac = BigFraction::from(number);

        assert_eq!(frac, BigFraction::from((42, 1)));
    }

    #[test]
    fn from_extremum() {
        type F8 = GenericFraction<u8>;

        let f = F8::from(u8::max_value());
        assert_eq!(Sign::Plus, f.sign().unwrap());
        assert_eq!(u8::max_value(), *f.numer().unwrap());
        assert_eq!(1, *f.denom().unwrap());
    }

    #[test]
    fn hashy() {
        {
            let mut map: HashMap<Fraction, ()> = HashMap::new();

            map.insert(Fraction::from(0.75), ());

            assert!(map.contains_key(&Fraction::new(3u8, 4u8))); // 0.75 == 3/4
            assert!(map.contains_key(&Fraction::new(6u16, 8u16))); // 0.75 == 6/8
            assert!(map.contains_key(&Fraction::new(12u32, 16u32))); // 0.75 == 12/16
            assert!(map.contains_key(&Fraction::new(24u64, 32u64))); // 0.75 == 24/32
            assert!(map.contains_key(&Fraction::new(48u8, 64u16))); // 0.75 == 48/64

            assert!(map.contains_key(&Fraction::from((3i8, 4i8))));
            assert!(map.contains_key(&Fraction::from((6i16, 8i16))));
            assert!(map.contains_key(&Fraction::from((12i32, 16i32))));
            assert!(map.contains_key(&Fraction::from((24i64, 32i64))));
            assert!(map.contains_key(&Fraction::from((48i8, 64i16))));

            assert!(!map.contains_key(&Fraction::from(0.5))); // 0.75 != 1/2
        }

        {
            assert_eq!(hash_it(&Fraction::nan()), hash_it(&Fraction::nan()));
            assert_ne!(hash_it(&Fraction::nan()), hash_it(&Fraction::zero()));
            assert_ne!(
                hash_it(&Fraction::infinity()),
                hash_it(&Fraction::neg_infinity())
            );
            assert_ne!(hash_it(&Fraction::infinity()), hash_it(&Fraction::nan()));
            assert_eq!(
                hash_it(&Fraction::infinity()),
                hash_it(&Fraction::infinity())
            );
            assert_eq!(
                hash_it(&Fraction::neg_infinity()),
                hash_it(&Fraction::neg_infinity())
            );
            assert_eq!(
                hash_it(&Fraction::neg_infinity()),
                hash_it(&Fraction::neg_infinity())
            );

            assert_eq!(
                hash_it(&Fraction::new(1u8, 2u8)),
                hash_it(&Fraction::new(2u8, 4u8))
            );
            assert_eq!(
                hash_it(&Fraction::new(1u8, 0u8)),
                hash_it(&Fraction::new(2u8, 0u8))
            );
            assert_eq!(
                hash_it(&Fraction::new(0u8, 1u8)),
                hash_it(&Fraction::new(0u8, 2u8))
            );

            assert_eq!(hash_it(&Fraction::zero()), hash_it(&Fraction::zero()));
            assert_eq!(hash_it(&Frac::zero()), hash_it(&Frac::neg_zero()));
        }
    }

    #[test]
    fn comparison() {
        assert_eq!(Frac::zero(), Frac::zero());
        assert_eq!(Frac::zero(), Frac::neg_zero());
        assert_eq!(Frac::from(0), Frac::zero());
        assert_eq!(Frac::from(0), Frac::neg_zero());
        assert_eq!(Frac::from(0.5), Frac::new(1u8, 2u8));
        assert_eq!(Frac::from(-0.5), Frac::new_neg(1u8, 2u8));
        assert_ne!(Frac::from(-0.5), Frac::new(1u8, 2u8));

        assert!(!(Frac::zero() < Frac::neg_zero()));
        assert!(!(Frac::neg_zero() < Frac::zero()));

        assert!(!(Frac::zero() > Frac::neg_zero()));
        assert!(!(Frac::neg_zero() > Frac::zero()));

        assert!(Frac::neg_zero() < Frac::new(1u8, 2u8));
        assert!(!(Frac::neg_zero() > Frac::new(1u8, 2u8)));

        assert!(Frac::zero() < Frac::new(1u8, 2u8));
        assert!(!(Frac::zero() > Frac::new(1u8, 2u8)));

        assert!(Frac::new_neg(1u8, 2u8) < Frac::neg_zero());
        assert!(Frac::new_neg(1u8, 2u8) < Frac::zero());

        assert!(!(Frac::new_neg(1u8, 2u8) > Frac::neg_zero()));
        assert!(!(Frac::new_neg(1u8, 2u8) > Frac::zero()));

        assert_eq!(Frac::new(1u8, 2u8), Frac::new(1u8, 2u8));
        assert_eq!(Frac::new_neg(1u8, 2u8), Frac::new_neg(1u8, 2u8));

        assert!(Frac::new_neg(1u8, 2u8) < Frac::new(1u8, 2u8));
        assert!(!(Frac::new(1u8, 2u8) < Frac::new_neg(1u8, 2u8)));
        assert!(!(Frac::new_neg(1u8, 2u8) < Frac::new_neg(1u8, 2u8)));
        assert!(Frac::new_neg(1u8, 2u8) < Frac::new_neg(1u8, 4u8));

        assert!(Frac::new_neg(1u8, 2u8) < Frac::neg_zero());
        assert!(Frac::new_neg(1u8, 2u8) < Frac::zero());
        assert!(!(Frac::neg_zero() < Frac::new_neg(1u8, 2u8)));
        assert!(!(Frac::zero() < Frac::new_neg(1u8, 2u8)));
        assert!(Frac::neg_zero() < Frac::new(1u8, 2u8));
        assert!(Frac::neg_zero() > Frac::new_neg(1u8, 2u8));
        assert!(Frac::zero() > Frac::new_neg(1u8, 2u8));
        assert!(Frac::new(1u8, 2u8) > Frac::neg_zero());
        assert!(!(Frac::new(1u8, 2u8) < Frac::neg_zero()));
        assert!(Frac::zero() < Frac::new(1u8, 2u8));
    }

    #[test]
    fn from_decimal_str() {
        assert_eq!(Ok(Frac::zero()), Frac::from_decimal_str("0"));
        assert_eq!(Ok(Frac::zero()), Frac::from_decimal_str("-0"));
        assert_eq!(Ok(Frac::zero()), Frac::from_decimal_str("+0"));

        assert_eq!(Ok(Frac::zero()), Frac::from_decimal_str("0.0"));
        assert_eq!(Ok(Frac::zero()), Frac::from_decimal_str("-0.0"));
        assert_eq!(Ok(Frac::zero()), Frac::from_decimal_str("+0.0"));

        assert_eq!(Ok(Fraction::zero()), Fraction::from_decimal_str("0.000000"));
        assert_eq!(
            Ok(Fraction::zero()),
            Fraction::from_decimal_str("-0.000000")
        );
        assert_eq!(
            Ok(Fraction::zero()),
            Fraction::from_decimal_str("+0.000000")
        );

        #[cfg(feature = "with-bigint")]
        {
            assert_eq!(
                Ok(BigFraction::zero()),
                BigFraction::from_decimal_str(
                    "00000000000000000000000000.0000000000000000000000000000000000000000000"
                )
            );
            assert_eq!(
                Ok(BigFraction::zero()),
                BigFraction::from_decimal_str(
                    "-0000000000000000000000000.0000000000000000000000000000000000000000000"
                )
            );
            assert_eq!(
                Ok(BigFraction::zero()),
                BigFraction::from_decimal_str(
                    "+0000000000000000000000000.0000000000000000000000000000000000000000000"
                )
            );
        }

        assert_eq!(Ok(Frac::one()), Frac::from_decimal_str("1"));
        assert_eq!(Ok(Frac::new_neg(1, 1)), Frac::from_decimal_str("-1"));
        assert_eq!(Ok(Frac::one()), Frac::from_decimal_str("+1"));

        assert_eq!(Ok(Frac::one()), Frac::from_decimal_str("1.0"));
        assert_eq!(Ok(Frac::new_neg(1, 1)), Frac::from_decimal_str("-1.0"));
        assert_eq!(Ok(Frac::one()), Frac::from_decimal_str("+1.00"));

        assert_eq!(Ok(Frac::new(1, 2)), Frac::from_decimal_str("0.5"));

        assert_eq!(
            Ok(Fraction::new(3333u64, 5000u64)),
            Fraction::from_decimal_str("0.6666")
        );

        assert_eq!(
            Err(ParseError::ParseIntError),
            Frac::from_decimal_str("test")
        );
        assert_eq!(
            Err(ParseError::ParseIntError),
            Frac::from_decimal_str("1test")
        );
        assert_eq!(
            Err(ParseError::ParseIntError),
            Frac::from_decimal_str("1.26t8")
        );

        // this is due to the std library which issues ParseIntError on the whole part overflow
        assert_eq!(
            Err(ParseError::ParseIntError),
            Frac::from_decimal_str("120202040")
        );
        assert_eq!(
            Err(ParseError::ParseIntError),
            Frac::from_decimal_str("1.20602604")
        );

        assert_eq!(
            Err(ParseError::OverflowError),
            Frac::from_decimal_str("255.255")
        );
    }

    #[test]
    fn new_generic() {
        {
            type F = GenericFraction<u8>;

            let f12 = F::new_generic(Sign::Plus, 1i8, 2u8).unwrap();
            let f34 = F::new_generic(Sign::Minus, 3i16, 4u32).unwrap();
            let f56 = F::new_generic(Sign::Plus, -5i64, 6u128).unwrap();
            let f78 = F::new_generic(Sign::Minus, 7usize, -8isize).unwrap();

            #[cfg(feature = "with-bigint")]
            {
                let fbig =
                    F::new_generic(Sign::Minus, -BigInt::from(254), BigUint::from(255u32)).unwrap();

                assert_eq!(
                    (
                        fbig.sign().unwrap(),
                        *fbig.numer().unwrap(),
                        *fbig.denom().unwrap()
                    ),
                    (Sign::Plus, 254u8, 255u8)
                );
            }

            assert_eq!(
                (
                    f12.sign().unwrap(),
                    *f12.numer().unwrap(),
                    *f12.denom().unwrap()
                ),
                (Sign::Plus, 1u8, 2u8)
            );
            assert_eq!(
                (
                    f34.sign().unwrap(),
                    *f34.numer().unwrap(),
                    *f34.denom().unwrap()
                ),
                (Sign::Minus, 3u8, 4u8)
            );
            assert_eq!(
                (
                    f56.sign().unwrap(),
                    *f56.numer().unwrap(),
                    *f56.denom().unwrap()
                ),
                (Sign::Minus, 5u8, 6u8)
            );
            assert_eq!(
                (
                    f78.sign().unwrap(),
                    *f78.numer().unwrap(),
                    *f78.denom().unwrap()
                ),
                (Sign::Plus, 7u8, 8u8)
            );

            assert_eq!(None, F::new_generic(Sign::Plus, 256, 1)); // overflow
            assert_eq!(None, F::new_generic(Sign::Plus, 1, 257)); // overflow
        }

        {
            type F = GenericFraction<i8>;

            let f12 = F::new_generic(Sign::Plus, 1i8, 2u8).unwrap();
            let f34 = F::new_generic(Sign::Minus, 3i16, 4u32).unwrap();
            let f56 = F::new_generic(Sign::Plus, -5i64, 6u128).unwrap();
            let f78 = F::new_generic(Sign::Minus, 7usize, -8isize).unwrap();

            assert_eq!(
                (
                    f12.sign().unwrap(),
                    *f12.numer().unwrap(),
                    *f12.denom().unwrap()
                ),
                (Sign::Plus, 1i8, 2i8)
            );
            assert_eq!(
                (
                    f34.sign().unwrap(),
                    *f34.numer().unwrap(),
                    *f34.denom().unwrap()
                ),
                (Sign::Minus, 3i8, 4i8)
            );
            assert_eq!(
                (
                    f56.sign().unwrap(),
                    *f56.numer().unwrap(),
                    *f56.denom().unwrap()
                ),
                (Sign::Minus, 5i8, 6i8)
            );
            assert_eq!(
                (
                    f78.sign().unwrap(),
                    *f78.numer().unwrap(),
                    *f78.denom().unwrap()
                ),
                (Sign::Plus, 7i8, 8i8)
            );

            assert_eq!(None, F::new_generic(Sign::Plus, 128, 1)); // overflow
            assert_eq!(None, F::new_generic(Sign::Plus, 256, 1)); // overflow

            #[cfg(feature = "with-bigint")]
            {
                let fbig =
                    F::new_generic(Sign::Minus, -BigInt::from(126), BigUint::from(127u8)).unwrap();

                assert_eq!(
                    (
                        fbig.sign().unwrap(),
                        *fbig.numer().unwrap(),
                        *fbig.denom().unwrap()
                    ),
                    (Sign::Plus, 126i8, 127i8)
                );
            }
        }

        #[cfg(feature = "with-bigint")]
        {
            type F = GenericFraction<BigUint>;

            let f12 = F::new_generic(Sign::Plus, 1i8, 2u8).unwrap();
            let f34 = F::new_generic(Sign::Minus, 3i16, 4u32).unwrap();
            let f56 = F::new_generic(Sign::Plus, -5i64, 6u128).unwrap();
            let f78 = F::new_generic(Sign::Minus, 7usize, -8isize).unwrap();
            let fbig =
                F::new_generic(Sign::Minus, -BigInt::from(254), BigUint::from(255u32)).unwrap();

            assert_eq!(
                (
                    f12.sign().unwrap(),
                    f12.numer().unwrap(),
                    f12.denom().unwrap()
                ),
                (Sign::Plus, &BigUint::from(1u8), &BigUint::from(2u8))
            );
            assert_eq!(
                (
                    f34.sign().unwrap(),
                    f34.numer().unwrap(),
                    f34.denom().unwrap()
                ),
                (Sign::Minus, &BigUint::from(3u8), &BigUint::from(4u8))
            );
            assert_eq!(
                (
                    f56.sign().unwrap(),
                    f56.numer().unwrap(),
                    f56.denom().unwrap()
                ),
                (Sign::Minus, &BigUint::from(5u8), &BigUint::from(6u8))
            );
            assert_eq!(
                (
                    f78.sign().unwrap(),
                    f78.numer().unwrap(),
                    f78.denom().unwrap()
                ),
                (Sign::Plus, &BigUint::from(7u8), &BigUint::from(8u8))
            );
            assert_eq!(
                (
                    fbig.sign().unwrap(),
                    fbig.numer().unwrap(),
                    fbig.denom().unwrap()
                ),
                (Sign::Plus, &BigUint::from(254u8), &BigUint::from(255u8))
            );
        }

        #[cfg(feature = "with-bigint")]
        {
            type F = GenericFraction<BigInt>;

            let f12 = F::new_generic(Sign::Plus, 1i8, 2u8).unwrap();
            let f34 = F::new_generic(Sign::Minus, 3i16, 4u32).unwrap();
            let f56 = F::new_generic(Sign::Plus, -5i64, 6u128).unwrap();
            let f78 = F::new_generic(Sign::Minus, 7usize, -8isize).unwrap();
            let fbig =
                F::new_generic(Sign::Minus, -BigInt::from(254), BigUint::from(255u32)).unwrap();

            assert_eq!(
                (
                    f12.sign().unwrap(),
                    f12.numer().unwrap(),
                    f12.denom().unwrap()
                ),
                (Sign::Plus, &BigInt::from(1u8), &BigInt::from(2u8))
            );
            assert_eq!(
                (
                    f34.sign().unwrap(),
                    f34.numer().unwrap(),
                    f34.denom().unwrap()
                ),
                (Sign::Minus, &BigInt::from(3u8), &BigInt::from(4u8))
            );
            assert_eq!(
                (
                    f56.sign().unwrap(),
                    f56.numer().unwrap(),
                    f56.denom().unwrap()
                ),
                (Sign::Minus, &BigInt::from(5u8), &BigInt::from(6u8))
            );
            assert_eq!(
                (
                    f78.sign().unwrap(),
                    f78.numer().unwrap(),
                    f78.denom().unwrap()
                ),
                (Sign::Plus, &BigInt::from(7u8), &BigInt::from(8u8))
            );
            assert_eq!(
                (
                    fbig.sign().unwrap(),
                    fbig.numer().unwrap(),
                    fbig.denom().unwrap()
                ),
                (Sign::Plus, &BigInt::from(254u8), &BigInt::from(255u8))
            );
        }

        {
            type F = GenericFraction<u128>;

            let f1 = F::new_generic(Sign::Plus, 123456788u64, 123456789i32).unwrap();
            let f2 = F::new_generic(Sign::Minus, 1234567890122u64, -1234567890123i64).unwrap();

            assert_eq!(
                (
                    f1.sign().unwrap(),
                    *f1.numer().unwrap(),
                    *f1.denom().unwrap()
                ),
                (Sign::Plus, 123456788u128, 123456789u128)
            );
            assert_eq!(
                (
                    f2.sign().unwrap(),
                    *f2.numer().unwrap(),
                    *f2.denom().unwrap()
                ),
                (Sign::Plus, 1234567890122u128, 1234567890123u128)
            );
        }
    }

    #[test]
    fn sign() {
        let p = Sign::Plus;
        let m = Sign::Minus;

        assert_ne!(p, m);
        assert_eq!(p, Sign::Plus);
        assert_eq!(m, Sign::Minus);

        assert_eq!(m, p * m);
        assert_eq!(p, p * p);
        assert_eq!(p, m * m);
        assert_eq!(m, m * p);

        assert!(p.is_positive());
        assert!(!p.is_negative());

        assert!(!m.is_positive());
        assert!(m.is_negative());
    }

    #[test]
    fn fraction() {
        assert_eq!(Frac::nan(), Frac::new(0, 0));
        assert_eq!(Frac::infinity(), Frac::new(1, 0));

        assert!(Frac::nan().numer().is_none());
        assert!(Frac::nan().denom().is_none());

        assert_eq!(
            Fraction::new(5u64, 8u64),
            Fraction::from_fraction(Frac::new(5u8, 8u8))
        );
        assert_eq!(Fraction::nan(), Fraction::from_fraction(Frac::nan()));
        assert_eq!(
            Fraction::infinity(),
            Fraction::from_fraction(Frac::infinity())
        );

        assert_eq!(Frac::min_value(), Frac::new_neg(255, 1));
        assert_eq!(Frac::max_value(), Frac::new(255, 1));

        assert_ne!(Frac::neg_infinity(), Frac::infinity());
        assert_ne!(Frac::nan(), Frac::zero());
        assert_ne!(Frac::zero(), Frac::nan());
        assert_ne!(Frac::new_neg(1, 2), Frac::new(1, 2));
        assert_eq!(Frac::neg_zero(), Frac::zero());
        assert_ne!(Frac::infinity(), Frac::nan());

        assert!(!(Frac::infinity() > Frac::infinity()));
        assert!((Frac::infinity() > Frac::neg_infinity()));
        assert!(!(Frac::neg_infinity() > Frac::infinity()));

        assert!(Frac::infinity() > Frac::max_value());
        assert!(Frac::min_value() > Frac::neg_infinity());

        assert_eq!(-Frac::infinity(), Frac::neg_infinity());

        assert_eq!(-&Frac::nan(), Frac::nan());
        assert_eq!(-&Frac::infinity(), Frac::neg_infinity());
        assert_eq!(-&Frac::one(), Frac::new_neg(1, 1));

        assert_eq!(-&Frac::zero(), Frac::zero());

        assert_eq!(
            Frac::new_neg(1, 1) + Frac::new_neg(1, 1),
            Frac::new_neg(2, 1)
        );
        assert_eq!(
            &Frac::new_neg(1, 1) + &Frac::new_neg(1, 1),
            Frac::new_neg(2, 1)
        );

        assert_eq!(Frac::new_neg(1, 1) - Frac::new_neg(1, 1), Frac::zero());
        assert_eq!(Frac::new_neg(1, 1) - Frac::new_neg(2, 1), Frac::one());
        assert_eq!(&Frac::new_neg(1, 1) - &Frac::new_neg(1, 1), Frac::zero());
        assert_eq!(&Frac::new_neg(1, 1) - &Frac::new_neg(2, 1), Frac::one());

        assert_eq!(Frac::new(1, 255), Frac::min_positive_value());

        assert!(Frac::infinity().is_infinite());
        assert!(Frac::neg_infinity().is_infinite());
        assert!(!Frac::one().is_infinite());

        assert!(!Frac::infinity().is_finite());
        assert!(!Frac::neg_infinity().is_finite());
        assert!(Frac::one().is_finite());

        assert_eq!(FpCategory::Normal, Frac::one().classify());
        assert_eq!(FpCategory::Infinite, Frac::infinity().classify());
        assert_eq!(FpCategory::Zero, Frac::zero().classify());
        assert_eq!(FpCategory::Nan, Frac::nan().classify());

        assert_eq!(Frac::nan(), Frac::nan().floor());
        assert_eq!(Frac::one(), Frac::new(3, 2).floor());

        assert_eq!(Frac::nan(), Frac::nan().ceil());
        assert_eq!(Frac::one(), Frac::new(1, 2).ceil());

        assert_eq!(Frac::nan(), Frac::nan().round());
        assert_eq!(Frac::one(), Frac::new(1, 2).round());
        assert_eq!(Frac::new(2, 1), Frac::new(3, 2).round());
        assert_eq!(Frac::one(), Frac::new(4, 3).round());

        assert_eq!(Frac::nan(), Frac::nan().trunc());
        assert_eq!(Frac::zero(), Frac::new(1, 2).trunc());
        assert_eq!(Frac::one(), Frac::new(3, 2).trunc());

        assert_eq!(Frac::nan(), Frac::nan().fract());
        assert_eq!(Frac::new(1, 2), Frac::new(1, 2).fract());
        assert_eq!(Frac::new(1, 2), Frac::new(3, 2).fract());

        assert!(!Frac::nan().is_sign_positive());
        assert!(!Frac::nan().is_sign_negative());

        assert!(Frac::infinity().is_sign_positive());
        assert!(!Frac::neg_infinity().is_sign_positive());

        assert!(!Frac::infinity().is_sign_negative());
        assert!(Frac::neg_infinity().is_sign_negative());

        assert!(Frac::one().is_sign_positive());
        assert!(!Frac::one().is_sign_negative());

        assert!(!Frac::new_neg(1, 1).is_sign_positive());
        assert!(Frac::new_neg(1, 1).is_sign_negative());

        assert_eq!(
            Frac::new(3, 1),
            Frac::one().mul_add(Frac::new(2, 1), Frac::one())
        );

        assert_eq!(Frac::nan(), Frac::nan().recip());
        assert_eq!(Frac::zero(), Frac::infinity().recip());
        assert_eq!(Frac::zero(), Frac::neg_infinity().recip());
        assert_eq!(Frac::infinity(), Frac::zero().recip());
        assert_eq!(Frac::new(2, 1), Frac::new(1, 2).recip());
    }

    #[test]
    fn add_assign() {
        {
            let mut v = Frac::zero();
            v += Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v += Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v += Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v += Frac::neg_infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v += Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v += Frac::new_neg(1, 1);
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v += Frac::new_neg(2, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v += Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new_neg(2, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v += Frac::new(1, 1);
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::new_neg(2, 1);
            v += Frac::new(1, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        /* Refs */

        {
            let mut v = Frac::zero();
            v += &Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v += &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v += &Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v += &Frac::neg_infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v += &Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v += &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v += &Frac::new_neg(2, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v += &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new_neg(2, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v += &Frac::new(1, 1);
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::new_neg(2, 1);
            v += &Frac::new(1, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }
    }

    #[test]
    fn sub_assign() {
        {
            let mut v = Frac::nan();
            v -= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v -= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v -= Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v -= Frac::neg_infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v -= Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v -= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v -= Frac::infinity();
            assert_eq!(v, Frac::neg_infinity());
        }

        {
            let mut v = Frac::one();
            v -= Frac::neg_infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v -= Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new(2, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v -= Frac::new(2, 1);
            assert_eq!(v, Frac::new_neg(3, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v -= Frac::new_neg(1, 1);
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v -= Frac::new_neg(2, 1);
            assert_eq!(v, Frac::one());
        }

        /* Refs */

        {
            let mut v = Frac::nan();
            v -= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v -= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v -= &Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v -= &Frac::neg_infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v -= &Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v -= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v -= &Frac::infinity();
            assert_eq!(v, Frac::neg_infinity());
        }

        {
            let mut v = Frac::one();
            v -= &Frac::neg_infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v -= &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new(2, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v -= &Frac::new(2, 1);
            assert_eq!(v, Frac::new_neg(3, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v -= &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v -= &Frac::new_neg(2, 1);
            assert_eq!(v, Frac::one());
        }
    }

    #[test]
    fn mul_assign() {
        {
            let mut v = Frac::nan();
            v *= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v *= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v *= Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v *= Frac::neg_infinity();
            assert_eq!(v, Frac::neg_infinity());
        }

        {
            let mut v = Frac::infinity();
            v *= Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v *= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v *= Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v *= Frac::neg_infinity();
            assert_eq!(v, Frac::neg_infinity());
        }

        {
            let mut v = Frac::one();
            v *= Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v *= Frac::new(2, 1);
            assert_eq!(v, Frac::new_neg(2, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v *= Frac::new_neg(1, 1);
            assert_eq!(v, Frac::one());
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v *= Frac::new_neg(2, 1);
            assert_eq!(v, Frac::new(2, 1));
        }

        {
            let mut v = Frac::infinity();
            v *= Frac::zero();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::zero();
            v *= Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        /* Refs */

        {
            let mut v = Frac::nan();
            v *= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v *= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v *= &Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::infinity();
            v *= &Frac::neg_infinity();
            assert_eq!(v, Frac::neg_infinity());
        }

        {
            let mut v = Frac::infinity();
            v *= &Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v *= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v *= &Frac::infinity();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v *= &Frac::neg_infinity();
            assert_eq!(v, Frac::neg_infinity());
        }

        {
            let mut v = Frac::one();
            v *= &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v *= &Frac::new(2, 1);
            assert_eq!(v, Frac::new_neg(2, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v *= &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::one());
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v *= &Frac::new_neg(2, 1);
            assert_eq!(v, Frac::new(2, 1));
        }

        {
            let mut v = Frac::infinity();
            v *= &Frac::zero();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::zero();
            v *= &Frac::infinity();
            assert_eq!(v, Frac::nan());
        }
    }

    #[test]
    fn div_assign() {
        {
            let mut v = Frac::nan();
            v /= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= Frac::neg_infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v /= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v /= Frac::infinity();
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v /= Frac::neg_infinity();
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v /= Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v /= Frac::new(2, 1);
            assert_eq!(v, Frac::new_neg(1, 2));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v /= Frac::new_neg(1, 1);
            assert_eq!(v, Frac::one());
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v /= Frac::new_neg(2, 1);
            assert_eq!(v, Frac::new(1, 2));
        }

        {
            let mut v = Frac::infinity();
            v /= Frac::zero();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::zero();
            v /= Frac::infinity();
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v /= Frac::zero();
            assert_eq!(v, Frac::infinity());
        }

        /* Refs */

        {
            let mut v = Frac::nan();
            v /= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= &Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= &Frac::neg_infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v /= &Frac::one();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::one();
            v /= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v /= &Frac::infinity();
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v /= &Frac::neg_infinity();
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v /= &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::new_neg(1, 1));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v /= &Frac::new(2, 1);
            assert_eq!(v, Frac::new_neg(1, 2));
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v /= &Frac::new_neg(1, 1);
            assert_eq!(v, Frac::one());
        }

        {
            let mut v = Frac::new_neg(1, 1);
            v /= &Frac::new_neg(2, 1);
            assert_eq!(v, Frac::new(1, 2));
        }

        {
            let mut v = Frac::infinity();
            v /= &Frac::zero();
            assert_eq!(v, Frac::infinity());
        }

        {
            let mut v = Frac::zero();
            v /= &Frac::infinity();
            assert_eq!(v, Frac::zero());
        }

        {
            let mut v = Frac::one();
            v /= &Frac::zero();
            assert_eq!(v, Frac::infinity());
        }
    }

    #[test]
    fn rem_assign() {
        {
            let mut v = Frac::infinity();
            v %= Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v %= Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v %= Frac::one();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v %= Frac::infinity();
            assert_eq!(v, Frac::one());
        }

        /* Refs */

        {
            let mut v = Frac::infinity();
            v %= &Frac::nan();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v %= &Frac::infinity();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::infinity();
            v %= &Frac::one();
            assert_eq!(v, Frac::nan());
        }

        {
            let mut v = Frac::one();
            v %= &Frac::infinity();
            assert_eq!(v, Frac::one());
        }
    }

    #[test]
    fn checked_add() {
        assert_eq!(Some(Frac::nan()), Frac::nan().checked_add(&Frac::nan()));

        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_add(&Frac::nan())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_add(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_add(&Frac::neg_infinity())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_add(&Frac::one())
        );

        assert_eq!(Some(Frac::nan()), Frac::one().checked_add(&Frac::nan()));
        assert_eq!(
            Some(Frac::infinity()),
            Frac::one().checked_add(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::one().checked_add(&Frac::neg_infinity())
        );

        assert_eq!(Some(Frac::new(2, 1)), Frac::one().checked_add(&Frac::one()));
        assert_eq!(
            Some(Frac::zero()),
            Frac::one().checked_add(&Frac::new_neg(1, 1))
        );
        assert_eq!(
            Some(Frac::zero()),
            Frac::new_neg(1, 1).checked_add(&Frac::one())
        );
        assert_eq!(
            Some(Frac::new_neg(2, 1)),
            Frac::new_neg(1, 1).checked_add(&Frac::new_neg(1, 1))
        );

        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::one().checked_add(&Frac::new_neg(2, 1))
        );
        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::new_neg(2, 1).checked_add(&Frac::one())
        );
    }

    #[test]
    fn checked_sub() {
        assert_eq!(Some(Frac::nan()), Frac::nan().checked_sub(&Frac::nan()));

        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_sub(&Frac::nan())
        );
        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_sub(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_sub(&Frac::neg_infinity())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_sub(&Frac::one())
        );

        assert_eq!(Some(Frac::nan()), Frac::one().checked_sub(&Frac::nan()));
        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::one().checked_sub(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::one().checked_sub(&Frac::neg_infinity())
        );

        assert_eq!(Some(Frac::zero()), Frac::one().checked_sub(&Frac::one()));
        assert_eq!(
            Some(Frac::new(2, 1)),
            Frac::one().checked_sub(&Frac::new_neg(1, 1))
        );
        assert_eq!(
            Some(Frac::new_neg(2, 1)),
            Frac::new_neg(1, 1).checked_sub(&Frac::one())
        );
        assert_eq!(
            Some(Frac::zero()),
            Frac::new_neg(1, 1).checked_sub(&Frac::new_neg(1, 1))
        );

        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::one().checked_sub(&Frac::new(2, 1))
        );
        assert_eq!(
            Some(Frac::one()),
            Frac::new_neg(1, 1).checked_sub(&Frac::new_neg(2, 1))
        );
    }

    #[test]
    fn checked_mul() {
        assert_eq!(Some(Frac::nan()), Frac::nan().checked_mul(&Frac::nan()));

        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_mul(&Frac::nan())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_mul(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::infinity().checked_mul(&Frac::neg_infinity())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_mul(&Frac::one())
        );

        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_mul(&Frac::zero())
        );
        assert_eq!(
            Some(Frac::nan()),
            Frac::zero().checked_mul(&Frac::infinity())
        );

        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::infinity().checked_mul(&Frac::new_neg(1, 1))
        );

        assert_eq!(Some(Frac::nan()), Frac::one().checked_mul(&Frac::nan()));
        assert_eq!(
            Some(Frac::infinity()),
            Frac::one().checked_mul(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::one().checked_mul(&Frac::neg_infinity())
        );

        assert_eq!(Some(Frac::one()), Frac::one().checked_mul(&Frac::one()));
        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::one().checked_mul(&Frac::new_neg(1, 1))
        );
        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::new_neg(1, 1).checked_mul(&Frac::one())
        );
        assert_eq!(
            Some(Frac::one()),
            Frac::new_neg(1, 1).checked_mul(&Frac::new_neg(1, 1))
        );

        assert_eq!(
            Some(Frac::new(2, 1)),
            Frac::one().checked_mul(&Frac::new(2, 1))
        );
        assert_eq!(
            Some(Frac::new(2, 1)),
            Frac::new_neg(1, 1).checked_mul(&Frac::new_neg(2, 1))
        );

        assert_eq!(Some(Frac::zero()), Frac::one().checked_mul(&Frac::zero()));
        assert_eq!(
            Some(Frac::zero()),
            Frac::new_neg(1, 1).checked_mul(&Frac::zero())
        );
        assert_eq!(Some(Frac::zero()), Frac::zero().checked_mul(&Frac::one()));
        assert_eq!(
            Some(Frac::zero()),
            Frac::zero().checked_mul(&Frac::new_neg(1, 1))
        );
    }

    #[test]
    fn checked_div() {
        assert_eq!(Some(Frac::nan()), Frac::nan().checked_div(&Frac::nan()));

        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_div(&Frac::nan())
        );
        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_div(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::nan()),
            Frac::infinity().checked_div(&Frac::neg_infinity())
        );
        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_div(&Frac::one())
        );
        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::infinity().checked_div(&Frac::new_neg(1, 1))
        );

        assert_eq!(
            Some(Frac::infinity()),
            Frac::infinity().checked_div(&Frac::zero())
        );
        assert_eq!(
            Some(Frac::zero()),
            Frac::zero().checked_div(&Frac::infinity())
        );

        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::infinity().checked_div(&Frac::new_neg(1, 1))
        );

        assert_eq!(Some(Frac::nan()), Frac::one().checked_div(&Frac::nan()));
        assert_eq!(
            Some(Frac::zero()),
            Frac::one().checked_div(&Frac::infinity())
        );
        assert_eq!(
            Some(Frac::zero()),
            Frac::one().checked_div(&Frac::neg_infinity())
        );

        assert_eq!(Some(Frac::one()), Frac::one().checked_div(&Frac::one()));
        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::one().checked_div(&Frac::new_neg(1, 1))
        );
        assert_eq!(
            Some(Frac::new_neg(1, 1)),
            Frac::new_neg(1, 1).checked_div(&Frac::one())
        );
        assert_eq!(
            Some(Frac::one()),
            Frac::new_neg(1, 1).checked_div(&Frac::new_neg(1, 1))
        );

        assert_eq!(
            Some(Frac::new(1, 2)),
            Frac::one().checked_div(&Frac::new(2, 1))
        );
        assert_eq!(
            Some(Frac::new(1, 2)),
            Frac::new_neg(1, 1).checked_div(&Frac::new_neg(2, 1))
        );

        assert_eq!(
            Some(Frac::infinity()),
            Frac::one().checked_div(&Frac::zero())
        );
        assert_eq!(
            Some(Frac::neg_infinity()),
            Frac::new_neg(1, 1).checked_div(&Frac::zero())
        );
        assert_eq!(Some(Frac::zero()), Frac::zero().checked_div(&Frac::one()));
        assert_eq!(
            Some(Frac::zero()),
            Frac::zero().checked_div(&Frac::new_neg(1, 1))
        );

        assert_eq!(Some(Frac::nan()), Frac::zero().checked_div(&Frac::zero()));
    }

    #[test]
    fn from_str_radix() {
        assert_eq!(Frac::one(), Frac::from_str_radix("5/5", 10).unwrap());
        assert_eq!(Frac::one(), Frac::from_str_radix("+5/5", 10).unwrap());
        assert_eq!(Frac::new(1, 2), Frac::from_str_radix("+5/10", 10).unwrap());
        assert_eq!(
            Frac::new_neg(4, 3),
            Frac::from_str_radix("-4/3", 10).unwrap()
        );
    }

    #[test]
    fn signed() {
        // abs
        assert_eq!(Frac::one(), <Frac as Signed>::abs(&Frac::new_neg(1, 1)));
        assert_eq!(Frac::nan(), <Frac as Signed>::abs(&Frac::nan()));
        assert_eq!(Frac::infinity(), <Frac as Signed>::abs(&Frac::infinity()));
        assert_eq!(
            Frac::infinity(),
            <Frac as Signed>::abs(&Frac::neg_infinity())
        );

        // abs_sub
        assert_eq!(Frac::nan(), Frac::nan().abs_sub(&Frac::nan()));
        assert_eq!(Frac::nan(), Frac::infinity().abs_sub(&Frac::nan()));
        assert_eq!(Frac::zero(), Frac::infinity().abs_sub(&Frac::infinity()));
        assert_eq!(
            Frac::infinity(),
            Frac::infinity().abs_sub(&Frac::neg_infinity())
        );
        assert_eq!(
            Frac::zero(),
            Frac::neg_infinity().abs_sub(&Frac::neg_infinity())
        );
        assert_eq!(
            Frac::zero(),
            Frac::neg_infinity().abs_sub(&Frac::infinity())
        );
        assert_eq!(Frac::infinity(), Frac::infinity().abs_sub(&Frac::one()));
        assert_eq!(
            Frac::infinity(),
            Frac::infinity().abs_sub(&Frac::new_neg(1, 1))
        );
        assert_eq!(Frac::zero(), Frac::neg_infinity().abs_sub(&Frac::one()));
        assert_eq!(Frac::nan(), Frac::one().abs_sub(&Frac::nan()));
        assert_eq!(Frac::zero(), Frac::one().abs_sub(&Frac::infinity()));
        assert_eq!(Frac::infinity(), Frac::one().abs_sub(&Frac::neg_infinity()));
        assert_eq!(
            Frac::neg_infinity(),
            Frac::new_neg(1, 1).abs_sub(&Frac::neg_infinity())
        );
        assert_eq!(Frac::one(), Frac::new(2, 1).abs_sub(&Frac::one()));
        assert_eq!(Frac::one(), Frac::one().abs_sub(&Frac::new(2, 1)));

        // signum
        assert_eq!(Frac::nan(), Frac::nan().signum());
        assert_eq!(Frac::one(), Frac::infinity().signum());
        assert_eq!(Frac::one(), Frac::zero().signum());
        assert_eq!(Frac::one(), Frac::one().signum());
        assert_eq!(-Frac::one(), Frac::neg_infinity().signum());
        assert_eq!(-Frac::one(), Frac::new_neg(1, 1).signum());
    }

    #[test]
    fn to_primitive() {
        assert!(Frac::nan().to_i64().is_none());
        assert!(Frac::nan().to_u64().is_none());

        assert!(Frac::infinity().to_i64().is_none());
        assert!(Frac::infinity().to_u64().is_none());

        assert!(Frac::neg_infinity().to_i64().is_none());
        assert!(Frac::neg_infinity().to_u64().is_none());

        assert_eq!(Some(1), Frac::one().to_i64());
        assert_eq!(Some(1), Frac::one().to_u64());

        assert!(Frac::new(1, 2).to_i64().is_none());
        assert!(Frac::new(1, 2).to_u64().is_none());

        assert_eq!(Some(-1), Frac::new_neg(1, 1).to_i64());
        assert!(Frac::new_neg(1, 1).to_u64().is_none());

        /* f64 */

        assert!(Frac::nan().to_f64().unwrap().is_nan());
        assert_eq!(::std::f64::INFINITY, Frac::infinity().to_f64().unwrap());
        assert_eq!(
            ::std::f64::NEG_INFINITY,
            Frac::neg_infinity().to_f64().unwrap()
        );

        assert_eq!(1f64, Frac::one().to_f64().unwrap());
    }

    #[test]
    fn summing_iterator() {
        let values = vec![Fraction::new(2u64, 3u64), Fraction::new(1u64, 3u64)];
        let sum: Fraction = values.iter().sum();
        assert_eq!(sum, Fraction::new(1u8, 1u8));
    }

    #[test]
    fn product_iterator() {
        let values = vec![Fraction::new(2u64, 3u64), Fraction::new(1u64, 3u64)];
        let product: Fraction = values.iter().product();
        assert_eq!(product, Fraction::new(2u8, 9u8));
    }
}

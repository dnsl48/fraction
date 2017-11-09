//! Fraction is a lossless float type implementation that can be used for matching, ordering and hashing.
//!
//! The main goal of the project is to keep precision that floats cannot do.
//!
//! Base arithmetic implemented upon the [num](https://crates.io/crates/num) crate (in particular its [rational](https://crates.io/crates/num-rational) module).
//!
//! The main object in the library is [`GenericFraction<T> where T: Integer`](enum.GenericFraction.html).
//!
//! However, there are two shortcuts for the two most common use cases:
//!
//!  - [`type Fraction = GenericFraction<u64>`](type.Fraction.html)
//!  - [`type BigFraction = GenericFraction<BigUint>`](type.BigFraction.html)


extern crate num;

use self::num::rational::{ Ratio, ParseRatioError };
use self::num::traits::{ /*Float, */Bounded, Zero, One, Signed, Num, ToPrimitive, CheckedMul, CheckedAdd };
use self::num::integer::Integer;
use self::num::bigint::{ BigInt, BigUint };

use std::num::FpCategory;
use std::ops::{ Add, Div, Mul, Neg, Rem, Sub, AddAssign, DivAssign, MulAssign, RemAssign, SubAssign };
use std::cmp::{ Eq, PartialEq, PartialOrd, Ordering };

use std::f64;
use std::fmt;
use std::mem;




/// Fraction consisting from two `u64` numbers
///
/// Allows to keep and work with fractions on stack.
///
/// Be aware of possible stack overflows that might be caused by
/// exceeding `u64` limits in some math operations, which will make thread to panic.
///
/// # Example
///
/// ```
/// use fraction::Fraction;
///
/// let first = Fraction::new (1u8, 2u8);
/// let second = Fraction::new (2u8, 8u8);
///
/// assert_eq! (first + second, Fraction::new (3u8, 4u8));
/// ```
pub type Fraction = GenericFraction<u64>;




/// Fraction consisting from two `BigUint` numbers
///
/// Allows to keep and work with fractions on heap.
///
/// BigUint number is based on heap and does not have any limits, which makes
/// BigFraction safe from stack overflows. However, it comes with a price of
/// making allocations on every math operation.
///
/// # Example
///
/// ```
/// use fraction::BigFraction;
///
/// let first = BigFraction::new (2u8, 3u8);
/// let second = BigFraction::new (1u8, 6u8);
///
/// assert_eq! (first + second, BigFraction::new (5u8, 6u8));
/// ```
pub type BigFraction = GenericFraction<BigUint>;



/// Sign representation
///
/// Fraction keeps its sign represented by the enum,
/// so that we can use unsigned ints as base data types.
#[derive (Copy, Clone, Hash, Debug, PartialEq, Eq)]
pub enum Sign {
    Plus,
    Minus
}




impl Neg for Sign {
    type Output = Self;

    fn neg (self) -> Sign {
        match self {
            Sign::Plus => Sign::Minus,
            Sign::Minus => Sign::Plus
        }
    }
}



impl fmt::Display for Sign {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Sign::Plus => write! (f, "+"),
            Sign::Minus => write! (f, "-")
        }
    }
}




/// Generic implementation of the fraction type
///
/// Even though it is implemented as `enum`, you should not use enum variants explicitly. Use `new`, `new_*` and `from` methods insdead.
///
/// Although there are two main specializations of this type ([Fraction](type.Fraction.html) and [BigFraction](type.BigFraction.html)),
/// you can easily define your own ones.
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
#[derive (Clone, Hash, Debug)]
pub enum GenericFraction<T>
    where T: Clone + Integer
{
    Rational (Sign, Ratio<T>),
    Infinity (Sign),
    NaN
}



/// Copy semantics to be applied for the target type, but only if T also has it.
impl<T> Copy for GenericFraction<T> where T: Copy + Integer {}



impl<T: Clone + Integer> GenericFraction<T> {
    fn _new<N, D> (sign: Sign, num: N, den: D) -> GenericFraction<T>
        where
            N: Into<T>,
            D: Into<T>
    {
        let num: T = num.into ();
        let den: T = den.into ();

        if den.is_zero () {
            if num.is_zero () {
                GenericFraction::NaN
            } else {
                GenericFraction::Infinity (sign)
            }
        } else {
            GenericFraction::Rational (sign, Ratio::new (num, den))
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
    /// let f = F::new (1u8, 2u16);
    /// ```
    pub fn new<N, D> (num: N, den: D) -> GenericFraction<T>
        where
            N: Into<T>,
            D: Into<T>
    {
        Self::_new (Sign::Plus, num, den)
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
    /// let f = F::new_neg (1u8, 2u16);
    /// ```
    pub fn new_neg<N, D> (num: N, den: D) -> GenericFraction<T>
        where
            N: Into<T>,
            D: Into<T>
    {
        Self::_new (Sign::Minus, num, den)
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
    /// let f = F::new_raw (1u8, 2u8);
    /// ```
    pub fn new_raw (num: T, den: T) -> GenericFraction<T> {
        GenericFraction::Rational (Sign::Plus, Ratio::new_raw (num, den))
    }


    /// The same as [fn new_raw](enum.GenericFraction.html#method.new_raw), but produces negative fractions.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let f = F::new_raw_neg (1u8, 2u8);
    /// ```
    pub fn new_raw_neg (num: T, den: T) -> GenericFraction<T> {
        GenericFraction::Rational (Sign::Minus, Ratio::new_raw (num, den))
    }


    /// Constructs NaN value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let nan = F::new_nan ();
    /// ```
    pub fn new_nan () -> GenericFraction<T> { GenericFraction::NaN }


    /// Constructs INF value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let nan = F::new_inf ();
    /// ```
    pub fn new_inf () -> GenericFraction<T> { GenericFraction::Infinity (Sign::Plus) }


    /// Constructs negative INF value
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// let nan = F::new_inf_neg ();
    /// ```
    pub fn new_inf_neg () -> GenericFraction<T> { GenericFraction::Infinity (Sign::Minus) }


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
    pub fn numer (&self) -> Option<&T> {
        match *self {
            GenericFraction::Rational (_, ref r) => Some (r.numer ()),
            _ => None
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
    pub fn denom (&self) -> Option<&T> {
        match *self {
            GenericFraction::Rational (_, ref r) => Some (r.denom ()),
            _ => None
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
    /// assert_eq! (Sign::Plus, *fra.sign ().unwrap ());
    ///
    /// let fra = F::new_neg (5u8, 6u8);
    /// assert_eq! (Sign::Minus, *fra.sign ().unwrap ());
    ///
    ///
    /// let fra = F::new_inf ();
    /// assert_eq! (Sign::Plus, *fra.sign ().unwrap ());
    ///
    /// let fra = F::new_inf_neg ();
    /// assert_eq! (Sign::Minus, *fra.sign ().unwrap ());
    ///
    ///
    /// let fra = F::new_nan ();
    /// assert_eq! (None, fra.sign ());
    /// ```
    pub fn sign (&self) -> Option<&Sign> {
        match *self {
            GenericFraction::Rational (ref s, _) => Some (s),
            GenericFraction::Infinity (ref s) => Some (s),
            _ => None
        }
    }


    /// Generates a new [BigFraction](type.BigFraction.html) from the current one
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::{ BigFraction, GenericFraction };
    /// type F = GenericFraction<u8>;
    ///
    /// let fra = F::new (5u8, 6u8).into_big ();
    /// assert_eq! (BigFraction::new (5u8, 6u8), fra);
    /// ```
    pub fn into_big (self) -> BigFraction where T: Into<BigUint> {
        match self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (sign) => GenericFraction::Infinity (sign),
            GenericFraction::Rational (sign, ratio) => {
                let n: BigUint = ratio.numer ().clone ().into ();
                let d: BigUint = ratio.denom ().clone ().into ();
                GenericFraction::Rational (sign, Ratio::new (n, d))
            }
        }
    }


    /// Returns a float representation of the fraction
    ///
    /// If you have a fraction "1/2", in float it should be "0.5".
    ///
    /// Since native floats can lose precision, we try to avoid converting to
    /// floats as long as possible. However, the current implementation is not
    /// ideal and still performs casting into native floats in case we have
    /// a "bad" number, like "1/3", "2/3", "5/6" etc.
    /// Please, feel free to PR fix if you feel power to solve this issue.
    ///
    /// Returns None in case it's a "bad" number and numerator or denominator
    /// so big that cannot be converted into f64.
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::GenericFraction;
    /// type F = GenericFraction<u8>;
    ///
    /// assert_eq! ("0.5", &F::new (1u8, 2u8).format_as_float ().unwrap ());
    /// assert_eq! ("0.8", &F::new (8u8, 10u8).format_as_float ().unwrap ());
    /// ```
    pub fn format_as_float (&self) -> Option<String>
        where
            T: From<u8> + Into<BigUint> + ToPrimitive + fmt::Display
    {
        match *self {
            GenericFraction::NaN => return Some (format! ("{}", std::f32::NAN)),
            GenericFraction::Infinity (sign) => match sign {
                Sign::Plus  => return Some (format! ("{}", std::f32::INFINITY)),
                Sign::Minus => return Some (format! ("{}", std::f32::NEG_INFINITY))
            },
            GenericFraction::Rational (_, _) => ()
        }

        let a = self.numer ().unwrap ();
        let b = self.denom ().unwrap ();

        let ma = Mint::from (a.clone ());
        let mb = Mint::from (b.clone ());

        let (f, mut r) = ma.div_rem (&mb);

        let mut x = Mint::from (1u8);
        let i10 = Mint::from (10u8);
        let i0 = Mint::from (0u8);

        let mut limit = 0;

        loop {
            limit += 1;
            if limit > 1000 { // TODO: do something with bad numbers here (eg 1/3)
                if let Some (a) = a.to_f64 () {
                    if let Some (b) = b.to_f64 () {
                        return Some (format! ("{}", a / b));
                    }
                }
                return None
            }

            x *= i10.clone ();
            if x < mb { continue; }
            if x.clone () % mb.clone () == i0 { break; }
        }

        x /= mb;
        r *= x;

        let r = format! ("{}", r);

        let l = if limit > r.len () {
            let mut l = String::with_capacity (limit - r.len ());
            for _ in 0 .. (limit - r.len ()) { l.push ('0') }
            l
        } else { String::new () };

        Some (format! ("{}.{}{}", f, l, r))
    }
}



impl<T: Bounded + Clone + Integer> Bounded for GenericFraction<T> {
    fn min_value () -> Self {
        let nil = T::zero ();
        let min = T::min_value ();

        if min < nil {
            let one = T::one ();
            GenericFraction::Rational (Sign::Minus, Ratio::new (min, one))
        } else {
            let max = T::max_value ();
            GenericFraction::Rational (Sign::Plus, Ratio::new (min, max))
        }
    }

    fn max_value () -> Self {
        let one = T::one ();
        let max = T::max_value ();

        GenericFraction::Rational (Sign::Plus, Ratio::new (max, one))
    }
}



impl<T: Clone + Integer> PartialEq for GenericFraction<T> {
    fn eq (&self, other: &Self) -> bool {
        match *self {
            GenericFraction::NaN => match *other {
                GenericFraction::NaN => true,
                _ => false
            },
            GenericFraction::Infinity (sign) => match *other {
                GenericFraction::Infinity (osign) => sign == osign,
                _ => false
            },
            GenericFraction::Rational (ref ls, ref l) => match *other {
                GenericFraction::Rational (ref rs, ref r) => {
                    if ls == rs {
                        l.eq (r)
                    } else {
                        l.is_zero () && r.is_zero ()
                    }
                }
                _ => false
            }
        }
    }
}



impl<T: Clone + Integer> Eq for GenericFraction<T> {}



impl<T: Clone + Integer> PartialOrd for GenericFraction<T> {
    fn partial_cmp (&self, other: &Self) -> Option<Ordering> {
        match *self {
            GenericFraction::NaN => None,
            GenericFraction::Infinity (sign) => match *other {
                GenericFraction::NaN => None,
                GenericFraction::Infinity (osign) => {
                    if sign == osign {
                        Some (Ordering::Equal)
                    } else if sign == Sign::Minus {
                        Some (Ordering::Less)
                    } else {
                        Some (Ordering::Greater)
                    }
                }
                GenericFraction::Rational (_, _) => if sign == Sign::Plus { Some (Ordering::Greater) } else { Some (Ordering::Less) }
            },
            GenericFraction::Rational (ref ls, ref l) => match *other {
                GenericFraction::NaN => None,
                GenericFraction::Infinity (rs) => if rs == Sign::Plus { Some (Ordering::Less) } else { Some (Ordering::Greater) },
                GenericFraction::Rational (ref rs, ref r) => {
                    if ls == rs {
                        match *ls {
                            Sign::Plus => l.partial_cmp (r),
                            Sign::Minus => r.partial_cmp (l)
                        }
                    } else if l.is_zero () && r.is_zero () {
                        Some (Ordering::Equal)
                    } else if *ls == Sign::Minus {
                        Some (Ordering::Less)
                    } else {
                        Some (Ordering::Greater)
                    }
                }
            }
        }
    }
}



impl<T: Clone + Integer> Neg for GenericFraction<T> {
    type Output = GenericFraction<T>;

    fn neg (self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity (sign) => GenericFraction::Infinity (-sign),
            GenericFraction::Rational (s, r) => {
                if r.is_zero () {
                    GenericFraction::Rational (Sign::Plus, r)
                } else {
                    GenericFraction::Rational (s.neg (), r)
                }
            }
        }
    }
}



impl<T: Clone + Integer> Add for GenericFraction<T> {
    type Output = Self;

    fn add (self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity (sign) => {
                match other {
                    GenericFraction::NaN => other,
                    GenericFraction::Rational (_, _) => self,
                    GenericFraction::Infinity (osign) => if sign != osign { GenericFraction::NaN } else { self }
                }
            }
            GenericFraction::Rational (ls, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (_) => other,
                GenericFraction::Rational (rs, r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        GenericFraction::Rational (Sign::Plus, l.add (r))
                    } else if ls == Sign::Plus {
                        if l < r {
                            GenericFraction::Rational (Sign::Minus, r.sub (l))
                        } else {
                            GenericFraction::Rational (Sign::Plus, l.sub (r))
                        }
                    } else if rs == Sign::Plus {
                        if r < l {
                            GenericFraction::Rational (Sign::Minus, l.sub (r))
                        } else {
                            GenericFraction::Rational (Sign::Plus, (r.sub (l)))
                        }
                    } else {
                        GenericFraction::Rational (Sign::Minus, l.add (r))
                    }
                }
            }
        }
    }
}



impl<T: Clone + Integer> AddAssign for GenericFraction<T> {
    fn add_assign (&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (ls) => {
                match other {
                    GenericFraction::NaN => GenericFraction::NaN,
                    GenericFraction::Rational (_, _) => GenericFraction::Infinity (ls),
                    GenericFraction::Infinity (rs) => if ls != rs { GenericFraction::NaN } else { GenericFraction::Infinity (ls) }
                }
            }
            GenericFraction::Rational (ls, ref mut l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (_) => other,
                GenericFraction::Rational (rs, r) => {
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    if ls == Sign::Plus && rs == Sign::Plus {
                        GenericFraction::Rational (Sign::Plus, l_.add (r))
                    } else if ls == Sign::Plus {
                        if l_ < r {
                            GenericFraction::Rational (Sign::Minus, r.sub (l_))
                        } else {
                            GenericFraction::Rational (Sign::Plus, l_.sub (r))
                        }
                    } else if rs == Sign::Plus {
                        if r < l_ {
                            GenericFraction::Rational (Sign::Minus, l_.sub (r))
                        } else {
                            GenericFraction::Rational (Sign::Plus, (r.sub (l_)))
                        }
                    } else {
                        GenericFraction::Rational (Sign::Minus, l_.add (r))
                    }
                }
            }
        };
    }
}



impl<T: Clone + Integer> Sub for GenericFraction<T> {
    type Output = Self;

    fn sub (self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity (sign) => {
                match other {
                    GenericFraction::NaN => other,
                    GenericFraction::Infinity (osign) => if sign == osign { GenericFraction::NaN } else { self },
                    GenericFraction::Rational (_, _) => self
                }
            }
            GenericFraction::Rational (ls, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (sign) => GenericFraction::Infinity (-sign),
                GenericFraction::Rational (rs, r) => {
                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l < r {
                            GenericFraction::Rational (Sign::Minus, r.sub (l))
                        } else {
                            GenericFraction::Rational (Sign::Plus, l.sub (r))
                        }
                    } else if ls == Sign::Plus {
                        GenericFraction::Rational (Sign::Plus, l.add (r))
                    } else if rs == Sign::Plus {
                        GenericFraction::Rational (Sign::Minus, l.add (r))
                    } else {
                        if l < r {
                            GenericFraction::Rational (Sign::Plus, r.sub (l))
                        } else {
                            GenericFraction::Rational (Sign::Minus, l.sub (r))
                        }
                    }
                }
            }
        }
    }
}



impl<T: Clone + Integer> SubAssign for GenericFraction<T> {
    fn sub_assign (&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (ls) => {
                match other {
                    GenericFraction::NaN => GenericFraction::NaN,
                    GenericFraction::Infinity (rs) => if ls == rs { GenericFraction::NaN } else { GenericFraction::Infinity (ls) },
                    GenericFraction::Rational (_, _) => GenericFraction::Infinity (ls)
                }
            }
            GenericFraction::Rational (ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (s) => GenericFraction::Infinity (-s),
                GenericFraction::Rational (rs, r) => {
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    if ls == Sign::Plus && rs == Sign::Plus {
                        if l_ < r {
                            GenericFraction::Rational (Sign::Minus, r.sub (l_))
                        } else {
                            GenericFraction::Rational (Sign::Plus, l_.sub (r))
                        }
                    } else if ls == Sign::Plus {
                        GenericFraction::Rational (Sign::Plus, l_.add (r))
                    } else if rs == Sign::Plus {
                        GenericFraction::Rational (Sign::Minus, l_.add (r))
                    } else {
                        if l_ < r {
                            GenericFraction::Rational (Sign::Plus, r.sub (l_))
                        } else {
                            GenericFraction::Rational (Sign::Minus, l_.sub (r))
                        }
                    }
                }
            }
        };
    }
}



impl<T: Clone + Integer> Mul for GenericFraction<T> {
    type Output = Self;

    fn mul (self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity (sign) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (osign) => GenericFraction::Infinity (if sign == osign { Sign::Plus } else { Sign::Minus }),
                GenericFraction::Rational (osign, l) => {
                    if l.is_zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if sign == osign { Sign::Plus } else { Sign::Minus })
                    }
                }
            },
            GenericFraction::Rational (sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (osign) => {
                    if l.is_zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if sign == osign { Sign::Plus } else { Sign::Minus })
                    }
                }
                GenericFraction::Rational (osign, r) => {
                    let s = if l.is_zero () || r.is_zero () {
                        Sign::Plus
                    } else if sign == osign {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };
                    GenericFraction::Rational (s, l.mul (r))
                }
            }
        }
    }
}



impl<T: Clone + Integer> MulAssign for GenericFraction<T> {
    fn mul_assign (&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (ls) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (rs) => GenericFraction::Infinity (if ls == rs { Sign::Plus } else { Sign::Minus }),
                GenericFraction::Rational (rs, r) => {
                    if r.is_zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
            },
            GenericFraction::Rational (ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (rs) => {
                    if l.is_zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
                GenericFraction::Rational (rs, r) => {
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    let s = if l_.is_zero () || r.is_zero () {
                        Sign::Plus
                    } else if ls == rs {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };

                    GenericFraction::Rational (s, l_.mul (r))
                }
            }
        };
    }
}



impl<T: Clone + Integer> Div for GenericFraction<T> {
    type Output = Self;

    fn div (self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity (sign) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (_) => GenericFraction::NaN,
                GenericFraction::Rational (osign, _) => GenericFraction::Infinity (if sign == osign { Sign::Plus } else { Sign::Minus })
            },
            GenericFraction::Rational (sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (_) => GenericFraction::Rational (Sign::Plus, Ratio::zero ()),
                GenericFraction::Rational (osign, r) => {
                    if l.is_zero () && r.is_zero () {
                        GenericFraction::NaN
                    } else if r.is_zero () {
                        GenericFraction::Infinity (sign)
                    } else if l.is_zero () {
                        GenericFraction::Rational (Sign::Plus, l)
                    } else {
                        GenericFraction::Rational (if sign == osign { Sign::Plus } else { Sign::Minus }, l / r)
                    }
                }
            }
        }
    }
}



impl<T: Clone + Integer> DivAssign for GenericFraction<T> {
    fn div_assign (&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (ls) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (_) => GenericFraction::NaN,
                GenericFraction::Rational (rs, _) => GenericFraction::Infinity (if ls == rs { Sign::Plus } else { Sign::Minus })
            },
            GenericFraction::Rational (ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (_) => GenericFraction::Rational (Sign::Plus, Ratio::zero ()),
                GenericFraction::Rational (rs, r) => {
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    if l_.is_zero () && r.is_zero () {
                        GenericFraction::NaN
                    } else if r.is_zero () {
                        GenericFraction::Infinity (ls)
                    } else if l_.is_zero () {
                        GenericFraction::Rational (Sign::Plus, l_)
                    } else {
                        GenericFraction::Rational (if ls == rs { Sign::Plus } else { Sign::Minus }, l_.div (r))
                    }
                }
            }
        };
    }
}



impl<T: Clone + Integer> Rem for GenericFraction<T> {
    type Output = Self;

    fn rem (self, other: Self) -> Self {
        match self {
            GenericFraction::NaN => self,
            GenericFraction::Infinity (_) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (_) => GenericFraction::NaN,
                GenericFraction::Rational (_, _) => GenericFraction::NaN
            },
            GenericFraction::Rational (sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (_) => GenericFraction::Rational (sign, l),
                GenericFraction::Rational (_, r) => {
                    if r.is_zero () {
                        GenericFraction::NaN
                    } else if l == r {
                        GenericFraction::Rational (Sign::Plus, Ratio::zero ())
                    } else {
                        GenericFraction::Rational (sign, l % r)
                    }
                }
            }
        }
    }
}



impl<T: Clone + Integer> RemAssign for GenericFraction<T> {
    fn rem_assign (&mut self, other: Self) {
        *self = match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (_) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (_) => GenericFraction::NaN,
                GenericFraction::Rational (_, _) => GenericFraction::NaN
            },
            GenericFraction::Rational (ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (_) => GenericFraction::Rational (ls, mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()))),
                GenericFraction::Rational (_, r) => {
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    if r.is_zero () {
                        GenericFraction::NaN
                    } else if l_ == r {
                        GenericFraction::Rational (Sign::Plus, Ratio::zero ())
                    } else {
                        GenericFraction::Rational (ls, l_.rem (r))
                    }
                }
            }
        };
    }
}



impl<T: Clone + Integer> Zero for GenericFraction<T> {
    fn zero() -> Self { GenericFraction::Rational (Sign::Plus, Ratio::zero ()) }

    fn is_zero(&self) -> bool {
        match *self {
            GenericFraction::Rational (_, ref r) => r.is_zero (),
            _ => false
        }
    }
}



impl<T: Clone + Integer> One for GenericFraction<T> {
    fn one() -> Self { GenericFraction::Rational (Sign::Plus, Ratio::one ()) }
}



impl<T: Clone + Integer> Num for GenericFraction<T> {
    type FromStrRadixErr = ParseRatioError;

    fn from_str_radix (str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        if str.starts_with ('-') {
            Ratio::from_str_radix (&str[1 ..], radix)
                .and_then (|ratio| Ok (GenericFraction::Rational (Sign::Minus, ratio)))
        } else if str.starts_with ('+') {
            Ratio::from_str_radix (&str[1 ..], radix)
                .and_then (|ratio| Ok (GenericFraction::Rational (Sign::Plus, ratio)))
        } else {
            Ratio::from_str_radix (str, radix)
                .and_then (|ratio| Ok (GenericFraction::Rational (Sign::Plus, ratio)))
        }
    }
}



impl<T: Clone + Integer> Signed for GenericFraction<T> {
    fn abs (&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (_) => GenericFraction::Infinity (Sign::Plus),
            GenericFraction::Rational (_, ref r) => GenericFraction::Rational (Sign::Plus, r.clone ())
        }
    }


    fn abs_sub(&self, other: &Self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (sign) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (osign) => if sign == Sign::Minus {
                    GenericFraction::zero ()
                } else {
                    if osign == Sign::Plus {
                        GenericFraction::zero ()
                    } else {
                        GenericFraction::Infinity (Sign::Plus)
                    }
                },
                GenericFraction::Rational (_, _) => if sign == Sign::Plus {
                    GenericFraction::Infinity (sign)
                } else {
                    GenericFraction::zero ()
                }
            },
            GenericFraction::Rational (sign, ref l) => match *other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (osign) => if osign == Sign::Plus {
                    GenericFraction::zero ()
                } else {
                    if sign == Sign::Minus {
                        GenericFraction::Infinity (Sign::Minus)
                    } else {
                        GenericFraction::Infinity (Sign::Plus)
                    }
                },
                GenericFraction::Rational (_, ref r) => {
                    if l < r {
                        GenericFraction::Rational (Sign::Plus, r - l)
                    } else {
                        GenericFraction::Rational (Sign::Plus, l - r)
                    }
                }
            }
        }
    }


    fn signum(&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (sign) => if sign == Sign::Plus {
                GenericFraction::Rational (Sign::Plus, Ratio::one ())
            } else {
                GenericFraction::Rational (Sign::Minus, Ratio::one ())
            },
            GenericFraction::Rational (sign, _) => if sign == Sign::Plus {
                GenericFraction::Rational (Sign::Plus, Ratio::one ())
            } else {
                GenericFraction::Rational (Sign::Minus, Ratio::one ())
            }
        }
    }


    fn is_positive(&self) -> bool {
        match *self {
            GenericFraction::NaN => false,
            GenericFraction::Infinity (sign) => if sign == Sign::Plus { true } else { false },
            GenericFraction::Rational (sign, _) => if sign == Sign::Plus { true } else { false }
        }
    }


    fn is_negative(&self) -> bool {
        match *self {
            GenericFraction::NaN => false,
            GenericFraction::Infinity (sign) => if sign == Sign::Minus { true } else { false },
            GenericFraction::Rational (sign, _) => if sign == Sign::Minus { true } else { false }
        }
    }
}



impl<T: Clone + Integer + PartialEq + ToPrimitive> ToPrimitive for GenericFraction<T> {
    fn to_i64 (&self) -> Option<i64> {
        match *self {
            GenericFraction::NaN => None,
            GenericFraction::Infinity (_) => None,
            GenericFraction::Rational (sign, ref r) if *r.denom () == T::one () => {
                if let Some (n) = r.numer ().to_i64 () {
                    if sign == Sign::Minus {
                        Some (-n)
                    } else {
                        Some (n)
                    }
                } else { None }
            },
            _ => None
        }
    }


    fn to_u64 (&self) -> Option<u64> {
        match *self {
            GenericFraction::NaN => None,
            GenericFraction::Infinity (_) => None,
            GenericFraction::Rational (sign, ref r) if *r.denom () == T::one () => {
                if sign == Sign::Minus {
                    None
                } else {
                    r.numer ().to_u64 ()
                }
            },
            _ => None
        }
    }


    fn to_f64 (&self) -> Option<f64> {
        match *self {
            GenericFraction::NaN => Some (f64::NAN),
            GenericFraction::Infinity (sign) => Some (if sign == Sign::Minus { f64::NEG_INFINITY } else { f64::INFINITY }),
            GenericFraction::Rational (sign, ref r) => r.numer ().to_f64 ()
                .and_then (|n| r.denom ().to_f64 ().map (|d| n / d))
                .map (|x| if sign == Sign::Minus { -x } else { x })
        }
    }
}



impl<T: Clone + Integer> /*Float for*/ GenericFraction<T> {
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
    pub fn nan () -> Self { GenericFraction::NaN }


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
    pub fn infinity () -> Self { GenericFraction::Infinity (Sign::Plus) }


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
    pub fn neg_infinity () -> Self { GenericFraction::Infinity (Sign::Minus) }


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
    pub fn neg_zero () -> Self { GenericFraction::Rational (Sign::Minus, Ratio::zero ()) }


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
    pub fn min_positive_value () -> Self where T: Bounded { GenericFraction::Rational (Sign::Plus, Ratio::new (T::one (), T::max_value ())) }


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
    pub fn is_nan (&self) -> bool { match *self { GenericFraction::NaN => true, _ => false } }


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
    pub fn is_infinite (&self) -> bool { match *self { GenericFraction::Infinity (_) => true, _ => false } }


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
    pub fn is_finite (&self) -> bool { match *self { GenericFraction::Infinity (_) => false, _ => true } }


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
    pub fn is_normal (&self) -> bool {
        match *self {
            GenericFraction::Rational (_, ref v) => !v.is_zero (),
            _ => false
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
            GenericFraction::Infinity (_) => FpCategory::Infinite,
            GenericFraction::Rational (_, ref v) if v.is_zero () => FpCategory::Zero,
            _ => FpCategory::Normal
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
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.floor ()),
            _ => self.clone ()
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
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.ceil ()),
            _ => self.clone ()
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
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.round ()),
            _ => self.clone ()
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
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.trunc ()),
            _ => self.clone ()
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
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.fract ()),
            _ => GenericFraction::NaN
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
            GenericFraction::Infinity (_) => GenericFraction::Infinity (Sign::Plus),
            GenericFraction::Rational (_, ref r) => GenericFraction::Rational (Sign::Plus, r.clone ())
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
            GenericFraction::Infinity (s) => if s == Sign::Plus {
                GenericFraction::Rational (Sign::Plus, Ratio::new (T::one (), T::one ()))
            } else {
                GenericFraction::Rational (Sign::Minus, Ratio::new (T::one (), T::one ()))
            },
            GenericFraction::Rational (s, _) => if s == Sign::Plus {
                GenericFraction::Rational (Sign::Plus, Ratio::new (T::one (), T::one ()))
            } else {
                GenericFraction::Rational (Sign::Minus, Ratio::new (T::one (), T::one ()))
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
            GenericFraction::Infinity (sign) => if sign == Sign::Plus { true } else { false },
            GenericFraction::Rational (sign, _) => if sign == Sign::Plus { true } else { false }
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
            GenericFraction::Infinity (sign) => if sign == Sign::Minus { true } else { false },
            GenericFraction::Rational (sign, _) => if sign == Sign::Minus { true } else { false }
        }
    }


    /// self.clone () * a + b
    ///
    /// Added for interface compatibility with float types
    pub fn mul_add(&self, a: Self, b: Self) -> Self { self.clone () * a + b }


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
            GenericFraction::Infinity (_) => GenericFraction::Rational (Sign::Plus, Ratio::new (T::zero (), T::one ())),
            GenericFraction::Rational (s, ref r) if r.is_zero () => GenericFraction::Infinity (s),
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.recip ())
        }
    }

    /* ... A lot of stuff here that has not been implemented for Ratio<T> ... */
}



impl<T: fmt::Display + Eq + One + Clone + Integer> fmt::Display for GenericFraction<T> {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            GenericFraction::NaN => write! (f, "NaN"),
            GenericFraction::Infinity (s) => write! (f, "{}{}", s, "inf"),
            GenericFraction::Rational (s, ref r) => write! (f, "{}{}", s, r)
        }
    }
}



macro_rules! generic_fraction_from_uint {
    ( $($from:ty),* ) => {
        $(
        impl<T: Clone + Integer> From<$from> for GenericFraction<T> where $from: Into<T> {
            fn from (val: $from) -> GenericFraction<T> {
                GenericFraction::Rational (Sign::Plus, Ratio::new (val.into (), T::one ()))
            }
        }
        )*
    }
}

generic_fraction_from_uint! (u8, u16, u32, u64, BigUint);



macro_rules! generic_fraction_from_int {
    ( $($from:ty),* ) => {
        $(
        impl<T: Clone + Integer> From<$from> for GenericFraction<T> {
            fn from (val: $from) -> GenericFraction<T> {
                let src = format! ("{:+}", val);

                let sign = if src.starts_with ('-') {
                    Sign::Minus
                } else if src.starts_with ('+') {
                    Sign::Plus
                } else {
                    return GenericFraction::NaN
                };

                let r: Result<GenericFraction<T>, T::FromStrRadixErr> = T::from_str_radix (&src[1 ..], 10)
                    .and_then (|t| Ok (GenericFraction::Rational (sign, Ratio::new (t, T::one ()))))
                    .or (Ok (GenericFraction::NaN));

                r.ok ().unwrap ()
            }
        }
        )*
    };
}

generic_fraction_from_int! (i8, i16, i32, i64, isize, usize);



macro_rules! generic_fraction_from_float {
    ( $($from:ty),*) => {
        $(
        impl<T: Clone + Integer + CheckedAdd + CheckedMul> From<$from> for GenericFraction<T> {
            fn from (val: $from) -> GenericFraction<T> {
                if val.is_nan () { return GenericFraction::NaN };
                if val.is_infinite () { return GenericFraction::Infinity (if val.is_sign_negative () { Sign::Minus } else { Sign::Plus }) };

                let src = format! ("{:+}", val);

                let sign = if src.starts_with ('-') {
                    Sign::Minus
                } else if src.starts_with ('+') {
                    Sign::Plus
                } else {
                    return GenericFraction::NaN
                };

                let dot = src.find ('.');
                let who = if dot.is_some () { &src[1 .. dot.unwrap ()] } else { &src[1 ..] };

                let num = T::from_str_radix (who, 10);
                if num.is_err () { return GenericFraction::NaN };

                let (fra, len) = if let Some (dot) = dot {
                    (T::from_str_radix (&src[dot + 1 ..], 10), src.len () - dot - 1)
                } else { (Ok (T::zero ()), 0) };
                if fra.is_err () { return GenericFraction::NaN };

                let mut num = num.ok ().unwrap ();
                let mut den = T::one ();

                if len > 0 {
                    let mut t10 = T::one ();
                    for _ in 0 .. 9 {
                        t10 = if let Some (t10) = t10.checked_add (&den) { t10 } else { return GenericFraction::NaN };
                    }

                    for _ in 0 .. len {
                        num = if let Some (num) = num.checked_mul (&t10) { num } else { return GenericFraction::NaN };
                        den = if let Some (den) = den.checked_mul (&t10) { den } else { return GenericFraction::NaN };
                    }
                }

                let fra = fra.ok ().unwrap ();
                let num = if let Some (num) = num.checked_add (&fra) { num } else { return GenericFraction::NaN };

                GenericFraction::Rational (sign, Ratio::new (num, den))
            }
        }
        )*
    };
}

generic_fraction_from_float! (f32, f64);



impl<T> From<BigInt> for GenericFraction<T>
    where
        T: Clone + Integer + From<BigUint>
{
    fn from (int: BigInt) -> Self {
        let (sign, numer) = match int.sign () {
            self::num::bigint::Sign::Minus => (Sign::Minus, int.abs ().to_biguint ().unwrap ()),
            _ => (Sign::Plus, int.to_biguint ().unwrap ())
        };

        let frac = GenericFraction::new (T::from (numer), T::one ());

        if sign == Sign::Minus { -frac } else { frac }
    }
}



impl<T, N, D> From<(N, D)> for GenericFraction<T>
    where
        T: Clone + Integer,
        N: fmt::Display,
        D: fmt::Display
{
    fn from (pair: (N, D)) -> GenericFraction<T> {
        let (num, den) = pair;

        let num = format! ("{:+}", num);

        let n_sign = if num.starts_with ('-') {
            Sign::Minus
        } else if num.starts_with ('+') {
            Sign::Plus
        } else {
            return GenericFraction::NaN
        };

        let n: Result<T, T::FromStrRadixErr> = T::from_str_radix (&num[1 ..], 10);

        if n.is_err () { return GenericFraction::NaN }


        let den = format! ("{:+}", den);

        let d_sign = if den.starts_with ('-') {
            Sign::Minus
        } else if den.starts_with ('+') {
            Sign::Plus
        } else {
            return GenericFraction::NaN
        };

        let d: Result<T, T::FromStrRadixErr> = T::from_str_radix (&den[1 ..], 10);

        if d.is_err () { return GenericFraction::NaN }

        GenericFraction::Rational (if n_sign == d_sign { Sign::Plus } else { Sign::Minus }, Ratio::new (n.ok ().unwrap (), d.ok ().unwrap ()))
    }
}




#[derive (Clone, Debug)]
enum Mint {
    I (u64),
    B (Option<BigUint>)
}



impl Mint {
    pub fn div_rem (&self, other: &Mint) -> (Mint, Mint) {
        match *self {
            Mint::I (s) => match *other {
                Mint::I (o) => (Mint::I (s / o), Mint::I (s % o)),
                Mint::B (Some (ref o)) => {
                    let (a, b) = BigUint::from (s).div_rem (o);
                    (Mint::B (Some (a)), Mint::B (Some (b)))
                }
                _ => unreachable! ()
            },
            Mint::B (Some (ref s)) => match *other {
                Mint::I (o) => {
                    let (a, b) = s.div_rem (&BigUint::from (o));
                    (Mint::B (Some (a)), Mint::B (Some (b)))
                }
                Mint::B (Some (ref o)) => {
                    let (a, b) = s.div_rem (o);
                    (Mint::B (Some (a)), Mint::B (Some (b)))
                },
                _ => unreachable! ()
            },
            _ => unreachable! ()
        }
    }

    fn is_i (&self) -> bool {
        match *self {
            Mint::I (_) => true,
            _ => false
        }
    }

    fn get_i (&self) -> u64 {
        match *self {
            Mint::I (v) => v,
            _ => unreachable! ()
        }
    }

    fn set_i (&mut self, val: u64) {
        match *self {
            Mint::I (ref mut v) => *v = val,
            _ => unreachable! ()
        }
    }

    fn take_b (&mut self) -> BigUint {
        match *self {
            Mint::B (ref mut v) => v.take ().unwrap (),
            _ => unreachable! ()
        }
    }
}



impl PartialOrd for Mint {
    fn partial_cmp (&self, other: &Mint) -> Option<Ordering> {
        match *self {
            Mint::I (s) => {
                match *other {
                    Mint::I (o) => s.partial_cmp (&o),
                    Mint::B (Some (ref o)) => BigUint::from (s).partial_cmp (o),
                    _ => unreachable! ()
                }
            }
            Mint::B (Some (ref s)) => {
                match *other {
                    Mint::I (o) => s.partial_cmp (&BigUint::from (o)),
                    Mint::B (Some (ref o)) => s.partial_cmp (o),
                    _ => unreachable! ()
                }
            }
            _ => unreachable! ()
        }
    }
}



impl PartialEq for Mint {
    fn eq (&self, other: &Mint) -> bool {
        match *self {
            Mint::I (s) => {
                match *other {
                    Mint::I (o) => s.eq (&o),
                    Mint::B (Some (ref o)) => BigUint::from (s).eq (o),
                    _ => unreachable! ()
                }
            }
            Mint::B (Some (ref s)) => {
                match *other {
                    Mint::I (o) => s.eq (&BigUint::from (o)),
                    Mint::B (Some (ref o)) => s.eq (o),
                    _ => unreachable! ()
                }
            }
            _ => unreachable! ()
        }
    }
}



impl Rem for Mint {
    type Output = Mint;

    fn rem (mut self, mut oth: Mint) -> Mint {
        if self.is_i () && oth.is_i () {
            if let Some (n) = self.get_i ().checked_rem (oth.get_i ()) {
                Mint::I (n)
            } else {
                let bi = BigUint::from (self.get_i ());
                Mint::B (Some (bi % BigUint::from (oth.get_i ())))
            }
        } else {
            let bi = self.take_b ();
            Mint::B (Some (bi % if oth.is_i () { BigUint::from (oth.get_i ()) } else { oth.take_b () }))
        }
    }
}



impl DivAssign<Mint> for Mint {
    fn div_assign (&mut self, mut oth: Mint) {
        if self.is_i () && oth.is_i () {
            if let Some (n) = self.get_i ().checked_div (oth.get_i ()) {
                self.set_i (n);
            } else {
                let mut bi = BigUint::from (self.get_i ());
                bi = bi / BigUint::from (oth.get_i ());
                *self = Mint::B (Some (bi));
            }
        } else {
            let mut bi = self.take_b ();
            bi = bi / if oth.is_i () { BigUint::from (oth.get_i ()) } else { oth.take_b () };
            *self = Mint::B (Some (bi));
        }
    }
}



impl MulAssign<Mint> for Mint {
    fn mul_assign (&mut self, mut oth: Mint) {
        if self.is_i () && oth.is_i () {
            if let Some (n) = self.get_i ().checked_mul (oth.get_i ()) {
                self.set_i (n);
            } else {
                let mut bi = BigUint::from (self.get_i ());
                bi = bi * BigUint::from (oth.get_i ());
                *self = Mint::B (Some (bi));
            }
        } else {
            let mut bi = self.take_b ();
            bi = bi * if oth.is_i () { BigUint::from (oth.get_i ()) } else { oth.take_b () };
            *self = Mint::B (Some (bi));
        }
    }
}



impl fmt::Display for Mint {
    fn fmt (&self, ftr: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Mint::I (ref v) => write! (ftr, "{}", v),
            Mint::B (ref v) => write! (ftr, "{}", v.as_ref ().unwrap ())
        }
    }
}



impl<T> From<T> for Mint
    where
        T: ToPrimitive + Into<BigUint>
{
    fn from (val: T) -> Self {
        if let Some (val) = val.to_u64 () {
            Mint::I (val.into ())
        } else {
            Mint::B (Some (val.into ()))
        }
    }
}




#[cfg (all (test, not (feature = "dev")))]
mod tests {
    use super::{ Fraction, BigFraction, GenericFraction, Sign };
    use super::num::{ BigInt, BigUint, Num, Zero };

    use std::collections::HashMap;


    type Frac = GenericFraction<u8>;


    #[test]
    fn op_add_assign () {
        let nan = Frac::nan ();
        let nin = Frac::neg_infinity ();
        let pin = Frac::infinity ();
        let nil = Frac::new (0, 1);
        let one = Frac::new (1, 1);

        let mut nan_ = Frac::nan ();
        nan_ += nan;
        assert_eq! (nan, nan_);

        nan_ += nin;
        assert_eq! (nan, nan_);

        nan_ += pin;
        assert_eq! (nan, nan_);

        nan_ += nil;
        assert_eq! (nan, nan_);

        let mut nil_ = nil;
        nil_ += nil_;
        assert_eq! (nil, nil_);

        nil_ += one;
        assert_eq! (one, nil_);
    }


    #[test]
    fn op_add () {
        let nan: Frac = GenericFraction::NaN;
        let ninf: Frac = GenericFraction::Infinity (Sign::Minus);
        let pinf: Frac = GenericFraction::Infinity (Sign::Plus);

        assert_eq! (nan, nan);
        assert_eq! (nan, nan + nan);
        assert_eq! (nan, nan + ninf);
        assert_eq! (nan, nan + pinf);
        assert_eq! (nan, ninf + nan);
        assert_eq! (nan, pinf + nan);

        assert_eq! (ninf, ninf + ninf);
        assert_eq! (pinf, pinf + pinf);
        assert_eq! (nan, ninf + pinf);
        assert_eq! (nan, pinf + ninf);


        let nil = Frac::new (0, 1);

        assert_eq! (nil, nil);
        assert_eq! (nil, nil + nil);
        assert_eq! (nan, nil + nan);
        assert_eq! (nan, nan + nil);
        assert_eq! (ninf, nil + ninf);
        assert_eq! (ninf, ninf + nil);
        assert_eq! (pinf, nil + pinf);
        assert_eq! (pinf, pinf + nil);


        let one = Frac::new (1, 1);

        assert_eq! (one, one);
        assert_eq! (one, one + nil);
        assert_eq! (one, nil + one);
        assert_eq! (nan, one + nan);
        assert_eq! (nan, nan + one);
        assert_eq! (ninf, one + ninf);
        assert_eq! (ninf, ninf + one);
        assert_eq! (pinf, one + pinf);
        assert_eq! (pinf, pinf + one);


        let two = Frac::new (2, 1);

        assert_eq! (two, two);
        assert_eq! (two, two + nil);
        assert_eq! (two, nil + two);
        assert_eq! (two, one + one);
        assert_eq! (nan, two + nan);
        assert_eq! (nan, nan + two);
        assert_eq! (ninf, two + ninf);
        assert_eq! (ninf, ninf + two);
        assert_eq! (pinf, two + pinf);
        assert_eq! (pinf, pinf + two);


        let mnil = -nil;

        assert_eq! (mnil, mnil);
        assert_eq! (mnil, nil);
        assert_eq! (mnil, nil + nil);
        assert_eq! (mnil, mnil + mnil);
        assert_eq! (mnil, mnil + nil);
        assert_eq! (mnil, nil + mnil);
        assert_eq! (nan, mnil + nan);
        assert_eq! (nan, nan + mnil);
        assert_eq! (ninf, mnil + ninf);
        assert_eq! (ninf, ninf + mnil);
        assert_eq! (pinf, mnil + pinf);
        assert_eq! (pinf, pinf + mnil);


        let mone = -one;

        assert_eq! (mone, mone);
        assert_eq! (mone, mone + nil);
        assert_eq! (mone, nil + mone);
        assert_eq! (nan, mone + nan);
        assert_eq! (nan, nan + mone);
        assert_eq! (nil, mone + one);
        assert_eq! (nil, one + mone);
        assert_eq! (one, mone + two);
        assert_eq! (one, two + mone);
        assert_eq! (nan, mone + nan);
        assert_eq! (nan, nan + mone);
        assert_eq! (ninf, mone + ninf);
        assert_eq! (ninf, ninf + mone);
        assert_eq! (pinf, mone + pinf);
        assert_eq! (pinf, pinf + mone);


        let mtwo = -two;

        assert_eq! (mtwo, mtwo);
        assert_eq! (mtwo, mtwo + nil);
        assert_eq! (mtwo, nil + mtwo);
        assert_eq! (mtwo, mtwo + mnil);
        assert_eq! (mtwo, mnil + mtwo);
        assert_eq! (mone, mtwo + one);
        assert_eq! (mone, one + mtwo);
        assert_eq! (nil, mtwo + two);
        assert_eq! (nil, two + mtwo);
        assert_eq! (nan, mtwo + nan);
        assert_eq! (nan, nan + mtwo);
        assert_eq! (ninf, mtwo + ninf);
        assert_eq! (ninf, ninf + mtwo);
        assert_eq! (pinf, mtwo + pinf);
        assert_eq! (pinf, pinf + mtwo);
    }


    #[test]
    fn op_sub () {
        let nan: Frac = GenericFraction::NaN;
        let ninf: Frac = GenericFraction::Infinity (Sign::Minus);
        let pinf: Frac = GenericFraction::Infinity (Sign::Plus);

        assert_eq! (nan, nan);
        assert_eq! (nan, nan - nan);
        assert_eq! (nan, nan - ninf);
        assert_eq! (nan, nan - pinf);
        assert_eq! (nan, ninf - nan);
        assert_eq! (nan, pinf - nan);

        assert_eq! (nan, ninf - ninf);
        assert_eq! (nan, pinf - pinf);
        assert_eq! (pinf, pinf - ninf);
        assert_eq! (ninf, ninf - pinf);


        let nil = Frac::new (0, 1);

        assert_eq! (nil, nil);
        assert_eq! (nil, nil - nil);
        assert_eq! (nan, nil - nan);
        assert_eq! (nan, nan - nil);
        assert_eq! (pinf, nil - ninf);
        assert_eq! (ninf, ninf - nil);
        assert_eq! (ninf, nil - pinf);
        assert_eq! (pinf, pinf - nil);


        let one = Frac::new (1, 1);
        let two = Frac::new (2, 1);

        let mone = -one;
        let mtwo = -two;

        assert_eq! (one, one);
        assert_eq! (one, one - nil);
        assert_eq! (mone, nil - one);
        assert_eq! (nan, one - nan);
        assert_eq! (nan, nan - one);
        assert_eq! (pinf, one - ninf);
        assert_eq! (ninf, ninf - one);
        assert_eq! (ninf, one - pinf);
        assert_eq! (pinf, pinf - one);
        assert_eq! (two, one - mone);
        assert_eq! (mtwo, mone - one);
    }


    #[test]
    fn op_mul () {
        let nan: Frac = GenericFraction::NaN;
        let ninf: Frac = GenericFraction::Infinity (Sign::Minus);
        let pinf: Frac = GenericFraction::Infinity (Sign::Plus);

        assert_eq! (nan, nan);
        assert_eq! (nan, nan * nan);
        assert_eq! (nan, nan * ninf);
        assert_eq! (nan, nan * pinf);
        assert_eq! (nan, ninf * nan);
        assert_eq! (nan, pinf * nan);

        assert_eq! (pinf, ninf * ninf);
        assert_eq! (pinf, pinf * pinf);
        assert_eq! (ninf, pinf * ninf);
        assert_eq! (ninf, ninf * pinf);


        let nil = Frac::new (0, 1);

        assert_eq! (nil, nil);
        assert_eq! (nil, nil * nil);
        assert_eq! (nan, nil * nan);
        assert_eq! (nan, nan * nil);
        assert_eq! (nan, nil * ninf);
        assert_eq! (nan, ninf * nil);
        assert_eq! (nan, nil * pinf);
        assert_eq! (nan, pinf * nil);


        let one = Frac::new (1, 1);

        assert_eq! (one, one);
        assert_eq! (nil, one * nil);
        assert_eq! (nil, nil * one);
        assert_eq! (nan, one * nan);
        assert_eq! (nan, nan * one);
        assert_eq! (ninf, one * ninf);
        assert_eq! (ninf, ninf * one);
        assert_eq! (pinf, one * pinf);
        assert_eq! (pinf, pinf * one);


        let two = Frac::new (2, 1);

        assert_eq! (two, two);
        assert_eq! (nil, two * nil);
        assert_eq! (nil, nil * two);
        assert_eq! (one, one * one);
        assert_eq! (nan, two * nan);
        assert_eq! (nan, nan * two);
        assert_eq! (ninf, two * ninf);
        assert_eq! (ninf, ninf * two);
        assert_eq! (pinf, two * pinf);
        assert_eq! (pinf, pinf * two);


        let mone = -one;
        let mtwo = -two;

        assert_eq! (mone, mone);
        assert_eq! (nil, mone * nil);
        assert_eq! (nil, nil * mone);
        assert_eq! (nan, mone * nan);
        assert_eq! (nan, nan * mone);
        assert_eq! (mone, mone * one);
        assert_eq! (mone, one * mone);
        assert_eq! (mtwo, mone * two);
        assert_eq! (mtwo, two * mone);
        assert_eq! (nan, mtwo * nan);
        assert_eq! (nan, nan * mtwo);
        assert_eq! (pinf, mone * ninf);
        assert_eq! (pinf, ninf * mone);
        assert_eq! (ninf, mone * pinf);
        assert_eq! (ninf, pinf * mone);
    }


    #[test]
    fn op_div () {
        let nan: Frac = GenericFraction::NaN;
        let ninf: Frac = GenericFraction::Infinity (Sign::Minus);
        let pinf: Frac = GenericFraction::Infinity (Sign::Plus);

        assert_eq! (nan, nan);
        assert_eq! (nan, nan / nan);
        assert_eq! (nan, nan / ninf);
        assert_eq! (nan, nan / pinf);
        assert_eq! (nan, ninf / nan);
        assert_eq! (nan, pinf / nan);

        assert_eq! (nan, ninf / ninf);
        assert_eq! (nan, pinf / pinf);
        assert_eq! (nan, pinf / ninf);
        assert_eq! (nan, ninf / pinf);


        let nil = Frac::new (0, 1);

        assert_eq! (nil, nil);
        assert_eq! (nan, nil / nil);
        assert_eq! (nan, nil / nan);
        assert_eq! (nan, nan / nil);
        assert_eq! (nil, nil / ninf);
        assert_eq! (ninf, ninf / nil);
        assert_eq! (nil, nil / pinf);
        assert_eq! (pinf, pinf / nil);


        let one = Frac::new (1, 1);

        assert_eq! (one, one);
        assert_eq! (one, one / one);
        assert_eq! (pinf, one / nil);
        assert_eq! (nil, nil / one);
        assert_eq! (nan, one / nan);
        assert_eq! (nan, nan / one);
        assert_eq! (nil, one / ninf);
        assert_eq! (ninf, ninf / one);
        assert_eq! (nil, one / pinf);
        assert_eq! (pinf, pinf / one);


        let two = Frac::new (2, 1);

        assert_eq! (two, two);
        assert_eq! (pinf, two / nil);
        assert_eq! (nil, nil / two);
        assert_eq! (nan, two / nan);
        assert_eq! (nan, nan / two);
        assert_eq! (nil, two / ninf);
        assert_eq! (ninf, ninf / two);
        assert_eq! (nil, two / pinf);
        assert_eq! (pinf, pinf / two);


        let mone = -one;
        let mtwo = -two;

        assert_eq! (mone, mone);

        assert_eq! (ninf, mone / nil);
        assert_eq! (nil, nil / mone);
        assert_eq! (nan, mone / nan);
        assert_eq! (nan, nan / mone);
        assert_eq! (mone, mone / one);
        assert_eq! (mone, one / mone);
        assert_eq! (-Frac::new (1, 2), mone / two);
        assert_eq! (mtwo, two / mone);
        assert_eq! (nan, mtwo / nan);
        assert_eq! (nan, nan / mtwo);
        assert_eq! (nil, mone / ninf);
        assert_eq! (pinf, ninf / mone);
        assert_eq! (nil, mone / pinf);
        assert_eq! (ninf, pinf / mone);
    }


    #[test]
    fn op_rem () {
        let nan: Frac = GenericFraction::NaN;
        let ninf: Frac = GenericFraction::Infinity (Sign::Minus);
        let pinf: Frac = GenericFraction::Infinity (Sign::Plus);

        assert_eq! (nan, nan);
        assert_eq! (nan, nan % nan);
        assert_eq! (nan, nan % ninf);
        assert_eq! (nan, nan % pinf);
        assert_eq! (nan, ninf % nan);
        assert_eq! (nan, pinf % nan);

        assert_eq! (nan, ninf % ninf);
        assert_eq! (nan, pinf % pinf);
        assert_eq! (nan, pinf % ninf);
        assert_eq! (nan, ninf % pinf);


        let nil = Frac::new (0, 1);

        assert_eq! (nil, nil);
        assert_eq! (nan, nil % nil);
        assert_eq! (nan, nil % nan);
        assert_eq! (nan, nan % nil);
        assert_eq! (nil, nil % ninf);
        assert_eq! (nan, ninf % nil);
        assert_eq! (nil, nil % pinf);
        assert_eq! (nan, pinf % nil);


        let one = Frac::new (1, 1);

        assert_eq! (one, one);
        assert_eq! (nil, one % one);
        assert_eq! (nan, one % nil);
        assert_eq! (nil, nil % one);
        assert_eq! (nan, one % nan);
        assert_eq! (nan, nan % one);
        assert_eq! (one, one % ninf);
        assert_eq! (nan, ninf % one);
        assert_eq! (one, one % pinf);
        assert_eq! (nan, pinf % one);


        let two = Frac::new (2, 1);

        assert_eq! (two, two);
        assert_eq! (nan, two % nil);
        assert_eq! (nil, nil % two);
        assert_eq! (nan, two % nan);
        assert_eq! (nan, nan % two);
        assert_eq! (two, two % ninf);
        assert_eq! (nan, ninf % two);
        assert_eq! (two, two % pinf);
        assert_eq! (nan, pinf % two);


        let mone = -one;
        let mtwo = -two;

        assert_eq! (mone, mone);

        assert_eq! (nan, mone % nil);
        assert_eq! (nil, nil % mone);
        assert_eq! (nan, mone % nan);
        assert_eq! (nan, nan % mone);
        assert_eq! (nil, mone % one);
        assert_eq! (nil, one % mone);
        assert_eq! (mone, mone % two);
        assert_eq! (nil, two % mone);
        assert_eq! (nan, mtwo % nan);
        assert_eq! (nan, nan % mtwo);
        assert_eq! (mone, mone % ninf);
        assert_eq! (nan, ninf % mone);
        assert_eq! (mone, mone % pinf);
        assert_eq! (nan, pinf % mone);
    }


    #[test]
    fn op_ord () {
        let pin = Frac::infinity ();
        let nin = Frac::neg_infinity ();
        let nil = Frac::zero ();

        let a = Frac::new (3, 4);
        let b = Frac::new (5, 7);

        assert! (a > b);
        assert! (a > nil);
        assert! (b > nil);
        assert! (nin < nil);
        assert! (nil < pin);
    }


    #[test]
    fn from_i8 () {
        let f = Fraction::from (-2i8);
        assert_eq! (Sign::Minus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (0i8);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2i8);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_u8 () {
        let f = Fraction::from (0u8);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2u8);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_i16 () {
        let f = Fraction::from (-2i16);
        assert_eq! (Sign::Minus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (0i16);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2i16);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_u16 () {
        let f = Fraction::from (0u16);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2u16);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_i32 () {
        let f = Fraction::from (-2i32);
        assert_eq! (Sign::Minus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (0i32);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2i32);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_u32 () {
        let f = Fraction::from (0u32);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2u32);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_i64 () {
        let f = Fraction::from (-2i64);
        assert_eq! (Sign::Minus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (0i64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2i64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_u64 () {
        let f = Fraction::from (0u64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2u64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_isize () {
        let f = Fraction::from (-2isize);
        assert_eq! (Sign::Minus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (0isize);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2isize);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_usize () {
        let f = Fraction::from (0usize);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (2usize);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (2, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_f64 () {
        let f = Fraction::from (0f64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (0, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());

        let f = Fraction::from (0.01f64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (1, *f.numer ().unwrap ());
        assert_eq! (100, *f.denom ().unwrap ());

        let f = Fraction::from (-0.01f64);
        assert_eq! (Sign::Minus, *f.sign ().unwrap ());
        assert_eq! (1, *f.numer ().unwrap ());
        assert_eq! (100, *f.denom ().unwrap ());

        let f = Fraction::from (1658425342060f64);
        assert_eq! (Sign::Plus, *f.sign ().unwrap ());
        assert_eq! (1658425342060u64, *f.numer ().unwrap ());
        assert_eq! (1, *f.denom ().unwrap ());
    }


    #[test]
    fn from_insanity () {
        let number = "2062065394209534095362056240654064520645230645230645230645230645206452064520645203642530940959212130935957";
        let fraction = format! ("{}/1", number);
        let f = BigFraction::from_str_radix (&fraction, 10);
        assert! (f.is_ok ());
        let f = f.ok ().unwrap ();
        assert_eq! (BigUint::from_str_radix (&number, 10).ok ().unwrap (), *f.numer ().unwrap ());
        assert_eq! (BigUint::from (1u8), *f.denom ().unwrap ());
    }


    #[test]
    fn from_bigint () {
        let number = BigInt::from (42);
        let frac = BigFraction::from (number);

        assert_eq! (frac, BigFraction::from ((42, 1)));


        let number = BigInt::from (-44);
        let frac = BigFraction::from (number);

        assert_eq! (frac, -BigFraction::from ((44, 1)));
    }


    #[test]
    fn from_biguint () {
        let number = BigUint::from (42u32);
        let frac = BigFraction::from (number);

        assert_eq! (frac, BigFraction::from ((42, 1)));
    }


    #[test]
    fn hashy () {
        let f = Fraction::from (0.75);

        let mut map: HashMap<Fraction, ()> = HashMap::new ();

        map.insert (f, ());

        assert! (map.contains_key (&Fraction::new (3u8, 4u8)));     // 0.75 == 3/4
        assert! (map.contains_key (&Fraction::new (6u16, 8u16)));   // 0.75 == 6/8
        assert! (map.contains_key (&Fraction::new (12u32, 16u32))); // 0.75 == 12/16
        assert! (map.contains_key (&Fraction::new (24u64, 32u64))); // 0.75 == 24/32
        assert! (map.contains_key (&Fraction::new (48u8, 64u16)));  // 0.75 == 48/64

        assert! (map.contains_key (&Fraction::from ( (3i8, 4i8) )));
        assert! (map.contains_key (&Fraction::from ( (6i16, 8i16) )));
        assert! (map.contains_key (&Fraction::from ( (12i32, 16i32) )));
        assert! (map.contains_key (&Fraction::from ( (24i64, 32i64) )));
        assert! (map.contains_key (&Fraction::from ( (48i8, 64i16) )));

        assert! (! map.contains_key (&Fraction::from (0.5))); // 0.75 != 1/2
    }


    #[test]
    fn into_big () {
        let f1 = Fraction::from (0.75);
        let b1 = f1.into_big ();

        let f2 = Frac::from (0.75);
        let b2 = f2.into_big ();

        let b3 = BigFraction::from (0.75);

        assert_eq! (b1, b2);
        assert_eq! (b2, b3);
        assert_eq! (b1, b3);
    }


    #[test]
    fn format_as_float () {
        use std::f32;

        let f1 = Frac::from (0.75);
        let fmt1 = f1.format_as_float ();

        assert! (fmt1.is_some ());
        assert_eq! ("0.75", fmt1.unwrap ());


        let f2 = Fraction::from ((33, 100));
        let fmt2 = f2.format_as_float ();

        assert! (fmt2.is_some ());
        assert_eq! ("0.33", fmt2.unwrap ());


        let f3 = Fraction::new (456u64, 10000000000u64);
        let fmt3 = f3.format_as_float ();

        assert! (fmt3.is_some ());
        assert_eq! ("0.0000000456", fmt3.unwrap ());


        let f4 = Fraction::from (f32::INFINITY);
        let fmt4 = f4.format_as_float ();

        assert! (fmt4.is_some ());
        assert_eq! ("inf", fmt4.unwrap ());


        let f5 = Fraction::from (f32::NEG_INFINITY);
        let fmt5 = f5.format_as_float ();

        assert! (fmt5.is_some ());
        assert_eq! ("-inf", fmt5.unwrap ());


        let f6 = Fraction::from (f32::NAN);
        let fmt6 = f6.format_as_float ();

        assert! (fmt6.is_some ());
        assert_eq! ("NaN", fmt6.unwrap ());


        let f7 = BigFraction::new (
            BigUint::from (42u8),
            BigUint::from (1000000000000000u64)
            * BigUint::from (1000000000000000u64)
            * BigUint::from (1000000000000000u64)
        );
        let fmt7 = f7.format_as_float ();

        assert! (fmt7.is_some ());
        assert_eq! ("0.000000000000000000000000000000000000000000042", fmt7.unwrap ());
    }


    #[test]
    fn comparison () {
        assert_eq! (Frac::zero (), Frac::zero ());
        assert_eq! (Frac::zero (), Frac::neg_zero ());
        assert_eq! (Frac::from (0), Frac::zero ());
        assert_eq! (Frac::from (0), Frac::neg_zero ());
        assert_eq! (Frac::from (0.5), Frac::new (1u8, 2u8));
        assert_eq! (Frac::from (-0.5), Frac::new_neg (1u8, 2u8));
        assert_ne! (Frac::from (-0.5), Frac::new (1u8, 2u8));

        assert! (! (Frac::zero () < Frac::neg_zero ()));
        assert! (! (Frac::neg_zero () < Frac::zero ()));

        assert! (! (Frac::zero () > Frac::neg_zero ()));
        assert! (! (Frac::neg_zero () > Frac::zero ()));

        assert! (Frac::neg_zero () < Frac::new (1u8, 2u8));
        assert! (! (Frac::neg_zero () > Frac::new (1u8, 2u8)));

        assert! (Frac::zero () < Frac::new (1u8, 2u8));
        assert! (! (Frac::zero () > Frac::new (1u8, 2u8)));

        assert! (Frac::new_neg (1u8, 2u8) < Frac::neg_zero ());
        assert! (Frac::new_neg (1u8, 2u8) < Frac::zero ());

        assert! (! (Frac::new_neg (1u8, 2u8) > Frac::neg_zero ()));
        assert! (! (Frac::new_neg (1u8, 2u8) > Frac::zero ()));

        assert_eq! (Frac::new (1u8, 2u8), Frac::new (1u8, 2u8));
        assert_eq! (Frac::new_neg (1u8, 2u8), Frac::new_neg (1u8, 2u8));

        assert! (Frac::new_neg (1u8, 2u8) < Frac::new (1u8, 2u8));
        assert! (! (Frac::new (1u8, 2u8) < Frac::new_neg (1u8, 2u8)));
        assert! (! (Frac::new_neg (1u8, 2u8) < Frac::new_neg (1u8, 2u8)));
        assert! (Frac::new_neg (1u8, 2u8) < Frac::new_neg (1u8, 4u8));

        assert! (Frac::new_neg (1u8, 2u8) < Frac::neg_zero ());
        assert! (Frac::new_neg (1u8, 2u8) < Frac::zero ());
        assert! (! (Frac::neg_zero () < Frac::new_neg (1u8, 2u8)));
        assert! (! (Frac::zero () < Frac::new_neg (1u8, 2u8)));
        assert! (Frac::neg_zero () < Frac::new (1u8, 2u8));
        assert! (Frac::neg_zero () > Frac::new_neg (1u8, 2u8));
        assert! (Frac::zero () > Frac::new_neg (1u8, 2u8));
        assert! (Frac::new (1u8, 2u8) > Frac::neg_zero ());
        assert! (! (Frac::new (1u8, 2u8) < Frac::neg_zero ()));
        assert! (Frac::zero () < Frac::new (1u8, 2u8));
    }
}

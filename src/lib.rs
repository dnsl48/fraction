extern crate num;

use self::num::rational::{Ratio, ParseRatioError};
use self::num::traits::{/*Float, */Bounded, Zero, One, Signed, Num, ToPrimitive, CheckedMul, CheckedAdd};
use self::num::integer::Integer;
use self::num::bigint::BigUint;

use std::num::FpCategory;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub, AddAssign, DivAssign, MulAssign, RemAssign, SubAssign};
use std::cmp::{Eq, PartialEq, PartialOrd, Ordering};

use std::f64;
use std::fmt;
use std::mem;



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




#[derive (Copy, Clone, Hash, Debug)]
pub enum GenericFraction<T> {
    Rational (Sign, Ratio<T>),
    Infinity (Sign),
    NaN
}


pub type Fraction = GenericFraction<u64>;
pub type BigFraction = GenericFraction<BigUint>;



impl BigFraction {
    pub fn format_as_float (&self) -> Option<String> {
        let a = self.numer ().unwrap ();
        let b = self.denom ().unwrap ();

        let (f, r) = a.div_rem (&b);

        let mut x: BigUint = BigUint::from (1u8);
        let bi10 = BigUint::from (10u8);
        let bi0 = BigUint::zero ();

        let mut limit = 0;

        loop {
            limit += 1;
            if limit > 1000 { // TODO: do something with bad numbers here (eg 3/4)
                if let Some (a) = a.to_f64 () {
                    if let Some (b) = b.to_f64 () {
                        return Some (format! ("{}", a / b));
                    }
                }
                return None
            }
            x = x * bi10.clone ();
            if x < *b { continue; }
            if x.clone () % b.clone () == bi0 { break; }
        }

        let l = r * (x / b);

        Some (format! ("{}.{}", f, l))
    }
}



impl<T: Clone + Integer> GenericFraction<T> {
    pub fn new<S> (num: S, den: S) -> GenericFraction<T> where S: fmt::Display {
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


    pub fn new_from<S> (num: S, den: S) -> GenericFraction<T> where T: From<S> {
        let num = T::from (num);
        let den = T::from (den);
        let nil = T::zero ();
        let sig = if num < nil { Sign::Minus } else { Sign::Plus };

        if den == nil {
            GenericFraction::Infinity (sig)
        } else {
            GenericFraction::Rational (sig, Ratio::new (num, den))
        }
    }


    pub fn new_raw (num: T, den: T) -> GenericFraction<T> {
        let nil = T::zero ();
        let sig = if num < nil { Sign::Minus } else { Sign::Plus };

        if den == nil {
            GenericFraction::Infinity (sig)
        } else {
            GenericFraction::Rational (sig, Ratio::new_raw (num, den))
        }
    }


    pub fn numer (&self) -> Option<&T> {
        match *self {
            GenericFraction::Rational (_, ref r) => Some (r.numer ()),
            _ => None
        }
    }


    pub fn denom (&self) -> Option<&T> {
        match *self {
            GenericFraction::Rational (_, ref r) => Some (r.denom ()),
            _ => None
        }
    }


    pub fn sign (&self) -> Option<&Sign> {
        match *self {
            GenericFraction::Rational (ref s, _) => Some (s),
            _ => None
        }
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
                GenericFraction::Rational (ref rs, ref r) => ls == rs && l.eq (r),
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
                        l.partial_cmp (r)
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
                if r == Ratio::zero () {
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
                    if l == Ratio::zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if sign == osign { Sign::Plus } else { Sign::Minus })
                    }
                }
            },
            GenericFraction::Rational (sign, l) => match other {
                GenericFraction::NaN => other,
                GenericFraction::Infinity (osign) => {
                    if l == Ratio::zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if sign == osign { Sign::Plus } else { Sign::Minus })
                    }
                }
                GenericFraction::Rational (osign, r) => {
                    let z = Ratio::zero ();
                    let s = if l == z || r == z {
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
                    if r == Ratio::zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
            },
            GenericFraction::Rational (ls, ref mut l) => match other {
                GenericFraction::NaN => GenericFraction::NaN,
                GenericFraction::Infinity (rs) => {
                    if *l == Ratio::zero () {
                        GenericFraction::NaN
                    } else {
                        GenericFraction::Infinity (if ls == rs { Sign::Plus } else { Sign::Minus })
                    }
                }
                GenericFraction::Rational (rs, r) => {
                    let z = Ratio::zero ();
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    let s = if l_ == z || r == z {
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
                    let z = Ratio::zero ();

                    if l == z && r == z {
                        GenericFraction::NaN
                    } else if r == z {
                        GenericFraction::Infinity (sign)
                    } else if l == z {
                        GenericFraction::Rational (Sign::Plus, z)
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
                    let z = Ratio::zero ();
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    if l_ == z && r == z {
                        GenericFraction::NaN
                    } else if r == z {
                        GenericFraction::Infinity (ls)
                    } else if l_ == z {
                        GenericFraction::Rational (Sign::Plus, z)
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
                    let z = Ratio::zero ();

                    if r == z {
                        GenericFraction::NaN
                    } else if l == r {
                        GenericFraction::Rational (Sign::Plus, z)
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
                    let z = Ratio::zero ();
                    let l_ = mem::replace (l, Ratio::new_raw (T::zero (), T::zero ()));

                    if r == z {
                        GenericFraction::NaN
                    } else if l_ == r {
                        GenericFraction::Rational (Sign::Plus, z)
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
    pub fn nan () -> Self { GenericFraction::NaN }

    pub fn infinity () -> Self { GenericFraction::Infinity (Sign::Plus) }

    pub fn neg_infinity () -> Self { GenericFraction::Infinity (Sign::Minus) }

    pub fn neg_zero () -> Self { GenericFraction::Rational (Sign::Plus, Ratio::new (T::zero (), T::one ())) }

    pub fn min_positive_value () -> Self where T: Bounded { GenericFraction::Rational (Sign::Plus, Ratio::new (T::one (), T::max_value ())) }

    pub fn is_nan (&self) -> bool { match *self { GenericFraction::NaN => true, _ => false } }

    pub fn is_infinite (&self) -> bool { match *self { GenericFraction::Infinity (_) => true, _ => false } }

    pub fn is_finite (&self) -> bool { match *self { GenericFraction::Infinity (_) => false, _ => true } }

    pub fn is_normal (&self) -> bool {
        match *self {
            GenericFraction::Rational (_, ref v) => !v.is_zero (),
            _ => false
        }
    }


    pub fn classify(&self) -> FpCategory {
        match *self {
            GenericFraction::NaN => FpCategory::Nan,
            GenericFraction::Infinity (_) => FpCategory::Infinite,
            GenericFraction::Rational (_, ref v) if v.is_zero () => FpCategory::Zero,
            _ => FpCategory::Normal
        }
    }


    pub fn floor(&self) -> Self {
        match *self {
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.floor ()),
            _ => self.clone ()
        }
    }


    pub fn ceil(&self) -> Self {
        match *self {
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.ceil ()),
            _ => self.clone ()
        }
    }


    pub fn round(&self) -> Self {
        match *self {
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.round ()),
            _ => self.clone ()
        }
    }


    pub fn trunc(&self) -> Self {
        match *self {
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.trunc ()),
            _ => self.clone ()
        }
    }


    pub fn fract(&self) -> Self {
        match *self {
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.fract ()),
            _ => GenericFraction::NaN
        }
    }


    pub fn abs(&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (_) => GenericFraction::Infinity (Sign::Plus),
            GenericFraction::Rational (_, ref r) => GenericFraction::Rational (Sign::Plus, r.clone ())
        }
    }


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


    pub fn is_sign_positive(&self) -> bool {
        match *self {
            GenericFraction::NaN => false,
            GenericFraction::Infinity (sign) => if sign == Sign::Plus { true } else { false },
            GenericFraction::Rational (sign, _) => if sign == Sign::Plus { true } else { false }
        }
    }


    pub fn is_sign_negative(&self) -> bool {
        match *self {
            GenericFraction::NaN => false,
            GenericFraction::Infinity (sign) => if sign == Sign::Minus { true } else { false },
            GenericFraction::Rational (sign, _) => if sign == Sign::Minus { true } else { false }
        }
    }


    pub fn mul_add(&self, a: Self, b: Self) -> Self { self.clone () * a + b }


    pub fn recip(&self) -> Self {
        match *self {
            GenericFraction::NaN => GenericFraction::NaN,
            GenericFraction::Infinity (_) => GenericFraction::Rational (Sign::Plus, Ratio::new (T::zero (), T::one ())),
            GenericFraction::Rational (s, ref r) => GenericFraction::Rational (s, r.recip ())
        }
    }

    /* ... A lot of stuff here that has not been implemented for Ratio<T> ... */
}



impl<T: fmt::Display + Eq + One> fmt::Display for GenericFraction<T> {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            GenericFraction::NaN => write! (f, "NaN"),
            GenericFraction::Infinity (s) => write! (f, "{}{}", s, "inf"),
            GenericFraction::Rational (s, ref r) => write! (f, "{}{}", s, r)
        }
    }
}




macro_rules! generic_fraction_from_int {
    ($from:ty) => {

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

    };
}


generic_fraction_from_int! (i8);
generic_fraction_from_int! (u8);
generic_fraction_from_int! (i16);
generic_fraction_from_int! (u16);
generic_fraction_from_int! (i32);
generic_fraction_from_int! (u32);
generic_fraction_from_int! (i64);
generic_fraction_from_int! (u64);
generic_fraction_from_int! (isize); 
generic_fraction_from_int! (usize);



macro_rules! generic_fraction_from_float {
    ($from:ty) => {

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

    };
}


generic_fraction_from_float! (f32);
generic_fraction_from_float! (f64);



#[cfg (all (test, not (feature = "dev")))]
mod tests {
    use super::{Fraction, BigFraction, GenericFraction, Sign};
    use super::num::{BigUint, Num, Zero};

    use std::collections::HashMap;


    #[test]
    fn op_add_assign () {
        type Frac = GenericFraction<u8>;

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
        type Frac = GenericFraction<u8>;

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
        type Frac = GenericFraction<u8>;

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
        type Frac = GenericFraction<u8>;

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
        type Frac = GenericFraction<u8>;

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
        type Frac = GenericFraction<u8>;

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
        type Frac = GenericFraction<u8>;

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
    fn hashy () {
        let f = Fraction::from (0.75);

        let mut map: HashMap<Fraction, ()> = HashMap::new ();

        map.insert (f, ());

        assert! (map.contains_key (&Fraction::new (3, 4)));   // 0.75 == 3/4
        assert! (map.contains_key (&Fraction::new (6, 8)));   // 0.75 == 6/8
        assert! (map.contains_key (&Fraction::new (12, 16))); // 0.75 == 12/16
        assert! (! map.contains_key (&Fraction::from (0.5))); // 0.75 != 1/2
    }
}

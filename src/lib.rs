//! # Fraction and its arithmetic
//!
//! The main goal of Fraction is keeping precision that floats cannot do.
//!
//! Fractions do not lose information about numbers and thus can be used for matching, comparisons and hashing (key values for HashMaps).
//!
//! Base arithmetic operators are also available (+ - / *), even though they work slower than for native numbers.
//!
//! Overflow checks are being performed for every arithmetic operation, so that Fraction becomes infinite, negative_infinite or NaN.
//!
//! # Examples
//!
//! ## Simple arithmetic
//! ```
//! use fraction::Fraction;
//!
//! fn main () {
//!     let mut fr = Fraction::zero ();
//!
//!     fr = fr + Fraction::from (2);   // 0 + 2   = 2
//!     fr = fr / Fraction::from (0.5); // 2 / 0.5 = 4
//!
//!     assert_eq! (fr, Fraction::from (4));
//! }
//! ```
//!
//! ## Using as keys for a HashMap
//! ```
//! use std::collections::HashMap;
//! use fraction::Fraction;
//!
//! fn main () {
//!     let f = Fraction::from (0.75);
//!
//!     let mut map: HashMap<Fraction, ()> = HashMap::new ();
//!
//!     map.insert (f, ());
//!
//!     assert! (map.contains_key (&Fraction::new (3, 4)));   // 0.75 == 3/4
//!     assert! (map.contains_key (&Fraction::new (6, 8)));   // 0.75 == 6/8
//!     assert! (map.contains_key (&Fraction::new (12, 16))); // 0.75 == 12/16
//!     assert! (! map.contains_key (&Fraction::from (0.5))); // 0.75 != 1/2
//! }
//! ```
//!
//! ## Comparison
//! ```
//! use fraction::Fraction;
//!
//! fn main () {
//!     let f14 = Fraction::new (1, 4); // 1/4 == 0.25
//!     let f12 = Fraction::new (1, 2); // 1/2 == 0.50
//!     let f24 = Fraction::new (2, 4); // 2/4 == 0.50
//!     let f34 = Fraction::new (3, 4); // 3/4 == 0.75
//!
//!     assert_eq! (f12, f24);                   // 1/2 == 2/4
//!     assert_eq! (f34, f12 + f14);             // 3/4 == 1/2 + 1/4
//!     assert_eq! (f14, Fraction::from (0.25)); // 1/4 == 0.25
//! }
//! ```


use std::convert::From;

use std::f64;


use std::cmp::{Ord, Ordering, PartialOrd};
use std::ops::{Add, Div, Mul, Neg, Sub};

use std::fmt;
use std::fmt::{Display, Formatter};



/// Fraction is the main structure that keeps number representation internally.
///
/// Possible options for instatiation are as follows:
///
///  - `Fraction::new`  - creates a number with custom numerator and denominator
///  - `Fraction::zero` - creates a new zero value (0/1)
///  - `Fraction::one`  - creates a new value (1/1)
///  - `Fraction::from` - converts a native rust number into a Fraction
///
/// Possible options for extracting the value:
///
///  - `Fraction::to_f64` - returns a native `f64` representation of the value
///  - `Fraction::unpack` - returns a tuple with `(sign, numerator, denominator)` values
///
/// # Examples
///
/// ## Instantiation
/// ```
/// use fraction::Fraction;
///
/// assert_eq! (
///     Fraction::zero (), // 0/1
///     Fraction::from (0) // 0/1
/// );
///
/// assert_eq! (
///     Fraction::one (),  // 1/1
///     Fraction::from (1) // 1/1
/// );
///
/// assert_eq! (
///     Fraction::new  (1, 5),     // 1/5
///     Fraction::from (1.0 / 5.0) // 1/5
/// );
/// ```
///
/// ## Extracting
/// ```
/// use fraction::Fraction;
///
/// assert_eq! (
///     Fraction::new (3, 4).unpack (),
///     (true, 3, 4)
/// );
///
/// assert_eq! (
///     Fraction::new (3, 4).to_f64 (),
///     0.75
/// );
/// ```
#[derive (Copy, Clone, Debug, Hash)]
pub struct Fraction {
    state: u8,

    numerator: u64,
    denominator: u64
}




impl Fraction {
    /// Creates a new fraction with custom numerator and denominator
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    ///
    /// Fraction::new (1, 1); // 1/1
    /// Fraction::new (1, 2); // 1/2
    /// ```
    pub fn new (numerator: u64, denominator: u64) -> Fraction {
        if denominator == 0 {
            Fraction { state: 1, numerator: numerator, denominator: denominator }
        } else {
            let (num, den) = Self::normalize ( (numerator, denominator) );
            Fraction { state: 0, numerator: num, denominator: den }
        }
    }



    /// Creates a new fraction with value `0/1`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    ///
    /// let zero = Fraction::zero (); // = 0
    ///
    /// assert_eq! (zero, Fraction::new (0, 1));
    /// ```
    pub fn zero () -> Fraction { Fraction { state: 0, numerator: 0, denominator: 1 } }



    /// Creates a new fraction with value `1/1`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    ///
    /// let one = Fraction::one (); // = 1
    ///
    /// assert_eq! (one, Fraction::new (1, 1));
    /// ```
    pub fn one () -> Fraction { Fraction { state: 0, numerator: 1, denominator: 1 } }



    /// Creates a new fraction with value `NaN`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// let nan = Fraction::nan ();
    ///
    /// assert_eq! (nan, Fraction::new (1, 0)); // 1/0 is NaN
    /// assert_eq! (nan, Fraction::from (f32::NAN));
    /// ```
    pub fn nan () -> Fraction { Fraction { state: 1, numerator: 0, denominator: 1 } }



    /// Creates a new fraction with value `INF`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// let inf = Fraction::inf ();
    ///
    /// assert_eq! (inf, Fraction::from (f32::INFINITY));
    /// assert_eq! (-inf, Fraction::from (f32::NEG_INFINITY));
    /// ```
    pub fn inf () -> Fraction { Fraction { state: 2, numerator: 0, denominator: 0 } }



    /// Creates a new fraction with value `-INF`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// let inf = Fraction::neg_inf ();
    ///
    /// assert_eq! (inf, Fraction::from (f32::NEG_INFINITY));
    /// assert_eq! (-inf, Fraction::from (f32::INFINITY));
    /// ```
    pub fn neg_inf () -> Fraction { Fraction { state: 130, numerator: 0, denominator: 0 } }



    /// Unpacks fraction into a tuple of `(sign, numerator, denominator)` values
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    ///
    /// assert_eq! ((true, 1, 4), Fraction::from (1.0/4.0).unpack ());
    /// assert_eq! ((false, 5, 4), Fraction::from (-1.25).unpack ());
    /// ```
    pub fn unpack (&self) -> (bool, u64, u64) { (!self.is_neg (), self.numerator, self.denominator) }



    /// Checks whether the value is `NaN`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// assert! (Fraction::nan ().is_nan ());
    /// assert! (Fraction::from (f32::NAN).is_nan ());
    /// assert! (Fraction::new (1, 0).is_nan ());
    /// ```
    pub fn is_nan (&self) -> bool { self.state & 1 == 1 }



    /// Checks whether the value is `INF`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// assert! (Fraction::inf ().is_infinite ());
    /// assert! (Fraction::from (f32::INFINITY).is_infinite ());
    /// assert! (Fraction::from (f32::NEG_INFINITY).is_infinite ());
    /// ```
    pub fn is_infinite (&self) -> bool { self.state & 2 == 2 }



    /// Checks whether the value is not `INF` and not is `NaN`
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// assert! (! Fraction::inf ().is_finite ());
    /// assert! (! Fraction::nan ().is_finite ());
    /// assert! (! Fraction::from (f32::INFINITY).is_finite ());
    /// ```
    pub fn is_finite (&self) -> bool { self.state & 1 == 0 && self.state & 2 == 0 }


    /// Checks whether the value is negative
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f32;
    ///
    /// assert! (Fraction::from (-1).is_neg ());
    /// assert! (Fraction::from (f32::NEG_INFINITY).is_neg ());
    /// ```
    pub fn is_neg (&self) -> bool { self.state & 128 == 128 }



    /// Returns native `f64` representation of the fraction
    ///
    /// # Examples
    ///
    /// ```
    /// use fraction::Fraction;
    /// use std::f64;
    ///
    /// assert_eq! (1.5f64, Fraction::from (1.5f32).to_f64 ());
    /// assert! (Fraction::nan ().to_f64 ().is_nan ());
    /// assert! (Fraction::inf ().to_f64 ().is_infinite ());
    /// assert! (Fraction::neg_inf ().to_f64 ().is_infinite ());
    /// ```
    pub fn to_f64 (&self) -> f64 {
        if self.state & 1 == 1 { f64::NAN }

        else if self.state & 2 == 2 {
            if self.state & 128 == 128 { f64::NEG_INFINITY }
            else { f64::INFINITY }
        }

        else { self.numerator as f64 / self.denominator as f64 * if self.state & 128 == 128 { -1f64 } else { 1f64 } }
    }


    fn normalize ( t: (u64, u64) ) -> (u64, u64) {
        let g = Self::gcd (t.0, t.1);

        (t.0 / g, t.1 / g)
    }


    fn gcd (mut x: u64, mut y: u64) -> u64 {
        while x != 0 {
            let z = x;
            x = y % x;
            y = z;
        }

        y
    }


    fn lcm (x: u64, y: u64) -> Option<u64> {
        let z = Self::gcd (x, y);

        x.checked_div (z).and_then (|x1| {
            x1.checked_mul (y)
        })
    }


    fn up (a: (u64, u64), b: (u64, u64)) -> Option<((u64, u64), u64)> {
        if a.1 == b.1 {
            return Some ( ((a.0, b.0), a.1) )
        } else {
            Self::lcm (a.1, b.1).and_then (|lcm| {
                a.0.checked_mul (lcm / a.1).and_then (|a0| {
                    b.0.checked_mul (lcm / b.1).and_then (|b0| {
                        Some ( (a0, b0) )
                    })
                }).and_then (|(a0, b0)| { Some ( ((a0, b0), lcm) ) })
            })
        }
    }
}



impl From<u8> for Fraction {
    fn from (val: u8) -> Fraction { Fraction { state: 0, numerator: val as u64, denominator: 1 } }
}



impl From<i8> for Fraction {
    fn from (val: i8) -> Fraction { Fraction { state: if val < 0 { 128 } else { 0 }, numerator: val.abs () as u64, denominator: 1 } }
}



impl From<u16> for Fraction {
    fn from (val: u16) -> Fraction { Fraction { state: 0, numerator: val as u64, denominator: 1 } }
}



impl From<i16> for Fraction {
    fn from (val: i16) -> Fraction { Fraction { state: if val < 0 { 128 } else { 0 }, numerator: val.abs () as u64, denominator: 1 } }
}



impl From<u32> for Fraction {
    fn from (val: u32) -> Fraction { Fraction { state: 0, numerator: val as u64, denominator: 1 } }
}



impl From<i32> for Fraction {
    fn from (val: i32) -> Fraction { Fraction { state: if val < 0 { 128 } else { 0 }, numerator: val.abs () as u64, denominator: 1 } }
}



impl From<u64> for Fraction {
    fn from (val: u64) -> Fraction { Fraction { state: 0, numerator: val as u64, denominator: 1 } }
}



impl From<i64> for Fraction {
    fn from (val: i64) -> Fraction { Fraction { state: if val < 0 { 128 } else { 0 }, numerator: val.abs () as u64, denominator: 1 } }
}



impl From<usize> for Fraction {
    fn from (val: usize) -> Fraction { Fraction { state: 0, numerator: val as u64, denominator: 1 } }
}



impl From<f32> for Fraction {
    fn from (val: f32) -> Fraction {
        if val.is_nan () { return Fraction::nan () };
        if val.is_infinite () { if val < 0f32 { return Fraction::neg_inf ()} else { return Fraction::inf () } };

        let state = if val < 0f32 { 128 } else { 0 };

        let mut n: u64 = val.abs ().floor () as u64;
        let mut d: u64 = 1;
        let mut f: f32 = val.abs ().fract ();

        for _ in 0 .. 12 {
            if f == 0f32 || f < 0.0000000000001 { break; }
            f = f * 10f32;

            if let Some (nn) = n.checked_mul (10) {
                if let Some (nn) = nn.checked_add (f.floor () as u64) {
                    n = nn;
                    f = f.fract ();

                    if let Some (nd) = d.checked_mul (10) {
                        d = nd;
                    } else { return Fraction { state: 2 | state, numerator: 0, denominator: 1 } }
                } else { return Fraction { state: 2 | state, numerator: 0, denominator: 1 } }
            } else { return Fraction { state: 2 | state, numerator: 0, denominator: 1 } }
        }

        let (num, den) = Self::normalize ( (n, d) );

        Fraction { state: state, numerator: num, denominator: den }
    }
}



impl From<f64> for Fraction {
    fn from (val: f64) -> Fraction {
        if val.is_nan () { return Fraction::nan () };
        if val.is_infinite () { if val < 0f64 { return Fraction::neg_inf ()} else { return Fraction::inf () } };

        let state = if val < 0f64 { 128 } else { 0 };

        let mut n: u64 = val.abs ().floor () as u64;
        let mut d: u64 = 1;
        let mut f: f64 = val.abs ().fract ();

        for _ in 0 .. 16 {
            if f == 0f64 || f < 0.0000000000001 { break; }
            f = f * 10f64;

            if let Some (nn) = n.checked_mul (10) {
                if let Some (nn) = nn.checked_add (f.floor () as u64) {
                    n = nn;
                    f = f.fract ();

                    if let Some (nd) = d.checked_mul (10) {
                        d = nd;
                    } else { return Fraction { state: 2 | state, numerator: 0, denominator: 1 } }
                } else { return Fraction { state: 2 | state, numerator: 0, denominator: 1 } }
            } else { return Fraction { state: 2 | state, numerator: 0, denominator: 1 } }
        }

        let (num, den) = Self::normalize ( (n, d) );

        Fraction { state: state, numerator: num, denominator: den }
    }
}



impl Neg for Fraction {
    type Output = Fraction;

    fn neg (self) -> Fraction {
        let mut s = self;

        if s.state & 128 == 128 { s.state = s.state ^ 128 }
        else { s.state = s.state | 128 };

        s
    }
}



impl Add for Fraction {
    type Output = Fraction;

    fn add (self, oth: Fraction) -> Fraction {
        if self.is_nan () || oth.is_nan () {
            Fraction::nan ()
        } else

        if self.is_infinite () || oth.is_infinite () {
            if self.is_infinite () && oth.is_infinite () {
                if self.is_neg () != oth.is_neg () {
                    Fraction::nan ()
                } else if self.is_neg () {
                    Fraction::neg_inf ()
                } else {
                    Fraction::inf ()
                }
            } else if self.is_infinite () {
                self
            } else { oth }
        } else

        if let Some ( ( (a, b), c ) ) = Self::up ( (self.numerator, self.denominator), (oth.numerator, oth.denominator) ) {
            if self.is_neg () == oth.is_neg () {
                if let Some (z) = a.checked_add (b) {
                    let (num, den) = Self::normalize ( (z, c) );
                    return Fraction { state: if self.is_neg () { 128 } else { 0 }, numerator: num, denominator: den }
                } else { return Fraction { state: if self.is_neg () { 128 } else { 0 } | 2, numerator: 0, denominator: 0 } }
            } else if a > b {
                if let Some (z) = a.checked_sub (b) {
                    let (num, den) = Self::normalize ( (z, c) );
                    return Fraction { state: if self.is_neg () { 128 } else { 0 }, numerator: num, denominator: den }
                } else { return Fraction { state: if self.is_neg () { 128 } else { 0 } | 2, numerator: 0, denominator: 0 } }
            } else {
                if let Some (z) = b.checked_sub (a) {
                    let (num, den) = Self::normalize ( (z, c) );
                    return Fraction { state: if self.is_neg () { 0 } else { 128 }, numerator: num, denominator: den }
                } else { return Fraction { state: if self.is_neg () { 0 } else { 128 } | 2, numerator: 0, denominator: 0 } }
            }
        } else { return Fraction { state: if self.is_neg () { 128 } else { 0 } | 2, numerator: 0, denominator: 0 } }
    }
}



impl Sub for Fraction {
    type Output = Fraction;

    fn sub (self, oth: Fraction) -> Fraction {
        if self.is_nan () || oth.is_nan () {
            Fraction::nan ()
        } else

        if self.is_infinite () || oth.is_infinite () {
            if self.is_infinite () && oth.is_infinite () {
                if self.is_neg () != oth.is_neg () {
                    Fraction::nan ()
                } else if self.is_neg () {
                    Fraction::neg_inf ()
                } else {
                    Fraction::inf ()
                }
            } else if self.is_infinite () {
                self
            } else { oth }
        } else

        if let Some ( ( (a, b), c ) ) = Self::up ( (self.numerator, self.denominator), (oth.numerator, oth.denominator) ) {

            if !self.is_neg () && !oth.is_neg () {
                if b > a {
                    let (num, den) = Self::normalize ( (b - a, c) );
                    return Fraction { state: 128, numerator: num, denominator: den }
                } else {
                    let (num, den) = Self::normalize ( (a - b, c) );
                    return Fraction { state: 0, numerator: num, denominator: den }
                }
            } else if self.is_neg () && oth.is_neg () {
                if a > b {
                    let (num, den) = Self::normalize ( (a - b, c) );
                    return Fraction { state: 128, numerator: num, denominator: den }
                } else {
                    let (num, den) = Self::normalize ( (b - a, c) );
                    return Fraction { state: 0, numerator: num, denominator: den }
                }
            } else if self.is_neg () {
                if let Some (z) = a.checked_add (b) {
                    let (num, den) = Self::normalize ( (z, c) );
                    return Fraction { state: 128, numerator: num, denominator: den }
                } else { Fraction { state: 128 | 2, numerator: 0, denominator: 0 } }
            } else {
                if let Some (z) = a.checked_add (b) {
                    let (num, den) = Self::normalize ( (z, c) );
                    return Fraction { state: 0, numerator: num, denominator: den }
                } else { Fraction { state: 2, numerator: 0, denominator: 0 } }
            }

        } else { return Fraction { state: if self.is_neg () { 128 } else { 0 } | 2, numerator: 0, denominator: 0 } }
    }
}



impl Mul for Fraction {
    type Output = Fraction;

    fn mul (self, oth: Fraction) -> Fraction {
        if self.is_nan () || oth.is_nan () {
            Fraction::nan ()
        } else

        if self.is_infinite () || oth.is_infinite () {
            if self.is_infinite () && oth.is_infinite () {
                if self.is_neg () != oth.is_neg () {
                    Fraction::nan ()
                } else if self.is_neg () {
                    Fraction::neg_inf ()
                } else {
                    Fraction::inf ()
                }
            } else if self.is_infinite () {
                self
            } else { oth }
        } else

        if let Some ( (num, den) ) = self.numerator.checked_mul (oth.numerator).and_then (|z| {
            self.denominator.checked_mul (oth.denominator).and_then (|q| {
                Some ( Self::normalize ( (z, q) ) )
            })
        }) {
            Fraction { state: if self.is_neg () == oth.is_neg () { 0 } else { 128 }, numerator: num, denominator: den }
        }

        else { return Fraction { state: 2 | if self.is_neg () == oth.is_neg () { 0 } else { 128 }, numerator: 0, denominator: 0 } }
    }
}



impl Div for Fraction {
    type Output = Fraction;

    fn div (self, oth: Fraction) -> Fraction {
        if self.is_nan () || oth.is_nan () {
            Fraction::nan ()
        } else

        if self.is_infinite () || oth.is_infinite () {
            if self.is_infinite () && oth.is_infinite () {
                if self.is_neg () != oth.is_neg () {
                    Fraction::nan ()
                } else if self.is_neg () {
                    Fraction::neg_inf ()
                } else {
                    Fraction::inf ()
                }
            } else if self.is_infinite () {
                self
            } else { oth }
        } else

        if let Some ( (num, den) ) = self.numerator.checked_mul (oth.denominator).and_then (|z| {
            self.denominator.checked_mul (oth.numerator).and_then (|q| {
                Some ( Self::normalize ( (z, q) ) )
            })
        }) {
            Fraction { state: if self.is_neg () == oth.is_neg () { 0 } else { 128 }, numerator: num, denominator: den }
        }

        else { return Fraction { state: 2 | if self.is_neg () == oth.is_neg () { 0 } else { 128 }, numerator: 0, denominator: 0 } }
    }
}



impl Ord for Fraction {
    fn cmp (&self, oth: &Fraction) -> Ordering {
        if self.is_neg () && !oth.is_neg () {
            Ordering::Less
        } else

        if !self.is_neg () && oth.is_neg () {
            Ordering::Greater
        } else

        if self.is_nan () && oth.is_nan () {
            Ordering::Equal
        } else

        if self.is_infinite () && oth.is_infinite () {
            Ordering::Equal
        } else

        if self.is_infinite () {
            Ordering::Greater
        } else

        if oth.is_infinite () {
            Ordering::Less
        } else

        {
            Self::up( (self.numerator, self.denominator), (oth.numerator, oth.denominator) ).and_then (|((a, b), _)| {
                Some (a.cmp (&b))
            }).unwrap_or (Ordering::Equal)
        }
    }
}



impl PartialOrd for Fraction {
    fn partial_cmp (&self, oth: &Fraction) -> Option<Ordering> {
        if self.is_nan () || oth.is_nan () { None }
        else { Some (self.cmp (oth)) }
    }
}



impl Eq for Fraction {}



impl PartialEq for Fraction {
    fn eq (&self, oth: &Fraction) -> bool {
        if self.is_neg () != oth.is_neg () { false } else
        if self.is_nan () && oth.is_nan () { true } else
        if self.is_infinite () && oth.is_infinite () { true } else
        {
            self.denominator == oth.denominator &&
            self.numerator == oth.numerator
        }
    }
}



impl Display for Fraction {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        if self.is_nan () {
            write! (formatter, "NaN")
        } else if self.is_infinite () {
            write! (formatter, "{}INF", if self.is_neg () { "-" } else { "" })
        } else {
            write! (
                formatter, "{}{}{}",
                if self.is_neg () { "-" } else { "" },
                self.numerator,
                if self.denominator > 1 { format! ("/{}", self.denominator) } else { "".to_string () },
            )
        }
    }
}




#[cfg (all (test, not (feature = "dev")))]
mod tests {
    use super::*;


    #[test]
    fn from () {
        let f = Fraction::from (-2i8);

        assert_eq! (f.state, 128);
        assert_eq! (f.numerator, 2);
        assert_eq! (f.denominator, 1);


        let f = Fraction::from (-2.18684f32);

        assert_eq! (f.state, 128);
        /* ~
        assert_eq! (f.denominator, 1000000000000000000);
        assert_eq! (f.numerator, 2186840057373046875);
        */

        let f = Fraction::from (1.1f64);
        assert_eq! (f.state, 0);
    }


    #[test]
    fn normalize () {
        let f = Fraction::new (2, 4);

        assert_eq! (f.numerator, 1);
        assert_eq! (f.denominator, 2);


        let f = Fraction::new (12, 18);

        assert_eq! (f.numerator, 2);
        assert_eq! (f.denominator, 3);


        let f = Fraction::new (21, 7);

        assert_eq! (f.numerator, 3);
        assert_eq! (f.denominator, 1);
    }



    #[test]
    fn add () {
        let f = Fraction::zero ();

        assert_eq! (f.numerator, 0);
        assert_eq! (f.denominator, 1);

        let f = f + Fraction::new (2, 1);

        assert_eq! (f.numerator, 2);
        assert_eq! (f.denominator, 1);


        let f = Fraction::new (1, 2) + Fraction::new (1, 2);

        assert_eq! (f.numerator, 1);
        assert_eq! (f.denominator, 1);


        let f = Fraction::new (1, 3) + Fraction::new (4, 8);

        assert_eq! (f.numerator, 5);
        assert_eq! (f.denominator, 6);


        let f = Fraction::new (2, 3) + Fraction::from (-2i8);

        assert_eq! (f.numerator, 4);
        assert_eq! (f.denominator, 3);
    }


    #[test]
    fn sub () {
        let f = Fraction::new (1, 2) - Fraction::new (1, 3);

        assert_eq! (f.numerator, 1);
        assert_eq! (f.denominator, 6);
    }


    #[test]
    fn mul () {
        let f = Fraction::new (1, 2) * Fraction::new (1, 2);

        assert_eq! (f.numerator, 1);
        assert_eq! (f.denominator, 4);
    }


    #[test]
    fn div () {
        let f = Fraction::new (1, 2) / Fraction::new (1, 6);

        assert_eq! (f.numerator, 3);
        assert_eq! (f.denominator, 1);
    }


    #[test]
    fn ord () {
        let a = Fraction::new (3, 4);
        let b = Fraction::new (5, 7);

        assert! (a > b);


        let a = Fraction::neg_inf ();
        let b = Fraction::zero ();

        assert! (a.is_neg ());
        assert! (!b.is_neg ());
        assert! (a < b);
    }
}

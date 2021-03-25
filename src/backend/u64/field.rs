//! Field arithmetic modulo `2^252 + 27742317777372353535851937790883648493`
//! which makes use of 64-bit limbs with 128-bit products.
//! In the 64-bit backend implementation, the `FieldElement` is
//! represented in radix `2^52`.
//!
//! The basic modular operations have been taken from the
//! [Curve25519-dalek repository](https://github.com/dalek-cryptography/curve25519-dalek) and refactored to work
//! for the Sonny finite field.

use core::convert::From;
use std::fmt::{Debug, Display};

use std::cmp::{Ord, Ordering, PartialOrd};
use std::default::Default;

use core::ops::{Add, Div, Mul, Neg, Sub};
use core::ops::{Index, IndexMut};

use subtle::{Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq};

use crate::backend::u64::constants;
use crate::scalar::Ristretto255Scalar;
use crate::traits::ops::*;
use crate::traits::Identity;

/// A `FieldElement` represents an element of the field
/// which has order of `2^252 + 27742317777372353535851937790883648493`
///
/// In the 64-bit backend implementation, the `FieldElement` is
/// represented in radix `2^52`
#[derive(Copy, Clone, Eq)]
pub struct FieldElement(pub [u64; 5]);

impl Debug for FieldElement {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "FieldElement({:?})", &self.0[..])
    }
}

impl Display for FieldElement {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "FieldElement({:?})", &self.0[..])
    }
}

impl Index<usize> for FieldElement {
    type Output = u64;
    fn index(&self, _index: usize) -> &u64 {
        &(self.0[_index])
    }
}

impl IndexMut<usize> for FieldElement {
    fn index_mut(&mut self, _index: usize) -> &mut u64 {
        &mut (self.0[_index])
    }
}

impl PartialOrd for FieldElement {
    fn partial_cmp(&self, other: &FieldElement) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

impl Ord for FieldElement {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..5).rev() {
            if self[i] > other[i] {
                return Ordering::Greater;
            } else if self[i] < other[i] {
                return Ordering::Less;
            }
        }
        Ordering::Equal
    }
}

impl Identity for FieldElement {
    /// Returns the Identity element over the finite field
    /// modulo `2^252 + 27742317777372353535851937790883648493`.
    ///
    /// It is defined as 1 on `FieldElement` format, and is therefore written as:
    /// `[1, 0, 0, 0, 0]`.
    fn identity() -> FieldElement {
        FieldElement([1, 0, 0, 0, 0])
    }
}

impl Default for FieldElement {
    ///Returns the default value for a FieldElement = Zero.
    fn default() -> FieldElement {
        FieldElement::zero()
    }
}

//-------------- From Implementations -----------------//
impl From<u8> for FieldElement {
    /// Performs the conversion.
    fn from(_inp: u8) -> FieldElement {
        let mut res = FieldElement::zero();
        res[0] = _inp as u64;
        res
    }
}

impl From<u16> for FieldElement {
    /// Performs the conversion.
    fn from(_inp: u16) -> FieldElement {
        let mut res = FieldElement::zero();
        res[0] = _inp as u64;
        res
    }
}

impl From<u32> for FieldElement {
    /// Performs the conversion.
    fn from(_inp: u32) -> FieldElement {
        let mut res = FieldElement::zero();
        res[0] = _inp as u64;
        res
    }
}

impl From<u64> for FieldElement {
    /// Performs the conversion.
    fn from(_inp: u64) -> FieldElement {
        let mut res = FieldElement::zero();
        let mask = (1u64 << 52) - 1;
        res[0] = _inp & mask;
        res[1] = _inp >> 52;
        res
    }
}

impl From<u128> for FieldElement {
    /// Performs the conversion.
    fn from(_inp: u128) -> FieldElement {
        let mut res = FieldElement::zero();
        let mask = (1u128 << 52) - 1;

        // Since 128 / 52 < 4 , we only need to be attentive to
        // the first three limbs.
        res[0] = (_inp & mask) as u64;
        res[1] = ((_inp >> 52) & mask) as u64;
        res[2] = (_inp >> 104) as u64;

        res
    }
}

impl<'a> From<&'a Ristretto255Scalar> for FieldElement {
    /// Given a Ristretto255Scalar on canonical bytes representation
    /// get it's FieldElement equivalent value as 5 limbs and
    /// radix-52.
    fn from(origin: &'a Ristretto255Scalar) -> FieldElement {
        let origin_bytes = origin.to_bytes();
        FieldElement::from_bytes(&origin_bytes)
    }
}

impl Into<Ristretto255Scalar> for FieldElement {
    /// Given a FieldElement reference get it's
    /// Ristretto255Scalar Equivalent on it's
    /// canonical bytes representation.
    fn into(self) -> Ristretto255Scalar {
        Ristretto255Scalar::from_canonical_bytes(self.to_bytes()).unwrap()
    }
}

impl<'a> Neg for &'a FieldElement {
    type Output = FieldElement;
    /// Computes `-self (mod l)`.
    /// Compute the negated value that corresponds to the
    /// complement of the two, of the input FieldElement.
    fn neg(self) -> FieldElement {
        &FieldElement::zero() - self
    }
}

impl Neg for FieldElement {
    type Output = FieldElement;
    /// Computes `-self (mod l)`.
    ///
    /// Compute the negated value that corresponds to the
    /// two's complement of the input FieldElement.
    fn neg(self) -> FieldElement {
        -&self
    }
}

impl<'a, 'b> Add<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    /// Compute `a + b (mod l)`.
    fn add(self, b: &'b FieldElement) -> FieldElement {
        let mut sum = FieldElement::zero();
        let mask = (1u64 << 52) - 1;

        // a + b
        let mut carry: u64 = 0;
        for i in 0..5 {
            carry = self.0[i] + b[i] + (carry >> 52);
            sum[i] = carry & mask;
        }
        // subtract l if the sum is >= l
        sum - constants::FIELD_L
    }
}

impl Add<FieldElement> for FieldElement {
    type Output = FieldElement;
    /// Compute `a + b (mod l)`.
    fn add(self, b: FieldElement) -> FieldElement {
        &self + &b
    }
}

impl<'a, 'b> Sub<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    /// Compute `a - b (mod l)`
    fn sub(self, b: &'b FieldElement) -> FieldElement {
        let mut sub = 0u64;
        let mut difference: FieldElement = FieldElement::zero();
        let mask = (1u64 << 52) - 1;
        // Save wrapping_sub result. Store as a reminder on the next limb.
        for i in 0..5 {
            sub = self.0[i].wrapping_sub(b[i] + (sub >> 63));
            difference[i] = sub & mask;
        }
        // Conditionaly add l, if difference is negative.
        // Be aware that here `sub` tells us the most significant bit of the last limb
        // so then we know whether or not the value is greater than `l`.
        let underflow_mask = ((sub >> 63) ^ 1).wrapping_sub(1);
        let mut carry = 0u64;
        for i in 0..5 {
            carry = (carry >> 52) + difference[i] + (constants::FIELD_L[i] & underflow_mask);
            difference[i] = carry & mask;
        }
        difference
    }
}

impl Sub<FieldElement> for FieldElement {
    type Output = FieldElement;
    /// Compute `a + b (mod l)`.
    fn sub(self, b: FieldElement) -> FieldElement {
        &self - &b
    }
}

impl<'a, 'b> Mul<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    /// This Mul implementation returns a double precision result.
    ///
    /// The result of the standard mul is stored on a [u128; 9].
    ///
    /// Then, we apply the Montgomery Reduction function to perform
    /// the modulo and the reduction to the `FieldElement` format: [u64; 5].
    fn mul(self, _rhs: &'b FieldElement) -> FieldElement {
        let prod = FieldElement::montgomery_reduce(&FieldElement::mul_internal(self, _rhs));
        FieldElement::montgomery_reduce(&FieldElement::mul_internal(&prod, &constants::RR_FIELD))
    }
}

impl Mul<FieldElement> for FieldElement {
    type Output = FieldElement;
    /// This Mul implementation returns a double precision result.
    ///
    /// The result of the standard mul is stored on a [u128; 9].
    ///
    /// Then, we apply the Montgomery Reduction function to perform
    /// the modulo and the reduction to the `FieldElement` format: [u64; 5].
    fn mul(self, _rhs: FieldElement) -> FieldElement {
        &self * &_rhs
    }
}

impl<'a, 'b> Div<&'a FieldElement> for &'b FieldElement {
    type Output = FieldElement;
    /// Performs the op: `x / y (mod l)`.
    ///
    /// Since on modular fields we don't divide, the equivalent op
    /// is: `x * (y^-1 (mod l))`, which is equivalent to the naive
    /// division but for Finite Fields.
    fn div(self, _rhs: &'a FieldElement) -> FieldElement {
        assert!(_rhs != &FieldElement::zero(), "Cannot divide by zero.");
        self * &_rhs.inverse()
    }
}

impl Div<FieldElement> for FieldElement {
    type Output = FieldElement;
    /// Performs the op: `x / y (mod l)`.
    ///
    /// Since on modular fields we don't divide, the equivalent op
    /// is: `x * (y^-1 (mod l))`, which is equivalent to the naive
    /// division but for Finite Fields.
    fn div(self, _rhs: FieldElement) -> FieldElement {
        &self * &_rhs.inverse()
    }
}

impl<'a> Square for &'a FieldElement {
    type Output = FieldElement;
    /// Compute `a^2 (mod l)`.
    ///
    /// This `Square` implementation returns a double precision result.
    /// The result of the standard square is stored on a [u128; 9].
    ///
    /// Then, we apply the Montgomery Reduction function to perform
    /// the modulo and the reduction to the `FieldElement` format: [u64; 5].
    fn square(self) -> FieldElement {
        let aa = FieldElement::montgomery_reduce(&FieldElement::square_internal(self));
        FieldElement::montgomery_reduce(&FieldElement::mul_internal(&aa, &constants::RR_FIELD))
    }
}

impl<'a> Half for &'a FieldElement {
    type Output = FieldElement;
    /// Give the half of the FieldElement value (mod l).
    fn half(self) -> FieldElement {
        self * &constants::INVERSE_MOD_TWO
    }
}

impl<'a, 'b> Pow<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    /// Performs the op: `a^b (mod l)`.
    ///
    /// Exponentiation by squaring classical algorithm
    /// implementation for `FieldElement`.
    ///
    /// Schneier, Bruce (1996). Applied Cryptography: Protocols,
    /// Algorithms, and Source Code in C, Second Edition (2nd ed.).
    fn pow(self, exp: &'b FieldElement) -> FieldElement {
        let (zero, one) = (FieldElement::zero(), FieldElement::one());
        let mut base = *self;
        let mut res = FieldElement::one();
        let mut expon = *exp;

        while expon > zero {
            if expon.is_even() {
                expon = expon.half_without_mod();
                base = base * base;
            } else {
                expon = expon - one;
                res = res * base;

                expon = expon.half_without_mod();
                base = base * base;
            }
        }

        res
    }
}

impl<'a> ModSqrt for &'a FieldElement {
    type Output = Option<FieldElement>;
    /// Performs the op: `sqrt(a) (mod l)`.
    ///
    /// Tonelli-Shanks prime modular square root
    /// algorithm implementation for `FieldElement`.
    ///
    /// Conditionally selects and returns the positive or the
    /// negative result of the `mod_sqrt` by analyzing the
    /// `Choice` sent as input:
    ///
    /// For `Choice(0)` -> Negative result.
    /// For `Choice(1)` -> Positive result.
    ///
    /// Daniel Shanks. Five Number Theoretic Algorithms.
    /// Proceedings of the Second Manitoba Conference on
    /// Numerical Mathematics. Pp. 51–70. 1973.
    ///
    /// This algorithm was translated from the python impl
    /// found in:
    /// https://codereview.stackexchange.com/questions/43210/tonelli-shanks-algorithm-implementation-of-prime-modular-square-root
    fn mod_sqrt(self, sign: Choice) -> Option<FieldElement> {
        let zero = FieldElement::zero();
        // If the input is `0` the sqrt is directly 0.
        if self.ct_eq(&FieldElement::zero()).unwrap_u8() == 1u8 {
            return Some(zero);
        }

        // Check if exists a solution insine the finite
        // field generated by `FIELD_L`.
        if self.legendre_symbol().unwrap_u8() == 0u8 {
            return None;
        }

        let (one, two, six) = (
            FieldElement::one(),
            FieldElement([2, 0, 0, 0, 0]),
            FieldElement([6, 0, 0, 0, 0]),
        );

        // Factor p-1 on the form q * 2^s (with Q odd).
        let mut q = FieldElement::minus_one();
        let mut s = zero;
        while q.is_even() {
            s = s + one;
            q = q.half_without_mod();
        }

        // Select a z which is a quadratic non resudue modulo p.
        // We pre-computed it so we know that 6 isn't QR.
        let mut c = six.pow(&q);

        // Search for a solution.
        let mut x = self.pow(&(q + one).half_without_mod());
        let mut t = self.pow(&q);
        let mut m = s;

        while t != one {
            // Find the lowest i such that t^(2^i) = 1.
            let mut i = zero;
            let mut e = FieldElement::from(2u8);
            let b;
            while i < m {
                i = i + one;
                if t.pow(&e).ct_eq(&one).unwrap_u8() == 1u8 {
                    break;
                }
                e = e * two;
            }

            // Update values for next iter
            b = c.pow(&two.pow(&(m - i - one)));
            x = x * b;
            t = t * b.square();
            c = b.square();
            m = i;
        }

        Some(FieldElement::conditional_select(
            &x,
            &(constants::FIELD_L - x),
            sign,
        ))
    }
}

impl InvSqrt for &FieldElement {
    type Output = (Choice, FieldElement);
    /// This is a convenience wrapper function over the `SqrtRatioI` trait
    /// implementation when `self = 1`:
    /// Computes `sqrt(1/self)`.
    ///
    /// This function always returns the non-negative result of the sqrt.
    ///
    /// # Returns:
    ///
    /// - `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
    /// - `(Choice(0), zero)           ` if `self` is zero;
    /// - `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;

    fn inv_sqrt(self) -> (Choice, FieldElement) {
        FieldElement::one().sqrt_ratio_i(self)
    }
}

impl SqrtRatioI<&FieldElement> for FieldElement {
    type Output = (Choice, FieldElement);

    #[allow(non_snake_case)]
    /// The first part of the return value signals whether u/v was square,
    /// and the second part contains a square root.
    /// Specifically, it returns:
    ///
    ///- (true, +sqrt(u/v)) if v is nonzero and u/v is square;
    ///- (true, zero) if u is zero;
    ///- (false, zero) if v is zero and u is nonzero;
    ///- (false, +sqrt(i*u/v)) if u/v is nonsquare (so iu/v is square).
    fn sqrt_ratio_i(&self, v: &FieldElement) -> (Choice, FieldElement) {
        let zero = &FieldElement::zero();

        match (self == zero, v == zero) {
            (true, _) => return (Choice::from(1u8), FieldElement::zero()),
            (false, true) => return (Choice::from(0u8), FieldElement::zero()),
            (false, false) => (),
        };

        // (false, false) case. We check "QRness".
        match (self / v).legendre_symbol().unwrap_u8() == 1u8 {
            // (u/v) is not QR, so we multiply by `i` and
            // return `(false, +sqrt(i*u/v))`.
            false => {
                let mut res = (constants::SQRT_MINUS_ONE * (self / v))
                    .mod_sqrt(Choice::from(1u8))
                    .unwrap();
                res.conditional_negate(!res.is_positive());
                (Choice::from(0u8), res)
            }
            // (u/v) is QR, so we don't need to do anything and
            // we return `(true, +sqrt(u/v))`.
            true => {
                let mut res = (self / v).mod_sqrt(Choice::from(1u8)).unwrap();
                res.conditional_negate(!res.is_positive());
                (Choice::from(1u8), res)
            }
        }
    }
}

/// u64 * u64 = u128 inline func multiply helpe
fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

impl FieldElement {

    /// Construct zero.
    pub const fn zero() -> FieldElement {
        FieldElement([0, 0, 0, 0, 0])
    }

    /// Construct one.
    pub const fn one() -> FieldElement {
        FieldElement([1, 0, 0, 0, 0])
    }

    /// Construct -1 (mod l).
    pub const fn minus_one() -> FieldElement {
        FieldElement([
            671914833335276,
            3916664325105025,
            1367801,
            0,
            17592186044416,
        ])
    }

    /// Evaluate if a `FieldElement` is even or not.
    pub fn is_even(self) -> bool {
        // Compare the last bit of the first limb to check evenness.
        // 0b0 -> true
        // 0b1 -> false
        self.0[0] & 0b01 == 0u64
    }

    /// Checks if a ´FieldElement` is considered negative following
    /// the Decaf paper criteria.
    ///
    /// The criteria says: Non-negative field elements.
    /// Let p > 2 be prime. Define a residue x ∈ F =Z/pZ to be
    /// “non-negative” if the least absolute residue for x is in
    /// `[0,(p−1)/2]`, and “negative” otherwise.
    ///
    /// # Returns:
    /// - `Choice(1)` if pos.
    /// - `Choice(0)` if neg.
    pub fn is_positive(&self) -> Choice {
        if self >= &FieldElement::zero() && self <= &constants::POS_RANGE {
            return Choice::from(1);
        }
        Choice::from(0)
    }

    /// Load a `FieldElement` from the low 253b bits of a 256-bit
    /// input. So Little Endian representation in bytes of a FieldElement.
    // @TODO: Macro for Inline load8 function as it has variadic arguments.
    #[warn(dead_code)]
    pub fn from_bytes(bytes: &[u8; 32]) -> FieldElement {
        let load8 = |input: &[u8]| -> u64 {
            (input[0] as u64)
                | ((input[1] as u64) << 8)
                | ((input[2] as u64) << 16)
                | ((input[3] as u64) << 24)
                | ((input[4] as u64) << 32)
                | ((input[5] as u64) << 40)
                | ((input[6] as u64) << 48)
                | ((input[7] as u64) << 56)
        };

        let low_52_bit_mask = (1u64 << 52) - 1;

        FieldElement(
            // load bits [  0, 64), no shift
            [
                load8(&bytes[0..]) & low_52_bit_mask, // load bits [ 48,112), shift to [ 52,112)
                (load8(&bytes[6..]) >> 4) & low_52_bit_mask, // load bits [ 96,160), shift to [104,160)
                (load8(&bytes[12..]) >> 8) & low_52_bit_mask, // load bits [152,216), shift to [156,216)
                (load8(&bytes[19..]) >> 4) & low_52_bit_mask, // load bits [192,256), shift to [208,256)
                (load8(&bytes[24..]) >> 16) & low_52_bit_mask,
            ],
        )
    }

    /// Serialize this `FieldElement` to a 32-byte array.  The
    /// encoding is canonical.
    pub fn to_bytes(self) -> [u8; 32] {
        let mut res = [0u8; 32];

        res[0] = (self.0[0] >> 0) as u8;
        res[1] = (self.0[0] >> 8) as u8;
        res[2] = (self.0[0] >> 16) as u8;
        res[3] = (self.0[0] >> 24) as u8;
        res[4] = (self.0[0] >> 32) as u8;
        res[5] = (self.0[0] >> 40) as u8;
        // Satisfy radix 52 with the next limb value shifted according the needs
        res[6] = ((self.0[0] >> 48) | (self.0[1] << 4)) as u8;
        res[7] = (self.0[1] >> 4) as u8;
        res[8] = (self.0[1] >> 12) as u8;
        res[9] = (self.0[1] >> 20) as u8;
        res[10] = (self.0[1] >> 28) as u8;
        res[11] = (self.0[1] >> 36) as u8;
        res[12] = (self.0[1] >> 44) as u8;
        res[13] = (self.0[2] >> 0) as u8;
        res[14] = (self.0[2] >> 8) as u8;
        res[15] = (self.0[2] >> 16) as u8;
        res[16] = (self.0[2] >> 24) as u8;
        res[17] = (self.0[2] >> 32) as u8;
        res[18] = (self.0[2] >> 40) as u8;
        res[19] = ((self.0[2] >> 48) | (self.0[3] << 4)) as u8;
        res[20] = (self.0[3] >> 4) as u8;
        res[21] = (self.0[3] >> 12) as u8;
        res[22] = (self.0[3] >> 20) as u8;
        res[23] = (self.0[3] >> 28) as u8;
        res[24] = (self.0[3] >> 36) as u8;
        res[25] = (self.0[3] >> 44) as u8;
        res[26] = (self.0[4] >> 0) as u8;
        res[27] = (self.0[4] >> 8) as u8;
        res[28] = (self.0[4] >> 16) as u8;
        res[29] = (self.0[4] >> 24) as u8;
        res[30] = (self.0[4] >> 32) as u8;
        res[31] = (self.0[4] >> 40) as u8;

        // High bit should be zero.
        //debug_assert!((res[31] & 0b1000_0000u8) == 0u8);
        res
    }

    /// Given a `k`: u64, compute `2^k` giving the resulting result
    /// as a `FieldElement`.
    ///
    /// See that the input must be between the range => 0..253.
    ///
    /// NOTE: This function implements an `assert!` statement that
    /// checks the correctness of the exponent provided as param.
    pub fn two_pow_k(exp: u64) -> FieldElement {
        // Check that exp has to be less than 260.
        // Note that a FieldElement can be as much
        // `2^252 + 27742317777372353535851937790883648493` so we pick
        // 253 knowing that 252 will be less than `FIELD_L`.
        assert!(exp < 253u64, "Exponent can't be greater than 260");

        let mut res = FieldElement::zero();
        match exp {
            0..=51 => {
                res[0] = 1u64 << exp;
            }
            52..=103 => {
                res[1] = 1u64 << (exp - 52);
            }
            104..=155 => {
                res[2] = 1u64 << (exp - 104);
            }
            156..=207 => {
                res[3] = 1u64 << (exp - 156);
            }
            _ => {
                res[4] = 1u64 << (exp - 208);
            }
        }
        res
    }

    /// Returns the half of an **EVEN** `FieldElement`.
    /// 
    /// This function performs almost 4x faster than the
    /// `Half` implementation but SHOULD be used carefully.
    /// 
    /// # Panics
    /// 
    /// When the `FieldElement` provided is not even.
    pub fn half_without_mod(self) -> FieldElement {
       //assert!(self.is_even());
        let mut carry = 0u64;
        let mut res = self;

        for i in (0..5).rev() {
            res[i] = res[i] | carry;
            
            carry = (res[i] & 1) << 52;
            res[i] >>= 1;
        }
        res
    }

    /// Given a FieldElement, this function evaluates if it is a quadratic
    /// residue (mod l).
    ///
    /// See: [https://en.wikipedia.org/wiki/Legendre_symbol](https://en.wikipedia.org/wiki/Legendre_symbol).
    ///
    /// Returns:
    ///
    /// `-1` -> Non-quadratic residue (mod l) == Choice(0).
    ///
    /// `1`  -> Quadratic residue (mod l) == Choice(1).
    ///
    /// `0`  -> `Input (mod l) == 0`. Not implemented since you can't pass
    /// an input which is multiple of `FIELD_L`.
    pub fn legendre_symbol(&self) -> Choice {
        let res = self.pow(&constants::MINUS_ONE_HALF);
        res.ct_eq(&FieldElement::minus_one()) ^ Choice::from(1u8)
    }

    /// Given a `k`: u64, compute `2^k` giving the resulting result
    /// as a `FieldElement`.
    ///
    /// NOTE: Usually, we will say 253, but since on inversion we 
    /// need to exponenciate to greater values, we set the
    /// max on the Montgomery modulo so `260`.
    #[doc(hidden)]
    pub(self) fn inner_two_pow_k(exp: u64) -> FieldElement {
        // Check that exp has to be less than 260.
        assert!(exp < 260u64, "Exponent can't be greater than 260");

        let mut res = FieldElement::zero();
        match exp {
            0..=51 => {
                res[0] = 1u64 << exp;
            }
            52..=103 => {
                res[1] = 1u64 << (exp - 52);
            }
            104..=155 => {
                res[2] = 1u64 << (exp - 104);
            }
            156..=207 => {
                res[3] = 1u64 << (exp - 156);
            }
            _ => {
                res[4] = 1u64 << (exp - 208);
            }
        }
        res
    }

    /// Compute `a * b` with the function multiplying helper
    pub(self) fn mul_internal(a: &FieldElement, b: &FieldElement) -> [u128; 9] {
        let mut res = [0u128; 9];
        // Note that this is just the normal way of performing a product.
        // We need to store the results on u128 as otherwise we'll end
        // up having overflowings.
        res[0] = m(a[0], b[0]);
        res[1] = m(a[0], b[1]) + m(a[1], b[0]);
        res[2] = m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]);
        res[3] = m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]);
        res[4] = m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]);
        res[5] = m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]);
        res[6] = m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]);
        res[7] = m(a[3], b[4]) + m(a[4], b[3]);
        res[8] = m(a[4], b[4]);

        res
    }

    /// Compute `a^2`.
    ///
    /// This operation is multo-precision. So it gives back
    /// an `[u128; 9]` with the result of the squaring.
    pub(self) fn square_internal(a: &FieldElement) -> [u128; 9] {
        let a_sqrt = [a[0] * 2, a[1] * 2, a[2] * 2, a[3] * 2];

        [
            m(a[0], a[0]),
            m(a_sqrt[0], a[1]),
            m(a_sqrt[0], a[2]) + m(a[1], a[1]),
            m(a_sqrt[0], a[3]) + m(a_sqrt[1], a[2]),
            m(a_sqrt[0], a[4]) + m(a_sqrt[1], a[3]) + m(a[2], a[2]),
            m(a_sqrt[1], a[4]) + m(a_sqrt[2], a[3]),
            m(a_sqrt[2], a[4]) + m(a[3], a[3]),
            m(a_sqrt[3], a[4]),
            m(a[4], a[4]),
        ]
    }

    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    pub(self) fn montgomery_reduce(limbs: &[u128; 9]) -> FieldElement {

        fn adjustment_fact(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(constants::LFACTOR_FIELD) & ((1u64 << 52) - 1);
            ((sum + m(p, constants::FIELD_L[0])) >> 52, p)
        }


        fn montg_red_res(sum: u128) -> (u128, u64) {
            let w = (sum as u64) & ((1u64 << 52) - 1);
            (sum >> 52, w)
        }

        // FIELD_L[3] = 0 so we can skip these products.
        let l = &constants::FIELD_L;

        // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
        let (carry, n0) = adjustment_fact(limbs[0]);
        let (carry, n1) = adjustment_fact(carry + limbs[1] + m(n0, l[1]));
        let (carry, n2) = adjustment_fact(carry + limbs[2] + m(n0, l[2]) + m(n1, l[1]));
        let (carry, n3) = adjustment_fact(carry + limbs[3] + m(n1, l[2]) + m(n2, l[1]));
        let (carry, n4) =
            adjustment_fact(carry + limbs[4] + m(n0, l[4]) + m(n2, l[2]) + m(n3, l[1]));

        // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
        let (carry, r0) = montg_red_res(carry + limbs[5] + m(n1, l[4]) + m(n3, l[2]) + m(n4, l[1]));
        let (carry, r1) = montg_red_res(carry + limbs[6] + m(n2, l[4]) + m(n4, l[2]));
        let (carry, r2) = montg_red_res(carry + limbs[7] + m(n3, l[4]));
        let (carry, r3) = montg_red_res(carry + limbs[8] + m(n4, l[4]));
        let r4 = carry as u64;

        // result may be >= r, so attempt to subtract l
        &FieldElement([r0, r1, r2, r3, r4]) - l
    }

    //--------------------InverseModMontgomery tools-----------------------//

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^253
    pub(self) fn montgomery_mul(a: &FieldElement, b: &FieldElement) -> FieldElement {
        FieldElement::montgomery_reduce(&FieldElement::mul_internal(a, b))
    }

    /// Puts a FieldElement into Montgomery form, i.e. computes `a*R (mod l)`
    #[allow(dead_code)]
    pub(self) fn to_montgomery(&self) -> FieldElement {
        FieldElement::montgomery_mul(self, &constants::RR_FIELD)
    }

    /// Takes a FieldElement out of Montgomery form, i.e. computes `a/R (mod l)`
    #[allow(dead_code)]
    pub(self) fn from_montgomery(&self) -> FieldElement {
        let mut limbs = [0u128; 9];
        for i in 0..5 {
            limbs[i] = self[i] as u128;
        }
        FieldElement::montgomery_reduce(&limbs)
    }

    /// Compute `a^-1 (mod l)` using the the Savas & Koç modular
    /// inverse algorithm. It's an optimization of the Kalinski
    /// modular inversion algorithm that extends the Binary GCD
    /// algorithm to perform the modular inverse operation.
    ///
    /// The `PhaseII` it's substituded by 1 or 2 Montgomery Multiplications,
    /// what makes the second part compute in almost ConstTime.
    ///
    /// # Panics
    /// It is not possible to invert `0` by obvious reasons. So an
    /// the function panics when trying to invert zero.
    ///
    /// Special issue on Montgomery arithmetic.
    /// Montgomery inversion - Erkay Sava ̧s & Çetin Kaya Koç
    /// J Cryptogr Eng (2018) 8:201–210
    /// https://doi.org/10.1007/s13389-017-0161-x.
    pub fn inverse(&self) -> FieldElement {
        /// This Phase I is indeed the Binary GCD algorithm , a version of Stein's algorithm
        /// which tries to remove the expensive division operation from the Classical
        /// Euclidean GDC algorithm by replacing it with Bit-shifting, subtraction and comparison.
        ///
        /// Output = `a^(-1) * 2^k (mod l)` where `k = log2(FIELD_L) == 253`.
        ///
        /// Stein, J.: Computational problems associated with Racah algebra.J. Comput. Phys.1, 397–405 (1967).

        fn phase1(a: &FieldElement) -> (FieldElement, u64) {
            assert!(a != &FieldElement::zero());

            // Declare L = 2^252 + 27742317777372353535851937790883648493
            let p = FieldElement([
                671914833335277,
                3916664325105025,
                1367801,
                0,
                17592186044416,
            ]);
            let mut u = p.clone();
            let mut v = *a;
            let mut r = FieldElement::zero();
            let mut s = FieldElement::one();
            let two = FieldElement([2, 0, 0, 0, 0]);
            let mut k = 0u64;

            while v > FieldElement::zero() {
                match (u.is_even(), v.is_even(), u > v, v >= u) {
                    // u is even
                    (true, _, _, _) => {
                        u = u.half_without_mod();
                        s = s * two;
                    }
                    // u isn't even but v is even
                    (false, true, _, _) => {
                        v = v.half_without_mod();
                        r = r * two;
                    }
                    // u and v aren't even and u > v
                    (false, false, true, _) => {
                        u = u - v;
                        u = u.half_without_mod();
                        r = r + s;
                        s = s * two;
                    }
                    // u and v aren't even and v > u
                    (false, false, false, true) => {
                        v = v - u;
                        v = v.half_without_mod();
                        s = r + s;
                        r = r * two;
                    }
                    (false, false, false, false) => panic!("Unexpected error has ocurred."),
                }
                k += 1;
            }
            if r > p {
                r = r - p;
            }
            (p - r, k)
        }

        let (mut r, mut z) = phase1(&self);
        if z > 260 {
            r = FieldElement::montgomery_mul(&r, &FieldElement::one());
            z -= 260;
        }
        let fact = FieldElement::inner_two_pow_k(260 - z);
        r = FieldElement::montgomery_mul(&r, &fact);
        r
    }
}

/// Module with constants used for `FieldElement` u64 implementation
/// testing. It also includes the tests but they remain hidden on the docs.
#[cfg(test)]
pub mod tests {

    use super::*;
    #[allow(unused_imports)]
    use crate::backend::u64::constants;
    #[allow(unused_imports)]
    use crate::scalar::Ristretto255Scalar;

    /// Bytes representation of `-1 (mod l) = 7237005577332262213973186563042994240857116359379907606001950938285454250988`
    pub static MINUS_ONE_BYTES: [u8; 32] = [
        236, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 16,
    ];

    /// `A = 182687704666362864775460604089535377456991567872`
    pub static A: FieldElement = FieldElement([0, 0, 0, 2, 0]);

    /// `A_SQUARE = A^2 = 7237005577332262213845247704030316590229102007346248927835171914574158222317`.
    pub static A_SQUARE: FieldElement = FieldElement([
        671914833335277,
        423018350096769,
        2042999080933985,
        4503598226741381,
        17592186044415,
    ]);

    /// `-A (mod l) = 7237005577332262213973186562860306536190753494604447001912415560828462683117`.
    pub static MINUS_A: FieldElement = FieldElement([
        671914833335277,
        3916664325105025,
        1367801,
        4503599627370494,
        17592186044415,
    ]);

    /// A on Montgomery domain = `(A * R (mod l)) = 474213518376757474787523690767343130291324218287585596341053150401850043342`.
    pub static INV_MONT_A: FieldElement = FieldElement([
        2317332620045262,
        1576144597389635,
        2025859686448975,
        2756776639866422,
        1152749206963,
    ]);

    /// `(A ^ (-1)) (mod l) = 7155219595916845557842258654134856828180378438239419449390401977965479867845`.
    pub static INV_MOD_A: FieldElement = FieldElement([
        1289905446467013,
        1277206401232501,
        2632844239031511,
        61125669693438,
        17393375336657,
    ]);

    /// `B = 904625697166532776746648320197686575422163851717637391703244652875051672039`
    pub static B: FieldElement = FieldElement([
        2766226127823335,
        4237835465749098,
        4503599626623787,
        4503599627370493,
        2199023255551,
    ]);

    /// `B_SQUARE = B^2 = 6084981972634577367347263098159392507879678891294474389120508780995125934784`.
    pub static B_SQUARE: FieldElement = FieldElement([
        3966658334128832,
        2102453619223755,
        4260110256982373,
        4297171677577933,
        14791771789536,
    ]);

    /// `-B (mod l) = 6332379880165729437226538242845307665434952507662270214298706285410402578950`.
    pub static MINUS_B: FieldElement = FieldElement([
        2409288332882438,
        4182428486726422,
        2114509,
        2,
        15393162788864,
    ]);

    /// `(B ^ (-1)) (mod l) = 4972823702408169985605068068612629707457302171484944010058343536981337191056`.
    pub static INV_MOD_B: FieldElement = FieldElement([
        3843051553829520,
        3394345223148522,
        3244765182786547,
        3746084408926180,
        12088264794607,
    ]);

    /// `C = 2009874587549`
    pub static C: FieldElement = FieldElement([2009874587549, 0, 0, 0, 0]);

    /// `(C ^ (-1)) (mod l) = 6974867113321324728532613090378096263200424274021140063642524210369192272949`.
    pub static INV_MOD_C: FieldElement = FieldElement([
        623443786605621,
        2862023947424023,
        16740108872882,
        4368084563887202,
        16954962737206,
    ]);

    /// `A + B (mod l) = 904625697166532776746648320380374280088526716493097995792780030332043239911`.
    pub static A_PLUS_B: FieldElement = FieldElement([
        2766226127823335,
        4237835465749098,
        4503599626623787,
        4503599627370495,
        2199023255551,
    ]);

    /// `A - B (mod l) = 6332379880165729437226538243027995370101315372437730818388241662867394146822`.
    pub static A_MINUS_B: FieldElement = FieldElement([
        2409288332882438,
        4182428486726422,
        2114509,
        4,
        15393162788864,
    ]);

    /// `(A - B) / 2 (mod l) = 3166189940082864718613269121513997685050657686218865409194120831433697073411`.
    pub static A_MINUS_B_HALF: FieldElement = FieldElement([
        1204644166441219,
        4343014057048459,
        1057254,
        2,
        7696581394432,
    ]);

    /// `B - A (mod l) = 904625697166532776746648320014998870755800986942176787613709275418060104167`.
    pub static B_MINUS_A: FieldElement = FieldElement([
        2766226127823335,
        4237835465749098,
        4503599626623787,
        4503599627370491,
        2199023255551,
    ]);

    /// `A * B (mod l) = 918847811638530094170030839746468112210851935758749834752998326598248143582`.
    pub static A_TIMES_B: FieldElement = FieldElement([
        2201910185007838,
        1263014888683320,
        1977367609994094,
        4238575041099341,
        2233595300724,
    ]);

    /// `A * C (mod l) = 367179375066579585494548942140953299433414959963106839625728`.
    pub static A_TIMES_C: FieldElement = FieldElement([0, 0, 0, 4019749175098, 0]);

    /// `A ^ C (mod l) = 4926010953911309783511345566079477610384765538467028491833000545584570071784`.
    pub static A_POW_C: FieldElement = FieldElement([
        2259014482295528,
        2217393058433059,
        1440043558784742,
        1085733660253890,
        11974469306680,
    ]);

    /// `A ^ B (mod l) = 612533706002824166597228381427431280753593716093812822782273907565605469682`.
    pub static A_POW_B: FieldElement = FieldElement([
        2052637523230194,
        348932787374078,
        3510905667454299,
        1125398793242937,
        1488986957289,
    ]);

    /// `2^197 (mod l) = 200867255532373784442745261542645325315275374222849104412672`.
    pub static TWO_POW_197: FieldElement = FieldElement([0, 0, 0, 2199023255552, 0]);

    /// `2^252 (mod l) = 7237005577332262213973186563042994240829374041602535252466099000494570602496`.
    pub static TWO_POW_252: FieldElement = FieldElement([0, 0, 0, 0, 17592186044416]);

    /// `2^104 (mod l) = 20282409603651670423947251286016`.
    pub static TWO_POW_104: FieldElement = FieldElement([0, 0, 1, 0, 0]);

    /// `Sqrt(17) (mod l) neg result = 6026942329506939059853402327369035495094411027391394856339285515474638846327`.
    pub static SQRT1_27_NEG: FieldElement = FieldElement([
        933733106825591,
        3470287880816342,
        2891894702196915,
        3836949834964192,
        14650685232542,
    ]);

    /// `Sqrt(17) (mod l) pos result = 1210063247825323154119784235673958745762705331988512749662665422810815404662`.
    pub static SQRT1_27_POS: FieldElement = FieldElement([
        4241781353880182,
        446376444288682,
        1611704926541382,
        666649792406303,
        2941500811873,
    ]);

    /// `InvSqrt(27) (mod l)` = `4686966027373617257777021023095661060676787060461041876429863790088902887212`.
    pub static INV_SQRT_27: FieldElement = FieldElement([
        2352169988867884,
        2446401460527425,
        986927416739735,
        989222758354178,
        11393383279360,
    ]);

    //------------------ Tests ------------------//

    #[test]
    fn addition_with_modulo() {
        let res = &FieldElement::minus_one() + &FieldElement::one();
        for i in 0..5 {
            assert!(res[i] == FieldElement::zero()[i]);
        }
    }

    #[test]
    fn addition_without_modulo() {
        let res = &A + &B;
        for i in 0..5 {
            assert!(res[i] == A_PLUS_B[i]);
        }
    }

    #[test]
    fn addition_mod_0() {
        let res = &FieldElement::minus_one() + &FieldElement::one();
        for i in 0..5 {
            assert!(res[i] == FieldElement::zero()[i]);
        }
    }

    #[test]
    fn add_field_l() {
        let a: FieldElement = FieldElement([2, 0, 0, 0, 0]);
        let res = &a + &constants::FIELD_L;
        for i in 0..5 {
            assert!(res[i] == a[i]);
        }
    }

    #[test]
    fn subtraction_with_mod() {
        let res = &A - &B;
        for i in 0..5 {
            assert!(res[i] == A_MINUS_B[i]);
        }
    }

    #[test]
    fn subtraction_without_mod() {
        let res = &B - &A;
        for i in 0..5 {
            assert!(res[i] == B_MINUS_A[i]);
        }
    }

    #[test]
    fn subtract_equals() {
        let res = &B - &B;
        for i in 0..5 {
            assert!(res[i] == FieldElement::zero()[i]);
        }
    }

    #[test]
    fn subtract_field_l() {
        let a: FieldElement = FieldElement([2, 0, 0, 0, 0]);
        let res = &a - &constants::FIELD_L;
        for i in 0..5 {
            assert!(res[i] == a[i]);
        }
    }

    #[test]
    fn mul_with_modulo() {
        let res = &A * &B;
        for i in 0..5 {
            assert!(res[i] == A_TIMES_B[i]);
        }
    }

    #[test]
    fn mul_without_modulo() {
        let res = &A * &C;
        for i in 0..5 {
            assert!(res[i] == A_TIMES_C[i]);
        }
    }

    #[test]
    fn square() {
        let res = &A.square();
        for i in 0..5 {
            assert!(res[i] == A_SQUARE[i]);
        }

        let res = &B.square();
        for i in 0..5 {
            assert!(res[i] == B_SQUARE[i]);
        }
    }

    #[test]
    fn square_zero_and_identity() {
        let zero = &FieldElement::zero().square();
        let one = &FieldElement::identity().square();

        for i in 0..5 {
            assert!(zero[i] == FieldElement::zero()[i]);
            assert!(one[i] == FieldElement::one()[i]);
        }
    }

    #[test]
    fn division() {
        let a: FieldElement = FieldElement([86649, 0, 0, 0, 0]);
        let b: FieldElement = FieldElement([86650, 0, 0, 0, 0]);

        let expected = FieldElement([
            939392471225133,
            587442007554368,
            4497154776428662,
            4184267646867733,
            2921744366591,
        ]);

        let res = -&a / b;

        for _i in 0..5 {
            assert!(res == expected);
        }
    }

    #[test]
    fn a_pow_b() {
        let res = A.pow(&C);
        let res2 = A.pow(&B);

        assert!(res == A_POW_C);
        assert!(res2 == A_POW_B);
    }

    #[test]
    fn legendre_symbol() {
        println!("{:?}", FieldElement::minus_one().half());
        let res1 = A.legendre_symbol();
        let res2 = FieldElement::from(17u8).legendre_symbol();

        assert!(!bool::from(res1));
        assert!(bool::from(res2));
    }

    #[test]
    fn mod_sqrt_tonelli_shanks() {
        // Test for valid Quadratic-residue values.
        let inp = FieldElement::from(17u8);
        let sqrt = inp.mod_sqrt(Choice::from(0u8)).unwrap();
        assert!(sqrt == SQRT1_27_NEG);

        let sqrt = inp.mod_sqrt(Choice::from(1u8)).unwrap();
        assert!(sqrt == SQRT1_27_POS);

        // Test for `0`
        let sqrt_zero = FieldElement::zero().mod_sqrt(Choice::from(0u8)).unwrap();
        assert!(sqrt_zero == FieldElement::zero());
        let sqrt_zero = FieldElement::zero().mod_sqrt(Choice::from(1u8)).unwrap();
        assert!(sqrt_zero == FieldElement::zero());
    }

    #[test]
    fn inv_sqrt() {
        let var = FieldElement::from(27u8);
        let res = var.inv_sqrt().1;
        assert!(-res == INV_SQRT_27);
    }

    #[allow(non_snake_case)]
    #[test]
    fn non_QRmod_sqrt_tonelli_shanks() {
        // Test for non-valid Quadratic-residue values.
        assert!(A.mod_sqrt(Choice::from(0u8)).is_none());
        assert!(A.mod_sqrt(Choice::from(1u8)).is_none());
    }

    #[test]
    fn from_bytes_conversion() {
        let num = FieldElement::from_bytes(&MINUS_ONE_BYTES);
        for i in 0..5 {
            assert!(num[i] == FieldElement::minus_one()[i]);
        }
    }

    #[test]
    fn to_bytes_conversion() {
        let bytes = FieldElement::minus_one().to_bytes();
        for i in 0..32 {
            assert!(bytes[i] == MINUS_ONE_BYTES[i]);
        }
    }

    #[test]
    fn from_u8() {
        let res = FieldElement::from(2u8);
        let two = FieldElement([2, 0, 0, 0, 0]);

        for i in 0..5 {
            assert!(res[i] == two[i]);
        }
    }

    #[test]
    fn from_u16() {
        let res = FieldElement::from(32768u16);
        let two_pow_15 = FieldElement([32768, 0, 0, 0, 0]);

        for i in 0..5 {
            assert!(res[i] == two_pow_15[i]);
        }
    }

    #[test]
    fn from_u32() {
        let res = FieldElement::from(2147483648u32);
        let two_pow_31 = FieldElement([2147483648, 0, 0, 0, 0]);
        print!("{:?}", res);
        for i in 0..5 {
            assert!(res[i] == two_pow_31[i]);
        }
    }

    #[test]
    fn from_u64() {
        let res = FieldElement::from(18446744073709551615u64);
        let two_pow_64_minus_one = FieldElement([4503599627370495, 4095, 0, 0, 0]);
        for i in 0..5 {
            assert!(res[i] == two_pow_64_minus_one[i]);
        }
    }

    #[test]
    fn from_u128() {
        let res = FieldElement::from(170141183460469231731687303715884105727u128);
        let two_pow_127_minus_one =
            FieldElement([4503599627370495, 4503599627370495, 8388607, 0, 0]);
        for i in 0..5 {
            assert!(res[i] == two_pow_127_minus_one[i]);
        }
    }

    #[test]
    fn from_ristretto255scalar() {
        // a = `2238329342913194256032495932344128051776374960164957527413114840482143558222` = res.
        let a: Ristretto255Scalar = Ristretto255Scalar::from_canonical_bytes([
            0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84, 0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2,
            0x7d, 0x52, 0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44, 0xd4, 0x49, 0xf4, 0xa8,
            0x79, 0xd9, 0xf2, 0x04,
        ])
        .unwrap();
        let a_conv = FieldElement::from(&a);
        let res = FieldElement([
            2330265455450702,
            481909309544512,
            146945097235906,
            1298816433963441,
            5441077225716,
        ]);

        for i in 0..5 {
            assert!(a_conv[i] == res[i]);
        }
    }

    #[test]
    fn into_ristretto255scalar() {
        // a = `2238329342913194256032495932344128051776374960164957527413114840482143558222` = res.
        let a: Ristretto255Scalar = Ristretto255Scalar::from_canonical_bytes([
            0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84, 0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2,
            0x7d, 0x52, 0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44, 0xd4, 0x49, 0xf4, 0xa8,
            0x79, 0xd9, 0xf2, 0x04,
        ])
        .unwrap();
        let res: Ristretto255Scalar = FieldElement([
            2330265455450702,
            481909309544512,
            146945097235906,
            1298816433963441,
            5441077225716,
        ])
        .into();

        for i in 0..32 {
            assert!(a[i] == res[i]);
        }
    }

    #[test]
    fn two_pow_k() {
        // Check for 0 value
        let zero = FieldElement::two_pow_k(0u64);
        for i in 0..5 {
            assert!(zero[i] == FieldElement::one()[i]);
        }

        // Check for MAX value
        let max = FieldElement::two_pow_k(252u64);
        for i in 0..5 {
            assert!(max[i] == TWO_POW_252[i]);
        }

        // Check for non 52-multiple `k` values
        let non_multiple = FieldElement::two_pow_k(197u64);
        for i in 0..5 {
            assert!(non_multiple[i] == TWO_POW_197[i]);
        }

        // Check for 52-multiple `k` values
        let non_multiple = FieldElement::two_pow_k(104u64);
        for i in 0..5 {
            assert!(non_multiple[i] == TWO_POW_104[i]);
        }
    }

    #[test]
    fn ord_impl() {
        assert!(&FieldElement([2, 0, 0, 0, 0]) < &FieldElement([0, 2, 0, 0, 0]));
        assert!(
            &FieldElement([0, 0, 0, 0, 1]) > &FieldElement([0, 2498436546, 6587652167965486, 0, 0])
        );
        assert!(&FieldElement([0, 1, 2, 3, 4]) == &FieldElement([0, 1, 2, 3, 4]));
    }

    #[test]
    fn half() {
        let two_pow_52: FieldElement = FieldElement([0, 1, 0, 0, 0]);
        let half: FieldElement = FieldElement([2251799813685248, 0, 0, 0, 0]);

        let comp_half = two_pow_52.half_without_mod();
        for i in 0..5 {
            assert!(comp_half[i] == half[i])
        }

        let a_minus_b_half_comp = A_MINUS_B.half_without_mod();
        for i in 0..5 {
            assert!(a_minus_b_half_comp[i] == A_MINUS_B_HALF[i]);
        }
    }

    #[test]
    fn to_montgomery_conv() {
        let mont_a = &A.to_montgomery();
        for i in 0..5 {
            assert!(mont_a[i] == INV_MONT_A[i])
        }
    }

    #[test]
    fn from_montgomery_conv() {
        let out_mont_a = &INV_MONT_A.from_montgomery();
        for i in 0..5 {
            assert!(out_mont_a[i] == A[i]);
        }
    }

    #[test]
    fn negation() {
        let minus_a = -&A;
        let minus_b = -&B;

        for i in 0..5 {
            assert!(minus_a[i] == MINUS_A[i]);
            assert!(minus_b[i] == MINUS_B[i]);
        }
    }

    #[test]
    fn negate_one() {
        let minus_one = -&FieldElement::one();
        for i in 0..5 {
            assert!(minus_one[i] == FieldElement::minus_one()[i]);
        }

        let one = -&FieldElement::minus_one();
        for i in 0..5 {
            assert!(one[i] == FieldElement::one()[i]);
        }
    }

    #[test]
    fn negate_zero() {
        let minus_zero = -&FieldElement::zero();
        for i in 0..5 {
            assert!(minus_zero[i] == FieldElement::zero()[i]);
        }
    }

    #[test]
    fn l_field_high_bit() {
        let msb = &constants::FIELD_L.to_bytes();
        let pos_sign = 1u8 << 7;
        assert!(msb[31] < pos_sign);
    }

    #[test]
    fn savas_koc_inverse() {
        let res = FieldElement::inverse(&A);
        for i in 0..5 {
            assert!(res[i] == INV_MOD_A[i]);
        }

        let res = FieldElement::inverse(&B);
        for i in 0..5 {
            assert!(res[i] == INV_MOD_B[i]);
        }

        let res = FieldElement::inverse(&C);
        for i in 0..5 {
            assert!(res[i] == INV_MOD_C[i]);
        }
    }

    #[test]
    fn evenness() {
        // Even number should return true.
        assert!(A.is_even());
        // Odd number should return false.
        assert!(!B.is_even());
    }
}

//! Symbolic parity prefixes, their affine forms, and congruence cylinders.
//!
//! A *parity prefix* of length `k` is the sequence of parities of
//! `n, T(n), ..., T^(k-1)(n)`. Two facts, both proved by induction on `k`,
//! underlie this module:
//!
//! 1. **Affine form.** If `n` has parity prefix `p` with `r` odd entries then
//!    `T^k(n) = (3^r * n + c) / 2^k`, where `c` depends only on `p`:
//!    `c = 0` for the empty prefix, an even step keeps `c`, and an odd step at
//!    position `k` replaces `c` by `3c + 2^k`.
//! 2. **Cylinder.** The set of non-negative integers with parity prefix `p` is
//!    exactly one residue class modulo `2^k`. Indeed, if `n = rho + 2^k * t`
//!    with `rho` in the class of the length-`k` prefix, then
//!    `T^k(n) = T^k(rho) + 3^r * t`, so the next parity is the parity of
//!    `T^k(rho) + t` and each choice of the next parity selects exactly one
//!    of the two classes modulo `2^(k+1)`.
//!
//! The residue is computed in two independent ways ([`Cylinder::extend`] and
//! [`residue_by_inverse`]) so the two can be cross-validated.

use std::fmt;
use std::str::FromStr;

use num_bigint::BigUint;
use num_traits::{One, Pow, Zero};

use crate::collatz;

/// A finite parity sequence; `true` means an odd step.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ParityPrefix(Vec<bool>);

impl ParityPrefix {
    pub fn empty() -> Self {
        Self(Vec::new())
    }

    pub fn from_bits(bits: Vec<bool>) -> Self {
        Self(bits)
    }

    /// The prefix `1^k`, realised by `n = -1 (mod 2^k)`.
    pub fn all_odd(len: usize) -> Self {
        Self(vec![true; len])
    }

    /// The actual parity prefix of `n`, by direct iteration.
    pub fn of(n: &BigUint, len: usize) -> Self {
        Self(collatz::parity_vector(n, len))
    }

    pub fn bits(&self) -> &[bool] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn odd_count(&self) -> usize {
        self.0.iter().filter(|&&odd| odd).count()
    }

    pub fn push(&mut self, odd: bool) {
        self.0.push(odd);
    }
}

impl fmt::Display for ParityPrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for &odd in &self.0 {
            f.write_str(if odd { "1" } else { "0" })?;
        }
        Ok(())
    }
}

/// Error for a parity string containing something other than `0` / `1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseParityError(pub char);

impl fmt::Display for ParseParityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid parity character {:?}; expected only '0' (even) or '1' (odd)",
            self.0
        )
    }
}

impl std::error::Error for ParseParityError {}

impl FromStr for ParityPrefix {
    type Err = ParseParityError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.chars()
            .map(|ch| match ch {
                '0' => Ok(false),
                '1' => Ok(true),
                other => Err(ParseParityError(other)),
            })
            .collect::<Result<Vec<bool>, _>>()
            .map(Self)
    }
}

/// The affine form `T^k(n) = (3^r * n + c) / 2^k` attached to a parity prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineMap {
    steps: usize,
    odd_steps: usize,
    multiplier: BigUint,
    offset: BigUint,
}

impl AffineMap {
    /// The identity map (empty prefix): `k = 0`, `r = 0`, `c = 0`.
    pub fn identity() -> Self {
        Self {
            steps: 0,
            odd_steps: 0,
            multiplier: BigUint::one(),
            offset: BigUint::zero(),
        }
    }

    pub fn from_prefix(prefix: &ParityPrefix) -> Self {
        let mut map = Self::identity();
        for &odd in prefix.bits() {
            map.push(odd);
        }
        map
    }

    /// Composes with one more step of the given parity.
    pub fn push(&mut self, odd: bool) {
        if odd {
            self.offset = &self.offset * 3u32 + (BigUint::one() << self.steps);
            self.multiplier *= 3u32;
            self.odd_steps += 1;
        }
        self.steps += 1;
    }

    /// `k`, the number of steps.
    pub fn steps(&self) -> usize {
        self.steps
    }

    /// `r`, the number of odd steps.
    pub fn odd_steps(&self) -> usize {
        self.odd_steps
    }

    /// `3^r`.
    pub fn multiplier(&self) -> &BigUint {
        &self.multiplier
    }

    /// `c`.
    pub fn offset(&self) -> &BigUint {
        &self.offset
    }

    /// `2^k`.
    pub fn denominator(&self) -> BigUint {
        BigUint::one() << self.steps
    }

    /// `3^r * n + c`.
    pub fn numerator(&self, n: &BigUint) -> BigUint {
        &self.multiplier * n + &self.offset
    }

    /// `(3^r * n + c) / 2^k` when the division is exact, otherwise `None`.
    ///
    /// The division is exact precisely when `n` lies in the cylinder of the
    /// prefix, and then the value equals `T^k(n)`.
    pub fn apply(&self, n: &BigUint) -> Option<BigUint> {
        let numerator = self.numerator(n);
        let quotient = &numerator >> self.steps;
        if (&quotient << self.steps) == numerator {
            Some(quotient)
        } else {
            None
        }
    }
}

/// Closed form of the offset, independent of the recursion in
/// [`AffineMap::push`]:
/// `c = sum over odd positions i of 3^(number of odd positions after i) * 2^i`.
pub fn closed_form_offset(bits: &[bool]) -> BigUint {
    let three = BigUint::from(3u32);
    let mut odd_after = bits.iter().filter(|&&odd| odd).count();
    let mut total = BigUint::zero();
    for (i, &odd) in bits.iter().enumerate() {
        if odd {
            odd_after -= 1;
            total += Pow::pow(&three, odd_after) << i;
        }
    }
    total
}

/// The residue of the cylinder, derived from the affine form alone:
/// membership forces `3^r * n + c = 0 (mod 2^k)`, i.e.
/// `n = -c * (3^r)^(-1) (mod 2^k)`. Since the cylinder is a single class
/// modulo `2^k`, this necessary condition determines it.
pub fn residue_by_inverse(map: &AffineMap) -> BigUint {
    let modulus = map.denominator();
    if modulus.is_one() {
        return BigUint::zero();
    }
    let inverse = map
        .multiplier()
        .modinv(&modulus)
        .expect("a power of 3 is invertible modulo a power of 2");
    let negated_offset = (&modulus - map.offset() % &modulus) % &modulus;
    negated_offset * inverse % modulus
}

/// A congruence cylinder: all `n = residue (mod 2^k)`, which is exactly the
/// set of non-negative integers whose parity prefix is `prefix`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cylinder {
    prefix: ParityPrefix,
    affine: AffineMap,
    residue: BigUint,
}

impl Cylinder {
    /// The cylinder of the empty prefix: all non-negative integers.
    pub fn root() -> Self {
        Self {
            prefix: ParityPrefix::empty(),
            affine: AffineMap::identity(),
            residue: BigUint::zero(),
        }
    }

    pub fn from_prefix(prefix: &ParityPrefix) -> Self {
        let mut cylinder = Self::root();
        for &odd in prefix.bits() {
            cylinder = cylinder.extend(odd);
        }
        cylinder
    }

    /// The length-`len` cylinder containing `n`.
    pub fn containing(n: &BigUint, len: usize) -> Self {
        Self::from_prefix(&ParityPrefix::of(n, len))
    }

    /// The sub-cylinder obtained by prescribing the next parity.
    pub fn extend(&self, odd: bool) -> Self {
        let image = self
            .affine
            .apply(&self.residue)
            .expect("the residue lies in its own cylinder");
        let residue = if collatz::is_odd(&image) == odd {
            self.residue.clone()
        } else {
            &self.residue + self.modulus()
        };
        let mut prefix = self.prefix.clone();
        prefix.push(odd);
        let mut affine = self.affine.clone();
        affine.push(odd);
        Self {
            prefix,
            affine,
            residue,
        }
    }

    pub fn prefix(&self) -> &ParityPrefix {
        &self.prefix
    }

    pub fn affine(&self) -> &AffineMap {
        &self.affine
    }

    /// The residue, normalised to `0 <= residue < 2^k`.
    pub fn residue(&self) -> &BigUint {
        &self.residue
    }

    /// `2^k`.
    pub fn modulus(&self) -> BigUint {
        self.affine.denominator()
    }

    pub fn len(&self) -> usize {
        self.prefix.len()
    }

    pub fn is_empty(&self) -> bool {
        self.prefix.is_empty()
    }

    pub fn contains(&self, n: &BigUint) -> bool {
        n % self.modulus() == self.residue
    }

    /// `residue + t * 2^k`.
    pub fn member(&self, t: &BigUint) -> BigUint {
        &self.residue + t * self.modulus()
    }

    /// The least member that is `>= bound`.
    pub fn least_member_at_least(&self, bound: &BigUint) -> BigUint {
        if bound <= &self.residue {
            return self.residue.clone();
        }
        let modulus = self.modulus();
        let gap = bound - &self.residue;
        let t = (&gap + &modulus - 1u32) / &modulus;
        self.member(&t)
    }

    /// `T^k(n)` through the affine form, or `None` if `n` is not a member.
    pub fn image(&self, n: &BigUint) -> Option<BigUint> {
        if self.contains(n) {
            self.affine.apply(n)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_and_display_round_trip() {
        let prefix: ParityPrefix = "11010".parse().unwrap();
        assert_eq!(prefix.len(), 5);
        assert_eq!(prefix.odd_count(), 3);
        assert_eq!(prefix.to_string(), "11010");
        assert_eq!("10x".parse::<ParityPrefix>(), Err(ParseParityError('x')));
    }

    #[test]
    fn known_small_cylinders() {
        // n = 1 (mod 4): odd then even, T^2(n) = (3n + 1) / 4.
        let cylinder = Cylinder::from_prefix(&"10".parse().unwrap());
        assert_eq!(cylinder.residue(), &BigUint::from(1u32));
        assert_eq!(cylinder.affine().offset(), &BigUint::from(1u32));
        assert_eq!(
            cylinder.image(&BigUint::from(5u32)),
            Some(BigUint::from(4u32))
        );
        assert_eq!(cylinder.image(&BigUint::from(3u32)), None);
        // n = 3 (mod 4): two odd steps, T^2(n) = (9n + 5) / 4.
        let cylinder = Cylinder::from_prefix(&"11".parse().unwrap());
        assert_eq!(cylinder.residue(), &BigUint::from(3u32));
        assert_eq!(cylinder.affine().offset(), &BigUint::from(5u32));
    }

    #[test]
    fn least_member_at_least_is_tight() {
        let cylinder = Cylinder::from_prefix(&"110".parse().unwrap());
        let modulus = cylinder.modulus();
        for bound in 0u32..40 {
            let bound = BigUint::from(bound);
            let member = cylinder.least_member_at_least(&bound);
            assert!(cylinder.contains(&member) && member >= bound);
            assert!(member < &bound + &modulus);
        }
    }
}

//! Conditional descent certificates for parity cylinders.
//!
//! For a cylinder with affine form `T^k(n) = (3^r n + c) / 2^k`:
//!
//! ```text
//! T^k(n) < n   <=>   3^r n + c < 2^k n   <=>   (2^k - 3^r) n > c.
//! ```
//!
//! * If `2^k > 3^r`, write `d = 2^k - 3^r > 0`. Then `T^k(n) < n` holds for a
//!   member `n` **iff** `n >= N0 = floor(c / d) + 1`. That is a
//!   [`DescentCertificate`]: an exact, conditional statement about one residue
//!   class above an explicit integer threshold.
//! * If `2^k <= 3^r` then `T^k(n) >= n` for every member, so *this* prefix
//!   length gives no descent and the class stays uncovered at this length.
//!
//! A certificate says nothing about members below the threshold (they are
//! listed as exceptions), nothing about other classes, and nothing about
//! convergence to 1.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};

use crate::prefix::Cylinder;
use crate::serde_dec;

/// At most this many below-threshold members are listed explicitly; the exact
/// count is always recorded in `exception_count`.
pub const MAX_LISTED_EXCEPTIONS: usize = 16;

/// A sound conditional descent statement for one residue class.
///
/// Claim: for every integer `n >= threshold` with `n = residue (mod modulus)`,
/// `T^steps(n) < n`; and for every positive member below `threshold`,
/// `T^steps(n) >= n`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DescentCertificate {
    /// Parity prefix as a string of `0` (even) and `1` (odd).
    pub parity: String,
    /// `k`: number of iterations of `T`.
    pub steps: usize,
    /// `r`: number of odd steps.
    pub odd_steps: usize,
    /// `c` in `T^k(n) = (3^r n + c) / 2^k`.
    #[serde(with = "serde_dec")]
    pub offset: BigUint,
    #[serde(with = "serde_dec")]
    pub residue: BigUint,
    /// `2^k`.
    #[serde(with = "serde_dec")]
    pub modulus: BigUint,
    /// `d = 2^k - 3^r`, strictly positive.
    #[serde(with = "serde_dec")]
    pub margin: BigUint,
    /// `N0 = floor(c / d) + 1`.
    #[serde(with = "serde_dec")]
    pub threshold: BigUint,
    /// Exact number of positive class members below the threshold.
    #[serde(with = "serde_dec")]
    pub exception_count: BigUint,
    /// The smallest such members (up to [`MAX_LISTED_EXCEPTIONS`]).
    #[serde(with = "serde_dec::vec")]
    pub exceptions: Vec<BigUint>,
}

impl DescentCertificate {
    /// The claim in words.
    pub fn statement(&self) -> String {
        format!(
            "for all n >= {} with n = {} (mod 2^{}): T^{}(n) = (3^{} n + {}) / 2^{} < n",
            self.threshold,
            self.residue,
            self.steps,
            self.steps,
            self.odd_steps,
            self.offset,
            self.steps
        )
    }

    /// `true` when the list of exceptions is complete.
    pub fn exceptions_complete(&self) -> bool {
        self.exception_count == BigUint::from(self.exceptions.len())
    }
}

/// Builds the descent certificate of a cylinder at exactly its own length, or
/// returns `None` when `2^k <= 3^r` (no member descends at step `k`).
pub fn certify(cylinder: &Cylinder) -> Option<DescentCertificate> {
    let affine = cylinder.affine();
    let modulus = cylinder.modulus();
    if &modulus <= affine.multiplier() {
        return None;
    }
    let margin = &modulus - affine.multiplier();
    let threshold = affine.offset() / &margin + 1u32;
    let residue = cylinder.residue().clone();

    // Positive members below the threshold: residue + t * modulus, t >= 0.
    let first_positive = if residue.is_zero() {
        modulus.clone()
    } else {
        residue.clone()
    };
    let exception_count = if first_positive >= threshold {
        BigUint::zero()
    } else {
        (&threshold - 1u32 - &first_positive) / &modulus + 1u32
    };
    let mut exceptions = Vec::new();
    let mut member = first_positive;
    while member < threshold && exceptions.len() < MAX_LISTED_EXCEPTIONS {
        exceptions.push(member.clone());
        member += &modulus;
    }

    Some(DescentCertificate {
        parity: cylinder.prefix().to_string(),
        steps: affine.steps(),
        odd_steps: affine.odd_steps(),
        offset: affine.offset().clone(),
        residue,
        modulus,
        margin,
        threshold,
        exception_count,
        exceptions,
    })
}

/// A residue class that received no certificate up to the explored depth.
/// This is an explicit record of what is **not** covered.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UncoveredClass {
    pub parity: String,
    pub steps: usize,
    pub odd_steps: usize,
    #[serde(with = "serde_dec")]
    pub residue: BigUint,
    #[serde(with = "serde_dec")]
    pub modulus: BigUint,
}

impl UncoveredClass {
    fn from_cylinder(cylinder: &Cylinder) -> Self {
        Self {
            parity: cylinder.prefix().to_string(),
            steps: cylinder.len(),
            odd_steps: cylinder.affine().odd_steps(),
            residue: cylinder.residue().clone(),
            modulus: cylinder.modulus(),
        }
    }
}

/// One leaf of the first-descent tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum CoverNode {
    /// The shortest prefix of this branch with `2^k > 3^r`.
    Certified(DescentCertificate),
    /// A depth-limit class with `2^j < 3^(r_j)` for every prefix length
    /// `1 <= j <= depth`.
    Uncovered(UncoveredClass),
}

/// Walks the first-descent tree to `depth`, in a deterministic order (even
/// branch before odd branch), calling `visit` once per leaf.
///
/// A branch stops at the *first* length `k >= 1` where `2^k > 3^r`. For such a
/// leaf, every proper prefix has `2^j < 3^(r_j)` and therefore `T^j(n) > n`
/// for all members, so for members `n >= threshold` the stopping time is
/// exactly `k`. Branches that reach `depth` without descending are reported
/// as uncovered. The leaves partition the non-negative integers.
pub fn walk_first_descent<F: FnMut(CoverNode)>(depth: usize, mut visit: F) {
    let mut stack = vec![Cylinder::root()];
    while let Some(cylinder) = stack.pop() {
        if let Some(certificate) = certify(&cylinder) {
            visit(CoverNode::Certified(certificate));
        } else if cylinder.len() >= depth {
            visit(CoverNode::Uncovered(UncoveredClass::from_cylinder(
                &cylinder,
            )));
        } else {
            stack.push(cylinder.extend(true));
            stack.push(cylinder.extend(false));
        }
    }
}

/// The collected first-descent cover to a fixed depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescentCover {
    pub depth: usize,
    pub certificates: Vec<DescentCertificate>,
    pub uncovered: Vec<UncoveredClass>,
}

impl DescentCover {
    pub fn build(depth: usize) -> Self {
        let mut cover = Self {
            depth,
            certificates: Vec::new(),
            uncovered: Vec::new(),
        };
        walk_first_descent(depth, |node| match node {
            CoverNode::Certified(certificate) => cover.certificates.push(certificate),
            CoverNode::Uncovered(class) => cover.uncovered.push(class),
        });
        cover
    }

    /// Number of residue classes modulo `2^depth` covered by a certificate.
    /// The covered natural density is this value divided by `2^depth`.
    ///
    /// A density is **not** a convergence statement: the uncovered set is
    /// non-empty at every depth, and certificates only assert one descent.
    pub fn covered_classes(&self) -> BigUint {
        self.total_classes() - BigUint::from(self.uncovered.len())
    }

    /// `2^depth`.
    pub fn total_classes(&self) -> BigUint {
        BigUint::one() << self.depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn certificate_for(parity: &str) -> Option<DescentCertificate> {
        certify(&Cylinder::from_prefix(&parity.parse().unwrap()))
    }

    #[test]
    fn even_class_descends_immediately() {
        let cert = certificate_for("0").unwrap();
        assert_eq!(cert.threshold, BigUint::one());
        assert_eq!(cert.exception_count, BigUint::zero());
    }

    #[test]
    fn one_mod_four_has_the_trivial_cycle_as_exception() {
        let cert = certificate_for("10").unwrap();
        assert_eq!(cert.residue, BigUint::one());
        assert_eq!(cert.threshold, BigUint::from(2u32));
        assert_eq!(cert.exceptions, vec![BigUint::one()]);
        assert!(cert.exceptions_complete());
    }

    #[test]
    fn expanding_prefixes_get_no_certificate() {
        for parity in ["", "1", "11", "110", "1101"] {
            assert!(certificate_for(parity).is_none(), "{parity}");
        }
        let cert = certificate_for("11010").unwrap();
        assert_eq!((cert.steps, cert.odd_steps), (5, 3));
        assert_eq!(cert.margin, BigUint::from(5u32));
    }

    #[test]
    fn non_minimal_prefix_threshold_is_exact() {
        // 1^4 0^3: c = 3^4 - 2^4 = 65, d = 2^7 - 3^4 = 47, N0 = 2.
        let cert = certificate_for("1111000").unwrap();
        assert_eq!(cert.offset, BigUint::from(65u32));
        assert_eq!(cert.threshold, BigUint::from(2u32));
        assert_eq!(cert.exception_count, BigUint::zero());
    }

    #[test]
    fn cover_partitions_the_integers() {
        for depth in 0..=12usize {
            let cover = DescentCover::build(depth);
            // Sum of 2^(depth - k) over certified leaves + uncovered = 2^depth.
            let mut total = BigUint::from(cover.uncovered.len());
            for cert in &cover.certificates {
                total += BigUint::one() << (depth - cert.steps);
            }
            assert_eq!(total, cover.total_classes(), "depth {depth}");
        }
    }
}

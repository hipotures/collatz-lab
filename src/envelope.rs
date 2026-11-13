//! Bounded comparison of Terras's mini-max envelope with exact class ratios.
//!
//! The domain is fixed at `1 <= r <= 12`, `k = bit_length(3^r) <= 20`.
//! Every first-crossing word is inspected; the refuted P1a shortcut is never
//! used. See `research/literature-cst.md`, Theorems 2.4 and 2.6, for the
//! independent extremal-word recurrence. No infinite-family claim follows.

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::Serialize;

use crate::certificate::certify;
use crate::collatz;
use crate::counting::{count_by_length, count_by_odd_positions, crossing_length};
use crate::hypothesis::Status;
use crate::prefix::{residue_by_inverse, AffineMap, Cylinder, ParityPrefix};
use crate::{serde_dec, verifier};

pub const MAX_ODD_STEPS: usize = 12;
pub const MAX_LENGTH: usize = 20;

/// A nonnegative reduced rational. Private fields keep the denominator
/// positive and equality consistent with exact cross-product ordering.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Ratio {
    #[serde(with = "serde_dec")]
    numerator: BigUint,
    #[serde(with = "serde_dec")]
    denominator: BigUint,
}

impl Ratio {
    /// Returns `None` for a zero denominator, including `0/0`.
    pub fn new(numerator: BigUint, denominator: BigUint) -> Option<Self> {
        if denominator.is_zero() {
            return None;
        }
        let (mut a, mut b) = (numerator.clone(), denominator.clone());
        while !b.is_zero() {
            let remainder = a % &b;
            a = b;
            b = remainder;
        }
        Some(Self {
            numerator: numerator / &a,
            denominator: denominator / a,
        })
    }

    /// In particular, `U / R` is `None` when `R = 0`: JSON `null`, report N/A.
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        Self::new(
            &self.numerator * &other.denominator,
            &self.denominator * &other.numerator,
        )
    }
}

impl Ord for Ratio {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.numerator * &other.denominator).cmp(&(&other.numerator * &self.denominator))
    }
}

impl PartialOrd for Ratio {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Ratio {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

/// One class, with normalized residue and least member `m >= 2`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Witness {
    pub parity: String,
    #[serde(with = "serde_dec")]
    pub residue: BigUint,
    #[serde(with = "serde_dec")]
    pub m: BigUint,
    #[serde(with = "serde_dec")]
    pub c: BigUint,
}

/// All extremizers are retained in lexicographic parity order, including ties.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnvelopeRow {
    pub r: usize,
    pub k: usize,
    #[serde(with = "serde_dec")]
    pub family_count: BigUint,
    #[serde(with = "serde_dec")]
    pub count_by_length: BigUint,
    #[serde(with = "serde_dec")]
    pub count_by_odd_positions: BigUint,
    #[serde(with = "serde_dec")]
    pub d: BigUint,
    #[serde(with = "serde_dec")]
    pub max_c: BigUint,
    #[serde(with = "serde_dec")]
    pub min_m: BigUint,
    pub terras_word: String,
    #[serde(with = "serde_dec")]
    pub terras_c: BigUint,
    pub max_c_witnesses: Vec<Witness>,
    pub min_m_witnesses: Vec<Witness>,
    pub max_ratio_witnesses: Vec<Witness>,
    pub r_ratio: Ratio,
    pub u_ratio: Ratio,
    pub e_ratio: Option<Ratio>,
    pub e_le_two: Option<bool>,
}

/// Separate evidence format; this does not change the hypothesis JSONL ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnvelopeExperiment {
    pub schema: String,
    pub tool_version: String,
    pub min_r: usize,
    pub max_r: usize,
    pub max_k: usize,
    pub zero_ratio_policy: String,
    pub e_le_two_status: Status,
    pub first_counterexample_r: Option<usize>,
    pub rows: Vec<EnvelopeRow>,
}

/// Terras's slowest admissible odd-count sequence, truncated at k-1 and
/// followed by zero. Compute its offset directly, without enumeration or
/// AffineMap. The caller checks both the odd count and the enumerated maximum.
fn terras_extremal(k: usize) -> (String, BigUint, usize) {
    let (mut power, mut offset) = (BigUint::one(), BigUint::zero());
    let mut word = String::new();
    let mut odd_steps = 0;
    for i in 0..k - 1 {
        let odd = power < (BigUint::one() << (i + 1));
        word.push(if odd { '1' } else { '0' });
        if odd {
            offset = offset * 3u32 + (BigUint::one() << i);
            power *= 3u32;
            odd_steps += 1;
        }
    }
    word.push('0');
    (word, offset, odd_steps)
}

fn checked_witness(prefix: &ParityPrefix, affine: &AffineMap) -> Result<Witness, String> {
    let residue = residue_by_inverse(affine);
    let modulus = affine.denominator();
    // All our words are nonempty, so one period suffices for residue 0 or 1.
    let m = if residue < BigUint::from(2u32) {
        &residue + &modulus
    } else {
        residue.clone()
    };
    // The lifting construction is independent of the modular inverse.
    let cylinder = Cylinder::from_prefix(prefix);
    if cylinder.affine() != affine
        || cylinder.residue() != &residue
        || cylinder.least_member_at_least(&BigUint::from(2u32)) != m
    {
        return Err(format!("{prefix}: inverse and lifted cylinder disagree"));
    }
    let cert = certify(&cylinder).ok_or_else(|| format!("{prefix}: not contracting"))?;
    // Independently rederive the closed-form offset and check the affine
    // identity and parities by direct iteration on two additional members.
    verifier::verify_certificate(&cert, 0).map_err(|e| format!("{prefix}: {e}"))?;
    if ParityPrefix::of(&m, prefix.len()) != *prefix
        || collatz::t_iter(&m, prefix.len()) * &modulus != affine.numerator(&m)
    {
        return Err(format!("{prefix}: direct iteration disagrees at m={m}"));
    }
    Ok(Witness {
        parity: prefix.to_string(),
        residue,
        m,
        c: affine.offset().clone(),
    })
}

fn enumerate_family(r: usize, k: usize) -> Result<Vec<Witness>, String> {
    let mut family = Vec::new();
    let mut stack = vec![(ParityPrefix::empty(), AffineMap::identity())];
    while let Some((prefix, affine)) = stack.pop() {
        if affine.denominator() > *affine.multiplier() {
            // Stop every branch at its first coefficient crossing, including
            // crossings with fewer than r odd steps. Never extend such a word.
            if affine.odd_steps() == r {
                if prefix.len() != k {
                    return Err(format!("r={r}: crossing has unexpected length"));
                }
                family.push(checked_witness(&prefix, &affine)?);
            }
            continue;
        }
        if prefix.len() == k {
            continue;
        }
        for odd in [true, false] {
            if odd && affine.odd_steps() == r {
                continue;
            }
            let mut next_prefix = prefix.clone();
            next_prefix.push(odd);
            let mut next_affine = affine.clone();
            next_affine.push(odd);
            stack.push((next_prefix, next_affine));
        }
    }
    family.sort_by(|a, b| a.parity.cmp(&b.parity));
    Ok(family)
}

fn summarize_family(r: usize, k: usize, family: &[Witness]) -> Result<EnvelopeRow, String> {
    let max_c = family.iter().map(|w| &w.c).max().ok_or("empty family")?;
    let min_m = family.iter().map(|w| &w.m).min().ok_or("empty family")?;
    // d is common to this family. Ranking c/m by cross multiplication scans
    // every class; minimizing m alone would reintroduce the refuted P1a.
    let best = family
        .iter()
        .max_by(|a, b| (&a.c * &b.m).cmp(&(&b.c * &a.m)))
        .ok_or("empty family")?;
    let d = (BigUint::one() << k) - BigUint::from(3u32).pow(r as u32);
    let (terras_word, terras_c, terras_r) = terras_extremal(k);
    if terras_r != r
        || &terras_c != max_c
        || !family
            .iter()
            .any(|w| w.parity == terras_word && w.c == terras_c)
    {
        return Err(format!(
            "r={r}: Terras recurrence disagrees with enumeration"
        ));
    }
    let r_ratio = Ratio::new(best.c.clone(), &d * &best.m).ok_or("zero R denominator")?;
    let u_ratio = Ratio::new(max_c.clone(), &d * min_m).ok_or("zero U denominator")?;
    let e_ratio = u_ratio.checked_div(&r_ratio);
    if e_ratio
        .as_ref()
        .is_some_and(|e| e.numerator < e.denominator)
    {
        return Err(format!("r={r}: E_r < 1"));
    }
    let e_le_two = e_ratio
        .as_ref()
        .map(|e| e.numerator <= &e.denominator * 2u32);
    Ok(EnvelopeRow {
        r,
        k,
        family_count: BigUint::from(family.len()),
        count_by_length: count_by_length(k).first_crossings[k].clone(),
        count_by_odd_positions: count_by_odd_positions(k).first_crossings_by_odd_steps[r].clone(),
        d,
        max_c: max_c.clone(),
        min_m: min_m.clone(),
        terras_word,
        terras_c,
        max_c_witnesses: family.iter().filter(|w| &w.c == max_c).cloned().collect(),
        min_m_witnesses: family.iter().filter(|w| &w.m == min_m).cloned().collect(),
        max_ratio_witnesses: family
            .iter()
            .filter(|w| &w.c * &best.m == &best.c * &w.m)
            .cloned()
            .collect(),
        r_ratio,
        u_ratio,
        e_ratio,
        e_le_two,
    })
}

/// Exhaust the fixed domain, stopping immediately on any invariant failure.
/// An E_r > 2 is an experimental outcome, not an invariant failure: the rest
/// of the fixed domain is still evaluated. No outputs are written here.
pub fn run_envelope() -> Result<EnvelopeExperiment, String> {
    let mut rows = Vec::new();
    for r in 1..=MAX_ODD_STEPS {
        let k = crossing_length(r);
        if k > MAX_LENGTH {
            return Err(format!("r={r}: crossing length exceeds {MAX_LENGTH}"));
        }
        let family = enumerate_family(r, k)?;
        let row = summarize_family(r, k, &family)?;
        if row.family_count != row.count_by_length || row.family_count != row.count_by_odd_positions
        {
            return Err(format!(
                "r={r}: enumeration and counting recurrences disagree"
            ));
        }
        rows.push(row);
    }
    let first_counterexample_r = rows
        .iter()
        .find(|row| row.e_le_two == Some(false))
        .map(|row| row.r);
    Ok(EnvelopeExperiment {
        schema: "collatz-lab-envelope-v1".into(),
        tool_version: env!("CARGO_PKG_VERSION").into(),
        min_r: 1,
        max_r: MAX_ODD_STEPS,
        max_k: MAX_LENGTH,
        zero_ratio_policy: "If R_r=0, E_r and e_le_two are null (N/A); no value is imputed.".into(),
        e_le_two_status: if first_counterexample_r.is_some() {
            Status::Refuted
        } else {
            Status::VerifiedForFiniteDomain
        },
        first_counterexample_r,
        rows,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratios_reduce_compare_and_handle_zero_without_overflow() {
        let huge = BigUint::one() << 200usize;
        let a = Ratio::new(&huge * 6u32, &huge * 9u32).unwrap();
        assert_eq!(a.to_string(), "2/3");
        let b = Ratio::new(&huge + 1u32, huge.clone()).unwrap();
        assert!(b > a);
        assert!(b > Ratio::new(huge.clone(), huge).unwrap());
        let zero = Ratio::new(BigUint::zero(), BigUint::from(7u32)).unwrap();
        assert_eq!(zero.to_string(), "0/1");
        assert!(a.checked_div(&zero).is_none());
        assert!(zero.checked_div(&zero).is_none());
        assert!(Ratio::new(BigUint::one(), BigUint::zero()).is_none());
        assert_eq!(
            serde_json::to_string(&a.checked_div(&zero)).unwrap(),
            "null"
        );
    }
}

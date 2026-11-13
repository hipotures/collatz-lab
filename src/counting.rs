//! Independent exact counts of first coefficient-crossing prefixes and of
//! surviving residue classes.
//!
//! The first-descent cover in [`crate::certificate`] *constructs* every
//! cylinder (residue, affine form, threshold). This module only *counts*
//! parity words, by two recurrences that share no code with that walker and
//! never build a residue:
//!
//! * [`count_by_length`]: a lattice recurrence over (length, odd steps),
//!   the recursion that the OEIS entry A076227 attributes to Terras (1976);
//! * [`count_by_odd_positions`]: enumeration by admissible positions of the
//!   odd steps, the organisation used in Winkler's work on coefficient
//!   stopping-time classes.
//!
//! Definitions. A parity word of length `k` with `r_j` odd steps among its
//! first `j` letters is a *survivor* if `2^j < 3^(r_j)` for all `1 <= j <= k`,
//! and a *first crossing* if its proper prefixes are survivors and
//! `2^k > 3^(r_k)`. Since every word corresponds to exactly one residue class
//! modulo `2^k` (see [`crate::prefix`]):
//!
//! * survivors of length `k` = uncovered classes modulo `2^k`
//!   (OEIS A076227, "Number of surviving Collatz residues mod 2^n");
//! * first crossings with exactly `r >= 1` odd steps = OEIS A100982(r)
//!   ("Number of admissible sequences of order n"). All of them have the same
//!   length [`crossing_length`]`(r)`.
//!
//! These are statements about finite counts only.

use num_bigint::BigUint;
use num_traits::{One, Pow, Zero};

/// The least `k >= 1` with `2^k > 3^r`, i.e. the bit length of `3^r`.
///
/// Every first crossing with `r` odd steps has exactly this length: its last
/// step is even, and a word with `r` odd steps crosses as soon as its length
/// reaches this value.
pub fn crossing_length(odd_steps: usize) -> usize {
    let power = Pow::pow(&BigUint::from(3u32), odd_steps);
    usize::try_from(power.bits()).expect("bit length fits in usize")
}

/// Counts indexed by word length, `0..=depth`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LengthCounts {
    /// `first_crossings[k]`: first crossings of length exactly `k`.
    pub first_crossings: Vec<BigUint>,
    /// `survivors[k]`: survivors of length exactly `k`.
    pub survivors: Vec<BigUint>,
}

impl LengthCounts {
    /// First crossings of length at most `depth` (the number of certificates
    /// in the first-descent cover to that depth).
    pub fn first_crossings_up_to(&self, depth: usize) -> BigUint {
        self.first_crossings[..=depth].iter().sum()
    }
}

/// Lattice recurrence. `state[r]` is the number of survivors of the current
/// length with `r` odd steps. Appending an odd step to a survivor always
/// gives a survivor (`2^k < 3^r` implies `2^(k+1) < 3^(r+1)`); appending an
/// even step gives a survivor or a first crossing according to the exact
/// comparison of `2^(k+1)` with `3^r`.
pub fn count_by_length(depth: usize) -> LengthCounts {
    let mut powers_of_three = vec![BigUint::one()];
    for r in 0..depth {
        let next = &powers_of_three[r] * 3u32;
        powers_of_three.push(next);
    }
    let mut state = vec![BigUint::zero(); depth + 2];
    state[0] = BigUint::one();
    let mut counts = LengthCounts {
        first_crossings: vec![BigUint::zero()],
        survivors: vec![BigUint::one()],
    };
    let mut power_of_two = BigUint::one();
    for length in 1..=depth {
        power_of_two <<= 1usize;
        let mut next = vec![BigUint::zero(); depth + 2];
        let mut crossings = BigUint::zero();
        for r in 0..length {
            if state[r].is_zero() {
                continue;
            }
            // Odd step: r + 1 odd steps at this length.
            assert!(
                power_of_two < powers_of_three[r + 1],
                "odd step cannot cross"
            );
            next[r + 1] += &state[r];
            // Even step: still r odd steps.
            if power_of_two > powers_of_three[r] {
                crossings += &state[r];
            } else {
                next[r] += &state[r];
            }
        }
        counts.survivors.push(next.iter().sum());
        counts.first_crossings.push(crossings);
        state = next;
    }
    counts
}

/// Counts obtained from the positions of the odd steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddPositionCounts {
    pub depth: usize,
    /// `first_crossings_by_odd_steps[r]`: first crossings with exactly `r`
    /// odd steps, for every `r` with `crossing_length(r) <= depth`.
    /// Entry 0 is the word `0`; entries `r >= 1` are OEIS A100982(r).
    pub first_crossings_by_odd_steps: Vec<BigUint>,
    /// Survivors of length exactly `depth`.
    pub survivors: BigUint,
}

impl OddPositionCounts {
    pub fn first_crossings_up_to_depth(&self) -> BigUint {
        self.first_crossings_by_odd_steps.iter().sum()
    }
}

/// Enumeration by odd positions.
///
/// Write a word by the 0-based positions `a_1 < a_2 < ... < a_r` of its odd
/// steps. No crossing happens before the word ends iff `a_1 = 0` and
/// `a_(i+1) <= crossing_length(i) - 1` for each `i >= 1`: with `i` odd steps
/// so far the word may grow to length `crossing_length(i) - 1` at most before
/// the next odd step must come. Hence
///
/// * first crossings with `r` odd steps are exactly the admissible position
///   sequences of length `r` (padded with even steps to `crossing_length(r)`);
/// * survivors of length `depth` are the admissible sequences with all
///   positions `< depth` and `crossing_length(r) > depth`.
///
/// `ways[p]` below is the number of admissible sequences of the current
/// length whose last position is `p`.
pub fn count_by_odd_positions(depth: usize) -> OddPositionCounts {
    let mut result = OddPositionCounts {
        depth,
        first_crossings_by_odd_steps: Vec::new(),
        survivors: BigUint::zero(),
    };
    // r = 0: the empty position sequence. It is the word 0 (a first crossing
    // of length 1) or, at depth 0, the empty word (a survivor).
    if crossing_length(0) <= depth {
        result.first_crossings_by_odd_steps.push(BigUint::one());
    } else {
        result.survivors += 1u32;
    }
    // r = 1: a_1 = 0. Positions never need to exceed depth.
    let mut ways = vec![BigUint::zero(); depth + 1];
    ways[0] = BigUint::one();
    for r in 1..=depth {
        if crossing_length(r) <= depth {
            result.first_crossings_by_odd_steps.push(ways.iter().sum());
        } else {
            result.survivors += ways[..depth].iter().sum::<BigUint>();
        }
        // Extend to r + 1 odd steps: a_(r+1) > a_r and a_(r+1) <= limit.
        let limit = crossing_length(r) - 1;
        let mut next = vec![BigUint::zero(); depth + 1];
        let mut running = BigUint::zero();
        for p in 0..=depth {
            if p <= limit {
                next[p] = running.clone();
            }
            running += &ways[p];
        }
        ways = next;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crossing_lengths_are_exact() {
        let expected = [1usize, 2, 4, 5, 7, 8, 10, 12, 13, 15, 16, 18, 20];
        for (r, &k) in expected.iter().enumerate() {
            assert_eq!(crossing_length(r), k);
            let power = Pow::pow(&BigUint::from(3u32), r);
            assert!((BigUint::one() << k) > power);
            assert!((BigUint::one() << (k - 1)) <= power);
        }
    }

    #[test]
    fn smallest_cases_by_hand() {
        // Length <= 4: first crossings are 0, 10, 1100; survivors of length 4
        // are 1101, 1110, 1111.
        let by_length = count_by_length(4);
        let crossings: Vec<u32> = by_length
            .first_crossings
            .iter()
            .map(|c| u32::try_from(c).unwrap())
            .collect();
        assert_eq!(crossings, vec![0, 1, 1, 0, 1]);
        assert_eq!(by_length.survivors[4], BigUint::from(3u32));
        let by_positions = count_by_odd_positions(4);
        assert_eq!(by_positions.first_crossings_by_odd_steps.len(), 3);
        assert_eq!(by_positions.survivors, BigUint::from(3u32));
    }
}

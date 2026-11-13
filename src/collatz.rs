//! The accelerated Collatz map and direct (non-symbolic) evaluation.
//!
//! These functions are the ground truth of the crate: every symbolic object
//! elsewhere is cross-checked against plain iteration of [`t_step`].

use num_bigint::BigUint;
use num_traits::One;
use serde::{Deserialize, Serialize};

/// Parity of `n`: `true` when `n` is odd.
pub fn is_odd(n: &BigUint) -> bool {
    n.bit(0)
}

/// One step of the accelerated map `T`.
///
/// The conjecture concerns positive integers; `T(0) = 0` is included only so
/// that the function is total on `BigUint`.
pub fn t_step(n: &BigUint) -> BigUint {
    if is_odd(n) {
        (n * 3u32 + 1u32) >> 1usize
    } else {
        n >> 1usize
    }
}

/// `T^steps(n)` by direct iteration.
pub fn t_iter(n: &BigUint, steps: usize) -> BigUint {
    let mut x = n.clone();
    for _ in 0..steps {
        x = t_step(&x);
    }
    x
}

/// The orbit segment `[n, T(n), ..., T^steps(n)]` (length `steps + 1`).
pub fn orbit(n: &BigUint, steps: usize) -> Vec<BigUint> {
    let mut out = Vec::with_capacity(steps + 1);
    let mut x = n.clone();
    for _ in 0..steps {
        let next = t_step(&x);
        out.push(x);
        x = next;
    }
    out.push(x);
    out
}

/// Parities of `n, T(n), ..., T^(steps-1)(n)`; `true` means odd.
pub fn parity_vector(n: &BigUint, steps: usize) -> Vec<bool> {
    let mut out = Vec::with_capacity(steps);
    let mut x = n.clone();
    for _ in 0..steps {
        out.push(is_odd(&x));
        x = t_step(&x);
    }
    out
}

/// Stopping (first-descent) time: the least `j >= 1` with `T^j(n) < n`.
///
/// Returns `None` if no such `j <= max_steps` exists. `None` is *not* evidence
/// of divergence; it only says the bounded search did not find a descent.
/// For `n = 0` and `n = 1` the answer is always `None`.
pub fn stopping_time(n: &BigUint, max_steps: u64) -> Option<u64> {
    let mut x = n.clone();
    for j in 1..=max_steps {
        x = t_step(&x);
        if &x < n {
            return Some(j);
        }
    }
    None
}

/// Total stopping time: the least `j >= 0` with `T^j(n) = 1`, searched up to
/// `max_steps`.
pub fn total_stopping_time(n: &BigUint, max_steps: u64) -> Option<u64> {
    let one = BigUint::one();
    let mut x = n.clone();
    if x == one {
        return Some(0);
    }
    for j in 1..=max_steps {
        x = t_step(&x);
        if x == one {
            return Some(j);
        }
    }
    None
}

/// One step of `T` on `u64`, or `None` if the result does not fit.
///
/// For odd `n`, `(3n + 1) / 2 = n + (n >> 1) + 1`, evaluated with a checked
/// addition so overflow can never go unnoticed.
pub fn t_step_u64(n: u64) -> Option<u64> {
    if n & 1 == 1 {
        n.checked_add((n >> 1) + 1)
    } else {
        Some(n >> 1)
    }
}

/// Same contract as [`stopping_time`], using `u64` arithmetic while it is
/// safe and continuing in `BigUint` from the first step that would overflow.
pub fn stopping_time_fast(n: u64, max_steps: u64) -> Option<u64> {
    let mut x = n;
    for j in 1..=max_steps {
        match t_step_u64(x) {
            Some(y) => {
                if y < n {
                    return Some(j);
                }
                x = y;
            }
            None => {
                let start = BigUint::from(n);
                let mut big = BigUint::from(x);
                for i in j..=max_steps {
                    big = t_step(&big);
                    if big < start {
                        return Some(i);
                    }
                }
                return None;
            }
        }
    }
    None
}

/// Result of a deterministic exhaustive check of a small range.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeOracle {
    /// Every `n` with `2 <= n <= limit` was examined.
    pub limit: u64,
    /// Step budget per starting value.
    pub max_steps: u64,
    /// Largest stopping time found, and the smallest `n` attaining it.
    pub max_stopping_time: u64,
    pub argmax: u64,
    /// Starting values with no descent within `max_steps` (kept visible).
    pub unresolved: Vec<u64>,
}

impl RangeOracle {
    /// If no value is unresolved then, by strong induction on `n`, every
    /// `1 <= n <= limit` reaches 1. This is a finite-domain statement only.
    pub fn all_reach_one(&self) -> bool {
        self.unresolved.is_empty()
    }
}

/// Computes the stopping time of every `n` in `[2, limit]`.
pub fn range_oracle(limit: u64, max_steps: u64) -> RangeOracle {
    let mut oracle = RangeOracle {
        limit,
        max_steps,
        max_stopping_time: 0,
        argmax: 0,
        unresolved: Vec::new(),
    };
    for n in 2..=limit {
        match stopping_time_fast(n, max_steps) {
            Some(time) => {
                if time > oracle.max_stopping_time {
                    oracle.max_stopping_time = time;
                    oracle.argmax = n;
                }
            }
            None => oracle.unresolved.push(n),
        }
    }
    oracle
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(n: u64) -> BigUint {
        BigUint::from(n)
    }

    #[test]
    fn orbit_of_seven() {
        let got: Vec<u64> = orbit(&big(7), 7)
            .iter()
            .map(|x| u64::try_from(x).unwrap())
            .collect();
        assert_eq!(got, vec![7, 11, 17, 26, 13, 20, 10, 5]);
        assert_eq!(stopping_time(&big(7), 100), Some(7));
        assert_eq!(total_stopping_time(&big(7), 100), Some(11));
    }

    #[test]
    fn trivial_cycle_never_descends() {
        assert_eq!(t_step(&big(1)), big(2));
        assert_eq!(t_step(&big(2)), big(1));
        assert_eq!(stopping_time(&big(1), 1000), None);
        assert_eq!(total_stopping_time(&big(1), 0), Some(0));
    }

    #[test]
    fn u64_step_reports_overflow() {
        assert_eq!(t_step_u64(u64::MAX), None);
        assert_eq!(t_step_u64(u64::MAX - 1), Some((u64::MAX - 1) / 2));
        // Largest odd value whose image still fits.
        let edge = 12_297_829_382_473_034_409u64;
        let image = t_step(&big(edge));
        assert_eq!(t_step_u64(edge).map(BigUint::from), Some(image));
        assert_eq!(t_step_u64(edge + 2), None);
        assert!(t_step(&big(edge + 2)) > big(u64::MAX));
    }

    #[test]
    fn fast_path_survives_overflow() {
        for n in [u64::MAX, u64::MAX - 2, u64::MAX - 4, (1u64 << 63) + 1] {
            assert_eq!(stopping_time_fast(n, 5000), stopping_time(&big(n), 5000));
        }
        // The step budget is honoured across the fallback boundary.
        let full = stopping_time(&big(u64::MAX), 5000).unwrap();
        assert_eq!(stopping_time_fast(u64::MAX, full - 1), None);
        assert_eq!(stopping_time_fast(u64::MAX, full), Some(full));
    }
}

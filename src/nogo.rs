//! No-go / adversarial baseline: fixed universal descent windows cannot work.
//!
//! **Identity (proved by induction on `j`).** For `L >= 0` and `0 <= j <= L`,
//!
//! ```text
//! T^j(2^L - 1) = 3^j * 2^(L - j) - 1.
//! ```
//!
//! For `j < L` the value `3^j 2^(L-j) - 1` is odd, and
//! `(3 (3^j 2^(L-j) - 1) + 1) / 2 = 3^(j+1) 2^(L-j-1) - 1`.
//!
//! More generally every `n = -1 (mod 2^W)` has parity prefix `1^W`, whose
//! affine form is `T^j(n) = (3^j (n + 1)) / 2^j - 1 > n` for `1 <= j <= W`.
//!
//! **Consequence.** For every window `W` and every bound `N` there is an
//! `n > N` with `T^j(n) > n` for all `1 <= j <= W`. So no statement of the
//! form "every sufficiently large `n` descends within `W` steps" is true, and
//! every finite-depth first-descent cover leaves the class `-1 (mod 2^depth)`
//! uncovered.
//!
//! Scope: this rules out *fixed-window* descent arguments only. It says
//! nothing about adaptive or unbounded-horizon certificates, or about other
//! kinds of potential functions.

use num_bigint::BigUint;
use num_traits::{One, Pow};

use crate::collatz;

/// `2^l - 1`.
pub fn mersenne(l: usize) -> BigUint {
    (BigUint::one() << l) - 1u32
}

/// The closed form `3^j * 2^(l - j) - 1`. Requires `j <= l`.
pub fn mersenne_closed_form(l: usize, j: usize) -> BigUint {
    assert!(j <= l, "closed form is only stated for j <= l");
    (Pow::pow(&BigUint::from(3u32), j) << (l - j)) - 1u32
}

/// Checks the identity for one `l` by direct iteration, for all `0 <= j <= l`.
/// Returns the first `j` at which it fails, if any.
pub fn check_mersenne_identity(l: usize) -> Result<(), usize> {
    let mut x = mersenne(l);
    for j in 0..=l {
        if x != mersenne_closed_form(l, j) {
            return Err(j);
        }
        x = collatz::t_step(&x);
    }
    Ok(())
}

/// The least `n >= lower_bound` with `n = -1 (mod 2^window)`.
pub fn window_witness(window: usize, lower_bound: &BigUint) -> BigUint {
    let modulus = BigUint::one() << window;
    // Least multiple of the modulus that is >= lower_bound + 1, minus 1.
    let target = lower_bound + 1u32;
    let multiple = (&target + &modulus - 1u32) / &modulus * &modulus;
    multiple - 1u32
}

/// Direct check that `T^j(n) > n` for every `1 <= j <= window`.
pub fn refutes_window(n: &BigUint, window: usize) -> bool {
    let mut x = n.clone();
    for _ in 0..window {
        x = collatz::t_step(&x);
        if &x <= n {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_is_least_and_in_class() {
        for window in 0..8usize {
            let modulus = BigUint::one() << window;
            for bound in 0u32..70 {
                let bound = BigUint::from(bound);
                let n = window_witness(window, &bound);
                assert!(n >= bound);
                assert_eq!((&n + 1u32) % &modulus, BigUint::default());
                assert!(n < &bound + &modulus);
            }
        }
    }
}

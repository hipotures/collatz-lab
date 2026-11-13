//! Exact census of paradoxical prefixes at small lengths.
//!
//! A pair `(n, k)` with `n > 2` is paradoxical when the length-`k` parity
//! prefix of `n` has `2^k > 3^r` and yet `T^k(n) >= n` (Rozier and Terracol,
//! Definition 1.1). In the lab's terms these are exactly the positive members
//! above 2 that lie below the threshold of a single-cylinder certificate, so
//! the census needs no bound on the seed: each cylinder's exception list is
//! complete.
//!
//! The result reproduces a known small case (the same five seeds at length
//! eight are a kernel-checked theorem, `paradoxical_eight_iff`, in the
//! third-party Lean project msharpe248/collatz); nothing here is new.

use collatz_lab::certificate::certify;
use collatz_lab::collatz::{stopping_time, t_iter};
use collatz_lab::prefix::Cylinder;
use num_bigint::BigUint;

/// All `(length, seed)` pairs with `seed > 2`, for every cylinder of each
/// length up to `max_len`.
fn census(max_len: usize) -> Vec<(usize, u64)> {
    let two = BigUint::from(2u32);
    let mut found = Vec::new();
    let mut level = vec![Cylinder::root()];
    for len in 1..=max_len {
        level = level
            .iter()
            .flat_map(|c| [c.extend(false), c.extend(true)])
            .collect();
        for cylinder in &level {
            let Some(cert) = certify(cylinder) else {
                continue;
            };
            assert!(cert.exceptions_complete());
            for n in cert.exceptions.iter().filter(|n| **n > two) {
                assert!(&t_iter(n, len) >= n);
                found.push((len, u64::try_from(n).unwrap()));
            }
        }
    }
    found.sort_unstable();
    found
}

#[test]
fn paradoxical_prefixes_up_to_length_14_are_five_seeds_at_length_eight() {
    let found = census(14);
    assert_eq!(found, vec![(8, 7), (8, 9), (8, 18), (8, 19), (8, 25)]);
    // None of them contradicts sigma = tau: each seed descends strictly
    // before step 8, at its own first coefficient crossing.
    let first_descents: Vec<u64> = found
        .iter()
        .map(|&(_, n)| stopping_time(&BigUint::from(n), 100).unwrap())
        .collect();
    assert_eq!(first_descents, vec![7, 2, 1, 4, 2]);
}

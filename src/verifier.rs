//! Independent deterministic verifier.
//!
//! This module deliberately does **not** use [`crate::prefix`] or the
//! certificate constructor. It re-derives everything from direct iteration of
//! [`crate::collatz::t_step`] plus elementary integer identities, so that a
//! bug in the symbolic layer cannot silently validate its own output.
//!
//! What a successful [`verify_certificate`] establishes, and how:
//!
//! * the stored parity string is the real parity prefix of class members
//!   (direct iteration of two members; the extension to the whole class is
//!   the cylinder lemma, proved by algebra in [`crate::prefix`]);
//! * the stored offset equals the closed-form sum for that parity string;
//! * the margin is `2^k - 3^r > 0` and the threshold is exactly
//!   `floor(c / margin) + 1`, checked by the two integer inequalities
//!   `margin * N0 > c >= margin * (N0 - 1)`;
//! * a few members at or above the threshold really descend and all listed
//!   exceptions really do not (direct iteration);
//! * the exception list is *exactly* the first
//!   `min(exception_count, MAX_LISTED_EXCEPTIONS)` positive class members
//!   below the threshold, in increasing order: omissions, duplicates, extra
//!   entries and wrongly truncated lists are all rejected.
//!
//! # Paradoxical prefixes versus first-crossing counterexamples
//!
//! A parity prefix of `n` with `2^k > 3^r` whose iterate nevertheless has
//! `T^k(n) >= n` is called *paradoxical*. Such prefixes exist and are
//! classical: for `n = 7` the prefix `11101001` has `3^5 / 2^8 < 1` and
//! `T^8(7) = 8 >= 7`. That is **not** a counterexample to the statement the
//! lab tests about first-descent certificates, because the coefficient
//! already crossed below 1 at step 7 (`3^4 < 2^7`), where `T^7(7) = 5 < 7`.
//!
//! [`FailureCase::ThresholdException`] means only the strong thing: the
//! prefix is a *first coefficient crossing* (`2^j < 3^(r_j)` for every
//! `1 <= j < k`, and `2^k > 3^r`) and still `T^k(n) >= n` for some `n >= 2`.
//! [`verify_failure_case`] re-derives that whole premise from the parity
//! string, so a later paradoxical segment can never be recorded under this
//! kind. No genuine instance is known; accepting one would be a
//! counterexample to the coefficient stopping time conjecture.

use num_bigint::BigUint;
use num_traits::{One, Pow, Zero};

use crate::certificate::{DescentCertificate, MAX_LISTED_EXCEPTIONS};
use crate::collatz::{is_odd, t_step};
use crate::hypothesis::FailureCase;

fn parse_parity(text: &str) -> Result<Vec<bool>, String> {
    text.chars()
        .map(|ch| match ch {
            '0' => Ok(false),
            '1' => Ok(true),
            other => Err(format!("invalid parity character {other:?}")),
        })
        .collect()
}

/// Iterates `T` directly, checking the parity at each step against `bits`.
/// Returns `T^k(n)`.
fn iterate_checking_parity(n: &BigUint, bits: &[bool]) -> Result<BigUint, String> {
    let mut x = n.clone();
    for (i, &odd) in bits.iter().enumerate() {
        if is_odd(&x) != odd {
            return Err(format!("n = {n} has the wrong parity at step {i}"));
        }
        x = t_step(&x);
    }
    Ok(x)
}

fn pow3(exponent: usize) -> BigUint {
    Pow::pow(&BigUint::from(3u32), exponent)
}

fn ensure(condition: bool, message: impl FnOnce() -> String) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message())
    }
}

/// Fully re-checks a descent certificate. `samples` members at or above the
/// threshold are additionally tested by direct iteration.
pub fn verify_certificate(cert: &DescentCertificate, samples: usize) -> Result<(), String> {
    let bits = parse_parity(&cert.parity)?;
    let k = bits.len();
    let r = bits.iter().filter(|&&odd| odd).count();
    ensure(k == cert.steps && r == cert.odd_steps, || {
        format!("step counts do not match parity string {}", cert.parity)
    })?;

    let modulus = BigUint::one() << k;
    ensure(cert.modulus == modulus, || "modulus is not 2^k".into())?;
    ensure(cert.residue < modulus, || {
        "residue is not normalised".into()
    })?;

    // Closed-form offset, independent of the recursive construction.
    let mut offset = BigUint::zero();
    let mut odd_after = r;
    for (i, &odd) in bits.iter().enumerate() {
        if odd {
            odd_after -= 1;
            offset += pow3(odd_after) << i;
        }
    }
    ensure(cert.offset == offset, || {
        "offset does not match closed form".into()
    })?;

    let multiplier = pow3(r);
    ensure(modulus > multiplier, || "2^k <= 3^r: no descent".into())?;
    ensure(cert.margin == &modulus - &multiplier, || {
        "margin is not 2^k - 3^r".into()
    })?;

    // Threshold exactness: margin * N0 > c >= margin * (N0 - 1), N0 >= 1.
    ensure(!cert.threshold.is_zero(), || {
        "threshold must be >= 1".into()
    })?;
    ensure(&cert.margin * &cert.threshold > cert.offset, || {
        "threshold too small".into()
    })?;
    ensure(
        &cert.margin * (&cert.threshold - 1u32) <= cert.offset,
        || "threshold not minimal".into(),
    )?;

    // The parity string is the true prefix of the class (two members), and
    // the affine identity holds exactly for them.
    for t in 1u32..=2 {
        let n = &cert.residue + &modulus * t;
        let image = iterate_checking_parity(&n, &bits)?;
        ensure(&image * &modulus == &multiplier * &n + &offset, || {
            format!("affine identity fails for n = {n}")
        })?;
    }

    // Members at or above the threshold descend.
    let mut n = &cert.residue + &modulus * (&cert.threshold / &modulus);
    while n < cert.threshold {
        n += &modulus;
    }
    for _ in 0..samples {
        let image = iterate_checking_parity(&n, &bits)?;
        ensure(image < n, || {
            format!("n = {n} >= threshold does not descend")
        })?;
        n += &modulus;
    }

    // Exceptions: exact count, and each one really fails to descend.
    let first_positive = if cert.residue.is_zero() {
        modulus.clone()
    } else {
        cert.residue.clone()
    };
    let expected_count = if first_positive >= cert.threshold {
        BigUint::zero()
    } else {
        (&cert.threshold - 1u32 - &first_positive) / &modulus + 1u32
    };
    ensure(cert.exception_count == expected_count, || {
        "exception count is wrong".into()
    })?;
    // The list must hold exactly the first min(count, cap) exceptions. The
    // comparison is done in BigUint so that huge counts need no cast.
    let expected_listed = expected_count.min(BigUint::from(MAX_LISTED_EXCEPTIONS));
    ensure(
        BigUint::from(cert.exceptions.len()) == expected_listed,
        || {
            format!(
                "exception list has {} entries but must list exactly {expected_listed}",
                cert.exceptions.len()
            )
        },
    )?;
    let mut expected = first_positive;
    for exception in &cert.exceptions {
        ensure(
            exception == &expected && exception < &cert.threshold,
            || format!("unexpected exception {exception}"),
        )?;
        let image = iterate_checking_parity(exception, &bits)?;
        ensure(&image >= exception, || {
            format!("listed exception {exception} actually descends")
        })?;
        expected += &modulus;
    }
    Ok(())
}

/// Position of the first coefficient crossing of a parity string: the least
/// `j >= 1` with `2^j > 3^(r_j)`, where `r_j` counts the odd steps among the
/// first `j`. `None` if the coefficient never drops below 1 on this string.
/// (`2^j = 3^(r_j)` is impossible for `j >= 1`.)
fn first_coefficient_crossing(bits: &[bool]) -> Option<usize> {
    let mut power_of_two = BigUint::one();
    let mut power_of_three = BigUint::one();
    for (i, &odd) in bits.iter().enumerate() {
        power_of_two <<= 1usize;
        if odd {
            power_of_three *= 3u32;
        }
        if power_of_two > power_of_three {
            return Some(i + 1);
        }
    }
    None
}

/// Re-checks a recorded counterexample by direct iteration, including the
/// full premise of the statement it is supposed to refute.
pub fn verify_failure_case(case: &FailureCase) -> Result<(), String> {
    match case {
        FailureCase::NoDescentWithinWindow { n, window } => {
            ensure(n > &BigUint::one(), || "n must be at least 2".into())?;
            let mut x = n.clone();
            for j in 1..=*window {
                x = t_step(&x);
                ensure(&x >= n, || format!("n = {n} descends at step {j}"))?;
            }
            Ok(())
        }
        FailureCase::OddMajorityDescent { parity, witness } => {
            let bits = parse_parity(parity)?;
            let k = bits.len();
            let r = bits.iter().filter(|&&odd| odd).count();
            ensure(2 * r > k, || "odd steps are not a majority".into())?;
            ensure((BigUint::one() << k) > pow3(r), || "2^k <= 3^r".into())?;
            let image = iterate_checking_parity(witness, &bits)?;
            ensure(&image < witness, || "witness does not descend".into())
        }
        FailureCase::ThresholdException { parity, n } => {
            let bits = parse_parity(parity)?;
            let k = bits.len();
            let r = bits.iter().filter(|&&odd| odd).count();
            ensure(n > &BigUint::one(), || "n must be at least 2".into())?;
            ensure(k >= 1, || "empty parity prefix".into())?;
            // Premise: the prefix is a first coefficient crossing, i.e.
            // 2^j < 3^(r_j) for all 1 <= j < k and 2^k > 3^r. Anything else
            // is at most a paradoxical segment after an earlier crossing.
            match first_coefficient_crossing(&bits) {
                Some(j) if j == k => {}
                Some(j) => {
                    return Err(format!(
                        "prefix {parity} is not a first coefficient crossing: the coefficient \
                         already drops below 1 at step {j} < {k}, so this is at most a \
                         paradoxical segment, not a first-crossing exception"
                    ))
                }
                None => return Err(format!("2^k <= 3^r for prefix {parity} (k = {k}, r = {r})")),
            }
            let image = iterate_checking_parity(n, &bits)?;
            ensure(&image >= n, || "n descends after all".into())
        }
    }
}

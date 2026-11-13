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
//!   exceptions really do not (direct iteration).

use num_bigint::BigUint;
use num_traits::{One, Pow, Zero};

use crate::certificate::DescentCertificate;
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

/// Re-checks a recorded counterexample by direct iteration.
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
            ensure((BigUint::one() << k) > pow3(r), || "2^k <= 3^r".into())?;
            let image = iterate_checking_parity(n, &bits)?;
            ensure(&image >= n, || "n descends after all".into())
        }
    }
}

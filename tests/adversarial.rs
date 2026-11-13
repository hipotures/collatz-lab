//! Adversarial evidence must not pass the independent verifier.
//!
//! Two families are covered:
//!
//! * tampered exception lists of descent certificates (omissions, duplicates,
//!   extra entries, wrong counts);
//! * *paradoxical* prefixes (`2^k > 3^r` but `T^k(n) >= n`) presented as
//!   first coefficient-crossing exceptions. The classical example is `n = 7`
//!   with prefix `11101001`; it is not a counterexample to the first-descent
//!   threshold statement because the coefficient first crosses at step 7.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use collatz_lab::certificate::{certify, DescentCertificate, MAX_LISTED_EXCEPTIONS};
use collatz_lab::collatz::{orbit, t_iter};
use collatz_lab::hypothesis::{run_experiment, ExperimentParams, FailureCase};
use collatz_lab::prefix::{Cylinder, ParityPrefix};
use collatz_lab::verifier::{verify_certificate, verify_failure_case};
use num_bigint::BigUint;
use num_traits::{One, Pow, Zero};
use proptest::prelude::*;

type Mutation = Box<dyn Fn(&mut DescentCertificate)>;

fn big(n: u64) -> BigUint {
    BigUint::from(n)
}

fn certificate_for(parity: &str) -> DescentCertificate {
    certify(&Cylinder::from_prefix(&parity.parse().unwrap())).expect("prefix has 2^k > 3^r")
}

/// Certificate of the length-`len` cylinder containing `n`, if `2^k > 3^r`.
fn certificate_of(n: u64, len: usize) -> Option<DescentCertificate> {
    certify(&Cylinder::containing(&big(n), len))
}

/// `true` iff `2^j < 3^(r_j)` for all `1 <= j < k` and `2^k > 3^r`.
fn is_first_crossing(prefix: &ParityPrefix) -> bool {
    let k = prefix.len();
    let below = |j: usize| {
        let odd = prefix.bits()[..j].iter().filter(|&&b| b).count();
        (BigUint::one() << j) > Pow::pow(&BigUint::from(3u32), odd)
    };
    k >= 1 && below(k) && (1..k).all(|j| !below(j))
}

// ---------------------------------------------------------------- defect A

#[test]
fn regression_cleared_exception_list_is_rejected() {
    let valid = certificate_for("10");
    assert_eq!(valid.exception_count, BigUint::one());
    assert_eq!(valid.exceptions, vec![BigUint::one()]);
    assert_eq!(verify_certificate(&valid, 3), Ok(()));

    let mut tampered = valid.clone();
    tampered.exceptions.clear();
    assert_eq!(tampered.exception_count, BigUint::one());
    let error = verify_certificate(&tampered, 3).unwrap_err();
    assert!(error.contains("exception list"), "{error}");
}

#[test]
fn exception_list_must_match_exactly() {
    // 11101001 is the class of 7 modulo 2^8; its only exception is n = 7.
    let valid = certificate_for("11101001");
    assert_eq!(valid.exceptions, vec![big(7)]);
    assert_eq!(verify_certificate(&valid, 3), Ok(()));

    let mutations: Vec<(&str, Mutation)> = vec![
        ("omitted", Box::new(|c| c.exceptions.clear())),
        ("duplicated", Box::new(|c| c.exceptions.push(big(7)))),
        ("extra member", Box::new(|c| c.exceptions.push(big(263)))),
        ("extra non-member", Box::new(|c| c.exceptions.push(big(8)))),
        ("replaced", Box::new(|c| c.exceptions = vec![big(263)])),
        (
            "count zeroed",
            Box::new(|c| c.exception_count = BigUint::zero()),
        ),
        ("count inflated", Box::new(|c| c.exception_count = big(2))),
        (
            "count and list dropped together",
            Box::new(|c| {
                c.exception_count = BigUint::zero();
                c.exceptions.clear();
            }),
        ),
        (
            "huge count",
            Box::new(|c| c.exception_count = BigUint::one() << 300usize),
        ),
    ];
    for (name, mutate) in &mutations {
        let mut tampered = valid.clone();
        mutate(&mut tampered);
        assert!(verify_certificate(&tampered, 3).is_err(), "{name}");
    }

    // A certificate without exceptions must not acquire any.
    let clean = certificate_for("0");
    assert!(clean.exceptions.is_empty());
    let mut tampered = clean.clone();
    tampered.exceptions.push(big(2));
    assert!(verify_certificate(&tampered, 3).is_err());
}

#[test]
fn exception_lists_of_small_cylinders_survive_no_tampering() {
    // Every certificate with a non-empty exception list among the cylinders
    // of 1 <= n < 300 up to length 40, attacked in each standard way.
    let mut attacked = 0usize;
    for n in 1u64..300 {
        for len in 1..=40usize {
            let Some(valid) = certificate_of(n, len) else {
                continue;
            };
            assert_eq!(verify_certificate(&valid, 1), Ok(()));
            assert!(valid.exceptions.len() <= MAX_LISTED_EXCEPTIONS);
            assert!(valid.exceptions_complete());
            if valid.exceptions.is_empty() {
                continue;
            }
            attacked += 1;
            let mut dropped = valid.clone();
            dropped.exceptions.pop();
            assert!(verify_certificate(&dropped, 1).is_err());
            let mut doubled = valid.clone();
            doubled.exceptions.push(valid.exceptions[0].clone());
            assert!(verify_certificate(&doubled, 1).is_err());
            let mut reversed = valid.clone();
            reversed
                .exceptions
                .insert(0, &valid.exceptions[0] + &valid.modulus);
            assert!(verify_certificate(&reversed, 1).is_err());
        }
    }
    assert!(attacked > 50, "only {attacked} certificates had exceptions");
}

// ---------------------------------------------------------------- defect B

#[test]
fn regression_paradoxical_seven_is_not_a_first_crossing_exception() {
    let seven = big(7);
    let values: Vec<u64> = orbit(&seven, 8)
        .iter()
        .map(|x| u64::try_from(x).unwrap())
        .collect();
    assert_eq!(values, vec![7, 11, 17, 26, 13, 20, 10, 5, 8]);

    let prefix = ParityPrefix::of(&seven, 8);
    assert_eq!(prefix.to_string(), "11101001");
    assert_eq!(prefix.odd_count(), 5);
    // Paradoxical: 3^5 = 243 < 256 = 2^8, yet T^8(7) = 8 >= 7.
    assert!(t_iter(&seven, 8) >= seven);
    // ... but the first crossing (and the first descent) is at step 7.
    assert!(!is_first_crossing(&prefix));
    assert!(is_first_crossing(&ParityPrefix::of(&seven, 7)));
    assert_eq!(t_iter(&seven, 7), big(5));

    let fake = FailureCase::ThresholdException {
        parity: "11101001".into(),
        n: seven.clone(),
    };
    let error = verify_failure_case(&fake).unwrap_err();
    assert!(
        error.contains("not a first coefficient crossing"),
        "{error}"
    );
    assert!(error.contains("step 7"), "{error}");

    // The genuine first-crossing prefix of 7 is no exception either: 7 descends.
    let honest = FailureCase::ThresholdException {
        parity: "1110100".into(),
        n: seven,
    };
    assert!(verify_failure_case(&honest).is_err());
}

#[test]
fn threshold_exception_premise_is_checked_in_full() {
    let reject = |parity: &str, n: u64| {
        let case = FailureCase::ThresholdException {
            parity: parity.into(),
            n: big(n),
        };
        verify_failure_case(&case).unwrap_err()
    };
    // n = 1 is excluded even though prefix 10 is a first crossing with T^2(1) = 1.
    assert!(reject("10", 1).contains("at least 2"));
    // Coefficient never crosses.
    assert!(reject("11", 3).contains("2^k <= 3^r"));
    // Empty prefix.
    assert!(reject("", 5).contains("empty"));
    // First crossing, right class, but the member descends.
    assert!(reject("10", 5).contains("descends"));
    // First crossing, wrong class.
    assert!(reject("10", 7).contains("wrong parity"));
    // Crossing happens earlier (step 1), later steps irrelevant.
    assert!(reject("011", 2).contains("step 1"));
}

#[test]
fn no_paradoxical_prefix_of_a_small_seed_passes_as_first_crossing_exception() {
    // Finite-domain check: for every 2 <= n < 3000 and every length up to
    // 120, the true parity prefix of n is never accepted. Paradoxical
    // prefixes do occur in this range and must be rejected for the right
    // reason. (Acceptance of any case here would be a counterexample to the
    // coefficient stopping time conjecture, far below the verified range.)
    let mut paradoxical = 0usize;
    for n in 2u64..3000 {
        let n_big = big(n);
        let full = ParityPrefix::of(&n_big, 120);
        for len in 1..=120usize {
            let prefix = ParityPrefix::from_bits(full.bits()[..len].to_vec());
            let case = FailureCase::ThresholdException {
                parity: prefix.to_string(),
                n: n_big.clone(),
            };
            let result = verify_failure_case(&case);
            assert!(result.is_err(), "n = {n}, prefix {prefix}");
            let crossed =
                (BigUint::one() << len) > Pow::pow(&BigUint::from(3u32), prefix.odd_count());
            if crossed && t_iter(&n_big, len) >= n_big {
                paradoxical += 1;
                assert!(!is_first_crossing(&prefix));
                assert!(result
                    .unwrap_err()
                    .contains("not a first coefficient crossing"));
            }
        }
    }
    assert!(
        paradoxical > 100,
        "only {paradoxical} paradoxical prefixes seen"
    );
}

// ------------------------------------------------------------ ledger gates

fn cli(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_collatz-lab"))
        .args(args)
        .output()
        .expect("failed to run the collatz-lab binary")
}

#[test]
fn verify_ledger_rejects_the_fake_refutation_and_keeps_genuine_cases() {
    let params = ExperimentParams {
        depth: 9,
        limit: 1_500,
        samples: 5,
        ..ExperimentParams::default()
    };
    let entries = run_experiment(&params, |_| Ok(()), |_| {}).unwrap().entries;
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("adversarial-ledger");
    fs::create_dir_all(&dir).unwrap();
    let write = |name: &str, entries: &[collatz_lab::hypothesis::LedgerEntry]| {
        let path = dir.join(name);
        let lines: Vec<String> = entries
            .iter()
            .map(|entry| serde_json::to_string(entry).unwrap())
            .collect();
        fs::write(&path, lines.join("\n") + "\n").unwrap();
        path
    };

    let genuine = write("genuine.jsonl", &entries);
    let output = cli(&["verify", "--ledger", genuine.to_str().unwrap()]);
    assert!(output.status.success(), "{output:?}");

    let mut forged = entries.clone();
    let target = forged
        .iter_mut()
        .find(|entry| entry.hypothesis_id == "threshold-exceptions-trivial")
        .unwrap();
    target.failure_cases.push(FailureCase::ThresholdException {
        parity: "11101001".into(),
        n: big(7),
    });
    let forged = write("forged.jsonl", &forged);
    let output = cli(&["verify", "--ledger", forged.to_str().unwrap()]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("not a first coefficient crossing"),
        "{stderr}"
    );
}

// ---------------------------------------------------------- property tests

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn tampered_exception_lists_are_rejected(
        n in 1u64..5_000,
        len in 1usize..60,
        attack in 0u8..6,
        extra in 1u64..1_000_000,
    ) {
        let Some(valid) = certificate_of(n, len) else {
            return Ok(());
        };
        prop_assert_eq!(verify_certificate(&valid, 1), Ok(()));
        let mut tampered = valid.clone();
        match attack {
            0 => {
                if tampered.exceptions.pop().is_none() {
                    return Ok(());
                }
            }
            1 => {
                let Some(first) = valid.exceptions.first() else {
                    return Ok(());
                };
                tampered.exceptions.push(first.clone());
            }
            2 => tampered.exceptions.push(big(extra)),
            3 => tampered.exceptions.insert(0, big(extra)),
            4 => tampered.exception_count += extra,
            _ => {
                // Claim one more exception: the next class member up.
                let next = valid.exceptions.last().map_or_else(
                    || if valid.residue.is_zero() { valid.modulus.clone() } else { valid.residue.clone() },
                    |last| last + &valid.modulus,
                );
                tampered.exceptions.push(next);
                tampered.exception_count += 1u32;
            }
        }
        prop_assert!(verify_certificate(&tampered, 1).is_err());
    }

    #[test]
    fn bogus_threshold_exceptions_are_rejected(
        n in 2u64..2_000_000,
        len in 1usize..100,
        flip in proptest::option::of(0usize..100),
    ) {
        // The true prefix of n, optionally with one parity flipped, is never
        // accepted as a first-crossing exception on this finite domain.
        let mut bits = ParityPrefix::of(&big(n), len).bits().to_vec();
        if let Some(index) = flip {
            let index = index % len;
            bits[index] = !bits[index];
        }
        let prefix = ParityPrefix::from_bits(bits);
        let case = FailureCase::ThresholdException { parity: prefix.to_string(), n: big(n) };
        let result = verify_failure_case(&case);
        prop_assert!(result.is_err());
        if !is_first_crossing(&prefix) && flip.is_none() {
            let message = result.unwrap_err();
            prop_assert!(
                message.contains("not a first coefficient crossing") || message.contains("2^k <= 3^r"),
                "{}", message
            );
        }
    }
}

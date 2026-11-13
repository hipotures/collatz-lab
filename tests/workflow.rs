//! End-to-end tests of the hypothesis workflow, the ledger and the CLI.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use collatz_lab::hypothesis::{run_experiment, ExperimentParams, FailureCase, LedgerEntry, Status};
use collatz_lab::verifier::verify_failure_case;
use num_bigint::BigUint;

fn small_params() -> ExperimentParams {
    ExperimentParams {
        seed: 42,
        depth: 10,
        limit: 2_000,
        window: 8,
        bits_factor: 2,
        sample_bits: 150,
        samples: 20,
        max_steps: 50_000,
    }
}

fn run(params: &ExperimentParams) -> Vec<LedgerEntry> {
    run_experiment(params, |_| Ok(()), |_| {}).unwrap().entries
}

fn status_of(entries: &[LedgerEntry], id: &str) -> Status {
    entries
        .iter()
        .find(|entry| entry.hypothesis_id == id)
        .unwrap_or_else(|| panic!("missing entry {id}"))
        .status
}

#[test]
fn experiment_assigns_the_expected_statuses() {
    let entries = run(&small_params());
    assert_eq!(status_of(&entries, "universal-window"), Status::Refuted);
    assert_eq!(status_of(&entries, "bounded-window"), Status::Refuted);
    assert_eq!(status_of(&entries, "bit-length-bound"), Status::Refuted);
    assert_eq!(
        status_of(&entries, "prefix-residue-bijection"),
        Status::ProvenByAlgebra
    );
    assert_eq!(
        status_of(&entries, "descent-needs-even-majority"),
        Status::Refuted
    );
    assert_eq!(
        status_of(&entries, "threshold-exceptions-trivial"),
        Status::VerifiedForFiniteDomain
    );
    assert_eq!(
        status_of(&entries, "threshold-exceptions-trivial-all-depths"),
        Status::Conjectured
    );
    assert_eq!(
        status_of(&entries, "sampled-stopping-times"),
        Status::ExperimentallyObserved
    );
}

#[test]
fn counterexamples_are_minimal_and_reverifiable() {
    let entries = run(&small_params());
    for entry in &entries {
        for case in &entry.failure_cases {
            verify_failure_case(case).unwrap();
        }
        // A refutation always comes with a concrete counterexample, and an
        // open statement always names what is missing.
        if entry.status == Status::Refuted {
            assert!(!entry.failure_cases.is_empty(), "{}", entry.hypothesis_id);
        }
        if entry.status == Status::Conjectured {
            assert!(!entry.proof_obligations.is_empty());
        }
    }
    let least = |id: &str| {
        let entry = entries.iter().find(|e| e.hypothesis_id == id).unwrap();
        entry.failure_cases[0].clone()
    };
    // 27 is the least n >= 2 with no descent within 8 accelerated steps.
    assert_eq!(
        least("bounded-window"),
        FailureCase::NoDescentWithinWindow {
            n: BigUint::from(27u32),
            window: 8
        }
    );
    // 7 has stopping time 7 > 2 * 3 bits.
    assert_eq!(
        least("bit-length-bound"),
        FailureCase::NoDescentWithinWindow {
            n: BigUint::from(7u32),
            window: 6
        }
    );
    assert_eq!(
        least("descent-needs-even-majority"),
        FailureCase::OddMajorityDescent {
            parity: "11010".into(),
            witness: BigUint::from(11u32)
        }
    );
}

#[test]
fn bounded_statements_are_not_promoted_when_the_domain_is_too_small() {
    // With limit 26 the window-8 statement has no counterexample in range
    // (the least is 27). It must be reported as a finite-domain result only,
    // while the unbounded form stays refuted.
    let params = ExperimentParams {
        limit: 26,
        ..small_params()
    };
    let entries = run(&params);
    assert_eq!(
        status_of(&entries, "bounded-window"),
        Status::VerifiedForFiniteDomain
    );
    assert_eq!(status_of(&entries, "universal-window"), Status::Refuted);
}

#[test]
fn verifier_rejects_false_failure_cases() {
    let bogus = [
        FailureCase::NoDescentWithinWindow {
            n: BigUint::from(27u32),
            window: 59,
        },
        FailureCase::NoDescentWithinWindow {
            n: BigUint::from(1u32),
            window: 5,
        },
        FailureCase::OddMajorityDescent {
            parity: "11010".into(),
            witness: BigUint::from(12u32),
        },
        FailureCase::OddMajorityDescent {
            parity: "1100".into(),
            witness: BigUint::from(3u32),
        },
        FailureCase::ThresholdException {
            parity: "10".into(),
            n: BigUint::from(5u32),
        },
        FailureCase::ThresholdException {
            parity: "1x".into(),
            n: BigUint::from(5u32),
        },
    ];
    for case in &bogus {
        assert!(verify_failure_case(case).is_err(), "{case:?}");
    }
    assert!(verify_failure_case(&FailureCase::NoDescentWithinWindow {
        n: BigUint::from(27u32),
        window: 58,
    })
    .is_ok());
}

#[test]
fn ledger_entries_round_trip_through_json() {
    for entry in run(&small_params()) {
        let line = serde_json::to_string(&entry).unwrap();
        assert!(!line.contains('\n'));
        let value: serde_json::Value = serde_json::from_str(&line).unwrap();
        for key in [
            "seed",
            "parameters",
            "hypothesis",
            "status",
            "evidence",
            "failure_cases",
        ] {
            assert!(value.get(key).is_some(), "missing {key}");
        }
        assert_eq!(serde_json::from_str::<LedgerEntry>(&line).unwrap(), entry);
    }
}

fn cli(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_collatz-lab"))
        .args(args)
        .output()
        .expect("failed to run the collatz-lab binary")
}

#[test]
fn cli_experiment_is_reproducible_and_its_ledger_verifies() {
    let base = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    let mut outputs = Vec::new();
    for name in ["cli-run-a", "cli-run-b"] {
        let dir = base.join(name);
        let _ = fs::remove_dir_all(&dir);
        let output = cli(&[
            "experiment",
            "--seed",
            "5",
            "--depth",
            "9",
            "--limit",
            "1500",
            "--samples",
            "10",
            "--out-dir",
            dir.to_str().unwrap(),
        ]);
        assert!(output.status.success(), "{output:?}");
        let ledger = fs::read_to_string(dir.join("ledger.jsonl")).unwrap();
        let summary = fs::read_to_string(dir.join("summary.md")).unwrap();
        let verified = cli(&[
            "verify",
            "--ledger",
            dir.join("ledger.jsonl").to_str().unwrap(),
        ]);
        assert!(verified.status.success(), "{verified:?}");
        // Compare the parts that do not mention the output directory.
        let summary = summary.replace(dir.to_str().unwrap(), "<out>");
        outputs.push((ledger, summary));
    }
    assert_eq!(outputs[0], outputs[1]);
    assert_eq!(outputs[0].0.lines().count(), 8);
    assert!(outputs[0].1.contains("uncovered classes modulo 2^9"));
}

#[test]
fn cli_refuses_large_bounds_without_opt_in() {
    let output = cli(&["certificates", "--depth", "40"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("--allow-large"));
    let output = cli(&["prefixes", "--length", "30"]);
    assert!(!output.status.success());
}

#[test]
fn cli_small_commands_succeed() {
    let output = cli(&[
        "verify",
        "--limit",
        "2000",
        "--depth",
        "8",
        "--mersenne-max",
        "40",
    ]);
    assert!(output.status.success(), "{output:?}");
    let output = cli(&["prefixes", "--parity", "11010"]);
    let text = String::from_utf8_lossy(&output.stdout).to_string();
    assert!(text.contains("n = 11 (mod 2^5)"), "{text}");
    assert!(text.contains("(3^3 n + 23) / 2^5"), "{text}");
    let output = cli(&[
        "prefixes",
        "--n",
        "340282366920938463463374607431768211457",
        "--length",
        "6",
    ]);
    assert!(output.status.success(), "{output:?}");
    let output = cli(&["certificates", "--parity", "11"]);
    assert!(String::from_utf8_lossy(&output.stdout).contains("no certificate"));
}

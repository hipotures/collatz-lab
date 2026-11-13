//! Human-readable summary of one bounded experiment.
//!
//! The output is a pure function of the experiment outcome (no timestamps or
//! host details), so a rerun with the same parameters reproduces it exactly.

use std::fmt::Write as _;

use crate::hypothesis::{ExperimentOutcome, FailureCase, Status};

fn describe_case(case: &FailureCase) -> String {
    match case {
        FailureCase::NoDescentWithinWindow { n, window } => {
            format!("n = {n}: T^j(n) >= n for all 1 <= j <= {window}")
        }
        FailureCase::OddMajorityDescent { parity, witness } => {
            format!(
                "prefix {parity} descends although odd steps are a majority; witness n = {witness}"
            )
        }
        FailureCase::ThresholdException { parity, n } => {
            format!("prefix {parity}: member n = {n} does not descend")
        }
    }
}

/// Renders the Markdown summary.
pub fn render_summary(outcome: &ExperimentOutcome, command: &str) -> String {
    let p = &outcome.params;
    let c = &outcome.cover;
    let mut out = String::new();
    // Writing to a String cannot fail.
    let _ = write!(
        out,
        "# Bounded experiment summary\n\n\
         This file is generated. It reports a **bounded** experiment on the accelerated \
         Collatz map `T`. Nothing below is a proof, a novelty claim, a completeness claim \
         or a counterexample to the Collatz conjecture.\n\n\
         Reproduce with:\n\n```text\n{command}\n```\n\n\
         ## Parameters\n\n\
         | parameter | value |\n|---|---|\n\
         | seed | {} |\n| cover depth | {} |\n| exhaustive limit | {} |\n\
         | candidate window | {} |\n| bit-length factor | {} |\n\
         | sample size | {} integers of {} bits |\n| sample step budget | {} |\n\
         | tool version | {} |\n\n",
        p.seed,
        p.depth,
        p.limit,
        p.window,
        p.bits_factor,
        p.samples,
        p.sample_bits,
        p.max_steps,
        env!("CARGO_PKG_VERSION"),
    );

    out.push_str(
        "## Status legend\n\n\
         - `proven-by-algebra`: follows from an explicit algebraic argument; finite checks are only a cross-check.\n\
         - `verified-for-finite-domain`: exhaustively checked on the stated finite domain and nowhere else.\n\
         - `experimentally-observed`: seen on a sample; not exhaustive.\n\
         - `conjectured`: open; recorded as a proof obligation, with no claim of truth.\n\
         - `refuted`: false as stated; counterexamples were re-checked by the independent verifier.\n\n\
         ## Hypotheses\n\n| id | status | domain | failure cases |\n|---|---|---|---|\n",
    );
    for entry in &outcome.entries {
        let _ = writeln!(
            out,
            "| `{}` | {} | {} | {} |",
            entry.hypothesis_id,
            entry.status.label(),
            entry.domain,
            entry.failure_cases.len()
        );
    }

    for entry in &outcome.entries {
        let _ = write!(
            out,
            "\n### `{}` ({})\n\n**Statement.** {}\n\n**Domain.** {}\n",
            entry.hypothesis_id,
            entry.status.label(),
            entry.hypothesis,
            entry.domain
        );
        if !entry.evidence.is_empty() {
            out.push_str("\n**Evidence.**\n\n");
            for line in &entry.evidence {
                let _ = writeln!(out, "- {line}");
            }
        }
        if !entry.failure_cases.is_empty() {
            let heading = if entry.status == Status::Refuted {
                "Counterexamples (verified by direct iteration)"
            } else {
                "Failure cases of the bounded statement"
            };
            let _ = write!(out, "\n**{heading}.**\n\n");
            for case in &entry.failure_cases {
                let _ = writeln!(out, "- {}", describe_case(case));
            }
        }
        if !entry.proof_obligations.is_empty() {
            out.push_str("\n**Open proof obligations.**\n\n");
            for line in &entry.proof_obligations {
                let _ = writeln!(out, "- {line}");
            }
        }
    }

    let _ = write!(
        out,
        "\n## First-descent cover to depth {depth}\n\n\
         - certified first-descent prefixes: {} (longest has length {})\n\
         - residue classes modulo 2^{depth} covered: {} of {}\n\
         - **uncovered classes modulo 2^{depth}: {}** (each has `2^j < 3^(r_j)` for every `1 <= j <= {depth}`)\n",
        c.certificates,
        c.max_certificate_steps,
        c.covered_classes,
        c.total_classes,
        c.uncovered,
        depth = c.depth,
    );
    if c.certificates_with_exceptions.is_empty() {
        out.push_str("- certificates with positive members below threshold: none\n");
    } else {
        out.push_str("- certificates with positive members below threshold:\n");
        for line in &c.certificates_with_exceptions {
            let _ = writeln!(out, "  - {line}");
        }
    }
    out.push_str(
        "\nEvery certificate was re-derived by the independent verifier (integer arithmetic \
         and direct iteration only). Each certificate is conditional: it asserts one descent \
         step count for one residue class above an explicit threshold.\n\n\
         ## What this does not show\n\n\
         - The uncovered set is non-empty at every depth: the class `-1 (mod 2^depth)` is \
         never certified (proven by algebra, see `universal-window`). A covered fraction \
         close to 1 is therefore not progress toward a proof by itself.\n\
         - A descent certificate gives `T^k(n) < n` once; turning a full family of such \
         statements into convergence needs every class covered and every exception handled, \
         which no finite depth provides.\n\
         - Finite searches and samples cover only their stated domains.\n",
    );
    out
}

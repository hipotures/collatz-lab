//! Human-readable summary of one bounded experiment.
//!
//! The output is a pure function of the experiment outcome (no timestamps or
//! host details), so a rerun with the same parameters reproduces it exactly.

use std::fmt::Write as _;

use crate::envelope::{EnvelopeExperiment, Witness};
use crate::hypothesis::{ExperimentOutcome, FailureCase, Status};

/// Deterministic Phase 2 report. The reproduction command always names the
/// canonical artifact directory, even if the CLI writes a scratch copy.
pub fn render_envelope(outcome: &EnvelopeExperiment) -> String {
    let mut out = String::from(
        "# Phase 2: tightness of Terras's mini-max envelope\n\n\
         Generated finite engineering/mathematical comparison for the accelerated map \
         `T(n)=n/2` (even), `(3n+1)/2` (odd). No originality claim, no all-`r` theorem, \
         and no proof of CST or Collatz is asserted. P1a is **refuted**; P1b remains open.\n\n\
         Reproduce this table and `evidence.json` from the repository root with:\n\n\
         ```text\ncargo run --locked --release -- envelope --out-dir research/envelope\n```\n\n\
         ## Definitions and scope\n\n\
         Exactly `1 <= r <= 12`, with `k = bit_length(3^r) <= 20`. Each family contains \
         every parity word whose first coefficient crossing is at length `k` and has \
         `r` odd steps. Write `T^k(n)=(3^r*n+c)/2^k`, `d=2^k-3^r`, and let `m` be \
         the least class member **at least 2**. The word `10` has residue 1 but `m=5`.\n\n\
         `C_r=max c`, `m_r=min m`, `R_r=max c/(d*m)`, `U_r=C_r/(d*m_r)`, and \
         `E_r=U_r/R_r`. If `R_r=0`, `E_r` and its comparison with 2 are **N/A** \
         (JSON `null`); no value is imputed. All fractions are reduced using gcd; \
         all rankings and comparisons use BigUint cross products.\n\n\
         ## Exhaustive results\n\n\
         Each extremum cell lists **all** tied words as `word (m, c)` in lexicographic \
         order, followed by the number of ties. A single listed word means a unique \
         extremizer. Counts, margins, normalized residues and the independent Terras \
         offsets are also recorded in `evidence.json`; arbitrary-size integers are \
         decimal strings.\n\n\
         | r | k | count | C_r words (m, c); ties | m_r words (m, c); ties | R_r words (m, c); ties | R_r | U_r | E_r | E_r <= 2 |\n\
         |---|---|---|---|---|---|---|---|---|---|\n",
    );
    let witnesses = |values: &[Witness]| {
        let words: Vec<_> = values
            .iter()
            .map(|w| format!("`{}` ({}, {})", w.parity, w.m, w.c))
            .collect();
        format!("{}; {} tie(s)", words.join("<br>"), values.len())
    };
    for row in &outcome.rows {
        let e = row
            .e_ratio
            .as_ref()
            .map_or_else(|| "N/A".into(), ToString::to_string);
        let comparison = match row.e_le_two {
            Some(true) => "yes",
            Some(false) => "no",
            None => "N/A",
        };
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            row.r,
            row.k,
            row.family_count,
            witnesses(&row.max_c_witnesses),
            witnesses(&row.min_m_witnesses),
            witnesses(&row.max_ratio_witnesses),
            row.r_ratio,
            row.u_ratio,
            e,
            comparison,
        );
    }
    out.push_str("\n## Finite prediction E_r <= 2\n\n");
    if let Some(r) = outcome.first_counterexample_r {
        let row = outcome
            .rows
            .iter()
            .find(|row| row.r == r)
            .expect("counterexample row");
        let e = row.e_ratio.as_ref().expect("counterexample ratio");
        let _ = writeln!(
            out,
            "**refuted on the tested domain**: the first counterexample is `r={r}`, \
             `k={}`, with `E_r={e} > 2`. This refutes only the finite prediction. \
             All twelve families were still evaluated.",
            row.k
        );
    } else {
        out.push_str(
            "**verified-for-finite-domain**: `E_r <= 2` for every tested `r` where \
             `R_r > 0`. This is only a bounded observation on `1 <= r <= 12`, \
             with no extrapolation to larger `r`.\n",
        );
    }
    out.push_str(
        "\nNeither outcome proves P1b or any infinite-family statement.\n\n\
         ## Checks and stopping behavior\n\n\
         Each family count agrees with both independent recurrences in \
         `src/counting.rs`. The enumerated maximum offset agrees with Terras's \
         independent extremal-word recurrence: start with power 1 and offset 0; \
         at positions `i=0..k-2` choose odd iff `3^(odd count so far) < 2^(i+1)`, \
         update `c <- 3*c+2^i` on odd steps, and append a final zero. This is the \
         construction of Theorems 2.4 and 2.6 described in \
         [the primary-source audit](../literature-cst.md).\n\n\
         Every enumerated word, including every reported extremizer, has its \
         modular-inverse residue checked against the independent lifting construction. \
         The independent certificate verifier rederives its closed-form affine offset \
         and checks two members by direct iteration. Its least member `m >= 2` is \
         additionally checked by direct iteration for its parities and affine identity. \
         The independent test in `tests/envelope.rs` scans a full residue period by \
         direct iteration and rechecks all extrema, ties and exact fractions.\n\n\
         P1a is never used to rank classes. At `r=6`, `1111101000` has \
         `(m,c)=(287,697)`, while `1101110100` has `(347,989)` and \
         `989/(295*347) > 697/(295*287)` (cross-product difference 12385280).\n\n\
         The command has fixed bounds and terminates at `r=12`, or immediately on \
         the first invariant failure. An `E_r>2` is a result, not an invariant failure. \
         No artifact is replaced until all mathematical checks pass. It retains one \
         family at a time (at most 2652 classes); the full run checks 4403 classes. \
         Runtime in milliseconds is printed to stderr and omitted from these \
         deterministic artifacts. See the repository README for measured performance.\n",
    );
    out
}

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

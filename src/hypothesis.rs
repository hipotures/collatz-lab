//! Bounded hypothesis workflow and the machine-readable research ledger.
//!
//! A fixed, small set of candidate statements about parity prefixes and
//! descent is generated from the experiment parameters; each is attacked with
//! exact arithmetic, and every recorded counterexample is re-checked by the
//! independent [`crate::verifier`] before it is written to the ledger.
//!
//! Each ledger entry carries exactly one [`Status`]. The statuses are never
//! promoted: a statement checked on a finite domain stays
//! `verified-for-finite-domain`, and its unbounded generalisation, if recorded
//! at all, is a separate `conjectured` entry.
//!
//! This module is the intended extension point for a future hypothesis
//! proposer: add a function returning [`LedgerEntry`] values and register it
//! in [`run_experiment`]. No autonomous loop is implemented here.

use std::collections::BTreeSet;
use std::error::Error;

use num_bigint::BigUint;
use num_traits::One;
use serde::{Deserialize, Serialize};

use crate::certificate::{certify, DescentCover};
use crate::collatz;
use crate::nogo;
use crate::prefix::{closed_form_offset, residue_by_inverse, Cylinder, ParityPrefix};
use crate::rng::SplitMix64;
use crate::serde_dec;
use crate::verifier;

pub const LEDGER_SCHEMA_VERSION: u32 = 1;

/// Largest prefix length for which the exhaustive prefix/residue check runs.
pub const MAX_EXHAUSTIVE_PREFIX_LEN: usize = 12;

/// Epistemic status of one ledger entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Status {
    /// Follows from an explicit algebraic argument stated in the entry or the
    /// module documentation; finite checks are only a cross-check.
    ProvenByAlgebra,
    /// Exhaustively checked on the stated finite domain, nothing more.
    VerifiedForFiniteDomain,
    /// Seen on a sample; not exhaustive even on the sampled domain.
    ExperimentallyObserved,
    /// Open statement recorded for future work; no claim of truth.
    Conjectured,
    /// False as stated; the entry lists verified counterexamples.
    Refuted,
}

impl Status {
    pub fn label(self) -> &'static str {
        match self {
            Status::ProvenByAlgebra => "proven-by-algebra",
            Status::VerifiedForFiniteDomain => "verified-for-finite-domain",
            Status::ExperimentallyObserved => "experimentally-observed",
            Status::Conjectured => "conjectured",
            Status::Refuted => "refuted",
        }
    }
}

/// A reproducible counterexample. Every variant can be re-checked from its
/// fields alone with [`verifier::verify_failure_case`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum FailureCase {
    /// `T^j(n) >= n` for every `1 <= j <= window`.
    NoDescentWithinWindow {
        #[serde(with = "serde_dec")]
        n: BigUint,
        window: u64,
    },
    /// A parity prefix with `2^k > 3^r` and `2r > k`, with a member that
    /// really descends after `k` steps.
    OddMajorityDescent {
        parity: String,
        #[serde(with = "serde_dec")]
        witness: BigUint,
    },
    /// A first-crossing exception: `parity` is the parity prefix of `n >= 2`,
    /// it is a *first coefficient crossing* (`2^j < 3^(r_j)` for every
    /// `1 <= j < k`, and `2^k > 3^r`), and yet `T^k(n) >= n`.
    ///
    /// This is strictly narrower than a paradoxical prefix (`2^k > 3^r` with
    /// `T^k(n) >= n` at *some* length): `n = 7` with prefix `11101001` is
    /// paradoxical but is not a `ThresholdException`, because its coefficient
    /// first crosses at step 7, where `T^7(7) = 5 < 7`. The verifier rejects
    /// such cases. No genuine instance of this variant is known.
    ThresholdException {
        parity: String,
        #[serde(with = "serde_dec")]
        n: BigUint,
    },
}

/// Parameters of one bounded experiment. Everything is explicit and finite.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExperimentParams {
    /// Seed of the deterministic sampler.
    pub seed: u64,
    /// Depth of the first-descent cover.
    pub depth: usize,
    /// Exhaustive searches cover `2 <= n <= limit`.
    pub limit: u64,
    /// Candidate universal descent window.
    pub window: usize,
    /// Candidate constant in `stopping time <= bits_factor * bit_length(n)`.
    pub bits_factor: u64,
    /// Bit length of sampled integers.
    pub sample_bits: usize,
    /// Number of sampled integers.
    pub samples: usize,
    /// Step budget for sampled stopping times.
    pub max_steps: u64,
}

impl Default for ExperimentParams {
    fn default() -> Self {
        Self {
            seed: 1,
            depth: 16,
            limit: 100_000,
            window: 16,
            bits_factor: 2,
            sample_bits: 192,
            samples: 200,
            max_steps: 100_000,
        }
    }
}

/// One line of the JSONL research ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LedgerEntry {
    pub schema_version: u32,
    pub tool_version: String,
    pub seed: u64,
    pub parameters: ExperimentParams,
    pub hypothesis_id: String,
    pub hypothesis: String,
    /// The exact domain the status refers to.
    pub domain: String,
    pub status: Status,
    pub evidence: Vec<String>,
    pub failure_cases: Vec<FailureCase>,
    /// What would still have to be proved; never empty for open statements.
    pub proof_obligations: Vec<String>,
}

impl LedgerEntry {
    fn new(params: &ExperimentParams, id: &str, hypothesis: String, domain: String) -> Self {
        Self {
            schema_version: LEDGER_SCHEMA_VERSION,
            tool_version: env!("CARGO_PKG_VERSION").to_string(),
            seed: params.seed,
            parameters: params.clone(),
            hypothesis_id: id.to_string(),
            hypothesis,
            domain,
            status: Status::Conjectured,
            evidence: Vec::new(),
            failure_cases: Vec::new(),
            proof_obligations: Vec::new(),
        }
    }
}

/// Summary of the first-descent cover used by the experiment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverStats {
    pub depth: usize,
    pub certificates: usize,
    pub uncovered: usize,
    #[serde(with = "serde_dec")]
    pub covered_classes: BigUint,
    #[serde(with = "serde_dec")]
    pub total_classes: BigUint,
    /// Longest certified prefix length.
    pub max_certificate_steps: usize,
    /// Certificates that have at least one positive member below threshold,
    /// as `(parity, exceptions)` rendered in text.
    pub certificates_with_exceptions: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct ExperimentOutcome {
    pub params: ExperimentParams,
    pub cover: CoverStats,
    pub entries: Vec<LedgerEntry>,
}

type Checked<T> = Result<T, String>;

/// H1: a universal descent window, unbounded form. Refuted by algebra.
fn universal_window(params: &ExperimentParams) -> Checked<LedgerEntry> {
    let w = params.window;
    let mut entry = LedgerEntry::new(
        params,
        "universal-window",
        format!("Every sufficiently large n satisfies T^j(n) < n for some 1 <= j <= {w}."),
        "all positive integers".into(),
    );
    entry.status = Status::Refuted;
    entry.evidence.push(format!(
        "[proven-by-algebra] every n = -1 (mod 2^{w}) has parity prefix 1^{w}, so \
         T^j(n) = 3^j (n + 1) / 2^j - 1 > n for 1 <= j <= {w}; the class is unbounded"
    ));
    let identity_max = 128usize.max(w);
    for l in 0..=identity_max {
        nogo::check_mersenne_identity(l)
            .map_err(|j| format!("Mersenne identity fails for L = {l} at j = {j}"))?;
    }
    entry.evidence.push(format!(
        "[verified-for-finite-domain] T^j(2^L - 1) = 3^j 2^(L - j) - 1 checked by direct \
         iteration for all 0 <= j <= L <= {identity_max}"
    ));
    let window = u64::try_from(w).map_err(|e| e.to_string())?;
    for bound_bits in [0usize, 64, 130] {
        let bound = BigUint::one() << bound_bits;
        let n = nogo::window_witness(w, &bound);
        entry
            .failure_cases
            .push(FailureCase::NoDescentWithinWindow { n, window });
    }
    entry.evidence.push(
        "[verified-for-finite-domain] the listed witnesses (least members of the class above \
         2^0, 2^64, 2^130) were re-checked by direct iteration"
            .into(),
    );
    Ok(entry)
}

/// H2: the same window on the finite search range.
fn bounded_window(params: &ExperimentParams) -> Checked<LedgerEntry> {
    let w = params.window;
    let window = u64::try_from(w).map_err(|e| e.to_string())?;
    let mut entry = LedgerEntry::new(
        params,
        "bounded-window",
        format!("Every n in the domain satisfies T^j(n) < n for some 1 <= j <= {w}."),
        format!("2 <= n <= {}", params.limit),
    );
    let counterexample =
        (2..=params.limit).find(|&n| collatz::stopping_time_fast(n, window).is_none());
    match counterexample {
        Some(n) => {
            entry.status = Status::Refuted;
            entry.evidence.push(format!(
                "exhaustive search in increasing order; {n} is the least counterexample"
            ));
            entry
                .failure_cases
                .push(FailureCase::NoDescentWithinWindow {
                    n: BigUint::from(n),
                    window,
                });
        }
        None => {
            entry.status = Status::VerifiedForFiniteDomain;
            entry.evidence.push(
                "exhaustive search found no counterexample in the domain; the unbounded \
                 statement is nevertheless false (see universal-window)"
                    .into(),
            );
        }
    }
    Ok(entry)
}

/// H3: stopping time bounded by a constant times the bit length.
fn bit_length_bound(params: &ExperimentParams) -> Checked<LedgerEntry> {
    let factor = params.bits_factor;
    let mut entry = LedgerEntry::new(
        params,
        "bit-length-bound",
        format!("Every n in the domain has stopping time at most {factor} * bit_length(n)."),
        format!("2 <= n <= {}", params.limit),
    );
    let budget = |n: u64| factor.saturating_mul(u64::from(u64::BITS - n.leading_zeros()));
    let counterexample =
        (2..=params.limit).find(|&n| collatz::stopping_time_fast(n, budget(n)).is_none());
    match counterexample {
        Some(n) => {
            entry.status = Status::Refuted;
            entry.evidence.push(format!(
                "exhaustive search in increasing order; {n} is the least counterexample \
                 (no descent within {} steps)",
                budget(n)
            ));
            entry
                .failure_cases
                .push(FailureCase::NoDescentWithinWindow {
                    n: BigUint::from(n),
                    window: budget(n),
                });
        }
        None => {
            entry.status = Status::VerifiedForFiniteDomain;
            entry
                .evidence
                .push("exhaustive search found no counterexample in the domain".into());
            entry.proof_obligations.push(
                "no argument is known for any n outside the domain; the Mersenne family \
                 shows any such bound needs factor > 1"
                    .into(),
            );
        }
    }
    Ok(entry)
}

/// H4: prefix <-> residue correspondence. Proved by algebra, cross-checked.
fn prefix_residue_bijection(params: &ExperimentParams) -> Checked<LedgerEntry> {
    let max_len = params.depth.min(MAX_EXHAUSTIVE_PREFIX_LEN);
    let mut entry = LedgerEntry::new(
        params,
        "prefix-residue-bijection",
        "For every k >= 0, parity prefixes of length k correspond bijectively to residue \
         classes modulo 2^k, and T^k(n) = (3^r n + c) / 2^k on each class."
            .into(),
        "all k >= 0".into(),
    );
    entry.status = Status::ProvenByAlgebra;
    entry.evidence.push(
        "[proven-by-algebra] induction on k: for n = rho + 2^k t in a length-k cylinder, \
         T^k(n) = T^k(rho) + 3^r t, so the next parity splits the class in two"
            .into(),
    );

    let mut level = vec![Cylinder::root()];
    for k in 0..=max_len {
        let mut residues = BTreeSet::new();
        for cylinder in &level {
            let bits = cylinder.prefix().bits();
            if residue_by_inverse(cylinder.affine()) != *cylinder.residue() {
                return Err(format!("residue mismatch for prefix {}", cylinder.prefix()));
            }
            if closed_form_offset(bits) != *cylinder.affine().offset() {
                return Err(format!("offset mismatch for prefix {}", cylinder.prefix()));
            }
            for t in 0u32..2 {
                let n = cylinder.member(&BigUint::from(t));
                if ParityPrefix::of(&n, k) != *cylinder.prefix() {
                    return Err(format!("n = {n} is not in cylinder {}", cylinder.prefix()));
                }
                if cylinder.image(&n) != Some(collatz::t_iter(&n, k)) {
                    return Err(format!("affine form fails for n = {n}"));
                }
            }
            residues.insert(cylinder.residue().clone());
        }
        if residues.len() != level.len() {
            return Err(format!("residues are not distinct at length {k}"));
        }
        if k < max_len {
            level = level
                .iter()
                .flat_map(|c| [c.extend(false), c.extend(true)])
                .collect();
        }
    }
    entry.evidence.push(format!(
        "[verified-for-finite-domain] for every prefix of length k <= {max_len}: residues are \
         pairwise distinct, two independent residue constructions agree, the recursive and \
         closed-form offsets agree, and the affine form matches direct iteration on two members"
    ));
    Ok(entry)
}

/// H5: "a descending prefix never has more odd than even steps". Refuted.
fn even_majority(params: &ExperimentParams, cover: &DescentCover) -> Checked<LedgerEntry> {
    let mut entry = LedgerEntry::new(
        params,
        "descent-needs-even-majority",
        "If a parity prefix of length k with r odd steps satisfies 2^k > 3^r, then 2r <= k.".into(),
        format!(
            "first-descent prefixes of length <= {} (all {} of them)",
            cover.depth,
            cover.certificates.len()
        ),
    );
    let counterexample = cover
        .certificates
        .iter()
        .filter(|cert| 2 * cert.odd_steps > cert.steps)
        .min_by(|a, b| (a.steps, &a.parity).cmp(&(b.steps, &b.parity)));
    match counterexample {
        Some(cert) => {
            let modulus = &cert.modulus;
            let mut witness = cert.residue.clone();
            while witness < cert.threshold {
                witness += modulus;
            }
            entry.status = Status::Refuted;
            entry.evidence.push(format!(
                "shortest counterexample in the cover: k = {}, r = {}, 2^k - 3^r = {}",
                cert.steps, cert.odd_steps, cert.margin
            ));
            entry.failure_cases.push(FailureCase::OddMajorityDescent {
                parity: cert.parity.clone(),
                witness,
            });
        }
        None => {
            entry.status = Status::VerifiedForFiniteDomain;
            entry
                .evidence
                .push("no counterexample among the enumerated prefixes".into());
            entry
                .proof_obligations
                .push("increase the depth; k = 5, r = 3 is a counterexample".into());
        }
    }
    Ok(entry)
}

/// H6 and H7: thresholds of first-descent certificates.
fn threshold_exceptions(
    params: &ExperimentParams,
    cover: &DescentCover,
) -> Checked<Vec<LedgerEntry>> {
    let statement = "For a first-descent prefix (2^k > 3^r, and 2^j < 3^(r_j) for all \
                     1 <= j < k), every class member n >= 2 satisfies T^k(n) < n; that is, \
                     the only positive member below the certificate threshold is n = 1 \
                     (prefix 10).";
    let mut finite = LedgerEntry::new(
        params,
        "threshold-exceptions-trivial",
        statement.into(),
        format!("first-descent prefixes of length k <= {}", cover.depth),
    );
    let one = BigUint::one();
    for cert in &cover.certificates {
        if !cert.exceptions_complete() {
            return Err(format!("exception list truncated for {}", cert.parity));
        }
        for n in cert.exceptions.iter().filter(|n| **n > one) {
            finite.failure_cases.push(FailureCase::ThresholdException {
                parity: cert.parity.clone(),
                n: n.clone(),
            });
        }
    }
    if finite.failure_cases.is_empty() {
        finite.status = Status::VerifiedForFiniteDomain;
        finite.evidence.push(format!(
            "all {} first-descent certificates were enumerated and their exact thresholds \
             compared with the least positive class member",
            cover.certificates.len()
        ));
    } else {
        finite.status = Status::Refuted;
        finite
            .evidence
            .push("exceptions above 1 were found; see failure cases".into());
    }

    let mut general = LedgerEntry::new(
        params,
        "threshold-exceptions-trivial-all-depths",
        statement.into(),
        "first-descent prefixes of every length".into(),
    );
    general.status = Status::Conjectured;
    general.evidence.push(format!(
        "only the finite check up to length {} (entry threshold-exceptions-trivial); this is \
         not evidence of truth for longer prefixes",
        cover.depth
    ));
    general.evidence.push(
        "appears to coincide with what the literature calls the coefficient stopping time \
         conjecture; that identification has not been reviewed in this project"
            .into(),
    );
    general.proof_obligations.push(
        "bound c / (2^k - 3^r) below the least positive class member for every first-descent \
         prefix; this needs control of how close 2^k can be to 3^r"
            .into(),
    );
    Ok(vec![finite, general])
}

/// H8: seeded sample of large integers. Observation only.
fn sampled_stopping_times(params: &ExperimentParams) -> Checked<LedgerEntry> {
    let mut entry = LedgerEntry::new(
        params,
        "sampled-stopping-times",
        format!(
            "Sampled {}-bit integers descend below themselves within {} steps.",
            params.sample_bits, params.max_steps
        ),
        format!(
            "{} integers of exactly {} bits drawn by SplitMix64 with seed {}",
            params.samples, params.sample_bits, params.seed
        ),
    );
    entry.status = Status::ExperimentallyObserved;
    let mut rng = SplitMix64::new(params.seed);
    let mut max_time = 0u64;
    let mut argmax = None;
    let mut unresolved = 0usize;
    for _ in 0..params.samples {
        let n = rng.next_biguint(params.sample_bits);
        let Some(time) = collatz::stopping_time(&n, params.max_steps) else {
            unresolved += 1;
            entry
                .failure_cases
                .push(FailureCase::NoDescentWithinWindow {
                    n,
                    window: params.max_steps,
                });
            continue;
        };
        // Cross-check the symbolic layer on this large value.
        let steps = usize::try_from(time).map_err(|e| e.to_string())?;
        let cylinder = Cylinder::containing(&n, steps);
        let cert = certify(&cylinder)
            .ok_or_else(|| format!("n = {n} descends at step {time} without a certificate"))?;
        let image = collatz::t_iter(&n, steps);
        if cylinder.image(&n).as_ref() != Some(&image) || image >= n || n < cert.threshold {
            return Err(format!(
                "symbolic and direct evaluation disagree for n = {n}"
            ));
        }
        if time > max_time {
            max_time = time;
            argmax = Some(n);
        }
    }
    entry.evidence.push(format!(
        "{} of {} samples descended; largest observed stopping time {max_time}{}",
        params.samples - unresolved,
        params.samples,
        argmax.map_or(String::new(), |n| format!(" at n = {n}"))
    ));
    entry.evidence.push(
        "for each descending sample the stopping-time prefix has 2^k > 3^r, the sample lies at \
         or above the certificate threshold, and the affine form equals direct iteration"
            .into(),
    );
    if unresolved > 0 {
        entry.evidence.push(format!(
            "{unresolved} samples did not descend within the step budget; they are listed as \
             failure cases of the bounded statement and are NOT counterexamples to the conjecture"
        ));
    }
    entry.proof_obligations.push(
        "a sample says nothing about unsampled integers; no density or convergence claim follows"
            .into(),
    );
    Ok(entry)
}

fn cover_stats(cover: &DescentCover) -> CoverStats {
    CoverStats {
        depth: cover.depth,
        certificates: cover.certificates.len(),
        uncovered: cover.uncovered.len(),
        covered_classes: cover.covered_classes(),
        total_classes: cover.total_classes(),
        max_certificate_steps: cover
            .certificates
            .iter()
            .map(|cert| cert.steps)
            .max()
            .unwrap_or(0),
        certificates_with_exceptions: cover
            .certificates
            .iter()
            .filter(|cert| !cert.exceptions.is_empty())
            .map(|cert| {
                let listed: Vec<String> = cert.exceptions.iter().map(BigUint::to_string).collect();
                format!("prefix {}: n in {{{}}}", cert.parity, listed.join(", "))
            })
            .collect(),
    }
}

/// Runs every candidate, verifies all recorded failure cases independently,
/// and hands each finished entry to `sink` immediately (so a ledger written
/// by the sink stays valid if the run is interrupted).
pub fn run_experiment<S, P>(
    params: &ExperimentParams,
    mut sink: S,
    mut progress: P,
) -> Result<ExperimentOutcome, Box<dyn Error>>
where
    S: FnMut(&LedgerEntry) -> Result<(), Box<dyn Error>>,
    P: FnMut(&str),
{
    let mut entries = Vec::new();
    let mut emit = |batch: Vec<LedgerEntry>, progress: &mut P| -> Result<(), Box<dyn Error>> {
        for entry in batch {
            for case in &entry.failure_cases {
                verifier::verify_failure_case(case).map_err(|reason| {
                    format!(
                        "verifier rejected a failure case of {}: {reason}",
                        entry.hypothesis_id
                    )
                })?;
            }
            sink(&entry)?;
            progress(&format!(
                "{}: {}",
                entry.hypothesis_id,
                entry.status.label()
            ));
            entries.push(entry);
        }
        Ok(())
    };

    progress(&format!(
        "building first-descent cover to depth {}",
        params.depth
    ));
    let cover = DescentCover::build(params.depth);
    progress(&format!(
        "cover: {} certificates, {} uncovered classes",
        cover.certificates.len(),
        cover.uncovered.len()
    ));
    for cert in &cover.certificates {
        verifier::verify_certificate(cert, 2)
            .map_err(|reason| format!("verifier rejected certificate {}: {reason}", cert.parity))?;
    }
    progress("all cover certificates passed the independent verifier");

    emit(vec![universal_window(params)?], &mut progress)?;
    emit(vec![bounded_window(params)?], &mut progress)?;
    emit(vec![bit_length_bound(params)?], &mut progress)?;
    emit(vec![prefix_residue_bijection(params)?], &mut progress)?;
    emit(vec![even_majority(params, &cover)?], &mut progress)?;
    emit(threshold_exceptions(params, &cover)?, &mut progress)?;
    emit(vec![sampled_stopping_times(params)?], &mut progress)?;

    Ok(ExperimentOutcome {
        params: params.clone(),
        cover: cover_stats(&cover),
        entries,
    })
}

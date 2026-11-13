//! Exact-arithmetic symbolic workbench for the Collatz problem.
//!
//! Everything in this crate works with the *accelerated* Collatz map
//!
//! ```text
//! T(n) = n / 2          if n is even,
//! T(n) = (3n + 1) / 2   if n is odd.
//! ```
//!
//! All validity checks use arbitrary-precision integers. No floating point is
//! used anywhere, and the only primitive-integer fast path
//! ([`collatz::stopping_time_fast`]) uses checked arithmetic and falls back to
//! `BigUint` on overflow.
//!
//! Module map:
//!
//! * [`collatz`] - the map, direct orbit evaluation, stopping times, oracles.
//! * [`prefix`] - parity prefixes, affine forms, congruence cylinders.
//! * [`certificate`] - conditional descent certificates and first-descent covers.
//! * [`counting`] - independent exact counts of first crossings and survivors.
//! * [`envelope`] - bounded exact comparison of Terras's mini-max envelope.
//! * [`nogo`] - the Mersenne adversarial baseline against fixed descent windows.
//! * [`verifier`] - an independent checker that only trusts direct iteration.
//! * [`hypothesis`] - bounded hypothesis workflow and the JSONL research ledger.
//! * [`report`] - human-readable experiment summary.
//!
//! Nothing here proves, or claims to prove, the Collatz conjecture.

pub mod certificate;
pub mod collatz;
pub mod counting;
pub mod envelope;
pub mod hypothesis;
pub mod nogo;
pub mod prefix;
pub mod report;
pub mod rng;
pub mod serde_dec;
pub mod verifier;

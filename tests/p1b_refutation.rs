//! Independent regression test for the refutation of slack hypothesis P1b
//! (`research/phase1-next-questions.md`).
//!
//! P1b claimed: `max rho` at `r` is at most `max rho` at `r = 5`
//! (`R_5 = 251/507`) for every `r > 5`. It is false at `r = 34` (`k = 54`),
//! witnessed by `m = 47` (`T^54(47) = 46`, `rho = 44834791551842521/62849190061324505`)
//! and `m = 63` (`T^54(63) = 61`, `rho = 48215861999407177/84244659018371145`).
//!
//! The direct-iteration helper below uses only `BigUint` arithmetic and does
//! not call the library's cylinder or envelope code; the library is consulted
//! only as a cross-check.

use collatz_lab::certificate::certify;
use collatz_lab::envelope::{
    run_envelope, run_envelope_extended, run_envelope_extended_with, verify_p1b_counterexample,
    EXTENDED_SUPPORTED_MAX_ODD_STEPS,
};
use collatz_lab::hypothesis::Status;
use collatz_lab::prefix::{Cylinder, ParityPrefix};
use collatz_lab::verifier;
use num_bigint::BigUint;
use num_traits::{One, Zero};

fn direct_first_crossing(seed: u64) -> (Vec<bool>, usize, usize, BigUint, BigUint) {
    let mut x = BigUint::from(seed);
    let mut bits = Vec::new();
    let mut r = 0usize;
    let mut k = 0usize;
    let mut c = BigUint::zero();
    let mut pow3 = BigUint::one();
    loop {
        let odd = (&x % 2u32) == BigUint::one();
        bits.push(odd);
        if odd {
            c = c * 3u32 + (BigUint::one() << k);
            x = (x * 3u32 + 1u32) >> 1usize;
            pow3 *= 3u32;
            r += 1;
        } else {
            x >>= 1usize;
        }
        k += 1;
        let pow2 = BigUint::one() << k;
        if pow2 > pow3 {
            return (bits, r, k, c, x);
        }
        assert!(k <= 100, "unexpectedly long prefix for seed {seed}");
    }
}

fn reduce_fraction(num: BigUint, den: BigUint) -> (BigUint, BigUint) {
    let (mut a, mut b) = (num.clone(), den.clone());
    while !b.is_zero() {
        let rem = a % &b;
        a = b;
        b = rem;
    }
    (num / &a, den / a)
}

#[test]
fn p1b_is_refuted_at_r34_by_47_and_63() {
    let r5_num = BigUint::from(251u32);
    let r5_den = BigUint::from(507u32);
    let expected = [
        (47u64, 46u64, "44834791551842521", "62849190061324505"),
        (63u64, 61u64, "48215861999407177", "84244659018371145"),
    ];

    for (seed, expected_end, exp_num, exp_den) in expected {
        let (bits, r, k, c, end) = direct_first_crossing(seed);
        assert_eq!((r, k), (34, 54));
        assert_eq!(end, BigUint::from(expected_end));

        let m = BigUint::from(seed);
        let pow2 = BigUint::one() << k;
        let pow3 = BigUint::from(3u32).pow(r as u32);
        let d = &pow2 - &pow3;
        assert!(m >= BigUint::from(2u32) && m < pow2);
        // Exact affine identity.
        assert_eq!(&end * &pow2, &pow3 * &m + &c);
        // Exact drop identity: d*m - c == 2^k * (m - T^k(m)).
        assert_eq!(&d * &m, &c + &pow2 * (&m - &end));

        let (rn, rd) = reduce_fraction(c.clone(), &d * &m);
        assert_eq!(rn.to_string(), exp_num);
        assert_eq!(rd.to_string(), exp_den);
        // Exact cross-product proof that rho(seed) > R_5 = 251/507.
        assert!(&rn * &r5_den > &r5_num * &rd);

        // Cross-check against library cylinder, certificate verifier, and verify_p1b_counterexample.
        let mut prefix = ParityPrefix::empty();
        for bit in bits {
            prefix.push(bit);
        }
        let cyl = Cylinder::from_prefix(&prefix);
        assert_eq!(cyl.least_member_at_least(&BigUint::from(2u32)), m);
        assert_eq!(cyl.affine().offset(), &c);
        let cert = certify(&cyl).expect("first crossing must contract");
        verifier::verify_certificate(&cert, 0).expect("independent certificate verification");

        let checked = verify_p1b_counterexample(seed).expect("library P1b witness check");
        assert_eq!(checked.seed, m);
        assert_eq!(checked.r, 34);
        assert_eq!(checked.k, 54);
        assert_eq!(checked.endpoint, end);
        assert_eq!(checked.rho.to_string(), format!("{exp_num}/{exp_den}"));
    }
}

#[test]
fn extended_envelope_matches_frozen_phase2_on_r1_to_12() {
    let baseline = run_envelope().expect("baseline Phase 2 envelope");
    let extended = run_envelope_extended(12).expect("extended envelope up to r=12");
    assert_eq!(extended.rows, baseline.rows);
    assert_eq!(extended.p1a_counterexample_rs, vec![6, 8]);
    assert_eq!(extended.first_counterexample_r, Some(11));
    assert_eq!(extended.e_le_two_status, Status::Refuted);
    assert_eq!(extended.p1b_status, Status::Refuted);
}

#[test]
fn extended_envelope_r14_refutes_p1a_again() {
    let extended = run_envelope_extended(15).expect("extended envelope up to r=15");
    assert_eq!(extended.p1a_counterexample_rs, vec![6, 8, 14]);
    let row14 = &extended.rows[13];
    assert_eq!((row14.r, row14.k), (14, 23));
    assert_eq!(row14.min_m, BigUint::from(639u32));
    assert_eq!(row14.max_ratio_witnesses.len(), 1);
    assert_eq!(row14.max_ratio_witnesses[0].m, BigUint::from(1115u32));
}

#[test]
fn extended_envelope_is_independent_of_thread_count() {
    // r = 14..17 have k = 23..27 > the split depth, so the parallel merge is exercised.
    let serial = run_envelope_extended(17).expect("serial scan");
    for threads in [2usize, 7] {
        let mut seen = Vec::new();
        let parallel = run_envelope_extended_with(17, threads, &mut |row| seen.push(row.clone()))
            .expect("parallel scan");
        assert_eq!(serial, parallel, "threads={threads} changed the result");
        assert_eq!(seen, parallel.rows, "callback must see every row in order");
    }
    assert_eq!(serial.rows[16].family_count, BigUint::from(312_455u32));
    assert!(run_envelope_extended(EXTENDED_SUPPORTED_MAX_ODD_STEPS + 1).is_err());
}

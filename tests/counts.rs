//! Reconciliation of three independent ways to count first coefficient
//! crossings and surviving residue classes: the constructive cover walker,
//! the lattice recurrence by length, and the enumeration by odd positions.
//! Known values are compared with OEIS A076227 and A100982 (retrieved
//! 2026-11-13).

use collatz_lab::certificate::{walk_first_descent, CoverNode, DescentCover};
use collatz_lab::counting::{count_by_length, count_by_odd_positions, crossing_length};
use num_bigint::BigUint;

/// OEIS A076227, offset 0: "Number of surviving Collatz residues mod 2^n."
const A076227: [u64; 26] = [
    1, 1, 1, 2, 3, 4, 8, 13, 19, 38, 64, 128, 226, 367, 734, 1295, 2114, 4228, 7495, 14990, 27328,
    46611, 93222, 168807, 286581, 573162,
];

/// OEIS A100982, offset 1: "Number of admissible sequences of order n;
/// related to 3x+1 problem and Wagon's constant."
const A100982: [u64; 20] = [
    1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637, 51033, 108950, 312455, 663535,
    1900470, 5936673,
];

/// (depth, certificates, uncovered) as recorded in research/phase0-report.md.
const RECORDED: [(usize, u64, u64); 6] = [
    (4, 3, 3),
    (8, 15, 19),
    (12, 57, 226),
    (16, 791, 2114),
    (20, 4404, 27328),
    (24, 81119, 286581),
];

fn big(n: u64) -> BigUint {
    BigUint::from(n)
}

#[test]
fn both_recurrences_match_the_oeis_terms() {
    let by_length = count_by_length(40);
    for (n, &term) in A076227.iter().enumerate() {
        assert_eq!(by_length.survivors[n], big(term), "A076227({n})");
        assert_eq!(
            count_by_odd_positions(n).survivors,
            big(term),
            "A076227({n})"
        );
    }
    let by_positions = count_by_odd_positions(crossing_length(A100982.len()));
    assert_eq!(by_positions.first_crossings_by_odd_steps[0], big(1));
    for (index, &term) in A100982.iter().enumerate() {
        let r = index + 1;
        assert_eq!(
            by_positions.first_crossings_by_odd_steps[r],
            big(term),
            "A100982({r})"
        );
        // All first crossings with r odd steps share one length.
        assert_eq!(by_length.first_crossings[crossing_length(r)], big(term));
    }
}

#[test]
fn recurrences_agree_with_each_other_far_beyond_the_walker() {
    let max_depth = 150usize;
    let by_length = count_by_length(max_depth);
    for depth in 0..=max_depth {
        let by_positions = count_by_odd_positions(depth);
        assert_eq!(
            by_positions.survivors, by_length.survivors[depth],
            "{depth}"
        );
        assert_eq!(
            by_positions.first_crossings_up_to_depth(),
            by_length.first_crossings_up_to(depth),
            "{depth}"
        );
    }
    // Lengths that are not a crossing length carry no first crossing.
    let lengths: Vec<usize> = (0..=max_depth).map(crossing_length).collect();
    for (depth, crossings) in by_length.first_crossings.iter().enumerate() {
        if !lengths.contains(&depth) {
            assert_eq!(crossings, &big(0), "{depth}");
        }
    }
}

#[test]
fn walker_matches_recurrences_at_every_depth_up_to_16() {
    let by_length = count_by_length(16);
    for depth in 0..=16usize {
        let cover = DescentCover::build(depth);
        assert_eq!(
            big(cover.uncovered.len() as u64),
            by_length.survivors[depth]
        );
        assert_eq!(
            big(cover.certificates.len() as u64),
            by_length.first_crossings_up_to(depth)
        );
        // Per-length and per-odd-step breakdowns agree too.
        let by_positions = count_by_odd_positions(depth);
        for (r, expected) in by_positions.first_crossings_by_odd_steps.iter().enumerate() {
            let found = cover
                .certificates
                .iter()
                .filter(|cert| cert.odd_steps == r)
                .inspect(|cert| assert_eq!(cert.steps, crossing_length(r)))
                .count();
            assert_eq!(&big(found as u64), expected, "depth {depth}, r = {r}");
        }
    }
}

#[test]
fn recorded_counts_reconcile_at_depths_4_to_24() {
    let by_length = count_by_length(24);
    for &(depth, certificates, uncovered) in &RECORDED {
        // Constructive walker, counted without storing the leaves.
        let (mut walked_certificates, mut walked_uncovered) = (0u64, 0u64);
        walk_first_descent(depth, |node| match node {
            CoverNode::Certified(_) => walked_certificates += 1,
            CoverNode::Uncovered(_) => walked_uncovered += 1,
        });
        assert_eq!(
            (walked_certificates, walked_uncovered),
            (certificates, uncovered)
        );
        // Lattice recurrence.
        assert_eq!(by_length.first_crossings_up_to(depth), big(certificates));
        assert_eq!(by_length.survivors[depth], big(uncovered));
        // Odd-position enumeration.
        let by_positions = count_by_odd_positions(depth);
        assert_eq!(
            by_positions.first_crossings_up_to_depth(),
            big(certificates)
        );
        assert_eq!(by_positions.survivors, big(uncovered));
        // OEIS.
        assert_eq!(A076227[depth], uncovered);
        let orders = by_positions.first_crossings_by_odd_steps.len() - 1;
        assert_eq!(1 + A100982[..orders].iter().sum::<u64>(), certificates);
    }
}

#[test]
fn partition_identity_holds_for_the_recurrence() {
    // Each first crossing of length k covers 2^(depth - k) classes modulo
    // 2^depth; together with the survivors they exhaust all 2^depth classes.
    for depth in [0usize, 1, 7, 64, 200] {
        let counts = count_by_length(depth);
        let mut total = counts.survivors[depth].clone();
        for (k, crossings) in counts.first_crossings.iter().enumerate() {
            total += crossings << (depth - k);
        }
        assert_eq!(total, BigUint::from(1u32) << depth, "depth {depth}");
    }
}

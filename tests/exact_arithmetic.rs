//! Deterministic cross-validation of the symbolic layer against direct
//! iteration: small exhaustive cases, seeded large integers (well beyond
//! `u128`), and the Mersenne adversarial family.

use std::collections::BTreeSet;

use collatz_lab::certificate::{certify, DescentCover};
use collatz_lab::collatz::{
    range_oracle, stopping_time, stopping_time_fast, t_iter, t_step, t_step_u64,
    total_stopping_time,
};
use collatz_lab::nogo;
use collatz_lab::prefix::{
    closed_form_offset, residue_by_inverse, AffineMap, Cylinder, ParityPrefix,
};
use collatz_lab::rng::SplitMix64;
use collatz_lab::verifier::verify_certificate;
use num_bigint::BigUint;
use num_traits::{One, Pow, Zero};

fn big(n: u64) -> BigUint {
    BigUint::from(n)
}

fn all_prefixes(len: usize) -> Vec<ParityPrefix> {
    (0u32..1 << len)
        .map(|mask| ParityPrefix::from_bits((0..len).map(|i| mask >> i & 1 == 1).collect()))
        .collect()
}

#[test]
fn u64_step_matches_biguint_on_small_range() {
    for n in 0u64..20_000 {
        assert_eq!(t_step_u64(n).map(BigUint::from), Some(t_step(&big(n))));
    }
}

#[test]
fn fast_stopping_time_matches_biguint_exhaustively() {
    for n in 2u64..5_000 {
        assert_eq!(
            stopping_time_fast(n, 1_000),
            stopping_time(&big(n), 1_000),
            "{n}"
        );
    }
}

#[test]
fn range_oracle_agrees_with_total_stopping_times() {
    let oracle = range_oracle(3_000, 1_000);
    assert!(oracle.all_reach_one());
    assert_eq!((oracle.argmax, oracle.max_stopping_time), (703, 81));
    for n in 1u64..=3_000 {
        assert!(total_stopping_time(&big(n), 1_000).is_some(), "{n}");
    }
    // A step budget that is too small must surface as unresolved, not vanish.
    let starved = range_oracle(30, 5);
    assert_eq!(starved.unresolved, vec![7, 15, 27]);
}

#[test]
fn prefixes_and_residues_are_in_bijection_up_to_length_10() {
    for len in 0..=10usize {
        let mut residues = BTreeSet::new();
        for prefix in all_prefixes(len) {
            let cylinder = Cylinder::from_prefix(&prefix);
            let residue = cylinder.residue().clone();
            assert!(residue < cylinder.modulus());
            // Two independent constructions of the residue.
            assert_eq!(residue_by_inverse(cylinder.affine()), residue);
            // Round trip residue -> prefix -> cylinder.
            assert_eq!(ParityPrefix::of(&residue, len), prefix);
            assert_eq!(Cylinder::containing(&residue, len), cylinder);
            // Recursive and closed-form offsets.
            assert_eq!(
                closed_form_offset(prefix.bits()),
                *cylinder.affine().offset()
            );
            residues.insert(residue);
        }
        assert_eq!(residues.len(), 1 << len);
    }
}

#[test]
fn affine_form_matches_direct_iteration_exhaustively() {
    for len in 0..=8usize {
        let modulus = 1u64 << len;
        for prefix in all_prefixes(len) {
            let cylinder = Cylinder::from_prefix(&prefix);
            let residue = u64::try_from(cylinder.residue()).unwrap();
            for n in 0..4 * modulus {
                let n_big = big(n);
                let member = n % modulus == residue;
                assert_eq!(cylinder.contains(&n_big), member);
                assert_eq!(ParityPrefix::of(&n_big, len) == prefix, member);
                let expected = member.then(|| t_iter(&n_big, len));
                assert_eq!(cylinder.image(&n_big), expected);
                // Exact divisibility characterises membership.
                assert_eq!(cylinder.affine().apply(&n_big), expected);
            }
        }
    }
}

#[test]
fn affine_composition_identity() {
    // The map of a concatenation p ++ q satisfies
    //   r = r_p + r_q,  c = 3^(r_q) c_p + 2^(k_p) c_q.
    for p in all_prefixes(5) {
        for q in all_prefixes(4) {
            let a = AffineMap::from_prefix(&p);
            let b = AffineMap::from_prefix(&q);
            let mut bits = p.bits().to_vec();
            bits.extend_from_slice(q.bits());
            let joined = AffineMap::from_prefix(&ParityPrefix::from_bits(bits));
            assert_eq!(joined.odd_steps(), a.odd_steps() + b.odd_steps());
            assert_eq!(joined.multiplier(), &(a.multiplier() * b.multiplier()));
            assert_eq!(
                joined.offset(),
                &(b.multiplier() * a.offset() + (b.offset() << a.steps()))
            );
        }
    }
}

#[test]
fn descent_thresholds_are_exact_for_every_prefix_up_to_length_10() {
    for len in 1..=10usize {
        let modulus = 1u64 << len;
        for prefix in all_prefixes(len) {
            let cylinder = Cylinder::from_prefix(&prefix);
            let residue = u64::try_from(cylinder.residue()).unwrap();
            let members = (0..64u64).map(|t| residue + t * modulus).filter(|&n| n > 0);
            match certify(&cylinder) {
                Some(cert) => {
                    verify_certificate(&cert, 4).unwrap();
                    assert!(cert.exceptions_complete());
                    for n in members {
                        let n = big(n);
                        let descends = t_iter(&n, len) < n;
                        assert_eq!(descends, n >= cert.threshold, "{prefix} n={n}");
                        assert_eq!(cert.exceptions.contains(&n), !descends);
                    }
                }
                None => {
                    for n in members {
                        assert!(t_iter(&big(n), len) >= big(n), "{prefix} n={n}");
                    }
                }
            }
        }
    }
}

#[test]
fn first_descent_leaves_have_stopping_time_equal_to_their_length() {
    let depth = 12usize;
    let cover = DescentCover::build(depth);
    // Brute force: classes modulo 2^depth with no coefficient descent.
    assert_eq!(
        cover.covered_classes() + BigUint::from(cover.uncovered.len()),
        BigUint::one() << depth
    );
    for cert in &cover.certificates {
        verify_certificate(cert, 3).unwrap();
        let mut n = cert.residue.clone();
        while n < cert.threshold {
            n += &cert.modulus;
        }
        for _ in 0..3 {
            assert_eq!(stopping_time(&n, 1_000), Some(cert.steps as u64));
            n += &cert.modulus;
        }
    }
    // Members of uncovered classes do not descend within `depth` steps.
    for class in &cover.uncovered {
        for t in 1u32..4 {
            let n = &class.residue + &class.modulus * t;
            assert!(nogo::refutes_window(&n, depth), "{n}");
        }
    }
    // The only positive member below any threshold is n = 1 (prefix 10).
    let with_exceptions: Vec<_> = cover
        .certificates
        .iter()
        .filter(|cert| !cert.exception_count.is_zero())
        .collect();
    assert_eq!(with_exceptions.len(), 1);
    assert_eq!(with_exceptions[0].parity, "10");
    assert_eq!(with_exceptions[0].exceptions, vec![BigUint::one()]);
}

#[test]
fn uncovered_counts_match_brute_force() {
    // Independent count: residues n mod 2^k (taken large enough that the
    // parity prefix is that of the class) whose prefix never has 2^j > 3^r.
    for depth in 0..=10usize {
        let brute = all_prefixes(depth)
            .iter()
            .filter(|prefix| {
                (1..=depth).all(|j| {
                    let odd = prefix.bits()[..j].iter().filter(|&&b| b).count();
                    (BigUint::one() << j) < Pow::pow(&BigUint::from(3u32), odd)
                })
            })
            .count();
        assert_eq!(
            DescentCover::build(depth).uncovered.len(),
            brute,
            "depth {depth}"
        );
    }
}

#[test]
fn seeded_large_integers_beyond_u128() {
    let mut rng = SplitMix64::new(0xC011A72);
    for bits in [129usize, 200, 257, 512, 1000] {
        for len in [1usize, 17, 64, 150] {
            let n = rng.next_biguint(bits);
            assert_eq!(n.bits(), bits as u64);
            assert!(n > BigUint::from(u128::MAX));
            let cylinder = Cylinder::containing(&n, len);
            assert!(cylinder.contains(&n));
            assert_eq!(cylinder.image(&n), Some(t_iter(&n, len)));
            assert_eq!(residue_by_inverse(cylinder.affine()), *cylinder.residue());
            // A neighbour outside the class is rejected by exact divisibility.
            assert_eq!(cylinder.affine().apply(&(&n + 1u32)), None);
            // Shifting by the modulus stays in the class and shifts the image by 3^r.
            let shifted = &n + cylinder.modulus();
            assert_eq!(
                cylinder.image(&shifted),
                Some(t_iter(&n, len) + cylinder.affine().multiplier())
            );
        }
    }
}

#[test]
fn seeded_large_integers_respect_their_descent_certificate() {
    let mut rng = SplitMix64::new(7);
    for _ in 0..40 {
        let n = rng.next_biguint(160);
        let time = stopping_time(&n, 100_000).expect("bounded search should succeed here");
        let cylinder = Cylinder::containing(&n, time as usize);
        let cert = certify(&cylinder).expect("stopping-time prefix has 2^k > 3^r");
        verify_certificate(&cert, 2).unwrap();
        assert!(n >= cert.threshold);
        // No shorter prefix of a large n can carry a certificate.
        for j in 1..time as usize {
            assert!(certify(&Cylinder::containing(&n, j)).is_none());
        }
    }
}

#[test]
fn mersenne_identity_and_all_odd_prefix() {
    for l in 0..=200usize {
        assert_eq!(nogo::check_mersenne_identity(l), Ok(()));
        let n = nogo::mersenne(l);
        // Symbolic side: the prefix is 1^l with c = 3^l - 2^l, residue 2^l - 1.
        let cylinder = Cylinder::from_prefix(&ParityPrefix::all_odd(l));
        let pow3 = Pow::pow(&BigUint::from(3u32), l);
        assert_eq!(ParityPrefix::of(&n, l), ParityPrefix::all_odd(l));
        assert_eq!(cylinder.affine().offset(), &(&pow3 - (BigUint::one() << l)));
        assert_eq!(
            cylinder.residue(),
            &if l == 0 { BigUint::zero() } else { n.clone() }
        );
        assert_eq!(cylinder.image(&n), Some(&pow3 - 1u32));
        assert!(certify(&cylinder).is_none());
        assert!(nogo::refutes_window(&n, l));
    }
}

#[test]
fn no_fixed_window_survives_its_witness() {
    for window in 1..=80usize {
        for bound_bits in [0usize, 70, 140] {
            let bound = BigUint::one() << bound_bits;
            let n = nogo::window_witness(window, &bound);
            assert!(n >= bound);
            assert!(nogo::refutes_window(&n, window));
            assert_eq!(stopping_time(&n, window as u64), None);
        }
    }
    // The witness class is sharp: the window + 1 step can descend.
    assert!(!nogo::refutes_window(&big(3), 4));
}

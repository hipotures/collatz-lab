//! Property tests (proptest) for the parity-prefix machinery.

use collatz_lab::certificate::certify;
use collatz_lab::collatz::{stopping_time, stopping_time_fast, t_iter, t_step, t_step_u64};
use collatz_lab::prefix::{
    closed_form_offset, residue_by_inverse, AffineMap, Cylinder, ParityPrefix,
};
use collatz_lab::verifier::verify_certificate;
use num_bigint::BigUint;
use proptest::prelude::*;

fn big_uint() -> impl Strategy<Value = BigUint> {
    proptest::collection::vec(any::<u32>(), 0..12).prop_map(BigUint::new)
}

fn parity_prefix(max_len: usize) -> impl Strategy<Value = ParityPrefix> {
    proptest::collection::vec(any::<bool>(), 0..=max_len).prop_map(ParityPrefix::from_bits)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn u64_step_agrees_or_reports_overflow(n in any::<u64>()) {
        let exact = t_step(&BigUint::from(n));
        match t_step_u64(n) {
            Some(value) => prop_assert_eq!(BigUint::from(value), exact),
            None => prop_assert!(exact > BigUint::from(u64::MAX)),
        }
    }

    #[test]
    fn fast_stopping_time_agrees_near_the_u64_boundary(offset in 0u64..1_000_000) {
        let n = u64::MAX - offset;
        prop_assert_eq!(stopping_time_fast(n, 2_000), stopping_time(&BigUint::from(n), 2_000));
    }

    #[test]
    fn every_integer_lies_in_the_cylinder_of_its_own_prefix(n in big_uint(), len in 0usize..90) {
        let prefix = ParityPrefix::of(&n, len);
        let cylinder = Cylinder::from_prefix(&prefix);
        prop_assert!(cylinder.contains(&n));
        prop_assert_eq!(cylinder.image(&n), Some(t_iter(&n, len)));
        prop_assert_eq!(&n % cylinder.modulus(), cylinder.residue().clone());
    }

    #[test]
    fn prefix_residue_round_trip(prefix in parity_prefix(80), t in big_uint()) {
        let cylinder = Cylinder::from_prefix(&prefix);
        prop_assert!(cylinder.residue() < &cylinder.modulus());
        prop_assert_eq!(residue_by_inverse(cylinder.affine()), cylinder.residue().clone());
        prop_assert_eq!(closed_form_offset(prefix.bits()), cylinder.affine().offset().clone());
        let member = cylinder.member(&t);
        prop_assert_eq!(ParityPrefix::of(&member, prefix.len()), prefix.clone());
        // The sibling class modulo 2^k differs somewhere in the prefix.
        if !prefix.is_empty() {
            let outsider = &member + (cylinder.modulus() >> 1usize);
            prop_assert_ne!(ParityPrefix::of(&outsider, prefix.len()), prefix);
        }
    }

    #[test]
    fn affine_maps_compose(p in parity_prefix(40), q in parity_prefix(40), t in big_uint()) {
        let mut bits = p.bits().to_vec();
        bits.extend_from_slice(q.bits());
        let joined = Cylinder::from_prefix(&ParityPrefix::from_bits(bits));
        let n = joined.member(&t);
        let first = AffineMap::from_prefix(&p).apply(&n).expect("n follows p");
        let second = AffineMap::from_prefix(&q).apply(&first).expect("T^|p|(n) follows q");
        prop_assert_eq!(joined.image(&n), Some(second));
    }

    #[test]
    fn descent_threshold_is_an_exact_boundary(prefix in parity_prefix(60), t in big_uint()) {
        let cylinder = Cylinder::from_prefix(&prefix);
        let len = prefix.len();
        let member = cylinder.member(&(t + 1u32));
        match certify(&cylinder) {
            Some(cert) => {
                prop_assert_eq!(verify_certificate(&cert, 2), Ok(()));
                prop_assert_eq!(t_iter(&member, len) < member, member >= cert.threshold);
                // Tightness at the boundary itself.
                let at = cylinder.least_member_at_least(&cert.threshold);
                prop_assert!(t_iter(&at, len) < at);
                if at >= cylinder.modulus() {
                    let below = &at - cylinder.modulus();
                    if below < cert.threshold {
                        prop_assert!(t_iter(&below, len) >= below);
                    }
                }
            }
            None => prop_assert!(t_iter(&member, len) >= member),
        }
    }

    #[test]
    fn tampered_certificates_are_rejected(prefix in parity_prefix(40), bump in 1u32..5) {
        let cylinder = Cylinder::from_prefix(&prefix);
        if let Some(cert) = certify(&cylinder) {
            let mut wrong = cert.clone();
            wrong.threshold += bump;
            prop_assert!(verify_certificate(&wrong, 1).is_err());
            let mut wrong = cert.clone();
            wrong.offset += bump;
            prop_assert!(verify_certificate(&wrong, 1).is_err());
            let mut wrong = cert.clone();
            wrong.residue = (&cert.residue + 1u32) % &cert.modulus;
            prop_assert!(verify_certificate(&wrong, 1).is_err());
        }
    }
}

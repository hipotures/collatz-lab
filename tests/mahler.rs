//! Independent verification and adversarial/negative tests for Phase 3 (`mahler`).
//!
//! These tests recompute the morphism word, survival inequalities, 2-adic
//! checkpoints, periodic control `-19/11`, Mahler functional equation, and Padé
//! identities independently of `src/mahler.rs`, and verify that the four
//! mandatory negative/adversarial failure modes are caught.

use std::fs;
use std::process::Command;

use collatz_lab::hypothesis::Status;
use collatz_lab::mahler::{
    degree4_linear_form, mu_bit_by_recurrence, mu_word_by_substitution, repaired_tower_step,
    run_mahler, verify_candidate_integrity, verify_mahler_experiment,
    verify_word_and_all_prefix_survival, CHECKPOINT_BITS, DEFAULT_MAX_BITS, MAX_PADE_DEGREE,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Pow, Zero};

/// Independently generates `w` up to `len` bits using only the base-4 digit
/// rules (without calling `mu_word_by_substitution` or `mu_bit_by_recurrence`).
fn independent_mu_word(len: usize) -> Vec<bool> {
    let mut w = vec![false; len];
    if len > 0 {
        w[0] = true;
    }
    for n in 0..len {
        let b = w[n];
        if 4 * n < len {
            w[4 * n] = true;
        }
        if 4 * n + 1 < len {
            w[4 * n + 1] = true;
        }
        if 4 * n + 2 < len {
            w[4 * n + 2] = b;
        }
        if 4 * n + 3 < len {
            w[4 * n + 3] = !b;
        }
    }
    w
}

/// Independently iterates `T(x)` on `x` for `steps` steps using raw `BigUint`
/// arithmetic, returning `(emitted_parities, final_iterate)`.
fn independent_direct_orbit(seed: &BigUint, steps: usize) -> (Vec<bool>, BigUint) {
    let mut x = seed.clone();
    let mut bits = Vec::with_capacity(steps);
    let three = BigUint::from(3u32);
    let one = BigUint::one();
    for _ in 0..steps {
        let odd = (&x & &one) == one;
        bits.push(odd);
        if odd {
            x = (&three * x + &one) >> 1usize;
        } else {
            x >>= 1usize;
        }
    }
    (bits, x)
}

/// Independently lifts the unique residue modulo `2^K` step-by-step using
/// only `T^j(x)` parity checks (`x` or `x + 2^j`).
fn independent_hensel_residue(target_bits: &[bool]) -> BigUint {
    let mut residue = BigUint::zero();
    for (step, &want_odd) in target_bits.iter().enumerate() {
        let (emitted, _) = independent_direct_orbit(&residue, step + 1);
        if emitted[step] != want_odd {
            residue += BigUint::one() << step;
        }
    }
    residue
}

/// Independently computes the affine offset `c(bits)` by applying `c <- 3c + 2^j`
/// on odd steps and `c <- c` on even steps.
fn independent_affine_offset(bits: &[bool]) -> (usize, BigUint) {
    let mut r = 0usize;
    let mut c = BigUint::zero();
    let three = BigUint::from(3u32);
    for (j, &odd) in bits.iter().enumerate() {
        if odd {
            r += 1;
            c = &three * c + (BigUint::one() << j);
        }
    }
    (r, c)
}

#[test]
fn independent_word_survival_and_five_way_checkpoints_up_to_1024() {
    let outcome = run_mahler().unwrap();
    assert_eq!(outcome.max_bits, DEFAULT_MAX_BITS);
    assert_eq!(outcome.max_pade_degree, MAX_PADE_DEGREE);

    let oracle_word = independent_mu_word(DEFAULT_MAX_BITS + 64);
    let sub_word = mu_word_by_substitution(DEFAULT_MAX_BITS + 64);
    assert_eq!(oracle_word, sub_word);
    for (i, &bit) in oracle_word.iter().enumerate() {
        assert_eq!(bit, mu_bit_by_recurrence(i), "mismatch at index {i}");
    }

    // Check all-prefix survival 3^(r_k) > 2^k and block lower bound 9/8 * (27/16)^q.
    let mut r_k = 0usize;
    for k in 1..=DEFAULT_MAX_BITS {
        if oracle_word[k - 1] {
            r_k += 1;
        }
        let pow3 = Pow::pow(&BigUint::from(3u32), r_k);
        let pow2 = BigUint::one() << k;
        assert!(pow3 > pow2, "crossing at k = {k}");
        let q = (k - 1) / 4;
        assert!(
            &pow3 * 8u32 * (BigUint::one() << (4 * q))
                >= &pow2 * 9u32 * Pow::pow(&BigUint::from(27u32), q),
            "block multiplier bound failed at k = {k}"
        );
    }

    // Check each checkpoint K in {16, 32, 64, 128, 256, 512, 1024} independently.
    assert_eq!(outcome.checkpoints.len(), CHECKPOINT_BITS.len());
    for (row, &k_bits) in outcome.checkpoints.iter().zip(CHECKPOINT_BITS.iter()) {
        assert_eq!(row.k_bits, k_bits);
        assert_eq!(row.odd_steps, 3 * (k_bits / 4));
        assert!(row.all_prefixes_survive);
        assert!(row.f2_functional_equation_matches);
        assert!(row.block_cocycle_matches);
        assert!(row.direct_iteration_matches);

        let prefix = &oracle_word[..k_bits];
        let hensel_res = independent_hensel_residue(prefix);
        assert_eq!(row.residue_affine_inverse, hensel_res);
        assert_eq!(row.residue_cylinder_lift, hensel_res);
        assert_eq!(row.residue_parity_positions, hensel_res);
        assert_eq!(row.residue_mahler_reduction, hensel_res);

        // Verify direct iteration on `hensel_res` emits `prefix` and satisfies
        // 2^K * T^K(x_K) == 3^(r_K) * x_K + c(w_<K).
        let (emitted, final_val) = independent_direct_orbit(&hensel_res, k_bits);
        assert_eq!(emitted, prefix);
        assert!(final_val > hensel_res);
        let (r, c) = independent_affine_offset(prefix);
        assert_eq!(r, row.odd_steps);
        let lhs = &final_val << k_bits;
        let rhs = Pow::pow(&BigUint::from(3u32), r) * &hensel_res + &c;
        assert_eq!(lhs, rhs);

        // Verify the 2-adic Mahler congruence:
        // 297 * x_K + 621 == 44 * F_2(16/27) (mod 2^K).
        let modulus = BigUint::one() << k_bits;
        let mahler_lhs = (&hensel_res * 297u32 + 621u32) % &modulus;
        let mahler_rhs = (&row.f2_mod_2k * 44u32) % &modulus;
        assert_eq!(
            mahler_lhs, mahler_rhs,
            "Mahler identity mismatch at K={k_bits}"
        );
    }
}

#[test]
fn independent_periodic_control_minus_19_over_11_and_finite_divergence() {
    let outcome = run_mahler().unwrap();
    assert_eq!(outcome.periodic_control.len(), CHECKPOINT_BITS.len());

    for (row, &k_bits) in outcome.periodic_control.iter().zip(CHECKPOINT_BITS.iter()) {
        assert_eq!(row.k_bits, k_bits);
        let modulus = BigUint::one() << k_bits;

        // 11 * n_K + 19 == 0 (mod 2^K)
        assert!(row.positive_seed >= BigUint::from(2u32));
        assert_eq!(
            (&row.positive_seed * 11u32 + 19u32) % &modulus,
            BigUint::zero()
        );

        // Iterate T directly past k_bits to find the exact divergence step.
        let (emitted, _) = independent_direct_orbit(&row.positive_seed, k_bits + 16);
        for (idx, &bit) in emitted[..k_bits].iter().enumerate() {
            let expected = (idx & 3) != 3;
            assert_eq!(
                bit, expected,
                "periodic prefix mismatch at K={k_bits}, step={idx}"
            );
        }
        let first_div = emitted
            .iter()
            .enumerate()
            .find_map(|(idx, &bit)| (bit != ((idx & 3) != 3)).then_some(idx))
            .expect("positive integer cannot follow (1110)^infinity forever");
        assert!(first_div >= k_bits);
        assert_eq!(row.first_divergence_step, first_div);
    }
}

#[test]
fn independent_pade_identities_and_cancelled_vs_uncancelled_mahler_tower() {
    let outcome = run_mahler().unwrap();
    let w = independent_mu_word(128);

    // 1. Check the degree-4 Padé jump: (1 + z + z^2) + (-1 + z^4) F(z) = z^14 - z^15 + O(z^26).
    let row4 = &outcome.pade_candidates[3];
    assert_eq!(row4.degree_bound, 4);
    assert_eq!(row4.reduced_vanishing_order, 14);
    assert_eq!(row4.leading_coeff, "1");
    assert!(row4.leading_coeff_is_odd);
    assert!(row4.closes_cancelled_tower_asymptotic);
    assert!(row4.closes_coarse_integer_ledger);

    // Check singular block on 4 <= m <= 9 and new primitive rows at m = 10..=16.
    for m in 4..=9 {
        let row = &outcome.pade_candidates[m - 1];
        assert_eq!(row.reduced_max_degree, 4);
        assert_eq!(row.reduced_vanishing_order, 14);
        assert_eq!(row.in_singular_block, m >= 5);
    }

    // 2. Check m = 15 has v_2(c) = 6 >= 4 (c = -960), where the z^32 term (v_2 = 128)
    //    strictly dominates the z^31 term (4*31 + 6 = 130) at z = 16/27.
    let row15 = &outcome.pade_candidates[14];
    assert_eq!(row15.degree_bound, 15);
    assert_eq!(row15.reduced_vanishing_order, 31);
    assert_eq!(row15.leading_coeff, "-960");
    assert_eq!(row15.leading_coeff_v2, 6);
    assert!(!row15.closes_coarse_integer_ledger);

    // 3. Check m = 16 jumps to N = 58 with c = 1.
    let row16 = &outcome.pade_candidates[15];
    assert_eq!(row16.degree_bound, 16);
    assert_eq!(row16.reduced_vanishing_order, 58);
    assert_eq!(row16.leading_coeff, "1");
    assert!(row16.closes_coarse_integer_ledger);

    // 4. Verify the B(z) = z^2(1 - z) denominator obstruction and a_0^2 cancellation
    //    directly on the actual checkpoint seed x_1024 (with D_0 = 11, u_0 = 27*(11*x_1024 + 23)/4).
    let a0 = BigInt::from(16u32);
    let b0 = BigInt::from(27u32);
    let d0 = BigInt::from(11u32);
    let d1_uncancelled =
        &d0 * Pow::pow(&a0, 2usize) * (&b0 - &a0) * (Pow::pow(&b0, 4usize) - Pow::pow(&a0, 4usize));
    assert_eq!(&d1_uncancelled % 256, BigInt::zero());
    assert_ne!(&d1_uncancelled % 512, BigInt::zero());
    assert_eq!(outcome.tower_summary.uncancelled_d1_two_adic_valuation, 8);
    assert_eq!(outcome.uncancelled_tower_status, Status::Refuted);

    let x_1024 = BigInt::from(
        outcome
            .checkpoints
            .last()
            .unwrap()
            .residue_affine_inverse
            .clone(),
    );
    let u0 = &b0 * ((BigInt::from(11u32) * &x_1024 + BigInt::from(23u32)) / BigInt::from(4u32));
    let coeff_geom = Pow::pow(&b0, 3usize) + &a0 * Pow::pow(&b0, 2usize) + Pow::pow(&a0, 3usize);
    let delta0 = (Pow::pow(&b0, 4usize) - Pow::pow(&a0, 4usize)) * &u0 - &d0 * &b0 * coeff_geom;
    assert_eq!(&delta0 % Pow::pow(&a0, 2usize), BigInt::zero());
    let _ = w;
}

/// Independently computes the homogenised prefix sum `preS(a, b, L) = sum_{q=0}^{L-1} w[q] a^q b^(L-1-q)`.
fn independent_pre_s(w: &[bool], a: &BigInt, b: &BigInt, len: usize) -> BigInt {
    let mut sum = BigInt::zero();
    for (q, &bit) in w.iter().take(len).enumerate() {
        if bit {
            sum += Pow::pow(a, q) * Pow::pow(b, len - 1 - q);
        }
    }
    sum
}

#[test]
fn regression_test_unnormalized_u0_fails_mod16_and_repaired_tower_succeeds_on_checkpoint_seeds() {
    let outcome = run_mahler().unwrap();
    let w = independent_mu_word(DEFAULT_MAX_BITS + 64);
    let a0 = BigInt::from(16u32);
    let b0 = BigInt::from(27u32);
    let d0 = BigInt::from(11u32);
    let a0_sq = Pow::pow(&a0, 2usize);
    let coeff_geom = Pow::pow(&b0, 3usize) + &a0 * Pow::pow(&b0, 2usize) + Pow::pow(&a0, 3usize);

    for (row, &k_bits) in outcome.checkpoints.iter().zip(CHECKPOINT_BITS.iter()) {
        let x_k_uint = independent_hensel_residue(&w[..k_bits]);
        assert_eq!(x_k_uint, row.residue_affine_inverse);
        let x_k = BigInt::from(x_k_uint.clone());

        // 11 * x_K + 23 is divisible by 4 because w(0) = w(1) = 1 => x_K == 3 (mod 4).
        let eleven_x_plus_23 = BigInt::from(11u32) * &x_k + BigInt::from(23u32);
        assert_eq!(&eleven_x_plus_23 % 4, BigInt::zero());

        // A. Unnormalized (buggy) definition: u_0^old = (11*x_K + 23)/4 with D_0 = 11.
        //    Since (11*x + 23)/4 = (11/27)*F_2(16/27), at L = 1 (preS(16, 27, 1) = 1),
        //    u_0^old == 11 * 27^(-1) == 11 * 3 == 1 != 11 == D_0 * preS(16, 27, 1) (mod 16).
        let u0_unnormalized = &eleven_x_plus_23 / 4;
        assert_eq!(
            &u0_unnormalized % &a0,
            BigInt::one(),
            "at K={k_bits}, unnormalized u0_old must equal 1 (mod 16), failing D0 * preS = 11 (mod 16)"
        );
        assert_ne!(
            &u0_unnormalized % &a0,
            (&d0 * independent_pre_s(&w, &a0, &b0, 1)) % &a0,
            "at K={k_bits}, unnormalized u0_old must fail the L=1 base congruence modulo 16"
        );
        let delta0_unnormalized = (Pow::pow(&b0, 4usize) - Pow::pow(&a0, 4usize))
            * &u0_unnormalized
            - &d0 * &b0 * &coeff_geom;
        let rem_delta0_unnorm = ((&delta0_unnormalized % &a0_sq) + &a0_sq) % &a0_sq;
        assert_eq!(
            rem_delta0_unnorm,
            BigInt::from(134u32),
            "at K={k_bits}, unnormalized Delta_0 must fail divisibility by a_0^2 = 256"
        );

        // B. Repaired definition: u_0 = 27*(11*x_K + 23)/4 = (297*x_K + 621)/4 with D_0 = 11.
        let u0_repaired = &b0 * &u0_unnormalized;
        assert_eq!(
            &u0_repaired % &a0,
            BigInt::from(11u32),
            "at K={k_bits}, repaired u0 must equal 11 == D0 * preS(16, 27, 1) (mod 16)"
        );

        // Verify the exact algebraic identity:
        // b_0^(L-1) * u_0 - D_0 * preS(a_0, b_0, L) == a_0^L * (11 * T^(4L)(x_K) + 23) / 4
        // for every 1 <= L <= K/4 - 1.
        let max_l0 = k_bits / 4 - 1;
        for l in 1..=max_l0 {
            let lhs =
                Pow::pow(&b0, l - 1) * &u0_repaired - &d0 * independent_pre_s(&w, &a0, &b0, l);
            let (_, y_l_uint) = independent_direct_orbit(&x_k_uint, 4 * l);
            let y_l = BigInt::from(y_l_uint);
            let q_l = (BigInt::from(11u32) * y_l + BigInt::from(23u32)) / 4;
            let a0_pow_l = Pow::pow(&a0, l);
            assert_eq!(
                lhs,
                &a0_pow_l * &q_l,
                "at K={k_bits}, L={l}: exact identity b_0^(L-1)*u_0 - D_0*preS == a_0^L * q_L failed"
            );
            assert_eq!(&lhs % &a0_pow_l, BigInt::zero());
        }

        // C. Transport to level 1 on every checkpoint seed x_K (K in 16..=1024):
        let (a1, b1, u1, d1) = repaired_tower_step(&a0, &b0, &u0_repaired, &d0)
            .expect("repaired step 0->1 must succeed");
        assert_eq!(d1, BigInt::from(56_374_505u64));
        assert_eq!(&d1 % 2, BigInt::one());
        let max_l1 = max_l0 / 4;
        for l in 1..=max_l1 {
            let diff = Pow::pow(&b1, l - 1) * &u1 - &d1 * independent_pre_s(&w, &a1, &b1, l);
            assert_eq!(
                diff % Pow::pow(&a1, l),
                BigInt::zero(),
                "at K={k_bits}, level-1 congruence failed at L={l}"
            );
        }

        // D. Verify the corrected degree-4 linear form E_k = D_k*P_0(a_k, b_k) + u_k*P_1(a_k, b_k)
        //    and its exact 2-adic valuation v_2(E_k) = 56 * 4^k whenever the checkpoint precision
        //    reaches L >= 15 at level k.
        if max_l0 >= 15 {
            let e0 = degree4_linear_form(&a0, &b0, &u0_repaired, &d0);
            assert!(!e0.is_zero());
            assert_eq!(e0.magnitude().trailing_zeros(), Some(56));
        }
        if max_l1 >= 15 {
            let e1 = degree4_linear_form(&a1, &b1, &u1, &d1);
            assert!(!e1.is_zero());
            assert_eq!(e1.magnitude().trailing_zeros(), Some(224));
        }
        if k_bits == 1024 {
            let (a2, b2, u2, d2) =
                repaired_tower_step(&a1, &b1, &u1, &d1).expect("repaired step 1->2 must succeed");
            assert_eq!(&d2 % 2, BigInt::one());
            for l in 1..=15 {
                let diff = Pow::pow(&b2, l - 1) * &u2 - &d2 * independent_pre_s(&w, &a2, &b2, l);
                assert_eq!(
                    diff % Pow::pow(&a2, l),
                    BigInt::zero(),
                    "at K=1024, level-2 congruence failed at L={l}"
                );
            }
            let e2 = degree4_linear_form(&a2, &b2, &u2, &d2);
            assert!(!e2.is_zero());
            assert_eq!(e2.magnitude().trailing_zeros(), Some(896));
        }
    }
}

#[test]
fn negative_test_1_detects_perturbed_parity_block() {
    // Flip a single bit in a parity block (e.g., changing block 0 from 1110 to 1100
    // or flipping index 2 in w), and verify that both the word verifier and the
    // candidate integrity verifier reject it.
    let mut perturbed = mu_word_by_substitution(64);
    perturbed[2] = !perturbed[2];
    let err = verify_word_and_all_prefix_survival(&perturbed)
        .expect_err("perturbed parity block must be rejected by word/survival check");
    assert!(
        err.contains("disagree at index 2"),
        "unexpected error message: {err}"
    );

    // Also verify that if a block is perturbed to 1000 (crossing 3^1 < 2^4),
    // coefficient crossing is caught.
    let crossing_block = vec![true, false, false, false];
    let err_cross = verify_word_and_all_prefix_survival(&crossing_block)
        .expect_err("crossing block 1000 must be rejected");
    assert!(
        err_cross.contains("disagree") || err_cross.contains("crossing"),
        "unexpected error: {err_cross}"
    );

    // And if we feed a perturbed word into `verify_candidate_integrity` or
    // `verify_mahler_experiment`, it is immediately rejected.
    let w32 = mu_word_by_substitution(32);
    let (_, true_c) = independent_affine_offset(&w32);
    let inv3 = Pow::pow(&BigUint::from(3u32), 24usize)
        .modinv(&(BigUint::one() << 32))
        .unwrap();
    assert!(verify_candidate_integrity(&w32, &true_c, &inv3, false).is_ok());
    let mut bad_w32 = w32.clone();
    bad_w32[7] = !bad_w32[7];
    assert!(verify_candidate_integrity(&bad_w32, &true_c, &inv3, false).is_err());

    let outcome = run_mahler().unwrap();
    let mut perturbed_full = mu_word_by_substitution(DEFAULT_MAX_BITS);
    perturbed_full[15] = !perturbed_full[15];
    let err_integrity = verify_mahler_experiment(&perturbed_full, &outcome)
        .expect_err("candidate integrity verifier must reject a perturbed parity block");
    assert!(
        err_integrity.contains("disagree") || err_integrity.contains("mismatch"),
        "unexpected error: {err_integrity}"
    );
}

#[test]
fn negative_test_2_detects_wrong_parity_offset() {
    // 1. Direct candidate integrity check on a wrong affine offset `c + 1`.
    let w32 = mu_word_by_substitution(32);
    let (_, true_c) = independent_affine_offset(&w32);
    let inv3 = Pow::pow(&BigUint::from(3u32), 24usize)
        .modinv(&(BigUint::one() << 32))
        .unwrap();
    let wrong_c = &true_c + 1u32;
    let err_direct = verify_candidate_integrity(&w32, &wrong_c, &inv3, false)
        .expect_err("wrong parity offset c+1 must be rejected");
    assert!(
        err_direct.contains("wrong parity offset"),
        "unexpected error: {err_direct}"
    );

    // 2. Perturb the Mahler block-offset constant (e.g. using 21 instead
    // of 23 in c(mu(b)) = 23 - 4b, which shifts the residue by +2/11 mod 2^K),
    // and verify that `verify_mahler_experiment` rejects it.
    let w = mu_word_by_substitution(DEFAULT_MAX_BITS);
    let mut outcome = run_mahler().unwrap();
    let k = outcome.checkpoints[0].k_bits;
    let modulus = BigUint::one() << k;
    let inv11 = BigUint::from(11u32).modinv(&modulus).unwrap();
    let wrong_offset_shift = (BigUint::from(2u32) * inv11) % &modulus;
    outcome.checkpoints[0].residue_mahler_reduction =
        (&outcome.checkpoints[0].residue_mahler_reduction + wrong_offset_shift) % &modulus;

    let err = verify_mahler_experiment(&w, &outcome)
        .expect_err("wrong parity offset in Mahler reduction must be rejected");
    assert!(
        err.contains("Mahler residue mismatch"),
        "unexpected error: {err}"
    );

    // Also verify that if all four residue fields are shifted by a wrong affine offset
    // (c + 2), direct iteration / closed-form affine check catches it immediately.
    let mut outcome2 = run_mahler().unwrap();
    let wrong_res = (&outcome2.checkpoints[0].residue_affine_inverse + 1u32) % &modulus;
    outcome2.checkpoints[0].residue_affine_inverse = wrong_res.clone();
    outcome2.checkpoints[0].residue_cylinder_lift = wrong_res.clone();
    outcome2.checkpoints[0].residue_parity_positions = wrong_res.clone();
    outcome2.checkpoints[0].residue_mahler_reduction = wrong_res;
    let err2 = verify_mahler_experiment(&w, &outcome2)
        .expect_err("wrong affine offset shifted into all residues must be rejected");
    assert!(
        err2.contains("wrong affine residue") || err2.contains("direct iteration"),
        "unexpected error: {err2}"
    );
}

#[test]
fn negative_test_3_detects_incorrect_modular_inverse() {
    // 1. Direct candidate integrity check on a corrupted modular inverse of 3^(r_K).
    let w32 = mu_word_by_substitution(32);
    let (_, true_c) = independent_affine_offset(&w32);
    let inv3 = Pow::pow(&BigUint::from(3u32), 24usize)
        .modinv(&(BigUint::one() << 32))
        .unwrap();
    let bad_inv3 = &inv3 ^ (BigUint::one() << 31);
    let err_inv = verify_candidate_integrity(&w32, &true_c, &bad_inv3, false)
        .expect_err("corrupted modular inverse for 3^(r_K) must be rejected");
    assert!(
        err_inv.contains("incorrect modular inverse"),
        "unexpected error: {err_inv}"
    );

    // 2. Perturb the modular inverse in `residue_by_inverse` or `f2_mod_2k` (e.g.
    // flipping the top bit 2^(K-1) of the modular inverse result at K=64),
    // and verify that `verify_mahler_experiment` rejects it.
    let w = mu_word_by_substitution(DEFAULT_MAX_BITS);
    let mut outcome = run_mahler().unwrap();
    let k = outcome.checkpoints[2].k_bits; // K = 64
    outcome.checkpoints[2].residue_affine_inverse ^= BigUint::one() << (k - 1);

    let err = verify_mahler_experiment(&w, &outcome)
        .expect_err("incorrect modular inverse at K=64 must be rejected");
    assert!(
        err.contains("wrong affine residue"),
        "unexpected error: {err}"
    );

    // Also perturb the modular inverse used in `f2_mod_2k` and verify that the
    // Mahler congruence check catches it.
    let mut outcome_f2 = run_mahler().unwrap();
    outcome_f2.checkpoints[2].f2_mod_2k += BigUint::one();
    let err_f2 = verify_mahler_experiment(&w, &outcome_f2)
        .expect_err("incorrect F_2(16/27) modular evaluation must be rejected");
    assert!(
        err_f2.contains("wrong F_2(16/27) mod 2^K"),
        "unexpected error: {err_f2}"
    );
}

#[test]
fn negative_test_4_detects_falsely_inferred_infinite_theorem_from_finite_checks() {
    let w32 = mu_word_by_substitution(32);
    let (_, true_c) = independent_affine_offset(&w32);
    let inv3 = Pow::pow(&BigUint::from(3u32), 24usize)
        .modinv(&(BigUint::one() << 32))
        .unwrap();
    let err_direct = verify_candidate_integrity(&w32, &true_c, &inv3, true)
        .expect_err("claiming an infinite orbit from finite checks must be rejected");
    assert!(
        err_direct.contains("invalid epistemic promotion"),
        "unexpected error: {err_direct}"
    );

    let w = mu_word_by_substitution(DEFAULT_MAX_BITS);

    // Part A: Promoting finite checkpoint verification to `ProvenByAlgebra` is rejected.
    let mut outcome_a = run_mahler().unwrap();
    outcome_a.finite_checkpoints_status = Status::ProvenByAlgebra;
    let err_a = verify_mahler_experiment(&w, &outcome_a)
        .expect_err("promoting finite checkpoints to ProvenByAlgebra must be rejected");
    assert!(
        err_a.contains("falsely promotes finite checks to an infinite theorem"),
        "unexpected error: {err_a}"
    );

    // Part B: Promoting the open shift/divergent-orbit conjecture to `ProvenByAlgebra`
    // or `VerifiedForFiniteDomain` is rejected.
    let mut outcome_b = run_mahler().unwrap();
    outcome_b.shift_and_general_divergent_status = Status::ProvenByAlgebra;
    let err_b = verify_mahler_experiment(&w, &outcome_b)
        .expect_err("promoting open shift/divergent conjecture must be rejected");
    assert!(
        err_b.contains("falsely claims resolution of open shift/divergent-orbit obligations"),
        "unexpected error: {err_b}"
    );

    // Part C: Claiming that the uncancelled polynomial Mahler tower keeps D_k odd
    // (`ProvenByAlgebra`) is rejected because v_2(D_1) = 8.
    let mut outcome_c = run_mahler().unwrap();
    outcome_c.uncancelled_tower_status = Status::ProvenByAlgebra;
    let err_c = verify_mahler_experiment(&w, &outcome_c)
        .expect_err("claiming uncancelled Odd D_k holds must be rejected");
    assert!(
        err_c.contains("uncancelled polynomial denominator tower"),
        "unexpected error: {err_c}"
    );

    // Part D: Mathematical witness via `(1110)^infinity`:
    // Even though at every tested K in {16..1024} there is a positive integer n_K >= 2
    // matching K steps of `(1110)^infinity` with T^K(n_K) > n_K, inferring that n_K
    // continues to follow `(1110)^infinity` for all k >= K is false at every K.
    let outcome = run_mahler().unwrap();
    for row in &outcome.periodic_control {
        let k = row.k_bits;
        let div_step = row.first_divergence_step;
        let (emitted, _) = independent_direct_orbit(&row.positive_seed, div_step + 1);
        assert_eq!(
            emitted[div_step],
            (div_step & 3) == 3,
            "at K={k}, positive representative n_K must diverge from (1110)^infinity at step {div_step}"
        );
    }
}

#[test]
fn cli_reproduces_committed_mahler_evidence_and_summary() {
    let base = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
    for name in ["mahler-a", "mahler-b"] {
        let dir = base.join(name);
        let output = Command::new(env!("CARGO_BIN_EXE_collatz-lab"))
            .args(["mahler", "--out-dir"])
            .arg(&dir)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            fs::read_to_string(dir.join("evidence.json")).unwrap(),
            include_str!("../research/mahler/evidence.json")
        );
        assert_eq!(
            fs::read_to_string(dir.join("summary.md")).unwrap(),
            include_str!("../research/mahler/summary.md")
        );
    }
}

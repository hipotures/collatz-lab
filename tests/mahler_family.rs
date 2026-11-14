//! Phase 5 (issue #10): exact finite certificates for the uniform morphism family
//!
//! ```text
//! mu_L(1) = 1^(L-1) 0,   mu_L(0) = 1^(L-2) 0 1,   w_L = lim mu_L^j(1),   L >= 4,
//! ```
//!
//! with the first new case `L = 5` (`mu_5(1) = 11110`, `mu_5(0) = 11101`,
//! `A = 32`, `B = 81`) written out explicitly.
//!
//! These tests are finite sanity checks of the identities used in
//! `research/mahler-generalization.md`. They recompute everything from the
//! definitions and prove nothing about any infinite statement; the all-`L`
//! theorem there is established by algebra, not by this file.

use collatz_lab::collatz::t_step;
use collatz_lab::mahler::{
    homogenised_prefix_sum, inverse_parity_preimage, mu_word_by_substitution,
    residue_by_parity_positions,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Pow, Signed, Zero};

fn mu_block(l: usize, bit: bool) -> Vec<bool> {
    let mut block = vec![true; l];
    if bit {
        block[l - 1] = false;
    } else {
        block[l - 2] = false;
    }
    block
}

/// `w_L` by literally iterating the substitution from the letter `1`.
fn family_word(l: usize, len: usize) -> Vec<bool> {
    let mut word = vec![true];
    while word.len() < len {
        word = word.iter().flat_map(|&bit| mu_block(l, bit)).collect();
    }
    word.truncate(len);
    word
}

/// `w_L` from the base-`L` symbol recurrence only.
fn family_word_by_recurrence(l: usize, len: usize) -> Vec<bool> {
    let mut word = vec![false; len];
    for i in 0..len {
        let (n, j) = (i / l, i % l);
        word[i] = if j + 3 <= l {
            true
        } else if j + 2 == l {
            word[n]
        } else {
            !word[n]
        };
    }
    word
}

fn big(value: u64) -> BigUint {
    BigUint::from(value)
}

fn pow_u(base: u64, exp: usize) -> BigUint {
    pow_big(&big(base), exp)
}

fn pow_mod(base: &BigUint, exp: usize, modulus: &BigUint) -> BigUint {
    base.modpow(&BigUint::from(exp), modulus)
}

fn inverse(value: &BigUint, modulus: &BigUint) -> BigUint {
    (value % modulus)
        .modinv(modulus)
        .expect("odd values are invertible modulo a power of two")
}

fn v2(value: &BigUint) -> u64 {
    value
        .trailing_zeros()
        .expect("valuation of zero is undefined")
}

/// `(x - y) mod modulus` for residues `x, y < modulus`.
fn sub_mod(x: &BigUint, y: &BigUint, modulus: &BigUint) -> BigUint {
    ((x % modulus) + modulus - (y % modulus)) % modulus
}

/// `F(z) = sum_n w(n) z^n` modulo a power of two, for even `z`.
fn series_value(word: &[bool], z: &BigUint, modulus: &BigUint) -> BigUint {
    let mut total = BigUint::zero();
    let mut z_pow = BigUint::one();
    for &bit in word {
        if z_pow.is_zero() {
            return total;
        }
        if bit {
            total = (total + &z_pow) % modulus;
        }
        z_pow = z_pow * z % modulus;
    }
    panic!("word too short for the requested 2-adic precision");
}

/// Offset `c(v)` of the affine map `T^|v|(y) = (3^r y + c(v)) / 2^|v|`.
fn block_offset(block: &[bool]) -> BigUint {
    let mut c = BigUint::zero();
    for (pos, &bit) in block.iter().enumerate() {
        if bit {
            c = c * 3u32 + (BigUint::one() << pos);
        }
    }
    c
}

/// `sum_j block[j] a^j b^(deg - j)` for a 0/1 coefficient vector.
fn homogenise(block: &[bool], a: &BigUint, b: &BigUint, deg: usize) -> BigUint {
    let mut total = BigUint::zero();
    for (j, &bit) in block.iter().enumerate() {
        if bit {
            total += pow_big(a, j) * pow_big(b, deg - j);
        }
    }
    total
}

fn pow_big(base: &BigUint, exp: usize) -> BigUint {
    Pow::pow(base, exp)
}

struct Level {
    valuation: u64,
    d_is_odd: bool,
}

/// Runs `levels` steps of the cancelled backward tower for `w_L` on the 2-adic
/// value `f_k = F(a_k / b_k)` (hypothetical denominator `q = 1`), checking every
/// identity of the proof modulo `2^bits`.
fn check_family_tower(l: usize, levels: usize) -> Vec<Level> {
    let order = l * l - 2;
    let bits = order * l.pow(levels as u32) + 8 * l + 64;
    let modulus = BigUint::one() << bits;
    let word = family_word(l, bits + 2 * l);
    let mu0 = mu_block(l, false);
    let mu1 = mu_block(l, true);

    let mut a = pow_u(2, l);
    let mut b = pow_u(3, l - 1);
    let mut d = &b - &a; // D_0 = (B - A) q with q = 1
    let mut out = Vec::new();
    for _ in 0..levels {
        let z = &a * inverse(&b, &modulus) % &modulus;
        let z_l = pow_mod(&z, l, &modulus);
        let f = series_value(&word, &z, &modulus);
        let f_next = series_value(&word, &z_l, &modulus);
        let one_minus_zl = sub_mod(&BigUint::one(), &z_l, &modulus);

        // Mahler equation (1 - z^L) F(z) = C(z) + z^(L-2) (1 - z) (1 - z^L) F(z^L).
        let c_z = (0..l)
            .filter(|&j| mu0[j])
            .fold(BigUint::zero(), |acc, j| acc + pow_mod(&z, j, &modulus));
        let multiplier = pow_mod(&z, l - 2, &modulus) * sub_mod(&BigUint::one(), &z, &modulus);
        let lhs = &one_minus_zl * &f % &modulus;
        let rhs = (c_z + multiplier * &one_minus_zl % &modulus * &f_next) % &modulus;
        assert_eq!(lhs, rhs, "Mahler equation fails for L = {l}");

        // Tower step a^(L-2) u_{k+1} = b^(L-1) Delta_k, with u_k = D_k f_k.
        let u = &d * &f % &modulus;
        let bl_minus_al = pow_big(&b, l) - pow_big(&a, l);
        let c_h = homogenise(&mu0, &a, &b, l - 1);
        let d_next = &d * (&b - &a) * &bl_minus_al;
        let u_next = &d_next * &f_next % &modulus;
        let delta = sub_mod(&(&bl_minus_al * &u), &(&d * &b * &c_h), &modulus);
        assert_eq!(
            pow_big(&a, l - 2) * &u_next % &modulus,
            pow_big(&b, l - 1) * &delta % &modulus,
            "tower step fails for L = {l}"
        );
        assert!(v2(&delta) >= (l as u64 - 2) * v2(&a));

        // Linear form E_k = D_k P_0(a, b) + u_k P_1(a, b) = D_k b^L R(a / b).
        let p0 = &b * homogenise(&mu1, &a, &b, l - 1);
        let e = sub_mod(&(&d * &p0), &(&bl_minus_al * &u), &modulus);
        let p0_z = (0..l - 1).fold(BigUint::zero(), |acc, j| acc + pow_mod(&z, j, &modulus));
        let r_z = sub_mod(&p0_z, &(&one_minus_zl * &f), &modulus);
        assert_eq!(
            e,
            &d * pow_mod(&b, l, &modulus) % &modulus * &r_z % &modulus
        );
        out.push(Level {
            valuation: v2(&e),
            d_is_odd: d.bit(0),
        });

        a = pow_big(&a, l);
        b = pow_big(&b, l);
        d = d_next;
    }
    out
}

#[test]
fn family_word_matches_recurrence_and_the_phase3_word() {
    for l in 4..=9 {
        let word = family_word(l, 3000);
        assert_eq!(word, family_word_by_recurrence(l, 3000), "L = {l}");
        assert!(word[..l - 1].iter().all(|&bit| bit) && !word[l - 1]);
    }
    assert_eq!(family_word(4, 3000), mu_word_by_substitution(3000));
    let prefix: String = family_word(5, 30)
        .iter()
        .map(|&bit| if bit { '1' } else { '0' })
        .collect();
    assert_eq!(prefix, "111101111011110111101110111110");
}

#[test]
fn family_prefixes_never_cross_the_coefficient_threshold() {
    for l in 4..=9 {
        let word = family_word(l, 2000);
        let (mut pow3, mut pow2) = (BigUint::one(), BigUint::one());
        for (k, &bit) in word.iter().enumerate() {
            pow2 *= 2u32;
            if bit {
                pow3 *= 3u32;
            }
            assert!(pow3 > pow2, "L = {l}, prefix length {}", k + 1);
        }
    }
    // L = 3 is excluded for a reason: the prefix `11011010` of its word crosses.
    let (mu0, mu1) = (vec![true, false, true], vec![true, true, false]);
    let mut word = vec![true];
    for _ in 0..3 {
        word = word
            .iter()
            .flat_map(|&bit| if bit { mu1.clone() } else { mu0.clone() })
            .collect();
    }
    let ones = word[..8].iter().filter(|&&bit| bit).count();
    assert!(pow_u(3, ones) < pow_u(2, 8));
}

#[test]
fn block_offsets_match_the_closed_forms() {
    for l in 4..=12 {
        let b = pow_u(3, l - 1);
        assert_eq!(block_offset(&mu_block(l, true)), &b - pow_u(2, l - 1));
        assert_eq!(block_offset(&mu_block(l, false)), &b - pow_u(2, l - 2));
    }
    assert_eq!(block_offset(&mu_block(5, true)), big(65));
    assert_eq!(block_offset(&mu_block(5, false)), big(73));
    assert_eq!(block_offset(&mu_block(4, true)), big(19));
    assert_eq!(block_offset(&mu_block(4, false)), big(23));
}

#[test]
fn seed_identity_agrees_with_parity_positions_and_direct_iteration() {
    for l in 4..=8 {
        let bits = 40 * l;
        let modulus = BigUint::one() << bits;
        let word = family_word(l, bits + 2 * l);
        let seed = residue_by_parity_positions(&word[..bits]);
        let a = pow_u(2, l);
        let b = pow_u(3, l - 1);
        let c0 = &b - pow_u(2, l - 2);
        let f0 = series_value(&word, &(&a * inverse(&b, &modulus) % &modulus), &modulus);
        // B ((B - A) x + c_0) = 2^(L-2) (B - A) F_2(A / B)  in Z_2.
        let lhs = &b * ((&b - &a) * &seed + &c0) % &modulus;
        let rhs = pow_u(2, l - 2) * (&b - &a) * &f0 % &modulus;
        assert_eq!(lhs, rhs, "seed identity fails for L = {l}");

        // A positive integer in the residue class follows the prefix and grows.
        let start = &seed + &modulus;
        let mut y = start.clone();
        for (j, &bit) in word[..bits].iter().enumerate() {
            assert_eq!(y.bit(0), bit, "L = {l}, step {j}");
            y = t_step(&y);
        }
        assert!(y > start);
    }
}

#[test]
fn l5_explicit_constants_and_periodic_control() {
    let bits = 640;
    let modulus = BigUint::one() << bits;
    let word = family_word(5, bits + 10);
    let seed = residue_by_parity_positions(&word[..bits]);
    let f0 = series_value(
        &word,
        &(big(32) * inverse(&big(81), &modulus) % &modulus),
        &modulus,
    );
    // x = -73/49 + (8/81) F_2(32/81)  <=>  81 (49 x + 73) = 392 F_2(32/81).
    assert_eq!(
        (big(3969) * &seed + big(5913)) % &modulus,
        big(392) * &f0 % &modulus
    );
    assert!(((big(49) * &seed + big(73)) % big(8)).is_zero());

    // Periodic control (11110)^infinity has the rational seed -65/49.
    let control = sub_mod(
        &BigUint::zero(),
        &(big(65) * inverse(&big(49), &modulus)),
        &modulus,
    );
    assert!(((big(49) * &control + big(65)) % &modulus).is_zero());
    let mut y = &control + &modulus;
    let mut first_divergence = None;
    for j in 0..bits + 10 {
        if y.bit(0) != (j % 5 != 4) {
            first_divergence = Some(j);
            break;
        }
        y = t_step(&y);
    }
    assert!(first_divergence.is_some_and(|j| j >= bits));
    // ... and it does not satisfy the identity of w_5 (first difference at bit 23).
    assert_ne!(control, seed);
    assert_eq!(
        control.clone() % (BigUint::one() << 23usize),
        &seed % (BigUint::one() << 23usize)
    );
    assert_ne!(
        control % (BigUint::one() << 24usize),
        seed % (BigUint::one() << 24usize)
    );
}

#[test]
fn periodic_approximant_has_order_l_squared_minus_two_with_unit_leading_coefficient() {
    for l in 4..=12 {
        let order = l * l - 2;
        let word = family_word(l, order + 4 * l);
        // R(t) = (1 + ... + t^(L-2)) - (1 - t^L) F(t).
        let coeff = |n: usize| -> i64 {
            let p0 = i64::from(n + 2 <= l);
            let shifted = if n >= l { i64::from(word[n - l]) } else { 0 };
            p0 - i64::from(word[n]) + shifted
        };
        assert!((0..order).all(|n| coeff(n) == 0), "L = {l}");
        assert_eq!(coeff(order), 1, "L = {l}");
    }
    // Negative control: the [1/1] pair (1, -1 + z) for L = 5 only reaches order 4.
    let word = family_word(5, 16);
    let coeff = |n: usize| -> i64 {
        let p0 = i64::from(n == 0);
        let shifted = if n >= 1 { i64::from(word[n - 1]) } else { 0 };
        p0 - i64::from(word[n]) + shifted
    };
    assert!((0..4).all(|n| coeff(n) == 0) && coeff(4) == 1);
}

#[test]
fn cancelled_tower_and_linear_form_valuations() {
    for (l, levels) in [(4usize, 3usize), (5, 3), (6, 2), (7, 2)] {
        let order = (l * l - 2) as u64;
        let result = check_family_tower(l, levels);
        for (k, level) in result.iter().enumerate() {
            assert!(level.d_is_odd, "L = {l}, level {k}");
            assert_eq!(level.valuation, order * (l as u64).pow(k as u32 + 1));
        }
    }
    let l5: Vec<u64> = check_family_tower(5, 3)
        .iter()
        .map(|x| x.valuation)
        .collect();
    assert_eq!(l5, vec![115, 575, 2875]);
    let l4: Vec<u64> = check_family_tower(4, 3)
        .iter()
        .map(|x| x.valuation)
        .collect();
    assert_eq!(l4, vec![56, 224, 896]); // the values recorded for Phase 3
}

#[test]
fn l5_level0_integer_congruence_uses_the_shared_prefix_sum() {
    // b^(n-1) u_0 = D_0 preS(a, b, n) (mod a^n) with a = 32, b = 81, D_0 = 49.
    let bits = 400;
    let modulus = BigUint::one() << bits;
    let word = family_word(5, bits + 10);
    let f0 = series_value(
        &word,
        &(big(32) * inverse(&big(81), &modulus) % &modulus),
        &modulus,
    );
    let u0 = BigInt::from(big(49) * &f0 % &modulus);
    let (a, b) = (BigInt::from(32), BigInt::from(81));
    let mut b_pow = BigInt::one();
    let mut a_pow = BigInt::one();
    for n in 1..=bits / 5 {
        a_pow *= &a;
        let pre = homogenised_prefix_sum(&word, &a, &b, n);
        let diff: BigInt = &b_pow * &u0 - BigInt::from(49) * pre;
        assert!((diff % &a_pow).is_zero(), "n = {n}");
        b_pow *= &b;
    }
}

#[test]
fn uncancelled_denominator_loses_oddness_but_cancelled_one_keeps_it() {
    for l in 4..=9 {
        let a = pow_u(2, l);
        let b = pow_u(3, l - 1);
        let cancelled = (&b - &a) * (&b - &a) * (pow_big(&b, l) - pow_big(&a, l));
        let uncancelled = &cancelled * pow_big(&a, l - 2);
        assert!(cancelled.bit(0));
        assert_eq!(v2(&uncancelled), (l * (l - 2)) as u64);
    }
    assert_eq!(v2(&(pow_u(32, 3) * big(49))), 15);
}

#[test]
fn height_ledger_closes_on_the_tested_range_only() {
    // Finite illustration of 2^(L (L^2 - 2)) > 3^(L^2 + L - 1); the proof for
    // every L >= 4 is the algebraic inequality 5 L^3 - 8 L^2 - 18 L + 8 > 0.
    for l in 4usize..=64 {
        let gain = l * (l * l - 2);
        let cost = l * l + l - 1;
        assert!(pow_u(2, gain) > pow_u(3, cost), "L = {l}");
        assert!(5 * gain > 8 * cost);
        assert_eq!(5 * gain - 8 * cost, 5 * l * l * l - 8 * l * l - 18 * l + 8);
    }
    assert!(pow_u(3, 5) < pow_u(2, 8));
    assert!(pow_u(2, 115) > pow_u(2, 69) * pow_u(3, 29));
    // The naive [1/1] ledger for L = 5 does not close.
    assert!(pow_u(2, 20) < pow_u(3, 13));
}

#[test]
fn inverse_branches_prepend_a_prefix_of_w5_to_a_rational_seed() {
    // If p/q realised the tail sigma^t(w_5), the preimage would realise w_5 on
    // its first t symbols: check the forward orbit of the preimage exactly.
    let word = family_word(5, 64);
    for t in [1usize, 4, 5, 23, 24, 40] {
        let (p, q) = (BigInt::from(-7), BigInt::from(5));
        let (num, den) = inverse_parity_preimage(&p, &q, &word[..t]);
        assert!(den.is_positive() && (&den % BigInt::from(2)).is_one());
        let mut current = num;
        for &bit in &word[..t] {
            let odd = !(&current % BigInt::from(2)).is_zero();
            assert_eq!(odd, bit);
            current = if odd {
                (BigInt::from(3) * &current + &den) / BigInt::from(2)
            } else {
                &current / BigInt::from(2)
            };
        }
        // current / den == p / q
        assert_eq!(&current * &q, &p * &den);
    }
}

#[test]
fn wrong_constants_are_rejected() {
    // Adversarial controls: each deliberately wrong ingredient must break a check.
    let bits = 200;
    let modulus = BigUint::one() << bits;
    let word = family_word(5, bits + 10);
    let seed = residue_by_parity_positions(&word[..bits]);
    let f0 = series_value(
        &word,
        &(big(32) * inverse(&big(81), &modulus) % &modulus),
        &modulus,
    );
    // c_1 = 65 in place of c_0 = 73.
    assert_ne!(
        big(81) * (big(49) * &seed + big(65)) % &modulus,
        big(392) * &f0 % &modulus
    );
    // The unnormalised numerator (49 x + 73) / 8 is not 49 F_2: the factor 81 matters.
    assert_ne!(
        (big(49) * &seed + big(73)) % &modulus,
        big(392) * &f0 % &modulus
    );
    // The L = 4 word does not satisfy the L = 5 identity.
    let word4 = family_word(4, bits + 10);
    let seed4 = residue_by_parity_positions(&word4[..bits]);
    assert_ne!(
        big(81) * (big(49) * &seed4 + big(73)) % &modulus,
        big(392) * &f0 % &modulus
    );
}

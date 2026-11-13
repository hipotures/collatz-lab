//! Independent finite oracle: scan seed residues and iterate T directly,
//! without the library's prefix, cylinder, cover or Terras constructions.

use std::fs;
use std::process::Command;

use collatz_lab::envelope::{run_envelope, Witness};
use collatz_lab::hypothesis::Status;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde_json::{json, Value};

fn big(n: u64) -> BigUint {
    BigUint::from(n)
}

/// One period at the largest length contains the least member >= 2 of
/// every class in the domain. Include 2^20+1 to handle the residue of 1.
/// Even seeds have r=0 at their first crossing, so only odd seeds are needed.
fn families_by_direct_iteration() -> Vec<Vec<Witness>> {
    let powers: Vec<BigUint> = (0..=20).map(|r| big(3).pow(r)).collect();
    let mut families = vec![Vec::new(); 13];
    for n in (3u64..(1u64 << 20) + 2).step_by(2) {
        let (mut x, mut r) = (n, 0);
        let mut word = String::new();
        for k in 1..=20 {
            let odd = x % 2 == 1;
            word.push(if odd { '1' } else { '0' });
            x = if odd {
                r += 1;
                x.checked_mul(3).unwrap().checked_add(1).unwrap() / 2
            } else {
                x / 2
            };
            if (BigUint::one() << k) > powers[r] {
                // Only the first member >= 2 of this class is counted.
                if r <= 12 && n < (1u64 << k) + 2 {
                    // Recover c from the orbit endpoint, not an affine recursion.
                    let c = (big(x) << k) - &powers[r] * n;
                    families[r].push(Witness {
                        parity: word,
                        residue: big(n % (1u64 << k)),
                        m: big(n),
                        c,
                    });
                }
                break;
            }
        }
    }
    for family in &mut families {
        family.sort_by(|a, b| a.parity.cmp(&b.parity));
    }
    families
}

/// Independent rational serialization; do not use the experiment's Ratio.
fn fraction(numerator: BigUint, denominator: BigUint) -> Value {
    assert!(!denominator.is_zero());
    let (mut gcd, mut remainder) = (numerator.clone(), denominator.clone());
    while !remainder.is_zero() {
        (gcd, remainder) = (remainder.clone(), gcd % remainder);
    }
    json!({
        "numerator": (numerator / &gcd).to_string(),
        "denominator": (denominator / gcd).to_string(),
    })
}

#[test]
fn all_extrema_ties_counts_and_fractions_match_an_independent_residue_scan() {
    let outcome = run_envelope().unwrap();
    assert_eq!((outcome.min_r, outcome.max_r, outcome.max_k), (1, 12, 20));
    assert_eq!(outcome.rows.len(), 12);
    let families = families_by_direct_iteration();
    let mut first_counterexample = None;
    let mut total = 0;
    for (index, row) in outcome.rows.iter().enumerate() {
        assert_eq!(row.r, index + 1);
        let family = &families[row.r];
        let k = big(3).pow(row.r as u32).bits() as usize;
        assert_eq!(row.k, k);
        assert!(family.iter().all(|w| w.parity.len() == k));
        let count = BigUint::from(family.len());
        assert_eq!(row.family_count, count);
        assert_eq!(row.count_by_length, count);
        assert_eq!(row.count_by_odd_positions, count);
        total += family.len();
        let max_c = family.iter().map(|w| &w.c).max().unwrap();
        let min_m = family.iter().map(|w| &w.m).min().unwrap();
        let best = family
            .iter()
            .max_by(|a, b| (&a.c * &b.m).cmp(&(&b.c * &a.m)))
            .unwrap();
        assert_eq!(&row.max_c, max_c);
        assert_eq!(&row.terras_c, max_c);
        assert_eq!(&row.min_m, min_m);
        assert_eq!(
            row.max_c_witnesses,
            family
                .iter()
                .filter(|w| &w.c == max_c)
                .cloned()
                .collect::<Vec<_>>()
        );
        assert_eq!(
            row.min_m_witnesses,
            family
                .iter()
                .filter(|w| &w.m == min_m)
                .cloned()
                .collect::<Vec<_>>()
        );
        assert_eq!(
            row.max_ratio_witnesses,
            family
                .iter()
                .filter(|w| &w.c * &best.m == &best.c * &w.m)
                .cloned()
                .collect::<Vec<_>>()
        );
        assert!(row
            .max_c_witnesses
            .iter()
            .any(|w| w.parity == row.terras_word));
        let d = (BigUint::one() << k) - big(3).pow(row.r as u32);
        assert_eq!(row.d, d);
        assert_eq!(
            serde_json::to_value(&row.r_ratio).unwrap(),
            fraction(best.c.clone(), &d * &best.m)
        );
        assert_eq!(
            serde_json::to_value(&row.u_ratio).unwrap(),
            fraction(max_c.clone(), &d * min_m)
        );
        // d cancels in U/R; these cross products also check E >= 1 and E <= 2.
        let e_numerator = max_c * &best.m;
        let e_denominator = min_m * &best.c;
        assert!(e_numerator >= e_denominator);
        let e_le_two = e_numerator <= &e_denominator * 2u32;
        assert_eq!(row.e_le_two, Some(e_le_two));
        assert_eq!(
            serde_json::to_value(&row.e_ratio).unwrap(),
            fraction(e_numerator, e_denominator)
        );
        if !e_le_two && first_counterexample.is_none() {
            first_counterexample = Some(row.r);
        }
    }
    assert_eq!(total, 4403);
    assert_eq!(outcome.first_counterexample_r, first_counterexample);
    assert_eq!(
        outcome.e_le_two_status,
        if first_counterexample.is_some() {
            Status::Refuted
        } else {
            Status::VerifiedForFiniteDomain
        }
    );
}

#[test]
fn r6_keeps_the_p1a_refutation_and_r1_excludes_seed_one() {
    let outcome = run_envelope().unwrap();
    let first = &outcome.rows[0];
    assert_eq!(first.family_count, big(1));
    assert_eq!(
        first.min_m_witnesses,
        vec![Witness {
            parity: "10".into(),
            residue: big(1),
            m: big(5),
            c: big(1),
        }]
    );
    assert_eq!(first.r_ratio.to_string(), "1/5");
    let row = &outcome.rows[5];
    assert_eq!((row.r, row.k), (6, 10));
    assert_eq!(row.family_count, big(12));
    assert_eq!(row.d, big(295));
    assert_eq!(
        row.min_m_witnesses,
        vec![Witness {
            parity: "1111101000".into(),
            residue: big(287),
            m: big(287),
            c: big(697),
        }]
    );
    assert_eq!(
        row.max_ratio_witnesses,
        vec![Witness {
            parity: "1101110100".into(),
            residue: big(347),
            m: big(347),
            c: big(989),
        }]
    );
    assert_eq!(row.max_c, big(1085));
    assert_eq!(row.max_c_witnesses[0].m, big(507));
    let cross_difference = big(989) * big(295) * big(287) - big(697) * big(295) * big(347);
    assert_eq!(cross_difference, big(12_385_280));
    assert!(cross_difference > BigUint::zero());
    assert_eq!(row.r_ratio.to_string(), "989/102365");
}

#[test]
fn cli_reproduces_committed_evidence_and_report_and_has_fixed_bounds() {
    let base = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
    for name in ["envelope-a", "envelope-b"] {
        let dir = base.join(name);
        let output = Command::new(env!("CARGO_BIN_EXE_collatz-lab"))
            .args(["envelope", "--out-dir"])
            .arg(&dir)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            fs::read_to_string(dir.join("evidence.json")).unwrap(),
            include_str!("../research/envelope/evidence.json")
        );
        assert_eq!(
            fs::read_to_string(dir.join("summary.md")).unwrap(),
            include_str!("../research/envelope/summary.md")
        );
    }
    let output = Command::new(env!("CARGO_BIN_EXE_collatz-lab"))
        .args(["envelope", "--max-r", "13"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let output = Command::new(env!("CARGO_BIN_EXE_collatz-lab"))
        .args(["envelope", "--allow-large"])
        .output()
        .unwrap();
    assert!(!output.status.success());
}

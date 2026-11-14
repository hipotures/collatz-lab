//! Independent finite verification of Phase 7 certificates; no infinite theorem here.
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use serde_json::Value;

fn evidence() -> Value {
    serde_json::from_str(include_str!("../research/mahler-uncovered/evidence.json")).unwrap()
}

// Digit recurrences, independent of the producer's literal substitution.
fn symbol(name: &str, n: usize) -> i64 {
    if n == 0 {
        return 1;
    }
    if name == "thue-morse" {
        1 - i64::from(n.count_ones() % 2)
    } else {
        match n % 3 {
            0 => symbol(name, n / 3),
            1 => 1 - symbol(name, n / 3),
            _ => 1,
        }
    }
}

fn coefficients(row: &Value, key: &str) -> Vec<BigInt> {
    row[key]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| BigInt::from(a.as_i64().unwrap()))
        .collect()
}

fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
    while !b.is_zero() {
        (a, b) = (b.clone(), a % b);
    }
    a.abs()
}

#[test]
fn every_pade_pair_has_the_claimed_exact_order_content_and_ledger() {
    let data = evidence();
    assert_eq!(data["max_search_degree"], 24);
    let mut checked = 0;
    for target in data["targets"].as_array().unwrap() {
        let name = target["name"].as_str().unwrap();
        let l = target["L"].as_u64().unwrap() as u32;
        let e = target["e"].as_u64().unwrap() as u32;
        let m = target["A"]
            .as_u64()
            .unwrap()
            .max(target["B"].as_u64().unwrap());
        for row in target["pade"].as_array().unwrap() {
            let p0 = coefficients(row, "p0");
            let p1 = coefficients(row, "p1");
            let order = row["order"].as_u64().unwrap() as usize;
            assert_eq!(
                p0.iter()
                    .chain(&p1)
                    .fold(BigInt::zero(), |a, b| gcd(a, b.clone())),
                BigInt::one()
            );
            for n in 0..512 {
                let coeff = p0.get(n).cloned().unwrap_or_default()
                    + p1.iter()
                        .take(n + 1)
                        .enumerate()
                        .map(|(j, a)| a * symbol(name, n - j))
                        .sum::<BigInt>();
                if n < order {
                    assert!(coeff.is_zero(), "{name}, n={n}, row={row}");
                } else if n == order {
                    assert_eq!(
                        coeff,
                        BigInt::from(row["leading_coefficient"].as_i64().unwrap())
                    );
                    assert_eq!(
                        coeff.abs().to_biguint().unwrap().trailing_zeros().unwrap(),
                        row["v2_leading"].as_u64().unwrap()
                    );
                }
            }
            let degree = (p0.len().max(p1.len()) - 1) as u32;
            let gain = l * (l - 1) * order as u32;
            let cost = (l - 1) * degree + l + e;
            assert_eq!(degree as u64, row["degree"].as_u64().unwrap());
            assert_eq!(gain as u64, row["gain_exp2"].as_u64().unwrap());
            assert_eq!(cost as u64, row["cost_exp_m"].as_u64().unwrap());
            assert_eq!(
                BigUint::from(2u32).pow(gain) > BigUint::from(m).pow(cost),
                row["ledger_closes"].as_bool().unwrap()
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 48);
}

fn series(name: &str, z: &BigInt, modulus: &BigInt) -> BigInt {
    let (mut f, mut power) = (BigInt::zero(), BigInt::one());
    for n in 0..1024 {
        if power.is_zero() {
            return f;
        }
        f = (f + &power * symbol(name, n)) % modulus;
        power = power * z % modulus;
    }
    panic!("insufficient precision");
}

#[test]
fn both_seed_identities_agree_with_actual_collatz_iteration() {
    let data = evidence();
    for target in data["targets"].as_array().unwrap() {
        let name = target["name"].as_str().unwrap();
        let a = BigInt::from(target["A"].as_u64().unwrap());
        let b = BigInt::from(target["B"].as_u64().unwrap());
        let c0 = BigInt::from(target["c0"].as_u64().unwrap());
        let c1 = BigInt::from(target["c1"].as_u64().unwrap());
        for cp in target["checkpoints"].as_array().unwrap() {
            let bits = cp["bits"].as_u64().unwrap() as usize;
            let modulus = BigInt::one() << bits;
            let seed: BigInt = cp["seed"].as_str().unwrap().parse().unwrap();
            let z = &a * b.modinv(&modulus).unwrap() % &modulus;
            let f = series(name, &z, &modulus);
            assert_eq!(
                (&b * ((&b - &a) * &seed + &c0) - (&b - &a) * (&c0 - &c1) * f) % &modulus,
                BigInt::zero()
            );
            let mut y = seed;
            for n in 0..bits {
                assert_eq!(&y % 2, BigInt::from(symbol(name, n)));
                y = if (&y % 2u32).is_zero() {
                    y / 2
                } else {
                    (3 * y + 1) / 2
                };
            }
            assert_eq!(
                y,
                cp["terminal_numerator"]
                    .as_str()
                    .unwrap()
                    .parse::<BigInt>()
                    .unwrap()
            );
        }
    }
}

fn homogenise(coeffs: &[BigInt], a: &BigInt, b: &BigInt, degree: usize) -> BigInt {
    coeffs
        .iter()
        .enumerate()
        .map(|(j, c)| c * a.pow(j as u32) * b.pow((degree - j) as u32))
        .sum()
}

#[test]
fn improved_unit_leading_pairs_have_exact_valuations_at_three_levels() {
    let data = evidence();
    let modulus = BigInt::one() << 512;
    for target in data["targets"].as_array().unwrap() {
        let name = target["name"].as_str().unwrap();
        let l = target["L"].as_u64().unwrap() as u32;
        let mut a = BigInt::from(target["A"].as_u64().unwrap());
        let mut b = BigInt::from(target["B"].as_u64().unwrap());
        let c0 = BigInt::from(target["c0"].as_u64().unwrap());
        let c1 = BigInt::from(target["c1"].as_u64().unwrap());
        let mut d = (&b - &a).abs() * (c0 - c1).abs(); // s=0 in both targets
        let index = if name == "thue-morse" { 2 } else { 1 };
        let row = &target["pade"][index];
        let p0 = coefficients(row, "p0");
        let p1 = coefficients(row, "p1");
        let degree = row["degree"].as_u64().unwrap() as usize;
        let order = row["order"].as_u64().unwrap();
        for k in 0..3 {
            let z = &a * b.modinv(&modulus).unwrap() % &modulus;
            let u = &d * series(name, &z, &modulus) % &modulus;
            let form = (&d * homogenise(&p0, &a, &b, degree) + u * homogenise(&p1, &a, &b, degree))
                % &modulus;
            assert_eq!(&d % 2u32, BigInt::one());
            assert_eq!(
                form.abs().to_biguint().unwrap().trailing_zeros(),
                Some(order * (l as u64).pow(k + 1))
            );
            d = d * (&b - &a).abs() * (b.pow(l) - a.pow(l)).abs();
            (a, b) = (a.pow(l), b.pow(l));
        }
    }
}

fn morphism_symbol(l: u32, zero: u64, one: u64, n: u32) -> u64 {
    if n == 0 {
        return 1;
    }
    let mask = if morphism_symbol(l, zero, one, n / l) == 1 {
        one
    } else {
        zero
    };
    (mask >> (n % l)) & 1
}

#[test]
fn periodic_catalogue_is_complete_and_every_finite_control_closes_its_ledger() {
    use std::collections::BTreeSet;
    let data = evidence();
    let mut expected = BTreeSet::new();
    for l in 2..=5 {
        for one in 0u64..(1 << l) {
            if one & 1 == 0 {
                continue;
            }
            for zero in 0u64..(1 << l) {
                if zero != one && zero.count_ones() == one.count_ones() {
                    expected.insert((l, zero, one));
                }
            }
        }
    }
    let mut actual = BTreeSet::new();
    let mut old_passes = 0;
    let mut max_period = 0;
    for row in data["small_catalogue"].as_array().unwrap() {
        let l = row["L"].as_u64().unwrap() as u32;
        let zero = row["zero_mask"].as_u64().unwrap();
        let one = row["one_mask"].as_u64().unwrap();
        let period = row["period"].as_u64().unwrap() as u32;
        let control = row["control_mask"].as_u64().unwrap();
        let order = row["order"].as_u64().unwrap() as u32;
        assert!(actual.insert((l, zero, one)), "duplicate catalogue row");
        assert!((1..=24).contains(&period) && period <= order);
        assert!(control < 1 << period);
        for n in 0..order {
            assert_eq!(
                morphism_symbol(l, zero, one, n),
                (control >> (n % period)) & 1
            );
        }
        assert_ne!(
            morphism_symbol(l, zero, one, order),
            (control >> (order % period)) & 1
        );
        let s = (0..l).find(|&j| (zero >> j) & 1 != (one >> j) & 1).unwrap();
        let e = (0..l)
            .rfind(|&j| (zero >> j) & 1 != (one >> j) & 1)
            .unwrap();
        let t = (0..l).find(|&j| (one >> j) & 1 == 0).unwrap();
        let m = BigUint::from(2u32)
            .pow(l)
            .max(BigUint::from(3u32).pow(one.count_ones()));
        assert_eq!(s as u64, row["first_difference"].as_u64().unwrap());
        assert!(BigUint::from(2u32).pow(l * (l - 1) * order) > m.pow(period * (l - 1) + l + e));
        let old = BigUint::from(2u32).pow(l * (l - 1) * (l * t + s)) > m.pow(l * l + e);
        assert_eq!(old, row["original_criterion"].as_bool().unwrap());
        old_passes += usize::from(old);
        max_period = max_period.max(period);
    }
    assert_eq!(expected, actual);
    assert_eq!(actual.len(), 144);
    assert_eq!(old_passes, 65);
    assert_eq!(max_period, 15);
}

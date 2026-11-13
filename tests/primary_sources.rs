//! Bounded reproductions for the primary-source audit in research/literature-cst.md.
//! The algorithms below are independent of the cylinder/cover implementation.

use collatz_lab::collatz::stopping_time;
use num_bigint::BigUint;
use num_traits::{One, Zero};

// Terras, Theorem 2.4 (p. 249): the slowest admissible odd-count sequence.
// At a possible crossing length k, replace its final bit with zero to get
// the unique maximal-remainder word (Theorem 2.6, p. 250).
fn terras_envelopes(limit: usize) -> Vec<Option<(BigUint, BigUint)>> {
    let mut power = BigUint::one();
    let mut offset = BigUint::zero();
    let mut rows = Vec::new();
    for position in 0..limit {
        let denominator = BigUint::one() << (position + 1);
        let choose_odd = power < denominator;
        rows.push(choose_odd.then(|| (offset.clone(), &denominator - &power)));
        if choose_odd {
            offset = offset * 3u32 + (BigUint::one() << position);
            power *= 3u32;
        }
    }
    rows
}

#[test]
fn terras_maximal_remainders_match_all_words_through_length_14() {
    for (index, envelope) in terras_envelopes(14).iter().enumerate() {
        let k = index + 1;
        let mut offsets = Vec::new();
        for word in 0u64..1 << k {
            let (mut power, mut offset) = (1u64, 0u64);
            for j in 0..k {
                if (word >> j) & 1 == 1 {
                    power *= 3;
                    offset = 3 * offset + (1 << j);
                }
                if power < 1 << (j + 1) {
                    if j + 1 == k {
                        offsets.push(offset);
                    }
                    break;
                }
            }
        }
        match envelope {
            None => assert!(offsets.is_empty(), "length {k}"),
            Some((maximum, _)) => {
                let found = offsets.iter().max().unwrap();
                assert_eq!(&BigUint::from(*found), maximum, "length {k}");
                assert_eq!(offsets.iter().filter(|c| *c == found).count(), 1);
            }
        }
    }
}

#[test]
fn terras_2592_cutoff_has_a_small_exact_exception_bound() {
    // Corollary 2.8 and the argument on p. 252: all potentially exceptional
    // members at tau <= 2592 are <= 250000. Use exact integers, not rounded
    // Table C decimals. The next jump is at 2593, outside this assertion.
    let rows = terras_envelopes(2593);
    let maximum_floor = rows[..2592]
        .iter()
        .flatten()
        .map(|(c, d)| c / d)
        .max()
        .unwrap();
    assert_eq!(maximum_floor, BigUint::from(238_670u32));
    assert!(maximum_floor < BigUint::from(250_000u32));
    let (c, d) = rows[2592].as_ref().unwrap();
    assert_eq!(c / d, BigUint::from(420_841u32));

    // Independently check the remaining finite range by direct iteration.
    // u64 orbit operations are checked; coefficient comparisons use BigUint.
    for n in 2u64..=250_000 {
        let (mut x, mut power, mut denominator) = (n, BigUint::one(), BigUint::one());
        let mut descended = false;
        for _ in 1..=135 {
            if x.is_multiple_of(2) {
                x /= 2;
            } else {
                x = x.checked_mul(3).unwrap().checked_add(1).unwrap() / 2;
                power *= 3u32;
            }
            denominator <<= 1usize;
            assert_eq!(x < n, power < denominator, "seed {n}");
            if x < n {
                descended = true;
                break;
            }
        }
        assert!(descended, "no descent in the stated bound for {n}");
    }
}

#[test]
fn garner_times_convert_using_the_number_of_odd_steps() {
    // Garner p. 20, first three examples. His ordinary-map times include
    // one extra step for every odd step of the accelerated map.
    for (n, accelerated, odd, ordinary) in [
        (27u64, 59, 37, 96),
        (703, 81, 51, 132),
        (35_655, 135, 85, 220),
    ] {
        let (mut x, mut odd_count) = (n, 0);
        for _ in 0..accelerated {
            if x.is_multiple_of(2) {
                x /= 2;
            } else {
                x = x.checked_mul(3).unwrap().checked_add(1).unwrap() / 2;
                odd_count += 1;
            }
        }
        assert_eq!(odd_count, odd);
        assert_eq!(accelerated + odd_count, ordinary);
        assert_eq!(stopping_time(&BigUint::from(n), 200), Some(accelerated));
        let mut y = n;
        for j in 1..=ordinary {
            y = if y.is_multiple_of(2) {
                y / 2
            } else {
                y.checked_mul(3).unwrap().checked_add(1).unwrap()
            };
            assert_eq!(y < n, j == ordinary);
        }
        assert_eq!(x, y);
    }
}

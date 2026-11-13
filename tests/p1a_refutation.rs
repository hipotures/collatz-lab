//! Regression test for the refutation of slack hypothesis P1a
//! (`research/phase1-next-questions.md`, issue #4).
//!
//! P1a claimed: among the first coefficient crossings with `r` odd steps, the
//! exact ratio `rho(p) = c / ((2^k - 3^r) * m)` is largest on the cylinder
//! with the smallest member `m >= 2`. It is false at `r = 6` (`k = 10`,
//! `d = 2^10 - 3^6 = 295`): the least member overall is 287, but the largest
//! ratio belongs to the cylinder whose least member is 347.
//!
//! The helpers below use plain `u64` arithmetic and direct iteration and do
//! not call the library; the library is consulted only as a cross-check.
//! This is a statement about twelve words. It says nothing about P1b and
//! nothing about the Coefficient Stopping Time conjecture.

use collatz_lab::collatz::{parity_vector, stopping_time};
use collatz_lab::prefix::{closed_form_offset, Cylinder, ParityPrefix};
use num_bigint::BigUint;

const LENGTH: usize = 10;
const ODD_STEPS: usize = 6;
const GAP: u64 = 295;

/// The cylinder with the least member of the whole `r = 6` family.
const LEAST: (&str, u64, u64) = ("1111101000", 287, 697);
/// A cylinder with a larger least member and a larger ratio.
const LARGER_RATIO: (&str, u64, u64) = ("1101110100", 347, 989);

/// Every first crossing with six odd steps: (word, least member, offset).
const FAMILY: [(&str, u64, u64); 12] = [
    ("1111101000", 287, 697),
    ("1101110100", 347, 989),
    ("1111011000", 367, 745),
    ("1110110100", 423, 881),
    ("1101101100", 507, 1085),
    ("1111110000", 575, 665),
    ("1110101100", 583, 977),
    ("1111100100", 735, 761),
    ("1111010100", 815, 809),
    ("1101111000", 923, 925),
    ("1111001100", 975, 905),
    ("1110111000", 999, 817),
];

fn bits(word: &str) -> Vec<bool> {
    word.chars().map(|letter| letter == '1').collect()
}

// The odd branch is written as the map is defined, not as a ceiling.
#[allow(clippy::manual_div_ceil)]
fn step(n: u64) -> u64 {
    if n.is_multiple_of(2) {
        n / 2
    } else {
        (3 * n + 1) / 2
    }
}

/// Offset by the recursion: an odd step at position `i` maps `c` to
/// `3c + 2^i`, an even step keeps it.
fn offset(word: &[bool]) -> u64 {
    let mut c = 0u64;
    for (position, &odd) in word.iter().enumerate() {
        if odd {
            c = 3 * c + (1u64 << position);
        }
    }
    c
}

/// `2^j < 3^(r_j)` for `1 <= j < k` and `2^k > 3^(r_k)`.
fn is_first_crossing(word: &[bool]) -> bool {
    let mut power_of_three = 1u64;
    for (index, &odd) in word.iter().enumerate() {
        if odd {
            power_of_three *= 3;
        }
        let crossed = (1u64 << (index + 1)) > power_of_three;
        if index + 1 == word.len() {
            return crossed;
        }
        if crossed {
            return false;
        }
    }
    false
}

/// The least `n >= 2` whose first parities, by direct iteration, spell `word`.
fn least_member(word: &[bool]) -> u64 {
    (2u64..(1 << word.len()) + 2)
        .find(|&n| {
            let mut x = n;
            word.iter().all(|&odd| {
                let matches = (x % 2 == 1) == odd;
                x = step(x);
                matches
            })
        })
        .expect("every word has a member in one period")
}

#[test]
fn both_triples_hold_by_direct_iteration() {
    assert_eq!((1u64 << LENGTH) - 3u64.pow(ODD_STEPS as u32), GAP);
    for (word, m, c) in [LEAST, LARGER_RATIO] {
        let word_bits = bits(word);
        assert_eq!(word_bits.len(), LENGTH);
        assert_eq!(word_bits.iter().filter(|&&odd| odd).count(), ODD_STEPS);
        assert_eq!(offset(&word_bits), c, "{word}");
        assert_eq!(least_member(&word_bits), m, "{word}");
        // T^10(m) = (3^6 m + c) / 2^10, and the member really descends, at
        // step 10 and not before.
        let orbit: Vec<u64> = std::iter::successors(Some(m), |&x| Some(step(x)))
            .take(LENGTH + 1)
            .collect();
        assert_eq!(orbit[LENGTH] << LENGTH, 729 * m + c, "{word}");
        assert!(orbit[LENGTH] < m, "{word}");
        assert!(orbit[1..LENGTH].iter().all(|&x| x > m), "{word}");
        assert!(GAP * m > c, "{word}");

        // Cross-check against the library.
        let prefix: ParityPrefix = word.parse().unwrap();
        let cylinder = Cylinder::from_prefix(&prefix);
        assert_eq!(cylinder.residue(), &BigUint::from(m), "{word}");
        assert_eq!(cylinder.affine().offset(), &BigUint::from(c), "{word}");
        assert_eq!(closed_form_offset(&word_bits), BigUint::from(c), "{word}");
        assert_eq!(parity_vector(&BigUint::from(m), LENGTH), word_bits);
        assert_eq!(stopping_time(&BigUint::from(m), 100), Some(10), "{word}");
    }
}

#[test]
fn both_words_are_first_coefficient_crossings() {
    assert!(is_first_crossing(&bits(LEAST.0)));
    assert!(is_first_crossing(&bits(LARGER_RATIO.0)));
    // Sanity of the predicate itself: the paradoxical prefix of n = 7 crosses
    // one step earlier, and the all-odd word never crosses.
    assert!(!is_first_crossing(&bits("11101001")));
    assert!(is_first_crossing(&bits("1110100")));
    assert!(!is_first_crossing(&bits("1111111111")));
}

#[test]
fn the_cylinder_with_the_larger_member_has_the_larger_ratio() {
    let (_, m_least, c_least) = LEAST;
    let (_, m_other, c_other) = LARGER_RATIO;
    assert!(m_least < m_other);
    let (denominator_least, denominator_other) = (GAP * m_least, GAP * m_other);
    assert_eq!((denominator_least, denominator_other), (84_665, 102_365));
    // rho(other) > rho(least)  iff  c_other * den_least > c_least * den_other.
    let (left, right) = (c_other * denominator_least, c_least * denominator_other);
    assert_eq!((left, right), (83_733_685, 71_348_405));
    assert_eq!(left - right, 12_385_280);
}

#[test]
fn enumeration_of_the_r6_family_refutes_p1a() {
    // Every word of length 1..=11, so that no first crossing with six odd
    // steps of another length can be missed (a longer one would need
    // 2^11 < 3^6).
    let mut found: Vec<(String, u64, u64)> = Vec::new();
    for length in 1..=LENGTH + 1 {
        for mask in 0u32..1 << length {
            let word: Vec<bool> = (0..length).map(|i| mask >> i & 1 == 1).collect();
            let odd_steps = word.iter().filter(|&&odd| odd).count();
            if odd_steps != ODD_STEPS || !is_first_crossing(&word) {
                continue;
            }
            assert_eq!(length, LENGTH);
            let text: String = word
                .iter()
                .map(|&odd| if odd { '1' } else { '0' })
                .collect();
            found.push((text, least_member(&word), offset(&word)));
        }
    }
    found.sort_by_key(|entry| entry.1);
    let expected: Vec<(String, u64, u64)> = FAMILY
        .iter()
        .map(|&(word, m, c)| (word.to_string(), m, c))
        .collect();
    assert_eq!(found, expected);

    // 287 is the least member of the family, attained once.
    let least = found.iter().min_by_key(|entry| entry.1).unwrap();
    assert_eq!((least.0.as_str(), least.1, least.2), LEAST);
    assert_eq!(found.iter().filter(|entry| entry.1 == least.1).count(), 1);

    // The largest ratio c / (d m) is attained once, by the cylinder of 347.
    // The common factor d cancels: compare c1 * m2 with c2 * m1.
    let greatest = found
        .iter()
        .max_by(|a, b| (a.2 * b.1).cmp(&(b.2 * a.1)))
        .unwrap();
    assert_eq!((greatest.0.as_str(), greatest.1, greatest.2), LARGER_RATIO);
    let ties = found
        .iter()
        .filter(|entry| entry.2 * greatest.1 == greatest.2 * entry.1)
        .count();
    assert_eq!(ties, 1);
    assert_ne!(greatest.1, least.1, "P1a would require these to coincide");

    // No member >= 2 of any of the twelve cylinders is below its threshold.
    assert!(found.iter().all(|entry| GAP * entry.1 > entry.2));
}

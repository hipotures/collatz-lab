//! A tiny deterministic generator (SplitMix64) for reproducible sampling.
//!
//! It is implemented locally so that sampled experiments are bit-for-bit
//! reproducible from the seed alone, independent of any external crate
//! version. It is used only to *choose inputs*; it never takes part in a
//! validity check.

use num_bigint::BigUint;
use num_traits::One;

#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A pseudo-random integer with exactly `bits` bits (top bit set).
    /// Returns zero when `bits == 0`.
    pub fn next_biguint(&mut self, bits: usize) -> BigUint {
        if bits == 0 {
            return BigUint::default();
        }
        let mut value = BigUint::default();
        let mut produced = 0usize;
        while produced < bits {
            value = (value << 64usize) | BigUint::from(self.next_u64());
            produced += 64;
        }
        value >>= produced - bits;
        value | (BigUint::one() << (bits - 1))
    }
}

//! Serde helpers that store `BigUint` values as decimal strings, so that
//! machine-readable artifacts stay exact and human-readable.

use num_bigint::BigUint;
use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serializer};

pub fn serialize<S: Serializer>(value: &BigUint, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&value.to_string())
}

pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<BigUint, D::Error> {
    let text = String::deserialize(deserializer)?;
    text.parse().map_err(D::Error::custom)
}

/// Same encoding for `Vec<BigUint>`.
pub mod vec {
    use super::*;

    pub fn serialize<S: Serializer>(values: &[BigUint], serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(values.iter().map(BigUint::to_string))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<BigUint>, D::Error> {
        let texts = Vec::<String>::deserialize(deserializer)?;
        texts
            .iter()
            .map(|text| text.parse().map_err(D::Error::custom))
            .collect()
    }
}

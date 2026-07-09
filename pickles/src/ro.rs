//! Deterministic "random oracle" for dummy values (port of pickles' `ro.ml`).
//!
//! Dummy proof data (unverified base-case proofs, padding challenges) is
//! derived from blake2s over `"{label}_{counter}"`, bit-unpacked LSB-first per
//! byte and truncated. The prover and the circuits must agree on these values;
//! matching OCaml's exact global counter interleaving is only needed for
//! cross-verifying mina-produced proofs (tracked as future work — the streams
//! here are internally consistent).

use ark_ff::PrimeField;

/// blake2s-256 of `s`, unpacked to `length` bits (LSB-first within each byte)
/// — `ro.ml::bits_random_oracle`.
pub fn bits_random_oracle(length: usize, s: &str) -> Vec<bool> {
    use blake2::{Blake2s256, Digest};
    let hash = Blake2s256::digest(s.as_bytes());
    let mut bits = Vec::with_capacity(256);
    for c in hash {
        for i in 0..8 {
            bits.push((c >> i) & 1 == 1);
        }
    }
    bits.truncate(length);
    bits
}

/// A labelled deterministic stream: call `n` yields
/// `bits_random_oracle(length, "{label}_{n}")` with `n` starting at 1
/// (`ro.ml::ro`).
pub struct Ro {
    label: &'static str,
    length: usize,
    counter: u64,
}

impl Ro {
    pub fn new(label: &'static str, length: usize) -> Self {
        Ro {
            label,
            length,
            counter: 0,
        }
    }

    /// The Tock (Fq) field stream (`Ro.tock`, label `"fq"`, 255 bits).
    pub fn tock() -> Self {
        Self::new("fq", 255)
    }

    /// The Tick (Fp) field stream (`Ro.tick`, label `"fp"`, 255 bits).
    pub fn tick() -> Self {
        Self::new("fp", 255)
    }

    /// The 128-bit challenge stream (`Ro.chal`).
    pub fn chal() -> Self {
        Self::new("chal", 128)
    }

    pub fn next_bits(&mut self) -> Vec<bool> {
        self.counter += 1;
        bits_random_oracle(self.length, &format!("{}_{}", self.label, self.counter))
    }

    /// The next value as a field element (`Field.of_bits`, little-endian).
    pub fn next_field<F: PrimeField>(&mut self) -> F {
        let bits = self.next_bits();
        let mut acc = F::zero();
        for &b in bits.iter().rev() {
            acc = acc + acc;
            if b {
                acc += F::one();
            }
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mina_curves::pasta::Fq;

    /// Streams are deterministic, distinct per counter, and sized correctly.
    #[test]
    fn ro_streams_deterministic() {
        let mut a = Ro::chal();
        let mut b = Ro::chal();
        let (x1, x2): (Fq, Fq) = (a.next_field(), a.next_field());
        assert_ne!(x1, x2, "counter advances");
        assert_eq!(x1, b.next_field(), "same stream, same values");

        let bits = bits_random_oracle(128, "chal_1");
        assert_eq!(bits.len(), 128);
        // 128-bit challenges fit in the low limbs
        use ark_ff::{BigInteger, PrimeField as _};
        assert!(x1.into_bigint().to_bits_le()[128..].iter().all(|b| !b));
    }

    /// Official Mina `test_ro.ml` regression vector.
    #[test]
    fn bits_random_oracle_matches_mina_regression_vector() {
        let expected = "0100000110111000111111110001100001100010001010001101001011011001\
                        0011101101101000001110001110100101010100001000001110101110111010"
            .chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| c == '1')
            .collect::<Vec<_>>();
        assert_eq!(bits_random_oracle(128, "BitsRandomOracle"), expected);
    }
}

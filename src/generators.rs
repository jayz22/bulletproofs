//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use digest::{ExtendableOutput, Update, XofReader};
use sha3::{Sha3_512, Shake256, Shake256Reader};

/// Represents a pair of base points for Pedersen commitments.
///
/// The Bulletproofs implementation and API is designed to support
/// pluggable bases for Pedersen commitments, so that the choice of
/// bases is not hard-coded.
///
/// The default generators are:
///
/// * `B`: the `ristretto255` basepoint;
/// * `B_blinding`: the result of `ristretto255` SHA3-512
/// hash-to-group on input `B_bytes`.
#[derive(Copy, Clone)]
pub struct PedersenGens {
    /// Base for the committed value
    pub B: RistrettoPoint,
    /// Base for the blinding factor
    pub B_blinding: RistrettoPoint,
}

impl PedersenGens {
    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: Scalar, blinding: Scalar) -> RistrettoPoint {
        RistrettoPoint::multiscalar_mul(&[value, blinding], &[self.B, self.B_blinding])
    }
}

impl Default for PedersenGens {
    fn default() -> Self {
        PedersenGens {
            B: RISTRETTO_BASEPOINT_POINT,
            B_blinding: RistrettoPoint::hash_from_bytes::<Sha3_512>(
                RISTRETTO_BASEPOINT_COMPRESSED.as_bytes(),
            ),
        }
    }
}

/// The `GeneratorsChain` creates an arbitrary-long sequence of
/// orthogonal generators.  The sequence can be deterministically
/// produced starting with an arbitrary point.
struct GeneratorsChain {
    reader: Shake256Reader,
}

impl GeneratorsChain {
    /// Creates a chain of generators, determined by the hash of `label`.
    fn new(label: &[u8]) -> Self {
        let mut shake = Shake256::default();
        shake.update(b"GeneratorsChain");
        shake.update(label);

        GeneratorsChain {
            reader: shake.finalize_xof(),
        }
    }

    /// Advances the reader n times, squeezing and discarding
    /// the result.
    fn fast_forward(mut self, n: usize) -> Self {
        for _ in 0..n {
            let mut buf = [0u8; 64];
            self.reader.read(&mut buf);
        }
        self
    }
}

impl Default for GeneratorsChain {
    fn default() -> Self {
        Self::new(&[])
    }
}

impl Iterator for GeneratorsChain {
    type Item = RistrettoPoint;

    fn next(&mut self) -> Option<Self::Item> {
        let mut uniform_bytes = [0u8; 64];
        self.reader.read(&mut uniform_bytes);

        Some(RistrettoPoint::from_uniform_bytes(&uniform_bytes))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// The `BulletproofGens` struct contains all the generators needed
/// for single-party range proofs up to `n` total dimensions.
///
/// # Simplified Single-Party Generation (following Solana's approach)
///
/// This implementation uses a flat generator system optimized for single-party
/// range proofs, removing the multi-party complexity of the original design.
/// We construct a single vector of generators using SHAKE256 with simple
/// domain separation labels "G" and "H".
///
/// This approach is:
/// - More efficient for single-party proofs (no aggregation overhead)
/// - Simpler to understand and maintain
/// - Compatible with Solana's range proof implementation
/// - Sufficient for confidential transaction use cases
///
/// The total capacity represents the maximum number of generators available,
/// which should be set to the maximum expected total dimensions (sum of bit
/// lengths across all values in an aggregated proof).
#[derive(Clone)]
pub struct BulletproofGens {
    /// The maximum number of usable generators.
    pub gens_capacity: usize,
    /// Precomputed \\(\mathbf G\\) generators (flat vector).
    G_vec: Vec<RistrettoPoint>,
    /// Precomputed \\(\mathbf H\\) generators (flat vector).
    H_vec: Vec<RistrettoPoint>,
}

impl BulletproofGens {
    /// Create a new `BulletproofGens` object for single-party range proofs.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the total number of generators to precompute.
    ///   For range proofs, this should be the maximum expected total dimension
    ///   (sum of bit lengths across all values). For example:
    ///   - Single 64-bit proof: 64
    ///   - Two 32-bit proofs: 64  
    ///   - Four 64-bit proofs: 256
    ///   - Eight 32-bit proofs: 256
    ///
    /// This simplified constructor matches Solana's approach and removes
    /// the multi-party complexity that's not needed for confidential transactions.
    pub fn new(gens_capacity: usize) -> Self {
        let mut gens = BulletproofGens {
            gens_capacity: 0,
            G_vec: Vec::new(),
            H_vec: Vec::new(),
        };
        gens.increase_capacity(gens_capacity);
        gens
    }
    

    /// Increases the generators' capacity to the amount specified.
    /// If less than or equal to the current capacity, does nothing.
    /// 
    /// This implementation follows Solana's approach with simple "G" and "H" labels.
    pub fn increase_capacity(&mut self, new_capacity: usize) {
        if self.gens_capacity >= new_capacity {
            return;
        }

        // Generate additional G generators using simple "G" label (Solana approach)
        self.G_vec.extend(
            &mut GeneratorsChain::new(b"G")
                .fast_forward(self.gens_capacity)
                .take(new_capacity - self.gens_capacity),
        );

        // Generate additional H generators using simple "H" label (Solana approach)  
        self.H_vec.extend(
            &mut GeneratorsChain::new(b"H")
                .fast_forward(self.gens_capacity)
                .take(new_capacity - self.gens_capacity),
        );

        self.gens_capacity = new_capacity;
    }

    /// Return an iterator over the first `n` G generators.
    /// This simplified interface matches Solana's approach for single-party proofs.
    pub(crate) fn G(&self, n: usize) -> impl Iterator<Item = &RistrettoPoint> {
        FlatGensIter {
            array: &self.G_vec,
            n,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the first `n` H generators.
    /// This simplified interface matches Solana's approach for single-party proofs.
    pub(crate) fn H(&self, n: usize) -> impl Iterator<Item = &RistrettoPoint> {
        FlatGensIter {
            array: &self.H_vec,
            n,
            gen_idx: 0,
        }
    }
    
}

/// Simple iterator over a flat vector of generators (following Solana's approach).
/// This replaces the complex AggregatedGensIter used for multi-party proofs.
struct FlatGensIter<'a> {
    array: &'a Vec<RistrettoPoint>,
    n: usize,
    gen_idx: usize,
}

impl<'a> Iterator for FlatGensIter<'a> {
    type Item = &'a RistrettoPoint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[cur_gen])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.n - self.gen_idx;
        (size, Some(size))
    }
}

// BulletproofGensShare is no longer needed in the single-party design.
// The simplified BulletproofGens directly provides access to generators
// without the complexity of party-specific shares.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flat_gens_work_correctly() {
        let gens = BulletproofGens::new(512);

        let helper = |n: usize| {
            let G_iter: Vec<RistrettoPoint> = gens.G(n).cloned().collect();
            let H_iter: Vec<RistrettoPoint> = gens.H(n).cloned().collect();
            
            // Check that we get the expected number of generators
            assert_eq!(G_iter.len(), n);
            assert_eq!(H_iter.len(), n);
            
            // Check that generators are deterministic (same on repeated calls)
            let G_iter2: Vec<RistrettoPoint> = gens.G(n).cloned().collect();
            let H_iter2: Vec<RistrettoPoint> = gens.H(n).cloned().collect();
            assert_eq!(G_iter, G_iter2);
            assert_eq!(H_iter, H_iter2);
            
            // Check that G and H generators are different
            assert_ne!(G_iter, H_iter);
        };

        helper(64);
        helper(128);
        helper(256);
        helper(512);
    }

    #[test]
    fn resizing_small_gens_matches_creating_bigger_gens() {
        let gens = BulletproofGens::new(512);

        let mut gen_resized = BulletproofGens::new(256);
        gen_resized.increase_capacity(512);

        let helper = |n: usize| {
            let gens_G: Vec<RistrettoPoint> = gens.G(n).cloned().collect();
            let gens_H: Vec<RistrettoPoint> = gens.H(n).cloned().collect();

            let resized_G: Vec<RistrettoPoint> = gen_resized.G(n).cloned().collect();
            let resized_H: Vec<RistrettoPoint> = gen_resized.H(n).cloned().collect();

            assert_eq!(gens_G, resized_G);
            assert_eq!(gens_H, resized_H);
        };

        helper(512);
        helper(256);
        helper(128);
        helper(64);
    }
}

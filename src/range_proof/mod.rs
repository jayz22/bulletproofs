#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../../docs/range-proof-protocol.md"))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate rand;

#[cfg(feature = "std")]
use self::rand::thread_rng;
use alloc::vec::Vec;

use core::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::TranscriptProtocol;
use crate::util;

use rand_core::{CryptoRng, RngCore};
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

// Direct range proof implementation for confidential transactions

/// The `RangeProof` struct represents a proof that one or more values
/// are in a range.
///
/// The `RangeProof` struct contains functions for creating and
/// verifying aggregated range proofs.  The single-value case is
/// implemented as a special case of aggregated range proofs.
///
/// This implementation implements a non-interactive range proof aggregation that is specified in
/// the original Bulletproofs [paper](https://eprint.iacr.org/2017/1066) (Section 4.3).
///
/// The bitsize of the range, as well as the list of commitments to
/// the values, are not included in the proof, and must be known to
/// the verifier.
///
/// This implementation requires that both the bitsize `n` and the
/// aggregation size `m` be powers of two, so that `n = 8, 16, 32, 64`
/// and `m = 1, 2, 4, 8, 16, ...`.  Note that the aggregation size is
/// not given as an explicit parameter, but is determined by the
/// number of values or commitments passed to the prover or verifier.
///
/// # Note
///
/// For proving, these functions run the multiparty aggregation
/// protocol locally.  That API is exposed in the [`aggregation`](::range_proof_mpc)
/// module and can be used to perform online aggregation between
/// parties without revealing secret values to each other.
#[derive(Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the bits of the value
    A: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl RangeProof {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple`].
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate bulletproofs;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 1.
    /// let bp_gens = BulletproofGens::new(64);
    ///
    /// // A secret value we want to prove lies in the range [0, 2^32)
    /// let secret_value = 1037578891u64;
    ///
    /// // The API takes a blinding factor for the commitment.
    /// let blinding = Scalar::random(&mut thread_rng());
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create a 32-bit rangeproof.
    /// let (proof, committed_value) = RangeProof::prove_single(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     secret_value,
    ///     &blinding,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_single_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
        rng: &mut T,
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        let (p, Vs) = RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            &[v],
            &[*v_blinding],
            n,
            rng,
        )?;
        Ok((p, Vs[0]))
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_single(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        RangeProof::prove_single_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            v,
            v_blinding,
            n,
            &mut thread_rng(),
        )
    }

    /// Create a rangeproof for a set of values.
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate bulletproofs;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 16.
    /// let bp_gens = BulletproofGens::new(1024); // 64 * 16 = 1024 total capacity
    ///
    /// // Four secret values we want to prove lie in the range [0, 2^32)
    /// let secrets = [4242344947u64, 3718732727u64, 2255562556u64, 2526146994u64];
    ///
    /// // The API takes blinding factors for the commitments.
    /// let blindings: Vec<_> = (0..4).map(|_| Scalar::random(&mut thread_rng())).collect();
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create an aggregated 32-bit rangeproof and corresponding commitments.
    /// let (proof, commitments) = RangeProof::prove_multiple(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     &secrets,
    ///     &blindings,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_multiple(&bp_gens, &pc_gens, &mut verifier_transcript, &commitments, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    /// Create aggregated range proofs using direct construction (Section 4.3 of Bulletproofs paper).
    /// 
    /// This implementation follows the non-interactive aggregated range proof protocol from the
    /// original Bulletproofs paper, removing the multi-party computation aspects present in the
    /// original zkcrypto implementation.
    /// 
    /// # Protocol Overview
    /// 1. Bit-decompose values and create vector commitment A using conditional assignment
    /// 2. Create blinding vector commitment S
    /// 3. Use Fiat-Shamir to derive challenges y, z from transcript
    /// 4. Construct polynomial l(x), r(x) with coefficients based on bit decompositions
    /// 5. Compute polynomial t(x) = <l(x), r(x)> and commit to its coefficients
    /// 6. Evaluate polynomials at challenge point x and create inner product proof
    pub fn prove_multiple_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
        _rng: &mut T,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        let m = values.len();

        // Validation checks inherited from original zkcrypto implementation
        // These constraints ensure compatibility with the generator system and
        // maintain the power-of-two requirements needed for efficient inner product proofs
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }

        // Bulletproofs aggregation requires m to be power of 2 for optimal inner product proof size
        if !m.is_power_of_two() {
            return Err(ProofError::InvalidAggregation);
        }

        // Ensure we have sufficient generators for the total proof dimensions
        // In the flat system, we need n*m total generators
        if bp_gens.gens_capacity < (n * m) {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        // Create Pedersen commitments V_i = v_i * G + r_i * H for each value
        // These commitments will be public inputs to the range proof verification
        let value_commitments: Vec<CompressedRistretto> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&value, &blinding)| pc_gens.commit(Scalar::from(value), blinding).compress())
            .collect();

        // Initialize transcript with domain separator (follows Merlin transcript protocol)
        // This binds the proof to specific dimensions (n-bit range, m values)
        transcript.rangeproof_domain_sep(n as u64, m as u64);

        // Add value commitments to transcript (makes them part of Fiat-Shamir challenge derivation)
        // This step is crucial for binding the proof to the specific commitments being proven
        for V in &value_commitments {
            transcript.append_point(b"V", V);
        }

        // === PHASE 1: BIT DECOMPOSITION AND VECTOR COMMITMENT A ===
        // Direct range proof construction following Section 4.3 of Bulletproofs paper
        let nm = n * m;  // Total dimension of vectors (n bits per value × m values)
        
        // Initialize bit decomposition vectors a_L, a_R where:
        // a_L[i] ∈ {0,1} represents the i-th bit
        // a_R[i] = a_L[i] - 1 ∈ {-1,0} (this creates the constraint a_L ∘ a_R = 0)
        let mut a_L = Vec::with_capacity(nm);
        let mut a_R = Vec::with_capacity(nm);
        
        // Generate cryptographic blinding factors for commitment security
        // These prevent the verifier from learning anything about the committed values
        let a_blinding = Scalar::random(_rng);
        let s_blinding = Scalar::random(_rng);
        
        // Generate random masking vectors for the S commitment
        // These will be used to create the blinding commitment S = <s_L, G> + <s_R, H> + s_blinding*B
        let s_L: Vec<Scalar> = (0..nm).map(|_| Scalar::random(_rng)).collect();
        let s_R: Vec<Scalar> = (0..nm).map(|_| Scalar::random(_rng)).collect();
        
        // === Bit decomposition with conditional assignment (inspired by Solana's implementation) ===
        // This approach is more efficient than computing separate scalar multiplications
        use subtle::{Choice, ConditionallySelectable};
        // Initialize A commitment with blinding component: A = a_blinding * B + Σ(conditional points)
        let mut A = pc_gens.B_blinding * a_blinding;
        
        // Iterate through generator pairs (G_i, H_i) for each bit position
        // Using flat generators: total dimension = n * m
        let mut gens_iter = bp_gens.G(n * m).zip(bp_gens.H(n * m));
        for &value in values {
            for i in 0..n {  // Process each bit position (LSB first)
                let (G_i, H_i) = gens_iter.next().unwrap();
                let bit = (value >> i) & 1;  // Extract i-th bit using bit shift
                a_L.push(Scalar::from(bit));  // Store bit as scalar (0 or 1)
                a_R.push(Scalar::from(bit) - Scalar::ONE);  // a_R[i] = a_L[i] - 1 ∈ {-1, 0}
                
                // === CONDITIONAL ASSIGNMENT TECHNIQUE (from Solana implementation) ===
                // Instead of: A += a_L[i] * G_i + a_R[i] * H_i
                // We use: A += (bit == 0) ? -H_i : G_i
                // This is equivalent but more efficient since a_L[i] ∈ {0,1} and a_R[i] ∈ {-1,0}
                let bit_choice = Choice::from(bit as u8);
                let mut point = -H_i;  // Default: add -H_i (when bit = 0)
                point.conditional_assign(G_i, bit_choice);  // If bit = 1, use G_i instead
                A += point;
            }
        }
        
        // === PHASE 2: BLINDING VECTOR COMMITMENT S ===
        // Compute S = s_blinding * B + <s_L, G> + <s_R, H>
        // This commitment hides the masking vectors s_L, s_R that will be revealed later
        use curve25519_dalek::traits::MultiscalarMul;
        let S = RistrettoPoint::multiscalar_mul(
            // Scalars: [s_blinding, s_L[0], ..., s_L[nm-1], s_R[0], ..., s_R[nm-1]]
            iter::once(s_blinding).chain(s_L.iter().cloned()).chain(s_R.iter().cloned()),
            // Points: [B, G[0], ..., G[nm-1], H[0], ..., H[nm-1]]
            iter::once(&pc_gens.B_blinding)
                .chain(bp_gens.G(n * m))
                .chain(bp_gens.H(n * m)),
        );
        
        // === FIAT-SHAMIR CHALLENGE DERIVATION ===
        // Add A and S commitments to transcript - this binds the challenges to our specific proof
        transcript.append_point(b"A", &A.compress());
        transcript.append_point(b"S", &S.compress());
        
        // Derive challenges y and z from transcript (replaces interactive verifier challenges)
        // y: used for creating linear combination of H generators (prevents degeneracy)
        // z: used for aggregating multiple range proofs into single inner product relation
        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        
        // === PHASE 3: POLYNOMIAL CONSTRUCTION ===
        // Construct degree-1 polynomials l(x), r(x) such that their inner product gives
        // the desired constraint equation. This is the core of the Bulletproofs protocol.
        // Note: z^2 will be computed by verifier during verification process
        let mut l_poly = util::VecPoly1::zero(nm);  // l(x) = l_0 + l_1*x
        let mut r_poly = util::VecPoly1::zero(nm);  // r(x) = r_0 + r_1*x
        
        let mut i = 0;
        let mut exp_z = z * z; // Start at z^2 for the first value (z^0, z^1 reserved)
        let mut exp_y = Scalar::ONE;  // Running product of powers of y
        
        // === POLYNOMIAL COEFFICIENTS (from Bulletproofs Section 4.3) ===
        for _j in 0..m {  // For each value being proven
            let mut exp_2 = Scalar::ONE;  // Running product: 2^0, 2^1, 2^2, ...
            
            for _k in 0..n {  // For each bit position
                // Left polynomial: l(x) = (a_L - z*1) + s_L*x
                // Constant term: a_L[i] - z (shifts bit vector by z)
                l_poly.0[i] = a_L[i] - z;
                // Linear term: s_L[i] (blinding vector coefficient)
                l_poly.1[i] = s_L[i];
                
                // Right polynomial: r(x) = y^i * (a_R + z*1) + z^(j+2) * 2^k + y^i * s_R*x
                // This combines three components:
                // 1. y^i * (a_R[i] + z): scaled shifted bit complement
                // 2. z^(j+2) * 2^k: aggregation term for value j, bit k
                // 3. y^i * s_R[i] * x: scaled blinding (linear term)
                r_poly.0[i] = exp_y * (a_R[i] + z) + exp_z * exp_2;
                r_poly.1[i] = exp_y * s_R[i];
                
                // Update running products for next iteration
                exp_y *= y;  // y^0, y^1, y^2, ...
                exp_2 = exp_2 + exp_2; // Efficient doubling: 2^0, 2^1, 2^2, ...
                i += 1;
            }
            exp_z *= z; // Move to next power: z^2, z^3, z^4, ... for aggregation
        }
        
        // === PHASE 4: INNER PRODUCT POLYNOMIAL ===
        // Calculate t(x) = <l(x), r(x)> = t_0 + t_1*x + t_2*x^2
        // This polynomial encodes the constraint that must be satisfied for a valid range proof
        let t_poly = l_poly.inner_product(&r_poly);
        
        // === COMMITMENTS TO POLYNOMIAL COEFFICIENTS ===
        // We commit to t_1 and t_2 (t_0 can be computed by verifier)
        // This allows verifier to check the polynomial evaluation without knowing the coefficients
        let t_1_blinding = Scalar::random(_rng);
        let t_2_blinding = Scalar::random(_rng);
        
        let T_1 = pc_gens.commit(t_poly.1, t_1_blinding);  // T_1 = t_1*G + t_1_blinding*H
        let T_2 = pc_gens.commit(t_poly.2, t_2_blinding);  // T_2 = t_2*G + t_2_blinding*H
        
        // Add T_1, T_2 to transcript for next challenge derivation
        transcript.append_point(b"T_1", &T_1.compress());
        transcript.append_point(b"T_2", &T_2.compress());
        
        // === PHASE 5: POLYNOMIAL EVALUATION ===
        // Derive evaluation challenge x from transcript
        let x = transcript.challenge_scalar(b"x");
        
        // Evaluate the polynomial t(x) at the challenge point
        let t_x = t_poly.eval(x);  // t_x = t_0 + t_1*x + t_2*x^2
        
        // === CRITICAL AGGREGATION FORMULA ===
        // Calculate the aggregated blinding factor for the polynomial evaluation
        // This must match the verifier's computation for the proof to verify
        // Formula: Σ(z^(i+2) * r_i) + x*t_1_blinding + x^2*t_2_blinding
        // where r_i are the original Pedersen commitment blinding factors
        let mut agg_opening = Scalar::ZERO;
        let mut exp_z = z;  // Start with z^1
        for &blinding in blindings {
            exp_z *= z; // Increment to z^2, z^3, ..., z^(m+1)
            agg_opening += exp_z * blinding;
        }
        
        // Total blinding for the evaluation: aggregated commitments + polynomial commitments
        let t_x_blinding = agg_opening + x * t_1_blinding + x * x * t_2_blinding;
        // Blinding factor for the vector commitment evaluation A + x*S
        let e_blinding = a_blinding + x * s_blinding;
        
        // === EVALUATE POLYNOMIALS AT CHALLENGE POINT ===
        // These vectors will be used in the inner product proof
        let l_vec = l_poly.eval(x);  // l(x) = (a_L - z*1) + x*s_L
        let r_vec = r_poly.eval(x);  // r(x) = y^i*(a_R + z*1) + z^j*2^k + x*y^i*s_R
        
        // === COMMIT EVALUATION RESULTS TO TRANSCRIPT ===
        // These values will be verified against the polynomial commitments
        transcript.append_scalar(b"t_x", &t_x);
        transcript.append_scalar(b"t_x_blinding", &t_x_blinding);
        transcript.append_scalar(b"e_blinding", &e_blinding);
        
        // === INNER PRODUCT PROOF SETUP ===
        // Generate challenge w for the inner product argument
        let w = transcript.challenge_scalar(b"w");
        let Q = w * pc_gens.B;  // Generator for inner product commitment
        
        // === PHASE 6: INNER PRODUCT PROOF ===
        // Create an inner product proof for <l_vec, r_vec> with respect to generators G, H'
        // where H'_i = y^(-i) * H_i (this reweighting is crucial for soundness)
        
        // G factors are all 1 (no reweighting needed for G generators)
        let G_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(nm).collect();
        // H factors are powers of y^(-1) (reweight H generators to break symmetry)
        let H_factors: Vec<Scalar> = util::exp_iter(y.invert()).take(nm).collect();
        
        // Create the recursive inner product proof
        // This proves knowledge of l_vec, r_vec such that:
        // P = <l_vec, G> + <r_vec, H'> + <l_vec, r_vec> * Q
        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,  // Generator for inner product term
            &G_factors,  // Scaling factors for G generators
            &H_factors,  // Scaling factors for H generators (y^(-i))
            bp_gens.G(n * m).cloned().collect(),  // G generator vector
            bp_gens.H(n * m).cloned().collect(),  // H generator vector
            l_vec,  // Left vector l(x)
            r_vec,  // Right vector r(x)
        );
        
        // === PROOF CONSTRUCTION COMPLETE ===
        // Return the complete range proof and the value commitments
        // The proof contains all necessary components for verification:
        // - A, S: Vector commitments to bit decomposition and blinding vectors
        // - T_1, T_2: Polynomial coefficient commitments
        // - t_x, t_x_blinding, e_blinding: Evaluation scalars and their blindings
        // - ipp_proof: Inner product proof for the final verification equation
        Ok((
            RangeProof {
                A: A.compress(),
                S: S.compress(),
                T_1: T_1.compress(),
                T_2: T_2.compress(),
                t_x,
                t_x_blinding,
                e_blinding,
                ipp_proof,
            },
            value_commitments,
        ))
    }

    /// Create a rangeproof for a set of values.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_multiple(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            values,
            blindings,
            n,
            &mut thread_rng(),
        )
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify_multiple` for the `m=1` case.
    pub fn verify_single_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(bp_gens, pc_gens, transcript, &[*V], n, rng)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around [`RangeProof::verify_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_single(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_single_with_rng(bp_gens, pc_gens, transcript, V, n, &mut thread_rng())
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    pub fn verify_multiple_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        // Ensure we have sufficient generators for verification (n*m total dimensions)
        if bp_gens.gens_capacity < (n * m) {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        // Party capacity check no longer needed in flat single-party system

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point(b"V", V);
        }

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        let zz = z * z;
        let minus_z = -z;

        transcript.validate_and_append_point(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point(b"T_2", &self.T_2)?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let w = transcript.challenge_scalar(b"w");

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<Scalar> = util::exp_iter(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z))
            .collect();

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let value_commitment_scalars = util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp);
        let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);

        use curve25519_dalek::traits::VartimeMultiscalarMul;
        let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::ONE)
                .chain(iter::once(x))
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(iter::once(basepoint_scalar))
                .chain(g)
                .chain(h)
                .chain(value_commitment_scalars),
            iter::once(self.A.decompress())
                .chain(iter::once(self.S.decompress()))
                .chain(iter::once(self.T_1.decompress()))
                .chain(iter::once(self.T_2.decompress()))
                .chain(self.ipp_proof.L_vec.iter().map(|L| L.decompress()))
                .chain(self.ipp_proof.R_vec.iter().map(|R| R.decompress()))
                .chain(iter::once(Some(pc_gens.B_blinding)))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(bp_gens.G(n * m).map(|&x| Some(x)))
                .chain(bp_gens.H(n * m).map(|&x| Some(x)))
                .chain(value_commitments.iter().map(|V| V.decompress())),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        use group::Group;
        if mega_check.is_identity().into() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    /// This is a convenience wrapper around [`RangeProof::verify_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            value_commitments,
            n,
            &mut thread_rng(),
        )
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * four compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        // 7 elements: points A, S, T1, T2, scalars tx, tx_bl, e_bl.
        let mut buf = Vec::with_capacity(7 * 32 + self.ipp_proof.serialized_size());
        buf.extend_from_slice(self.A.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend(self.ipp_proof.to_bytes_iter());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `RangeProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<RangeProof, ProofError> {
        if slice.len() % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        if slice.len() < 7 * 32 {
            return Err(ProofError::FormatError);
        }

        use crate::util::read32;

        let A = CompressedRistretto(read32(&slice[0 * 32..]));
        let S = CompressedRistretto(read32(&slice[1 * 32..]));
        let T_1 = CompressedRistretto(read32(&slice[2 * 32..]));
        let T_2 = CompressedRistretto(read32(&slice[3 * 32..]));

        let t_x = Option::from(Scalar::from_canonical_bytes(read32(&slice[4 * 32..])))
            .ok_or(ProofError::FormatError)?;
        let t_x_blinding = Option::from(Scalar::from_canonical_bytes(read32(&slice[5 * 32..])))
            .ok_or(ProofError::FormatError)?;
        let e_blinding = Option::from(Scalar::from_canonical_bytes(read32(&slice[6 * 32..])))
            .ok_or(ProofError::FormatError)?;

        let ipp_proof = InnerProductProof::from_bytes(&slice[7 * 32..])?;

        Ok(RangeProof {
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
}

impl Serialize for RangeProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for RangeProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct RangeProofVisitor;

        impl<'de> Visitor<'de> for RangeProofVisitor {
            type Value = RangeProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                formatter.write_str("a valid RangeProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<RangeProof, E>
            where
                E: serde::de::Error,
            {
                // Using Error::custom requires T: Display, which our error
                // type only implements when it implements std::error::Error.
                #[cfg(feature = "std")]
                return RangeProof::from_bytes(v).map_err(serde::de::Error::custom);
                // In no-std contexts, drop the error message.
                #[cfg(not(feature = "std"))]
                return RangeProof::from_bytes(v)
                    .map_err(|_| serde::de::Error::custom("deserialization error"));
            }
        }

        deserializer.deserialize_bytes(RangeProofVisitor)
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n \cdot m} \rangle - \sum_{j=0}^{m-1} z^{j+3} \cdot \langle \mathbf{1}, {\mathbf{2}}^{n \cdot m} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from(2u64), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::generators::PedersenGens;

    #[test]
    fn test_delta() {
        let mut rng = rand::thread_rng();
        let y = Scalar::random(&mut rng);
        let z = Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::ZERO;
        let mut exp_y = Scalar::ONE; // start at y^0 = 1
        let mut exp_2 = Scalar::ONE; // start at 2^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        assert_eq!(power_g, delta(n, 1, &y, &z),);
    }

    /// Given a bitsize `n`, test the following:
    ///
    /// 1. Generate `m` random values and create a proof they are all in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn singleparty_create_and_verify_helper(n: usize, m: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        //use bincode; // already present in lib.rs

        // Both prover and verifier have access to the generators and the proof
        let max_bitsize = 64;
        let max_parties = 8;
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(max_bitsize * max_parties);

        // Prover's scope
        let (proof_bytes, value_commitments) = {
            use self::rand::Rng;
            let mut rng = rand::thread_rng();

            // 0. Create witness data
            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min..max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            // 1. Create the proof
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");
            let (proof, value_commitments) = RangeProof::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &values,
                &blindings,
                n,
            )
            .unwrap();

            // 2. Return serialized proof and value commitments
            (bincode::serialize(&proof).unwrap(), value_commitments)
        };

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: RangeProof = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

            assert!(proof
                .verify_multiple(&bp_gens, &pc_gens, &mut transcript, &value_commitments, n)
                .is_ok());
        }
    }

    #[test]
    fn create_and_verify_n_32_m_1() {
        singleparty_create_and_verify_helper(32, 1);
    }

    #[test]
    fn create_and_verify_n_32_m_2() {
        singleparty_create_and_verify_helper(32, 2);
    }

    #[test]
    fn create_and_verify_n_32_m_4() {
        singleparty_create_and_verify_helper(32, 4);
    }

    #[test]
    fn create_and_verify_n_32_m_8() {
        singleparty_create_and_verify_helper(32, 8);
    }

    #[test]
    fn create_and_verify_n_64_m_1() {
        singleparty_create_and_verify_helper(64, 1);
    }

    #[test]
    fn create_and_verify_n_64_m_2() {
        singleparty_create_and_verify_helper(64, 2);
    }

    #[test]
    fn create_and_verify_n_64_m_4() {
        singleparty_create_and_verify_helper(64, 4);
    }

    #[test]
    fn create_and_verify_n_64_m_8() {
        singleparty_create_and_verify_helper(64, 8);
    }

}

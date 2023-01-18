use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, PrimeField};
use ark_poly::polynomial::{univariate::DensePolynomial, UVPolynomial};
use ark_std::{cfg_iter, Zero};

use crate::compress_field;
use rayon::prelude::*;
use std::ops::Neg;

use super::{
    commitment,
    commitment::VKey,
    compress,
    errors::Error,
    ip,
    proof::{AggregateProof, GipaProof, KZGOpening, TippMippProof},
    srs::ProverSRS,
    transcript::Transcript,
};

/// Aggregate `n` zkSnark proofs, where `n` must be a power of two.
/// WARNING: transcript_include represents everything that should be included in
/// the transcript from outside the boundary of this function. This is especially
/// relevant for ALL public inputs of ALL individual proofs. In the regular case,
/// one should input ALL public inputs from ALL proofs aggregated. However, IF ALL the
/// public inputs are **fixed, and public before the aggregation time**, then there is
/// no need to hash those. The reason we specify this extra assumption is because hashing
/// the public inputs from the decoded form can take quite some time depending on the
/// number of proofs and public inputs (+100ms in our case). In the case of Filecoin, the only
/// non-fixed part of the public inputs are the challenges derived from a seed. Even though this
/// seed comes from a random beeacon, we are hashing this as a safety precaution.
pub fn aggregate_keys<E: PairingEngine + std::fmt::Debug, T: Transcript>(
    srs: &ProverSRS<E>,
    transcript: &mut T,
    bits: Vec<bool>,
    keys: Vec<E::G1Affine>,
    // (T,U) = Com(v, C)
    com_c: commitment::Output<E::Fqk>,
    // Z = SUM C_i ^ b_i
    agg_c: E::G1Affine,
) -> Result<AggregateProof<E>, Error> {
    if bits.len() != keys.len() {
        return Err(Error::InvalidProof(
            "Invalid size between key list and bits".to_string(),
        ));
    }
    if !keys.len().is_power_of_two() {
        return Err(Error::InvalidProof(
            "invalid key list size: not power of two".to_string(),
        ));
    }

    if !srs.has_correct_len(keys.len()) {
        return Err(Error::InvalidSRS("SRS len != proofs len".to_string()));
    }

    let proof = prove_mipp(&srs, transcript, bits, keys, &agg_c)?;

    Ok(AggregateProof {
        com_c,
        agg_c,
        tmipp: proof,
    })
}

fn prove_mipp<E: PairingEngine, T: Transcript>(
    srs: &ProverSRS<E>,
    transcript: &mut T,
    bits: Vec<bool>,
    keys: Vec<E::G1Affine>,
    agg_c: &E::G1Affine,
) -> Result<TippMippProof<E>, Error> {
    // Run GIPA
    let (proof, mut challenges, mut challenges_inv) =
        gipa_mipp(transcript, bits, keys, &srs.vkey, agg_c)?;

    // Prove final commitment keys are wellformed
    // we reverse the transcript so the polynomial in kzg opening is constructed
    // correctly - the formula indicates x_{l-j}. Also for deriving KZG
    // challenge point, input must be the last challenge.
    challenges.reverse();
    challenges_inv.reverse();

    // KZG challenge point
    transcript.append(b"kzg-challenge", &challenges[0]);
    transcript.append(b"vkey0", &proof.final_vkey.0);
    transcript.append(b"vkey1", &proof.final_vkey.1);
    let z = transcript.challenge_scalar::<E::Fr>(b"z-challenge");
    // Complete KZG proofs
    let vkey_opening = prove_commitment_v(
        &srs.h_alpha_powers_table,
        &srs.h_beta_powers_table,
        &challenges_inv,
        &z,
    );

    Ok(TippMippProof {
        gipa: proof,
        vkey_opening: vkey_opening?,
    })
}

/// gipa_mipp peforms the recursion of the GIPA protocol for TIPP and MIPP.
/// It returns a proof containing all intermdiate committed values, as well as
/// the challenges generated necessary to do the polynomial commitment proof
/// later in TIPP.
fn gipa_mipp<E: PairingEngine>(
    transcript: &mut impl Transcript,
    bits: Vec<bool>,
    keys: Vec<E::G1Affine>,
    vkey: &VKey<E>,
    agg_c: &E::G1Affine,
) -> Result<(GipaProof<E>, Vec<E::Fr>, Vec<E::Fr>), Error> {
    let bits_f = bits
        .into_par_iter()
        .map(|b| E::Fr::from(b))
        .collect::<Vec<_>>();
    let nproofs = keys.len();
    // the values of vectors C and bits rescaled at each step of the loop
    // these are A and y
    let (mut m_c, mut m_r) = (keys, bits_f);
    // the values of the commitment keys rescaled at each step of the loop
    // these are the h for me
    let mut vkey = vkey.clone();

    // storing the values for including in the proof
    // these are T_l and T_r
    let mut comms_c = Vec::new();
    // these are U_l and U_r
    let mut z_c = Vec::new();
    // these are the x-es
    let mut challenges: Vec<E::Fr> = Vec::new();
    let mut challenges_inv: Vec<E::Fr> = Vec::new();

    transcript.append(b"comm-c", agg_c);

    while m_c.len() > 1 {
        // recursive step
        // Recurse with problem of half size
        let split = m_c.len() / 2;

        // MIPP ///
        // c[:n']   c[n':]
        let (c_left, c_right) = m_c.split_at_mut(split);
        // r[:n']   r[:n']
        let (r_left, r_right) = m_r.split_at_mut(split);

        let (vk_left, vk_right) = vkey.split(split);

        // since we do this in parallel we take reference first so it can be
        // moved within the macro's rayon scope.
        let (rvk_left, rvk_right) = (&vk_left, &vk_right);
        let (rc_left, rc_right) = (&c_left, &c_right);
        let (rr_left, rr_right) = (&r_left, &r_right);
        // See section 3.3 for paper version with equivalent names
        try_par! {
            // MIPP part
            // Compute cross commitment C^r
            // z_l = c[n':] ^ r[:n']
            // TODO to replace by bitsf_multiexp
            let zc_l = ip::multiexponentiation(rc_right, &rr_left),
            // Z_r = c[:n'] ^ r[n':]
            let zc_r = ip::multiexponentiation(rc_left, &rr_right),
            // Compute C commitment over the distinct halfs of C
            // u_l = c[n':] * v[:n']
            let tuc_l = commitment::single_g1::<E>(&rvk_left, rc_right),
            // u_r = c[:n'] * v[n':]
            let tuc_r = commitment::single_g1::<E>(&rvk_right, rc_left)
        };

        // Fiat-Shamir challenge
        transcript.append(b"zc_l", &zc_l);
        transcript.append(b"zc_r", &zc_r);
        transcript.append(b"tuc_l", &tuc_l);
        transcript.append(b"tuc_r", &tuc_r);
        let c_inv = transcript.challenge_scalar::<E::Fr>(b"challenge_i");

        // Optimization for multiexponentiation to rescale G2 elements with
        // 128-bit challenge Swap 'c' and 'c_inv' since can't control bit size
        // of c_inv
        let c = c_inv.inverse().unwrap();

        // Set up values for next step of recursion
        // c[:n'] + c[n':]^x
        compress(&mut m_c, split, &c);
        compress_field(&mut m_r, split, &c_inv);

        // v_left + v_right^x^-1
        vkey = vk_left.compress(&vk_right, &c_inv)?;

        comms_c.push((tuc_l, tuc_r));
        z_c.push((zc_l.into_affine(), zc_r.into_affine()));
        challenges.push(c);
        challenges_inv.push(c_inv);
    }

    assert!(m_c.len() == 1 && m_r.len() == 1);
    assert!(vkey.a.len() == 1 && vkey.b.len() == 1);

    let final_c = m_c[0];
    let final_vkey = vkey.first();
    println!("PROVER: last challenge {}", challenges.last().unwrap());
    println!("PROVER: last compressed bit {}", m_r.last().unwrap());
    println!("PROVER: last final c {:?}", m_c.last().unwrap());

    Ok((
        GipaProof {
            nproofs: nproofs as u32,
            comms_c,
            z_c,
            final_c,
            final_vkey,
        },
        challenges,
        challenges_inv,
    ))
}

fn prove_commitment_v<G: AffineCurve>(
    srs_powers_alpha_table: &[G],
    srs_powers_beta_table: &[G],
    transcript: &[G::ScalarField],
    kzg_challenge: &G::ScalarField,
) -> Result<KZGOpening<G>, Error> {
    // f_v
    let vkey_poly =
        DensePolynomial::from_coefficients_vec(polynomial_coefficients_from_transcript(transcript));

    // f_v(z)
    let vkey_poly_z =
        polynomial_evaluation_product_form_from_transcript(&transcript, kzg_challenge);
    create_kzg_opening(
        srs_powers_alpha_table,
        srs_powers_beta_table,
        vkey_poly,
        vkey_poly_z,
        kzg_challenge,
    )
}

/// Returns the KZG opening proof for the given commitment key. Specifically, it
/// returns $g^{f(alpha) - f(z) / (alpha - z)}$ for $a$ and $b$.
fn create_kzg_opening<G: AffineCurve>(
    srs_powers_alpha_table: &[G], // h^alpha^i
    srs_powers_beta_table: &[G],  // h^beta^i
    poly: DensePolynomial<G::ScalarField>,
    eval_poly: G::ScalarField,
    kzg_challenge: &G::ScalarField,
) -> Result<KZGOpening<G>, Error> {
    let mut neg_kzg_challenge = *kzg_challenge;
    neg_kzg_challenge = neg_kzg_challenge.neg();

    if poly.coeffs().len() != srs_powers_alpha_table.len() {
        return Err(Error::InvalidSRS(
            format!(
                "SRS len {} != coefficients len {}",
                srs_powers_alpha_table.len(),
                poly.coeffs().len(),
            )
            .to_string(),
        ));
    }

    // f_v(X) - f_v(z) / (X - z)
    let quotient_polynomial = &(&poly - &DensePolynomial::from_coefficients_vec(vec![eval_poly]))
        / &(DensePolynomial::from_coefficients_vec(vec![neg_kzg_challenge, G::ScalarField::one()]));

    let mut quotient_polynomial_coeffs = quotient_polynomial.coeffs;
    quotient_polynomial_coeffs.resize(srs_powers_alpha_table.len(), <G::ScalarField>::zero());
    let quotient_repr = cfg_iter!(quotient_polynomial_coeffs)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();

    assert_eq!(
        quotient_polynomial_coeffs.len(),
        srs_powers_alpha_table.len()
    );
    assert_eq!(
        quotient_polynomial_coeffs.len(),
        srs_powers_beta_table.len()
    );

    // we do one proof over h^a and one proof over h^b (or g^a and g^b depending
    // on the curve we are on). that's the extra cost of the commitment scheme
    // used which is compatible with Groth16 CRS insteaf of the original paper
    // of Bunz'19
    let (a, b) = rayon::join(
        || VariableBaseMSM::multi_scalar_mul(&srs_powers_alpha_table, &quotient_repr),
        || VariableBaseMSM::multi_scalar_mul(&srs_powers_beta_table, &quotient_repr),
    );
    Ok(KZGOpening::new_from_proj(a, b))
}

/// It returns the evaluation of the polynomial $\prod (1 + x_{l-j}(rX)^{2j}$ at
/// the point z, where transcript contains the reversed order of all challenges (the x).
/// THe challenges must be in reversed order for the correct evaluation of the
/// polynomial in O(logn)
pub(super) fn polynomial_evaluation_product_form_from_transcript<F: Field>(
    transcript: &[F],
    z: &F,
) -> F {
    // this is the term (rz) that will get squared at each step to produce the
    // $(rz)^{2j}$ of the formula
    let mut power_zr = *z;

    let one = F::one();

    let mut res = one + transcript[0] * &power_zr;
    for x in &transcript[1..] {
        power_zr = power_zr.square();
        res.mul_assign(one + *x * &power_zr);
    }

    res
}

// Compute the coefficients of the polynomial $\prod_{j=0}^{l-1} (1 + x_{l-j}(rX)^{2j})$
// It does this in logarithmic time directly; here is an example with 2
// challenges:
//
//     We wish to compute $(1+x_1ra)(1+x_0(ra)^2) = 1 +  x_1ra + x_0(ra)^2 + x_0x_1(ra)^3$
//     Algorithm: $c_{-1} = [1]$; $c_j = c_{i-1} \| (x_{l-j} * c_{i-1})$; $r = r*r$
//     $c_0 = c_{-1} \| (x_1 * r * c_{-1}) = [1] \| [rx_1] = [1, rx_1]$, $r = r^2$
//     $c_1 = c_0 \| (x_0 * r^2c_0) = [1, rx_1] \| [x_0r^2, x_0x_1r^3] = [1, x_1r, x_0r^2, x_0x_1r^3]$
//     which is equivalent to $f(a) = 1 + x_1ra + x_0(ra)^2 + x_0x_1r^2a^3$
//
// This method expects the coefficients in reverse order so transcript[i] =
// x_{l-j}.
// f(Y) = Y^n * \prod (1 + x_{l-j-1} (r_shiftY^{2^j}))
fn polynomial_coefficients_from_transcript<F: Field>(transcript: &[F]) -> Vec<F> {
    let mut coefficients = vec![F::one()];
    let mut power_2_r = F::one();

    for (i, x) in transcript.iter().enumerate() {
        let n = coefficients.len();
        if i > 0 {
            power_2_r = power_2_r.square();
        }
        for j in 0..n {
            let coeff = coefficients[j] * &(*x * &power_2_r);
            coefficients.push(coeff);
        }
    }

    coefficients
}

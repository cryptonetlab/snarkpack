use crate::Error;
use crate::{compress, compress_field, ip, Transcript};

use super::commitment;
use ark_ec::ProjectiveCurve;
use ark_ec::{AffineCurve, PairingEngine};
use ark_ff::{Field, PrimeField};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_poly_commit::multilinear_pc::data_structures::{
    Commitment_G2, CommitterKey, Proof, Proof_G1, VerifierKey,
};
use ark_poly_commit::multilinear_pc::MultilinearPC;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::One;
use ark_std::Zero;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::ParallelIterator;
use rayon::prelude::IntoParallelIterator;
use std::ops::{Add, AddAssign, Mul, MulAssign, SubAssign};
#[derive(Debug, Clone, CanonicalDeserialize, CanonicalSerialize)]
pub struct MippProof<E: PairingEngine> {
    pub comms_t: Vec<(<E as PairingEngine>::Fqk, <E as PairingEngine>::Fqk)>,
    pub comms_u: Vec<(E::G1Affine, E::G1Affine)>,
    pub final_a: E::G1Affine,
    pub final_h: E::G2Affine,
    pub pst_proof_h: Proof_G1<E>,
}

impl<E: PairingEngine> MippProof<E> {
    pub fn prove<T: Transcript>(
        transcript: &mut impl Transcript,
        ck: &CommitterKey<E>,
        a: Vec<E::G1Affine>,
        y: Vec<E::Fr>,
        h: Vec<E::G2Affine>,
        U: &E::G1Affine,
        T: &<E as PairingEngine>::Fqk,
    ) -> Result<MippProof<E>, Error> {
        // the values of vectors A and y rescaled at each step of the loop
        let (mut m_a, mut m_y) = (a.clone(), y.clone());
        // the values of the commitment keys h for the vector A rescaled at
        //  each step of the loop
        let mut m_h = h.clone();

        // storing the cross commitments for including in the proofs
        let mut comms_t = Vec::new();
        let mut comms_u = Vec::new();

        // the transcript challenges
        let mut xs: Vec<E::Fr> = Vec::new();
        let mut xs_inv: Vec<E::Fr> = Vec::new();

        transcript.append(b"U", U);

        while m_a.len() > 1 {
            // recursive step
            // Recurse with problem of half size
            let split = m_a.len() / 2;

            // MIPP ///
            // c[:n']   c[n':]
            let (a_l, a_r) = m_a.split_at_mut(split);
            // r[:n']   r[:n']
            let (y_l, y_r) = m_y.split_at_mut(split);

            let (h_l, h_r) = m_h.split_at_mut(split);

            // since we do this in parallel we take reference first so it can be
            // moved within the macro's rayon scope.
            let (rh_l, rh_r) = (&h_l, &h_r);
            let (ra_l, ra_r) = (&a_l, &a_r);
            let (ry_l, ry_r) = (&y_l, &y_r);
            // See section 3.3 for paper version with equivalent names
            try_par! {
                // MIPP part
                // Compute cross commitment U^y
                // u_l = a[n':] ^ y[:n']
                // TODO to replace by bitsf_multiexp
                let comm_u_l = ip::multiexponentiation(ra_l, &ry_r),
                // u_r = a[:n'] ^ y[n':]
                let comm_u_r = ip::multiexponentiation(ra_r, &ry_l)

            };
            // Compute IPP commitment over the distinct halfs of A
            // t_l = a[n':] * h[:n']
            let comm_t_l = commitment::pairings_product::<E>(&ra_l, rh_r);
            // t_r = a[:n'] * h[n':]
            let comm_t_r = commitment::pairings_product::<E>(&ra_r, rh_l);

            // Fiat-Shamir challenge
            transcript.append(b"comm_u_l", &comm_u_l);
            transcript.append(b"comm_u_r", &comm_u_r);
            transcript.append(b"comm_t_l", &comm_t_l);
            transcript.append(b"comm_t_r", &comm_t_r);
            let c_inv = transcript.challenge_scalar::<E::Fr>(b"challenge_i");

            // Optimization for multiexponentiation to rescale G2 elements with
            // 128-bit challenge Swap 'c' and 'c_inv' since we
            // can't control bit size of c_inv
            let c = c_inv.inverse().unwrap();

            // Set up values for next step of recursion
            // a[n':] + a[:n']^x
            compress(&mut m_a, split, &c);
            compress_field(&mut m_y, split, &c_inv);

            // h[n':] + h[:n']^x_inv
            compress(&mut m_h, split, &c_inv);

            comms_t.push((comm_t_l, comm_t_r));
            comms_u.push((comm_u_l.into_affine(), comm_u_r.into_affine()));
            xs.push(c);
            xs_inv.push(c_inv);
        }

        assert!(m_a.len() == 1 && m_y.len() == 1 && m_h.len() == 1);

        let final_a = m_a[0];
        let final_h = m_h[0];

        // get polynomial f_h
        let poly = DenseMultilinearExtension::<E::Fr>::from_evaluations_vec(
            xs_inv.len(),
            Self::polynomial_evaluations_from_transcript::<E::Fr>(&xs_inv),
        );
        let c = MultilinearPC::<E>::commit_g2(ck, &poly);
        debug_assert!(c.h_product == final_h);

        // create proof that final_h is well-formed
        let mut point: Vec<E::Fr> = (0..poly.num_vars)
            .into_iter()
            .map(|_| transcript.challenge_scalar::<E::Fr>(b"random_point"))
            .collect();

        let pst_proof_h = MultilinearPC::<E>::open_g1(ck, &poly, &point);

        // println!("PROVER: last challenge {}", xs.last().unwrap());
        // println!("PROVER: last y {}", m_y.last().unwrap());
        // println!("PROVER: last final c {:?}", m_a.last().unwrap());

        Ok((MippProof {
            comms_t,
            comms_u,
            final_a,
            final_h,
            pst_proof_h,
        }))
    }

    fn polynomial_evaluations_from_transcript<F: Field>(cs_inv: &[F]) -> Vec<F> {
        let m = cs_inv.len();
        let pow_m = 2_usize.pow(m as u32);

        let evals = (0..pow_m)
            .into_par_iter()
            .map(|i| {
                let mut res = F::one();
                for j in 0..m {
                    if (i >> j) & 1 == 1 {
                        res *= cs_inv[m - j - 1];
                    }
                }
                res
            })
            .collect();
        evals
    }

    pub fn verify<T: Transcript>(
        vk: &VerifierKey<E>,
        transcript: &mut impl Transcript,
        proof: &MippProof<E>,
        point: Vec<E::Fr>,
        U: &E::G1Affine,
        T: &<E as PairingEngine>::Fqk,
    ) -> bool {
        let comms_u = proof.comms_u.clone();
        let comms_t = proof.comms_t.clone();

        let mut xs = Vec::new();
        let mut xs_inv = Vec::new();
        let mut final_y = E::Fr::one();

        let mut final_res = MippTU {
            tc: T.clone(),
            uc: U.into_projective(),
        };

        transcript.append(b"U", U);

        // Challenges need to be generated first in sequential order so the
        // prover and the verifier have a consistent view of the transcript
        for (i, (comm_u, comm_t)) in comms_u.iter().zip(comms_t.iter()).enumerate() {
            let (comm_u_l, comm_u_r) = comm_u;
            let (comm_t_l, comm_t_r) = comm_t;

            // Fiat-Shamir challenge
            transcript.append(b"comm_u_l", comm_u_l);
            transcript.append(b"comm_u_r", comm_u_r);
            transcript.append(b"comm_t_l", comm_t_l);
            transcript.append(b"comm_t_r", comm_t_r);
            let c_inv = transcript.challenge_scalar::<E::Fr>(b"challenge_i");

            let c = c_inv.inverse().unwrap();
            xs.push(c);
            xs_inv.push(c_inv);

            // the verifier computes the final_y by themselves given
            // it's field operations it is quite fast and parallelisation
            // doesn't bring much improvement
            final_y *= E::Fr::one() + c_inv.mul(point[i]) - point[i];
        }
        enum Op<'a, E: PairingEngine> {
            TC(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
            UC(&'a E::G1Affine, <E::Fr as PrimeField>::BigInt),
        }

        let res = comms_t
            .par_iter()
            .zip(comms_u.par_iter())
            .zip(xs.par_iter().zip(xs_inv.par_iter()))
            .flat_map(|((comm_t, comm_u), (c, c_inv))| {
                let (comm_t_l, comm_t_r) = comm_t;
                let (comm_u_l, comm_u_r) = comm_u;

                let c_repr = c.into_repr();
                let c_inv_repr = c_inv.into_repr();

                // we multiple left side by x^-1 and right side by x
                vec![
                    Op::TC::<E>(comm_t_l, c_inv_repr),
                    Op::TC(comm_t_r, c_repr),
                    Op::UC(comm_u_l, c_inv_repr),
                    Op::UC(comm_u_r, c_repr),
                ]
            })
            .fold(MippTU::<E>::default, |mut res, op: Op<E>| {
                match op {
                    Op::TC(tx, c) => {
                        let tx: E::Fqk = tx.pow(c);
                        res.tc.mul_assign(&tx);
                    }
                    Op::UC(zx, c) => {
                        let uxp: E::G1Projective = zx.mul(c);
                        res.uc.add_assign(&uxp);
                    }
                }
                res
            })
            .reduce(MippTU::default, |mut acc_res, res| {
                acc_res.merge(&res);
                acc_res
            });

        // the initial values of T and U are merged to get the final result
        let ref_final_res = &mut final_res;
        ref_final_res.merge(&res);

        let mut point: Vec<E::Fr> = Vec::new();
        let m = xs_inv.len();
        for i in 0..m {
            let r = transcript.challenge_scalar::<E::Fr>(b"random_point");
            point.push(r);
        }
        let v = (0..m)
            .into_par_iter()
            .map(|i| E::Fr::one() + point[i].mul(xs_inv[m - i - 1]) - point[i])
            .product();

        let comm_h = Commitment_G2 {
            nv: m,
            h_product: proof.final_h,
        };
        let check_h = MultilinearPC::<E>::check_2(vk, &comm_h, &point, v, &proof.pst_proof_h);

        let final_u = proof.final_a.mul(final_y);
        let final_t: <E as PairingEngine>::Fqk = E::pairing(proof.final_a, proof.final_h);

        let check_t = ref_final_res.tc == final_t;

        let check_u = ref_final_res.uc == final_u;

        check_h & check_u & check_t
    }
}

/// Keeps track of the variables that have been sent by the prover and must
/// be multiplied together by the verifier.
struct MippTU<E: PairingEngine> {
    pub tc: E::Fqk,
    pub uc: E::G1Projective,
}

impl<E> Default for MippTU<E>
where
    E: PairingEngine,
{
    fn default() -> Self {
        Self {
            tc: E::Fqk::one(),
            uc: E::G1Projective::zero(),
        }
    }
}

impl<E> MippTU<E>
where
    E: PairingEngine,
{
    fn merge(&mut self, other: &Self) {
        self.tc.mul_assign(&other.tc);
        self.uc.add_assign(&other.uc);
    }
}

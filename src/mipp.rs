use crate::Error;
use crate::{compress, compress_field, ip, Transcript};

use super::commitment;
use ark_ec::ProjectiveCurve;
use ark_ec::{AffineCurve, PairingEngine};
use ark_ff::{Field, PrimeField};
use ark_std::One;
use std::ops::Mul;

#[derive(Debug, Clone)]
pub struct MippProof<E: PairingEngine> {
    pub comms_t: Vec<(<E as PairingEngine>::Fqk, <E as PairingEngine>::Fqk)>,
    pub comms_u: Vec<(E::G1Affine, E::G1Affine)>,
    pub final_a: E::G1Affine,
    pub final_h: E::G2Affine,
}

impl<E: PairingEngine> MippProof<E> {
    pub fn prove<T: Transcript>(
        transcript: &mut impl Transcript,
        a: Vec<E::G1Affine>,
        y: Vec<E::Fr>,
        h: Vec<E::G2Affine>,
        U: &E::G1Affine,
        T: &<E as PairingEngine>::Fqk,
    ) -> Result<MippProof<E>, Error> {
        // let nproofs = keys.len();
        // the values of vectors C and bits rescaled at each step of the loop
        // these are A and y
        let (mut m_a, mut m_y) = (a, y);
        // the values of the commitment keys rescaled at each step of the loop
        // these are the h for me
        let mut m_h = h.clone();

        // storing the values for including in the proof
        // these are T_l and T_r
        let mut comms_t = Vec::new();
        // these are U_l and U_r
        let mut comms_u = Vec::new();
        // these are the x-es
        let mut xs: Vec<E::Fr> = Vec::new();
        let mut xs_inv: Vec<E::Fr> = Vec::new();

        // we already appended t
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
                // Compute cross commitment C^r
                // z_l = c[n':] ^ r[:n']
                // TODO to replace by bitsf_multiexp
                let comm_u_l = ip::multiexponentiation(ra_l, &ry_r),
                // Z_r = c[:n'] ^ r[n':]
                let comm_u_r = ip::multiexponentiation(ra_r, &ry_l)
            };
            // Compute C commitment over the distinct halfs of C
            // u_l = c[n':] * v[:n']
            let comm_t_l = commitment::pairings_product::<E>(&ra_l, rh_r);
            // u_r = c[:n'] * v[n':]
            let comm_t_r = commitment::pairings_product::<E>(&ra_r, rh_l);

            // Fiat-Shamir challenge
            transcript.append(b"comm_u_l", &comm_u_l);
            transcript.append(b"comm_u_r", &comm_u_r);
            transcript.append(b"comm_t_l", &comm_t_l);
            transcript.append(b"comm_t_r", &comm_t_r);
            let c_inv = transcript.challenge_scalar::<E::Fr>(b"challenge_i");

            // Optimization for multiexponentiation to rescale G2 elements with
            // 128-bit challenge Swap 'c' and 'c_inv' since can't control bit size
            // of c_inv
            let c = c_inv.inverse().unwrap();

            // Set up values for next step of recursion
            // c[:n'] + c[n':]^x
            compress(&mut m_a, split, &c);
            compress_field(&mut m_y, split, &c_inv);

            // v_left + v_right^x^-1
            compress(&mut m_h, split, &c_inv);

            comms_t.push((comm_t_l, comm_t_r));
            comms_u.push((comm_u_l.into_affine(), comm_u_r.into_affine()));
            xs.push(c);
            xs_inv.push(c_inv);
        }

        // TODO: do h stuff

        assert!(m_a.len() == 1 && m_y.len() == 1 && m_h.len() == 1);

        let final_a = m_a[0];
        let final_h = m_h[0];
        println!("PROVER: last challenge {}", xs.last().unwrap());
        println!("PROVER: last compressed bit {}", m_y.last().unwrap());
        println!("PROVER: last final c {:?}", m_a.last().unwrap());

        Ok((MippProof {
            comms_t,
            comms_u,
            final_a,
            final_h,
        }))
    }

    pub fn verify<T: Transcript>(
        transcript: &mut impl Transcript,
        proof: &MippProof<E>,
        point: Vec<E::Fr>,
        U: &E::G1Affine,
        T: &<E as PairingEngine>::Fqk,
    ) -> bool {
        let comms_u = proof.comms_u.clone();
        let comms_t = proof.comms_t.clone();

        // let xs = Vec::new();
        // let xs_inv = Vec::new();
        let mut final_y = E::Fr::one();
        let mut u_prime = U.clone().into_projective();
        let mut t_prime = T.clone();

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

            final_y *= E::Fr::one() - point[i] + c_inv.mul(point[i]);
            let c_repr = c.into_repr();
            let c_inv_repr = c_inv.into_repr();

            let (comm_u_l_proj, comm_u_r_proj) =
                (comm_u_l.into_projective(), comm_u_r.into_projective());

            u_prime += comm_u_l_proj.mul(c_inv_repr) + comm_u_r_proj.mul(c_repr);
            t_prime *= comm_t_l.pow(c_inv_repr) * comm_t_r.pow(c_repr);
        }

        // TODO: prove that h is correct

        let final_u = proof.final_a.mul(final_y);
        let final_t = E::pairing(proof.final_a, proof.final_h);

        let check1 = u_prime == final_u;
        let check2 = t_prime == final_t;

        check1 & check2
    }
}

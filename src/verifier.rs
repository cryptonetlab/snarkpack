use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_std::{rand::Rng, sync::Mutex, One, Zero};
use crossbeam_channel::{bounded, Sender};
use rayon::prelude::*;
use std::ops::{AddAssign, MulAssign, Neg, SubAssign};

use super::{
    commitment::Output,
    pairing_check::PairingCheck,
    proof::{AggregateProof, KZGOpening},
    prover::polynomial_evaluation_product_form_from_transcript,
    srs::VerifierSRS,
    transcript::Transcript,
};
use crate::{Error, compress_field};

use std::default::Default;
use std::time::Instant;

/// Verifies the aggregated proofs thanks to the Groth16 verifying key, the
/// verifier SRS from the aggregation scheme, all the public inputs of the
/// proofs and the aggregated proof.
///
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
pub fn verify_aggregate_proof<
    E: PairingEngine + std::fmt::Debug,
    R: Rng + Send,
    T: Transcript + Send,
>(
    ip_verifier_srs: &VerifierSRS<E>,
    proof: &AggregateProof<E>,
    bits: Vec<bool>,
    rng: R,
    mut transcript: &mut T,
) -> Result<(), Error> {
    dbg!("verify aggregate keys");
    proof.parsing_check()?;

    let mut_rng = Mutex::new(rng);

    // channels to send/recv pairing checks so we aggregate them all in a
    // loop - 9 places where we send pairing checks
    let (send_checks, rcv_checks) = bounded(9);
    // channel to receive the final results so aggregate waits on all.
    let (valid_send, valid_rcv) = bounded(1);
    rayon::scope(move |s| {
        // Continuous loop that aggregate pairing checks together
        s.spawn(move |_| {
            let mut acc = PairingCheck::new();
            while let Ok(tuple) = rcv_checks.recv() {
                acc.merge(&tuple);
            }
            valid_send.send(acc.verify()).unwrap();
        });

        // 2.Check MIPP proof c
        let checkclone = send_checks.clone();
        s.spawn(move |_| {
            let now = Instant::now();
            verify_mipp::<E, R, T>(
                ip_verifier_srs,
                proof,
                bits,
                &mut transcript,
                &mut_rng,
                checkclone,
            );
            dbg!("TIPP took {} ms", now.elapsed().as_millis(),);
        });
    });
    let res = valid_rcv.recv().unwrap();
    dbg!(format!("aggregate verify done: valid ? {}", res));
    match res {
        true => Ok(()),
        false => Err(Error::InvalidProof("Proof Verification Failed".to_string())),
    }
}

/// verify_mipp returns a pairing equation to check the tipp proof.  $r$ is
/// the randomness used to produce a random linear combination of A and B and
/// used in the MIPP part with C
fn verify_mipp<E: PairingEngine, R: Rng + Send, T: Transcript + Send>(
    v_srs: &VerifierSRS<E>,
    proof: &AggregateProof<E>,
    bits: Vec<bool>,
    transcript: &mut T,
    rng: &Mutex<R>,
    checks: Sender<PairingCheck<E>>,
) {
    dbg!("verify with srs shift");
    let now = Instant::now();
    // (T,U), Z for MIPP  and all challenges
    let (final_res,final_b, challenges, challenges_inv) =
        gipa_verify_mipp(&proof, bits, transcript);
    dbg!(
        "TIPP verify: gipa verify tipp {}ms",
        now.elapsed().as_millis()
    );

    // Verify commitment keys wellformed
    let fvkey = proof.tmipp.gipa.final_vkey;
    // KZG challenge point
    transcript.append(b"kzg-challenge", &challenges[0]);
    transcript.append(b"vkey0", &proof.tmipp.gipa.final_vkey.0);
    transcript.append(b"vkey1", &proof.tmipp.gipa.final_vkey.1);
    let c = transcript.challenge_scalar::<E::Fr>(b"z-challenge");
    // we take reference so they are able to be copied in the par! macro
    let final_c = &proof.tmipp.gipa.final_c;
    let final_tc = &final_res.tc;
    let final_uc = &final_res.uc;

    let vclone = checks.clone();
    let now = Instant::now();
    par! {
        // check the opening proof for v
        let _vtuple = verify_kzg_v(
            v_srs,
            &fvkey,
            &proof.tmipp.vkey_opening,
            &challenges_inv,
            &c,
            rng,
            vclone,
        ),
        // We create a sequence of pairing tuple that we aggregate together at
        // the end to perform only once the final exponentiation.
        // MIPP
        // Verify base inner product commitment
        // Z ==  c ^ r
        let final_z = final_c.mul(final_b.into_repr()),
        // Check commiment correctness
        // T = e(C,v1)
        //let _check_t = tclone.send(PairingCheck::rand(&rng,&[(final_c,&fvkey.0)],final_tc)).unwrap(),
        let pcheckt = PairingCheck::rand(&rng,&[(final_c,&fvkey.0)],final_tc),
        // U = e(A,v2)
        //let _check_u = uclone.send(PairingCheck::rand(&rng,&[(final_c,&fvkey.1)],final_uc)).unwrap()
        let pchecku = PairingCheck::rand(&rng,&[(final_c,&fvkey.1)],final_uc)
    };

    checks.send(pcheckt).unwrap();
    checks.send(pchecku).unwrap();
    dbg!(format!(
        "TIPP verify: parallel checks before merge: {}ms",
        now.elapsed().as_millis()
    ));
    // only check that doesn't require pairing so we can give a tuple
    // that will render the equation wrong in case it's false
    if final_z != final_res.zc {
        dbg!(format!(
            "tipp verify: INVALID final_z check {} vs {}",
            final_z, final_res.zc
        ));
        checks.send(PairingCheck::new_invalid()).unwrap()
    }
}

/// gipa_verify_mipp recurse on the proof and statement and produces the final
/// values to be checked by TIPP and MIPP verifier, namely, for TIPP for example:
/// * T,U: the final commitment values of A and B
/// * Z the final product between A and B.
/// * Challenges are returned in inverse order as well to avoid
/// repeating the operation multiple times later on.
/// * There are T,U,Z vectors as well for the MIPP relationship. Both TIPP and
/// MIPP share the same challenges however, enabling to re-use common operations
/// between them, such as the KZG proof for commitment keys.
fn gipa_verify_mipp<E: PairingEngine, T: Transcript + Send>(
    proof: &AggregateProof<E>,
    bits: Vec<bool>,
    transcript: &mut T,
) -> (GipaTUZ<E>, E::Fr, Vec<E::Fr>, Vec<E::Fr>) {
    dbg!("gipa verify TIPP");
    let mut bits_f = bits.par_iter().map(|b| E::Fr::from(*b)).collect::<Vec<_>>();
    let gipa = &proof.tmipp.gipa;
    // COM(C,r) = SUM C^r given by prover
    let comms_c = &gipa.comms_c;
    // Z vectors coming from the GIPA proofs
    let zs_c = &gipa.z_c;

    let now = Instant::now();

    let mut challenges = Vec::new();
    let mut challenges_inv = Vec::new();

    transcript.append(b"comm-c", &proof.agg_c);

    // We first generate all challenges as this is the only consecutive process
    // that can not be parallelized then we scale the commitments in a
    // parallelized way
    for (_i, (comm_c, z_c)) in comms_c.iter().zip(zs_c.iter())
        .enumerate()
    {
        let split = bits_f.len() / 2;

        let (tuc_l, tuc_r) = comm_c;
        let (zc_l, zc_r) = z_c;

        // Fiat-Shamir challenge
        transcript.append(b"zc_l", zc_l);
        transcript.append(b"zc_r", zc_r);
        transcript.append(b"tuc_l", tuc_l);
        transcript.append(b"tuc_r", tuc_r);
        let c_inv = transcript.challenge_scalar::<E::Fr>(b"challenge_i");
        let c = c_inv.inverse().unwrap();
        // the verifier recomputes the final b value manually - which is O(N) but
        // this is only field operations so this can be done quite fast.
        // TODO make it in a separate thread after the challenge generation instead of blocking the rest
        compress_field(&mut bits_f, split, &c);
        challenges.push(c);
        challenges_inv.push(c_inv);
    }

    println!("VERIFIER: last challenge {}",challenges.last().unwrap());
    println!("VERIFIER: last compressed bit {}",bits_f.last().unwrap());
    println!("PROVER: last final c {:?}", gipa.final_c);

    dbg!(
        "TIPP verify: gipa challenge gen took {}ms",
        now.elapsed().as_millis()
    );

    assert!(bits_f.len() == 1,"recursion loop pow2 error");
    let final_b = *bits_f.last().unwrap();
    let now = Instant::now();
    // COM(v,C)
    //let (t_c, u_c) = (comc2.0, comc2.1);
    let Output { 0: t_c, 1: u_c } = proof.com_c.clone();
    let z_c = proof.agg_c.into_projective(); // in the end must be equal to Z = C^r

    let mut final_res = GipaTUZ {
        tc: t_c,
        uc: u_c,
        zc: z_c,
    };

    // we first multiply each entry of the Z U and L vectors by the respective
    // challenges independently
    // Since at the end we want to multiple all "t" values together, we do
    // multiply all of them in parrallel and then merge then back at the end.
    // same for u and z.
    enum Op<'a, E: PairingEngine> {
        TC(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
        UC(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
        ZC(&'a E::G1Affine, <E::Fr as PrimeField>::BigInt),
    }

    let res = 
        comms_c.par_iter().zip(zs_c.par_iter())
        .zip(challenges.par_iter().zip(challenges_inv.par_iter()))
        .flat_map(|((comm_c, z_c), (c, c_inv))| {
            // T and U values for right and left for C part
            let (Output { 0: tc_l, 1: uc_l }, Output { 0: tc_r, 1: uc_r }) = comm_c;
            let (zc_l, zc_r) = z_c;

            let c_repr = c.into_repr();
            let c_inv_repr = c_inv.into_repr();

            // we multiple left side by x and right side by x^-1
            vec![
                Op::TC::<E>(tc_l, c_repr),
                Op::TC(tc_r, c_inv_repr),
                Op::UC(uc_l, c_repr),
                Op::UC(uc_r, c_inv_repr),
                Op::ZC(zc_l, c_repr),
                Op::ZC(zc_r, c_inv_repr),
            ]
        })
        .fold(GipaTUZ::<E>::default, |mut res, op: Op<E>| {
            match op {
                Op::TC(tx, c) => {
                    let tx: E::Fqk = tx.pow(c);
                    res.tc.mul_assign(&tx);
                }
                Op::UC(ux, c) => {
                    let ux: E::Fqk = ux.pow(c);
                    res.uc.mul_assign(&ux);
                }
                Op::ZC(zx, c) => {
                    // TODO replace by MSM ?
                    let zxp: E::G1Projective = zx.mul(c);
                    res.zc.add_assign(&zxp);
                }
            }
            res
        })
        .reduce(GipaTUZ::default, |mut acc_res, res| {
            acc_res.merge(&res);
            acc_res
        });
    // we reverse the order because the polynomial evaluation routine expects
    // the challenges in reverse order.Doing it here allows us to compute the final_r
    // in log time. Challenges are used as well in the KZG verification checks.
    challenges.reverse();
    challenges_inv.reverse();

    let ref_final_res = &mut final_res;

    ref_final_res.merge(&res);

    dbg!(
        "TIPP verify: gipa prep and accumulate took {}ms",
        now.elapsed().as_millis()
    );
    (final_res, final_b, challenges, challenges_inv)
}

/// verify_kzg_opening_g2 takes a KZG opening, the final commitment key, SRS and
/// any shift (in TIPP we shift the v commitment by r^-1) and returns a pairing
/// tuple to check if the opening is correct or not.
pub fn verify_kzg_v<E: PairingEngine, R: Rng + Send>(
    v_srs: &VerifierSRS<E>,
    final_vkey: &(E::G2Affine, E::G2Affine),
    vkey_opening: &KZGOpening<E::G2Affine>,
    challenges: &[E::Fr],
    kzg_challenge: &E::Fr,
    rng: &Mutex<R>,
    checks: Sender<PairingCheck<E>>,
) {
    // f_v(z)
    let vpoly_eval_z = polynomial_evaluation_product_form_from_transcript(
        challenges,
        kzg_challenge,
    );
    // -g such that when we test a pairing equation we only need to check if
    // it's equal 1 at the end:
    // e(a,b) = e(c,d) <=> e(a,b)e(-c,d) = 1
    let ng = v_srs.g.neg();
    // e(A,B) = e(C,D) <=> e(A,B)e(-C,D) == 1 <=> e(A,B)e(C,D)^-1 == 1
    let ng = ng.into_affine();

    let v1clone = checks.clone();
    let v2clone = checks.clone();

    par! {
        // e(g, C_f * h^{-y}) == e(v1 * g^{-x}, \pi) = 1
        let _check1 = kzg_check_v::<E, R>(
            v_srs,
            ng,
            *kzg_challenge,
            vpoly_eval_z,
            final_vkey.0.into_projective(),
            v_srs.g_alpha,
            vkey_opening.0,
            &rng,
            v1clone,
        ),

        // e(g, C_f * h^{-y}) == e(v2 * g^{-x}, \pi) = 1
        let _check2 = kzg_check_v::<E, R>(
            v_srs,
            ng,
            *kzg_challenge,
            vpoly_eval_z,
            final_vkey.1.into_projective(),
            v_srs.g_beta,
            vkey_opening.1,
            &rng,
            v2clone,
        )
    };
}

fn kzg_check_v<E: PairingEngine, R: Rng + Send>(
    v_srs: &VerifierSRS<E>,
    ng: E::G1Affine,
    x: E::Fr,
    y: E::Fr,
    cf: E::G2Projective,
    vk: E::G1Projective,
    pi: E::G2Affine,
    rng: &Mutex<R>,
    checks: Sender<PairingCheck<E>>,
) {
    // KZG Check: e(g, C_f * h^{-y}) = e(vk * g^{-x}, \pi)
    // Transformed, such that
    // e(-g, C_f * h^{-y}) * e(vk * g^{-x}, \pi) = 1

    // C_f - (y * h)
    let b = sub!(cf, &mul!(v_srs.h, y)).into_affine();

    // vk - (g * x)
    let c = sub!(vk, &mul!(v_srs.g, x)).into_affine();
    let p = PairingCheck::rand(&rng, &[(&ng, &b), (&c, &pi)], &E::Fqk::one());
    checks.send(p).unwrap();
}

/// Keeps track of the variables that have been sent by the prover and must
/// be multiplied together by the verifier. Both MIPP and TIPP are merged
/// together.
struct GipaTUZ<E: PairingEngine> {
    pub tc: E::Fqk,
    pub uc: E::Fqk,
    pub zc: E::G1Projective,
}

impl<E> Default for GipaTUZ<E>
where
    E: PairingEngine,
{
    fn default() -> Self {
        Self {
            tc: E::Fqk::one(),
            uc: E::Fqk::one(),
            zc: E::G1Projective::zero(),
        }
    }
}

impl<E> GipaTUZ<E>
where
    E: PairingEngine,
{
    fn merge(&mut self, other: &Self) {
        self.tc.mul_assign(&other.tc);
        self.uc.mul_assign(&other.uc);
        self.zc.add_assign(&other.zc);
    }
}

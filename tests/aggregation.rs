use ark_bls12_381::{Bls12_381, G1Projective, G1Affine, Fr};
use ark_ff::One;
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_ff::UniformRand;
use ark_ec::ProjectiveCurve;
use snarkpack;
use snarkpack::transcript::Transcript;

use rand_core::SeedableRng;

#[test]
fn bls_aggregation() {
    let nkeys = 8;
    let mut rng = rand_chacha::ChaChaRng::seed_from_u64(1u64);
    let srs = snarkpack::srs::setup_fake_srs::<Bls12_381, _>(&mut rng, nkeys);
    let (prover_srs, ver_srs) = srs.specialize(nkeys);
    // create all the keys
    let keys = (0..nkeys)
        .map(|_|  G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();
    let bitset = vec![true; nkeys];

    let mut prover_transcript = snarkpack::transcript::new_merlin_transcript(b"test aggregation");
    let aggregate_proof = snarkpack::aggregate_keys(
        &prover_srs, 
        &mut prover_transcript, 
    bitset.clone(), keys).expect("error in aggregation");

    let mut ver_transcript = snarkpack::transcript::new_merlin_transcript(b"test aggregation");
    snarkpack::verify_aggregate_proof(
        &ver_srs,
        &aggregate_proof,
        bitset,
        &mut rng,
        &mut ver_transcript,
    )
    .expect("error in verification");
}

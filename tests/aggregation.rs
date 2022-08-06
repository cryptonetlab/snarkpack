use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective};
use ark_ec::ProjectiveCurve;
use ark_ff::One;
use ark_ff::UniformRand;
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use snarkpack;
use snarkpack::transcript::Transcript;
use snarkpack::commitment::single_g1;

use rand::Rng;
use rand_core::SeedableRng;
use std::time::Instant;

macro_rules! timer {
    ($e:expr) => {{
        let before = Instant::now();
        let ret = $e;
        (
            ret,
            (before.elapsed().as_secs() * 1000 as u64 + before.elapsed().subsec_millis() as u64),
        )
    }};
}

#[test]
fn small_test() {
    bls_aggregation(8, 3);
}

#[test]
fn big_test() {
    bls_aggregation(16384, 500)
}

fn bls_aggregation(nkeys: usize, absent: usize) {
    let mut rng = rand_chacha::ChaChaRng::seed_from_u64(1u64);
    let srs = snarkpack::srs::setup_fake_srs::<Bls12_381, _>(&mut rng, nkeys);
    let (prover_srs, ver_srs) = srs.specialize(nkeys);
    // create all the keys
    let keys = (0..nkeys)
        .map(|_| G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();
    let mut bitset = vec![true; nkeys];
    // create some absent keys
    (0..absent).for_each(|_| {
        let idx = rng.gen_range(0..nkeys);
        bitset[idx] = false;
    });
    // Precompute commitment to the keys
    // (T,U) = Com(v, C)
    let (com_c ,tcomm) = timer!(single_g1::<Bls12_381>(&prover_srs.vkey, &keys).unwrap());
    // Precompute aggregate keys with bitfield
    // Z = SUM C_i ^ b_i
    let (agg_c ,taggc) = timer!(snarkpack::ip::bit_multiexp(&bitset, &keys).unwrap());

    let mut prover_transcript = snarkpack::transcript::new_merlin_transcript(b"test aggregation");

    let (aggregate_proof ,tprover)= timer!(snarkpack::aggregate_keys(
        &prover_srs,
        &mut prover_transcript,
        bitset.clone(),
        keys.clone(),
        com_c,
        agg_c,
    )
    .expect("error in aggregation"));

    let mut buff = Vec::new();
    aggregate_proof.write(&mut buff).unwrap();
    let mut ver_transcript = snarkpack::transcript::new_merlin_transcript(b"test aggregation");
    let (_,tverify) = timer!(snarkpack::verify_aggregate_proof(
        &ver_srs,
        &aggregate_proof,
        bitset,
        &mut rng,
        &mut ver_transcript,
    )
    .expect("error in verification"));

    println!("\n\n------------- BENCHMARK --------------\n");
    println!("- Number of keys aggregating: {} ",nkeys);
    println!("- Number of absent keys (bit false): {} ",absent);
    println!("- Size of proof: {} bytes",buff.len());
    println!("- Time generating commitment: {} ms",tcomm);
    println!("- Time generating aggregate key: {} ms",taggc);
    println!("- Time generating IPP proof: {} ms", tprover);
    println!("- Time verifying IPP proof: {} ms",tverify);
    println!("\n----------------------------------------\n");

}

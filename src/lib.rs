#[macro_use]
mod macros;

mod commitment;
mod errors;
mod ip;
mod pairing_check;
mod proof;
mod prover;
pub mod srs;
pub mod transcript;
mod verifier;

pub use errors::*;
pub use prover::*;
pub use transcript::*;
pub use verifier::*;

use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{PrimeField};
use rayon::prelude::*;

/// compress is similar to commit::{V,W}KEY::compress: it modifies the `vec`
/// vector by setting the value at index $i:0 -> split$  $vec[i] = vec[i] +
/// vec[i+split]^scaler$. The `vec` vector is half of its size after this call.
pub(crate) fn compress<C: AffineCurve>(vec: &mut Vec<C>, split: usize, scaler: &C::ScalarField) {
    let (left, right) = vec.split_at_mut(split);
    left.par_iter_mut()
        .zip(right.par_iter())
        .for_each(|(a_l, a_r)| {
            // TODO remove that with master version
            let mut x = a_r.mul(scaler.into_repr());
            x.add_assign_mixed(&a_l);
            *a_l = x.into_affine();
        });
    let len = left.len();
    vec.resize(len, C::zero());
}

// TODO make that generic with points as well
pub(crate) fn compress_field<F: PrimeField>(vec: &mut Vec<F>, split: usize, scaler: &F) {
    let (left, right) = vec.split_at_mut(split);
    left.par_iter_mut()
        .zip(right.par_iter())
        .for_each(|(a_l, a_r)| {
            // TODO remove copy
            *a_l = *a_l + *a_r * scaler;
        });
    let len = left.len();
    vec.resize(len, F::zero());
}
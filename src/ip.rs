use crate::Error;
use std::ops::AddAssign;
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_std::{cfg_iter, vec::Vec};
use ark_std::Zero;
use rayon::prelude::*;

pub(crate) fn pairing_miller_affine<E: PairingEngine>(
    left: &[E::G1Affine],
    right: &[E::G2Affine],
) -> Result<E::Fqk, Error> {
    if left.len() != right.len() {
        return Err(Error::InvalidIPVectorLength);
    }
    let pairs: Vec<(E::G1Prepared, E::G2Prepared)> = left
        .par_iter()
        .map(|e| E::G1Prepared::from(*e))
        .zip(right.par_iter().map(|e| E::G2Prepared::from(*e)))
        .collect::<Vec<_>>();

    Ok(E::miller_loop(pairs.iter()))
}

/// Returns the miller loop result of the inner pairing product
pub(crate) fn pairing<E: PairingEngine>(
    left: &[E::G1Affine],
    right: &[E::G2Affine],
) -> Result<E::Fqk, Error> {
    E::final_exponentiation(&pairing_miller_affine::<E>(left, right)?).ok_or(Error::InvalidPairing)
}

pub fn bit_multiexp<G: AffineCurve>(bits: &[bool], points: &[G]) -> Result<G,Error> {
    if bits.len() != points.len() {
        return Err(Error::InvalidIPVectorLength);
    }
    Ok(bits.par_iter().zip(points.par_iter())
        .filter(|(b,_)| **b)
        .fold(|| G::Projective::zero(), |mut acc,(_,e)| {
        acc.add_assign_mixed(e);
        acc
    }).reduce(|| G::Projective::zero(), |mut acc, p| { 
        acc.add_assign(p);
        acc
    }).into_affine())
 
}

pub(crate) fn bitsf_multiexp<G: AffineCurve>(bits: &[G::ScalarField], points: &[G]) -> Result<G,Error> {
    if bits.len() != points.len() {
        return Err(Error::InvalidIPVectorLength);
    }
    Ok(bits.par_iter()
        .zip(points.par_iter())
        .filter(|(b,_)| 
            b.is_zero())
        .fold(|| G::Projective::zero(), |mut acc,(_,p)| {
        acc.add_assign_mixed(p);
        acc
    }).reduce(|| G::Projective::zero(), |mut acc, p| { 
        acc.add_assign(p);
        acc
    }).into_affine())
}


pub(crate) fn multiexponentiation<G: AffineCurve>(
    left: &[G],
    right: &[G::ScalarField],
) -> Result<G::Projective, Error> {
    if left.len() != right.len() {
        return Err(Error::InvalidIPVectorLength);
    }

    Ok(VariableBaseMSM::multi_scalar_mul(
        left,
        &cfg_iter!(right).map(|s| s.into_repr()).collect::<Vec<_>>(),
    ))
}
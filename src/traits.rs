use ark_crypto_primitives::{
    crh::{CRHScheme, CRHSchemeGadget},
    merkle_tree::{constraints::ConfigGadget, Config},
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Merkle tree has two types of hashes.
/// * `LeafHash`: Convert leaf to leaf digest
/// * `NToOneHash`: Compress N inner digests to one inner digest
pub trait NAryConfig<const N: usize, P: Config> {
    type NToOneHashParams: Clone + CanonicalSerialize + CanonicalDeserialize + Sync;
    type NToOneHash: CRHScheme<
        Input = [P::InnerDigest],
        Output = P::InnerDigest,
        Parameters = Self::NToOneHashParams,
    >;
}

pub trait NAryConfigGadget<
    const N: usize,
    P: Config,
    F: PrimeField,
    PG: ConfigGadget<P, F>,
    NP: NAryConfig<N, P>,
>
{
    type NToOneHash: CRHSchemeGadget<
        <NP as NAryConfig<N, P>>::NToOneHash,
        F,
        InputVar = [PG::InnerDigest],
        OutputVar = PG::InnerDigest,
    >;
}

pub trait NArySparseConfig<const N: usize, P: Config>: NAryConfig<N, P> {
    // NOTE: n leaves will be N^{HEIGHT - 1}
    const HEIGHT: u64;
}

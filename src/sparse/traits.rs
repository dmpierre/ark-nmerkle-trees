use ark_crypto_primitives::{
    crh::{CRHScheme, CRHSchemeGadget},
    merkle_tree::{constraints::ConfigGadget, Config},
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub trait NArySparseConfig<const N: usize, P: Config> {
    type NToOneHashParams: Clone + CanonicalSerialize + CanonicalDeserialize + Sync;
    type NToOneHash: CRHScheme<
        Input = [P::InnerDigest],
        Output = P::InnerDigest,
        Parameters = Self::NToOneHashParams,
    >;
    // NOTE: n leaves will be N^{HEIGHT - 1}
    const HEIGHT: u64;
}

pub trait NArySparseConfigGadget<
    const N: usize,
    P: Config,
    PG: ConfigGadget<P, F>,
    F: PrimeField,
    SP: NArySparseConfig<N, P>,
>
{
    const HEIGHT: u64;

    type NToOneHash: CRHSchemeGadget<
        <SP as NArySparseConfig<N, P>>::NToOneHash,
        F,
        InputVar = [PG::InnerDigest],
        OutputVar = PG::InnerDigest,
    >;
}

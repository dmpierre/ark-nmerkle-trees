use ark_crypto_primitives::{
    crh::{CRHScheme, CRHSchemeGadget},
    merkle_tree::{constraints::ConfigGadget, Config},
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub trait NArySparseConfig<P: Config> {
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
    P: Config,
    PG: ConfigGadget<P, F>,
    F: PrimeField,
    SP: NArySparseConfig<P>,
>
{
    const HEIGHT: u64;

    type NToOneHash: CRHSchemeGadget<
        <SP as NArySparseConfig<P>>::NToOneHash,
        F,
        InputVar = [PG::InnerDigest],
        OutputVar = PG::InnerDigest,
    >;
}

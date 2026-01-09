use std::marker::PhantomData;

use ark_crypto_primitives::{
    crh::CRHSchemeGadget,
    merkle_tree::{constraints::ConfigGadget, Config},
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    prelude::Boolean,
    GR1CSVar,
};
use ark_relations::gr1cs::SynthesisError;
use ark_std::log2;
use num::BigUint;

use crate::sparse::traits::{NArySparseConfig, NArySparseConfigGadget};

use super::NArySparsePath;

pub struct NArySparsePathVar<
    const N: usize,
    P: Config,
    PG: ConfigGadget<P, F>,
    F: PrimeField,
    SP: NArySparseConfig<P>,
    SPG: NArySparseConfigGadget<P, PG, F, SP>,
> {
    pub leaf_siblings_hashes: Vec<PG::LeafDigest>,
    pub auth_path: Vec<Vec<PG::InnerDigest>>,
    pub index: FpVar<F>,
    _m: PhantomData<(SP, SPG)>,
}

impl<
        const N: usize,
        P: Config + Clone,
        PG: ConfigGadget<P, F>,
        F: PrimeField,
        SP: NArySparseConfig<P>,
        SPG: NArySparseConfigGadget<P, PG, F, SP>,
    > AllocVar<NArySparsePath<N, P, SP>, F> for NArySparsePathVar<N, P, PG, F, SP, SPG>
{
    fn new_variable<T: std::borrow::Borrow<NArySparsePath<N, P, SP>>>(
        cs: impl Into<ark_relations::gr1cs::Namespace<F>>,
        f: impl FnOnce() -> Result<T, ark_relations::gr1cs::SynthesisError>,
        mode: ark_r1cs_std::prelude::AllocationMode,
    ) -> Result<Self, ark_relations::gr1cs::SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let NArySparsePath {
            leaf_siblings_hashes,
            auth_path,
            index,
            _m,
        } = v.borrow();
        let leaf_siblings_hashes =
            Vec::new_variable(cs.clone(), || Ok(leaf_siblings_hashes.clone()), mode)?;
        let auth_path = auth_path
            .iter()
            .map(|i| Vec::new_variable(cs.clone(), || Ok(&i[..]), mode))
            .collect::<Result<_, _>>()?;
        let index = FpVar::new_variable(cs.clone(), || Ok(F::from(*index as u64)), mode)?;
        Ok(NArySparsePathVar {
            leaf_siblings_hashes,
            auth_path,
            index,
            _m: PhantomData::<(SP, SPG)>,
        })
    }
}

type LeafParam<PG, P, F> = <<PG as ConfigGadget<P, F>>::LeafHash as CRHSchemeGadget<
    <P as Config>::LeafHash,
    F,
>>::ParametersVar;

type NToOneParam<
    const N: usize,
    P,
    PG,
    F,
    SP: NArySparseConfig<P>,
    SPG: NArySparseConfigGadget<P, PG, F, SP>,
> = <<SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash as CRHSchemeGadget<
    <SP as NArySparseConfig<P>>::NToOneHash,
    F,
>>::ParametersVar;

impl<
        const N: usize,
        P: Config,
        PG: ConfigGadget<P, F, LeafDigest = FpVar<F>, InnerDigest = FpVar<F>>,
        F: PrimeField,
        SP: NArySparseConfig<P>,
        SPG: NArySparseConfigGadget<P, PG, F, SP>,
    > NArySparsePathVar<N, P, PG, F, SP, SPG>
{
    /// Calculate the root of the Merkle tree assuming that `leaf` is the leaf on the path defined by `self`.
    pub fn calculate_root(
        &self,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, PG, F, SP, SPG>,
        leaf: &PG::Leaf,
    ) -> Result<PG::InnerDigest, SynthesisError> {
        let claimed_leaf_hash = PG::LeafHash::evaluate(leaf_params, leaf)?;

        let index_bits_chunks = {
            let mut limbs_bits = vec![];
            let mut v: BigUint = self.index.value().unwrap_or_default().into();
            for _ in 0..SP::HEIGHT - 1 {
                let mut bits = (&v % BigUint::from(N as u64))
                    .to_radix_le(2)
                    .into_iter()
                    .map(|b| b != 0)
                    .collect::<Vec<_>>();
                bits.resize(log2(N) as usize, false);
                limbs_bits.push(bits);
                v /= BigUint::from(N as u64);
            }

            let limbs_bits = limbs_bits
                .iter()
                .map(|i| Vec::new_variable_with_inferred_mode(self.index.cs(), || Ok(&i[..])))
                .collect::<Result<Vec<_>, _>>()?;

            let mut sum = FpVar::zero();
            let mut power = FpVar::one();
            for bits in &limbs_bits {
                sum += Boolean::le_bits_to_fp(bits)? * &power;
                power *= FpVar::constant(F::from(N as u64));
            }

            sum.enforce_equal(&self.index)?;

            limbs_bits
        };

        fn mux<F: PrimeField>(
            mut vec: Vec<FpVar<F>>,
            pos: &[Boolean<F>],
        ) -> Result<FpVar<F>, SynthesisError> {
            vec.resize(2usize.pow(pos.len() as u32), FpVar::zero());
            for b in pos {
                vec = vec
                    .chunks(2)
                    .map(|v| b.select(&v[1], &v[0]))
                    .collect::<Result<_, _>>()?;
            }
            assert_eq!(vec.len(), 1);
            Ok(vec.swap_remove(0))
        }

        mux(self.leaf_siblings_hashes.clone(), &index_bits_chunks[0])?
            .enforce_equal(&claimed_leaf_hash)?;

        let mut curr_hash = <SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash::evaluate(
            n_to_one_params,
            &self.leaf_siblings_hashes,
        )?;

        for step in 0..self.auth_path.len() {
            mux(self.auth_path[step].clone(), &index_bits_chunks[step + 1])?
                .enforce_equal(&curr_hash)?;

            curr_hash = <SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash::evaluate(
                n_to_one_params,
                &self.auth_path[step],
            )?;
        }

        Ok(curr_hash)
    }

    pub fn verify_membership(
        &self,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, PG, F, SP, SPG>,
        root: &PG::InnerDigest,
        leaf: &PG::Leaf,
    ) -> Result<Boolean<F>, SynthesisError> {
        let expected_root = self.calculate_root(leaf_params, n_to_one_params, leaf)?;
        Ok(expected_root.is_eq(root)?)
    }

    pub fn update_leaf(
        &self,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, PG, F, SP, SPG>,
        old_root: &PG::InnerDigest,
        old_leaf: &PG::Leaf,
        new_leaf: &PG::Leaf,
    ) -> Result<PG::InnerDigest, SynthesisError> {
        let old_leaf_hash = PG::LeafHash::evaluate(leaf_params, old_leaf)?;
        let new_leaf_hash = PG::LeafHash::evaluate(leaf_params, new_leaf)?;
        let index_limbs = {
            let mut limbs_bits = vec![];
            let mut v: BigUint = self.index.value().unwrap_or_default().into();
            for _ in 0..SP::HEIGHT - 1 {
                let mut bits = (&v % BigUint::from(N as u64))
                    .to_radix_le(2)
                    .into_iter()
                    .map(|b| b != 0)
                    .collect::<Vec<_>>();
                bits.resize(log2(N) as usize, false);
                limbs_bits.push(bits);
                v /= BigUint::from(N as u64);
            }

            let limbs_bits = limbs_bits
                .iter()
                .map(|i| Vec::new_variable_with_inferred_mode(self.index.cs(), || Ok(&i[..])))
                .collect::<Result<Vec<_>, _>>()?;

            let mut limbs = vec![];

            let mut sum = FpVar::zero();
            let mut power = FpVar::one();
            for bits in limbs_bits {
                let limb = Boolean::le_bits_to_fp(&bits)?;
                sum += &limb * &power;
                power *= FpVar::constant(F::from(N as u64));
                limbs.push(limb);
            }

            sum.enforce_equal(&self.index)?;

            limbs
        };

        let b = {
            let v = index_limbs
                .value()
                .unwrap_or(vec![F::zero(); SP::HEIGHT as usize - 1]);
            let bits = v
                .into_iter()
                .map(|j| {
                    (0..N)
                        .map(|i| {
                            Boolean::new_variable_with_inferred_mode(index_limbs.cs(), || {
                                Ok(j == F::from(i as u64))
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;

            let mut sum1 = FpVar::zero();
            let mut sum2 = FpVar::zero();
            for j in 0..SP::HEIGHT as usize - 1 {
                for i in 0..N {
                    sum1 += FpVar::from(bits[j][i].clone()) * F::from(i as u64);
                    sum2 += FpVar::from(bits[j][i].clone())
                }
                sum1 -= &index_limbs[j];
                sum1 *= F::from(N.pow(j as u32) as u64);
                sum2 -= FpVar::one();
                sum2 *= F::from(2u64.pow(j as u32));
            }
            sum1.enforce_equal(&FpVar::zero())?;
            sum2.enforce_equal(&FpVar::zero())?;
            bits
        };

        let mut old_curr_hash =
            <SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash::evaluate(
                n_to_one_params,
                &b[0]
                    .iter()
                    .zip(&self.leaf_siblings_hashes)
                    .map(|(bit, i)| bit.select(&old_leaf_hash, i))
                    .collect::<Result<Vec<_>, _>>()?[..],
            )?;
        let mut new_curr_hash =
            <SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash::evaluate(
                n_to_one_params,
                &b[0]
                    .iter()
                    .zip(&self.leaf_siblings_hashes)
                    .map(|(bit, i)| bit.select(&new_leaf_hash, i))
                    .collect::<Result<Vec<_>, _>>()?[..],
            )?;

        for step in 0..self.auth_path.len() {
            old_curr_hash = <SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash::evaluate(
                n_to_one_params,
                &b[step + 1]
                    .iter()
                    .zip(&self.auth_path[step])
                    .map(|(bit, i)| bit.select(&old_curr_hash, i))
                    .collect::<Result<Vec<_>, _>>()?[..],
            )?;
            new_curr_hash = <SPG as NArySparseConfigGadget<P, PG, F, SP>>::NToOneHash::evaluate(
                n_to_one_params,
                &b[step + 1]
                    .iter()
                    .zip(&self.auth_path[step])
                    .map(|(bit, i)| bit.select(&new_curr_hash, i))
                    .collect::<Result<Vec<_>, _>>()?[..],
            )?;
        }

        old_curr_hash.enforce_equal(old_root)?;

        Ok(new_curr_hash)
    }

    pub fn update_and_check(
        &self,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, PG, F, SP, SPG>,
        old_root: &PG::InnerDigest,
        new_root: &PG::InnerDigest,
        old_leaf: &PG::Leaf,
        new_leaf: &PG::Leaf,
    ) -> Result<Boolean<F>, SynthesisError> {
        let actual_new_root =
            self.update_leaf(leaf_params, n_to_one_params, old_root, old_leaf, new_leaf)?;
        Ok(actual_new_root.is_eq(&new_root)?)
    }
}

#[cfg(test)]
pub mod tests {

    use ark_r1cs_std::GR1CSVar;
    use std::{collections::BTreeMap, marker::PhantomData};

    use ark_bn254::Fr;
    use ark_crypto_primitives::{
        crh::{
            poseidon::{
                constraints::{CRHGadget, CRHParametersVar, TwoToOneCRHGadget},
                CRH,
            },
            CRHSchemeGadget,
        },
        merkle_tree::{constraints::ConfigGadget, IdentityDigestConverter},
        sponge::{poseidon::PoseidonConfig, Absorb},
    };
    use ark_ff::PrimeField;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
    use ark_relations::gr1cs::ConstraintSystem;

    use crate::{
        sparse::{
            tests::{NoArrayCRH, NoArrayPoseidonTree},
            traits::{NArySparseConfig, NArySparseConfigGadget},
            NAryMerkleSparseTree,
        },
        tests::initialize_poseidon_config,
    };

    use super::NArySparsePathVar;

    pub struct NoArrayPoseidonTreeGadget<F: PrimeField + Absorb> {
        _f: PhantomData<F>,
    }

    pub struct NoArrayCRHGadget<F: PrimeField> {
        _f: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> CRHSchemeGadget<NoArrayCRH<F>, F> for NoArrayCRHGadget<F> {
        type InputVar = FpVar<F>;
        type OutputVar = FpVar<F>;
        type ParametersVar = CRHParametersVar<F>;

        fn evaluate(
            parameters: &Self::ParametersVar,
            input: &Self::InputVar,
        ) -> Result<Self::OutputVar, ark_relations::gr1cs::SynthesisError> {
            CRHGadget::evaluate(parameters, [input.clone()].as_slice())
        }
    }

    impl<F: PrimeField + Absorb> ConfigGadget<NoArrayPoseidonTree<F>, F>
        for NoArrayPoseidonTreeGadget<F>
    {
        type Leaf = FpVar<F>;
        type LeafDigest = FpVar<F>;
        type LeafInnerConverter = IdentityDigestConverter<FpVar<F>>;
        type InnerDigest = FpVar<F>;
        type LeafHash = NoArrayCRHGadget<F>;
        type TwoToOneHash = TwoToOneCRHGadget<F>;
    }

    impl
        NArySparseConfigGadget<
            NoArrayPoseidonTree<Fr>,
            NoArrayPoseidonTreeGadget<Fr>,
            Fr,
            NoArrayPoseidonTree<Fr>,
        > for NoArrayPoseidonTreeGadget<Fr>
    {
        type NToOneHash = CRHGadget<Fr>;
        const HEIGHT: u64 = 4;
    }

    fn run_test<
        const N: usize,
        SP: NArySparseConfig<NoArrayPoseidonTree<Fr>, NToOneHash = CRH<Fr>>,
        SPG: NArySparseConfigGadget<
            NoArrayPoseidonTree<Fr>,
            NoArrayPoseidonTreeGadget<Fr>,
            Fr,
            SP,
            NToOneHash = CRHGadget<Fr>,
        >,
    >(
        poseidon_conf: PoseidonConfig<Fr>,
        index_values: Vec<(usize, Fr)>,
    ) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let poseidon_conf_var =
            CRHParametersVar::new_constant(cs.clone(), poseidon_conf.clone()).unwrap();

        // testing binary tree
        let mut sparse_leaves = BTreeMap::<usize, Fr>::new();
        for (i, value) in index_values.clone() {
            sparse_leaves.insert(i, value);
        }

        let mut sparse_mt = NAryMerkleSparseTree::<N, NoArrayPoseidonTree<Fr>, SP>::new(
            &poseidon_conf,
            &poseidon_conf,
            &sparse_leaves,
            &Fr::default(),
        )
        .unwrap();

        for (i, value) in index_values.clone() {
            let proof = sparse_mt.generate_proof(i as usize).unwrap();
            let root = <NoArrayPoseidonTreeGadget<Fr> as ConfigGadget<
                NoArrayPoseidonTree<Fr>,
                Fr,
            >>::InnerDigest::new_witness(cs.clone(), || Ok(sparse_mt.root()))
            .unwrap();
            let proof_var = NArySparsePathVar::<
                N,
                NoArrayPoseidonTree<Fr>,
                NoArrayPoseidonTreeGadget<Fr>,
                Fr,
                SP,
                SPG,
            >::new_witness(cs.clone(), || Ok(proof))
            .unwrap();

            // check membership logic
            let leaf = FpVar::new_witness(cs.clone(), || Ok(value)).unwrap();
            let res = proof_var
                .verify_membership(&poseidon_conf_var, &poseidon_conf_var, &root, &leaf)
                .unwrap();
            assert!(res.value().unwrap());

            // check update logic
            let new_leaf = value + Fr::from(1);
            sparse_mt.update(i, &new_leaf).unwrap();

            let new_root = <NoArrayPoseidonTreeGadget<Fr> as ConfigGadget<
                NoArrayPoseidonTree<Fr>,
                Fr,
            >>::InnerDigest::new_witness(cs.clone(), || {
                Ok(sparse_mt.root())
            })
            .unwrap();

            let new_leaf_var = FpVar::new_witness(cs.clone(), || Ok(new_leaf)).unwrap();

            let update = proof_var
                .update_and_check(
                    &poseidon_conf_var,
                    &poseidon_conf_var,
                    &root,
                    &new_root,
                    &leaf,
                    &new_leaf_var,
                )
                .unwrap();
            assert!(update.value().unwrap());
        }
        println!("{} {}", cs.num_constraints(), cs.num_variables());
    }

    #[test]
    fn test_nary_sparse_trees_constraints() {
        let poseidon_conf = initialize_poseidon_config::<Fr>();
        let index_values = vec![(0, Fr::from(42)), (2, Fr::from(43))];
        run_test::<2, NoArrayPoseidonTree<Fr>, NoArrayPoseidonTreeGadget<Fr>>(
            poseidon_conf.clone(),
            index_values.clone(),
        );

        let index_values: Vec<(
            usize,
            ark_ff::Fp<ark_ff::MontBackend<ark_bn254::FrConfig, 4>, 4>,
        )> = vec![(0, Fr::from(42)), (4, Fr::from(24)), (25, Fr::from(42))];
        run_test::<3, NoArrayPoseidonTree<Fr>, NoArrayPoseidonTreeGadget<Fr>>(
            poseidon_conf.clone(),
            index_values.clone(),
        );

        let index_values = vec![
            (0, Fr::from(42)),
            (4, Fr::from(24)),
            (70, Fr::from(24)),
            (123, Fr::from(42)),
        ];
        run_test::<5, NoArrayPoseidonTree<Fr>, NoArrayPoseidonTreeGadget<Fr>>(
            poseidon_conf.clone(),
            index_values,
        );
    }
}

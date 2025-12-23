use std::marker::PhantomData;

use ark_crypto_primitives::{
    crh::CRHSchemeGadget,
    merkle_tree::{constraints::ConfigGadget, Config},
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, prelude::Boolean};
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};

use crate::{
    constraints::{index_to_selector, PathStepVar},
    sparse::traits::{NArySparseConfig, NArySparseConfigGadget},
};

use super::NArySparsePath;

pub struct NArySparsePathVar<
    const N: usize,
    P: Config,
    PG: ConfigGadget<P, F>,
    F: PrimeField,
    SP: NArySparseConfig<N, P>,
    SPG: NArySparseConfigGadget<N, P, PG, F, SP>,
> {
    pub leaf_siblings_hashes: Vec<PG::LeafDigest>,
    pub auth_path: Vec<PathStepVar<N, P, F, PG>>,
    pub leaf_selectors: Vec<Boolean<F>>, // indicates position in the array before hashing siblings leaf nodes
    _m: PhantomData<(SP, SPG)>,
}

impl<
        const N: usize,
        P: Config,
        PG: ConfigGadget<P, F, LeafDigest = FpVar<F>>,
        F: PrimeField,
        SP: NArySparseConfig<N, P>,
        SPG: NArySparseConfigGadget<N, P, PG, F, SP>,
    > NArySparsePathVar<N, P, PG, F, SP, SPG>
{
    // returns a vector which will then be hashed according to a provided vector of selectors and values
    // for a tree of arity N, we have N - 1 candidate siblings but N selectors (since nodes have N
    // values)
    // eg: siblings: [sibling_0, sibling1], to_insert: value, selectors: [0, 1, 0]
    // ---> [sibling0, value, sibling1]
    pub fn get_node(
        cs: ConstraintSystemRef<F>,
        siblings: &Vec<PG::LeafDigest>,
        selectors: &Vec<Boolean<F>>,
        claimed_hash: &PG::LeafDigest,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut to_hash = Vec::with_capacity(N);

        // first element of vector to be hashed
        let s_0: &FpVar<F> = &selectors[0].clone().into();
        let y_0 = &siblings[0] + s_0 * (claimed_hash - &siblings[0]);

        to_hash.push(y_0);

        // t indicates if insertion has occured within the vector
        let mut t_i = s_0.clone();
        let one = FpVar::new_constant(cs.clone(), F::one())?;

        // we already did first sibling, iterate from the first to the penultimate
        for i in 1..N - 1 {
            let s_i: FpVar<F> = selectors[i].clone().into();
            let x_i_minus_1 = &siblings[i - 1];
            let x_i = &siblings[i];

            let t_i_xi_minus_1 = &t_i * x_i_minus_1;
            let c: FpVar<F> = &s_i * (claimed_hash - x_i);
            let y_i = t_i_xi_minus_1 + (&one - &t_i) * (x_i + c);
            to_hash.push(y_i);
            t_i += &s_i;
        }

        // do ultimate sibling
        let s_last: &FpVar<F> = &selectors[N - 1].clone().into();
        let y_last = &siblings[N - 2] + s_last * (claimed_hash - &siblings[N - 2]);

        to_hash.push(y_last);

        Ok(to_hash)
    }
}

impl<
        const N: usize,
        P: Config + Clone,
        PG: ConfigGadget<P, F>,
        F: PrimeField,
        SP: NArySparseConfig<N, P>,
        SPG: NArySparseConfigGadget<N, P, PG, F, SP>,
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
            leaf_index,
            _m,
        } = v.borrow();
        let leaf_siblings_hashes =
            Vec::new_variable(cs.clone(), || Ok(leaf_siblings_hashes.clone()), mode)?;
        let auth_path = Vec::<PathStepVar<N, P, F, PG>>::new_variable(
            cs.clone(),
            || Ok(auth_path.to_vec()),
            mode,
        )?;
        let leaf_selectors =
            Vec::new_variable(cs.clone(), || Ok(index_to_selector::<N>(*leaf_index)), mode)?;
        Ok(NArySparsePathVar {
            leaf_siblings_hashes,
            auth_path,
            leaf_selectors,
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
    SP: NArySparseConfig<N, P>,
    SPG: NArySparseConfigGadget<N, P, PG, F, SP>,
> = <<SPG as NArySparseConfigGadget<N, P, PG, F, SP>>::NToOneHash as CRHSchemeGadget<
    <SP as NArySparseConfig<N, P>>::NToOneHash,
    F,
>>::ParametersVar;

impl<
        const N: usize,
        P: Config,
        PG: ConfigGadget<P, F, LeafDigest = FpVar<F>, InnerDigest = FpVar<F>>,
        F: PrimeField,
        SP: NArySparseConfig<N, P>,
        SPG: NArySparseConfigGadget<N, P, PG, F, SP>,
    > NArySparsePathVar<N, P, PG, F, SP, SPG>
{
    /// Calculate the root of the Merkle tree assuming that `leaf` is the leaf on the path defined by `self`.
    pub fn calculate_root(
        &self,
        cs: ConstraintSystemRef<F>,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, PG, F, SP, SPG>,
        leaf: &PG::Leaf,
    ) -> Result<PG::InnerDigest, SynthesisError> {
        let claimed_leaf_hash = PG::LeafHash::evaluate(leaf_params, leaf)?;

        let leaf_node = NArySparsePathVar::<N, P, PG, F, SP, SPG>::get_node(
            cs.clone(),
            &self.leaf_siblings_hashes,
            &self.leaf_selectors,
            &claimed_leaf_hash,
        )?;

        let mut curr_hash = <SPG as NArySparseConfigGadget<N, P, PG, F, SP>>::NToOneHash::evaluate(
            n_to_one_params,
            leaf_node.as_slice(),
        )?;

        // To traverse up a MT, we iterate over the path from bottom to top (i.e. in reverse)
        for step in (0..self.auth_path.len()).rev() {
            let node = NArySparsePathVar::<N, P, PG, F, SP, SPG>::get_node(
                cs.clone(),
                &self.auth_path[step].siblings,
                &self.auth_path[step].selectors,
                &curr_hash,
            )?;

            curr_hash = <SPG as NArySparseConfigGadget<N, P, PG, F, SP>>::NToOneHash::evaluate(
                &n_to_one_params,
                node.as_slice(),
            )?;
        }

        Ok(curr_hash)
    }

    pub fn verify_membership(
        &self,
        cs: ConstraintSystemRef<F>,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, PG, F, SP, SPG>,
        root: &PG::InnerDigest,
        leaf: &PG::Leaf,
    ) -> Result<Boolean<F>, SynthesisError> {
        let expected_root = self.calculate_root(cs, leaf_params, n_to_one_params, leaf)?;
        Ok(expected_root.is_eq(root)?)
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
            tests::{
                NoArrayBinaryPoseidonTree, NoArrayCRH, NoArrayPoseidonTree,
                NoArrayQuinaryPoseidonTree, NoArrayTernaryPoseidonTree,
            },
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

    pub struct NoArrayBinaryPoseidonTreeGadget<F: PrimeField + Absorb> {
        _f: PhantomData<F>,
    }
    impl
        NArySparseConfigGadget<
            2,
            NoArrayPoseidonTree<Fr>,
            NoArrayPoseidonTreeGadget<Fr>,
            Fr,
            NoArrayBinaryPoseidonTree<Fr>,
        > for NoArrayBinaryPoseidonTreeGadget<Fr>
    {
        type NToOneHash = CRHGadget<Fr>;
        const HEIGHT: u64 = 4;
    }

    pub struct NoArrayTernaryPoseidonTreeGadget<F: PrimeField + Absorb> {
        _f: PhantomData<F>,
    }
    impl
        NArySparseConfigGadget<
            3,
            NoArrayPoseidonTree<Fr>,
            NoArrayPoseidonTreeGadget<Fr>,
            Fr,
            NoArrayTernaryPoseidonTree<Fr>,
        > for NoArrayTernaryPoseidonTreeGadget<Fr>
    {
        type NToOneHash = CRHGadget<Fr>;
        const HEIGHT: u64 = 4;
    }

    pub struct NoArrayQuinaryPoseidonTreeGadget<F: PrimeField + Absorb> {
        _f: PhantomData<F>,
    }
    impl
        NArySparseConfigGadget<
            5,
            NoArrayPoseidonTree<Fr>,
            NoArrayPoseidonTreeGadget<Fr>,
            Fr,
            NoArrayQuinaryPoseidonTree<Fr>,
        > for NoArrayQuinaryPoseidonTreeGadget<Fr>
    {
        type NToOneHash = CRHGadget<Fr>;
        const HEIGHT: u64 = 4;
    }

    fn run_test<
        const N: usize,
        SP: NArySparseConfig<N, NoArrayPoseidonTree<Fr>, NToOneHash = CRH<Fr>>,
        SPG: NArySparseConfigGadget<
            N,
            NoArrayPoseidonTree<Fr>,
            NoArrayPoseidonTreeGadget<Fr>,
            Fr,
            SP,
            NToOneHash = CRHGadget<Fr>,
        >,
    >(
        n_leaf_nodes: usize,
        poseidon_conf: PoseidonConfig<Fr>,
        index_values: Vec<(usize, Fr)>,
    ) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let poseidon_conf_var =
            CRHParametersVar::new_constant(cs.clone(), poseidon_conf.clone()).unwrap();

        // testing binary tree
        let mut leaves = vec![[Fr::default()]; n_leaf_nodes];
        let mut sparse_leaves = BTreeMap::<usize, Fr>::new();
        for (i, value) in index_values.clone() {
            leaves[i as usize] = [value];
            sparse_leaves.insert(i, value);
        }

        let mut sparse_mt = NAryMerkleSparseTree::<N, NoArrayPoseidonTree<Fr>, SP>::new(
            &poseidon_conf,
            &poseidon_conf,
            &sparse_leaves,
            &Fr::default(),
        )
        .unwrap();

        let root = <NoArrayPoseidonTreeGadget<Fr> as ConfigGadget<NoArrayPoseidonTree<Fr>, Fr>>::InnerDigest::new_witness(
            cs.clone(),
            || Ok(sparse_mt.root()),
        ).unwrap();

        for (i, value) in index_values.clone() {
            let proof = sparse_mt.generate_proof(i as usize).unwrap();
            let proof_var = NArySparsePathVar::<
                N,
                NoArrayPoseidonTree<Fr>,
                NoArrayPoseidonTreeGadget<Fr>,
                Fr,
                SP,
                SPG,
            >::new_witness(cs.clone(), || Ok(proof))
            .unwrap();
            let leaf = FpVar::new_witness(cs.clone(), || Ok(value)).unwrap();
            let res = proof_var
                .verify_membership(
                    cs.clone(),
                    &poseidon_conf_var,
                    &poseidon_conf_var,
                    &root,
                    &leaf,
                )
                .unwrap();
            assert!(res.value().unwrap());

            // check proof verification fails for bad leaf
            let res = proof_var
                .verify_membership(
                    cs.clone(),
                    &poseidon_conf_var,
                    &poseidon_conf_var,
                    &root,
                    &(leaf + FpVar::new_constant(cs.clone(), Fr::from(1)).unwrap()),
                )
                .unwrap();
            assert!(!res.value().unwrap())
        }

        // check update logic
        for (i, value) in index_values.clone() {}
    }

    #[test]
    fn test_nary_sparse_trees() {
        let poseidon_conf = initialize_poseidon_config::<Fr>();
        let index_values = vec![(0, Fr::from(42)), (4, Fr::from(24))];
        run_test::<2, NoArrayBinaryPoseidonTree<Fr>, NoArrayBinaryPoseidonTreeGadget<Fr>>(
            8,
            poseidon_conf.clone(),
            index_values.clone(),
        );

        let index_values = vec![(0, Fr::from(42)), (4, Fr::from(24)), (25, Fr::from(42))];
        run_test::<3, NoArrayTernaryPoseidonTree<Fr>, NoArrayTernaryPoseidonTreeGadget<Fr>>(
            27,
            poseidon_conf.clone(),
            index_values.clone(),
        );

        let index_values = vec![
            (0, Fr::from(42)),
            (4, Fr::from(24)),
            (70, Fr::from(24)),
            (123, Fr::from(42)),
        ];
        run_test::<5, NoArrayQuinaryPoseidonTree<Fr>, NoArrayQuinaryPoseidonTreeGadget<Fr>>(
            125,
            poseidon_conf.clone(),
            index_values,
        );
    }
}

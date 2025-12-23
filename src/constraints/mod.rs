use std::marker::PhantomData;

use ark_crypto_primitives::{
    crh::CRHSchemeGadget,
    merkle_tree::{constraints::ConfigGadget, Config},
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, prelude::Boolean, GR1CSVar};
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};

use crate::{
    traits::{NAryConfig, NAryConfigGadget},
    NAryPath, PathStep,
};

pub(crate) fn index_to_selector<const N: usize>(idx: usize) -> [bool; N] {
    let mut idx_as_vec = [false; N];
    idx_as_vec[idx] = true;
    idx_as_vec
}

#[derive(Default)]
pub struct PathStepVar<const N: usize, P: Config, F: PrimeField, PG: ConfigGadget<P, F>> {
    pub selectors: Vec<Boolean<F>>,
    pub siblings: Vec<PG::InnerDigest>,
}

impl<const N: usize, P: Config, F: PrimeField, PG: ConfigGadget<P, F>> AllocVar<PathStep<P>, F>
    for PathStepVar<N, P, F, PG>
{
    fn new_variable<T: std::borrow::Borrow<PathStep<P>>>(
        cs: impl Into<ark_relations::gr1cs::Namespace<F>>,
        f: impl FnOnce() -> Result<T, ark_relations::gr1cs::SynthesisError>,
        mode: ark_r1cs_std::prelude::AllocationMode,
    ) -> Result<Self, ark_relations::gr1cs::SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let PathStep { index, siblings } = v.borrow();
        let selectors = Vec::new_variable(cs.clone(), || Ok(index_to_selector::<N>(*index)), mode)?;
        let siblings =
            Vec::<PG::InnerDigest>::new_variable(cs.clone(), || Ok(siblings.clone()), mode)?;
        Ok(PathStepVar {
            selectors,
            siblings,
        })
    }
}

pub struct NAryPathVar<
    const N: usize,
    P: Config,
    F: PrimeField,
    PG: ConfigGadget<P, F>,
    NP: NAryConfig<N, P>,
    NPG: NAryConfigGadget<N, P, F, PG, NP>,
> {
    leaf_siblings_hashes: Vec<PG::LeafDigest>,
    auth_path: Vec<PathStepVar<N, P, F, PG>>,
    leaf_selectors: Vec<Boolean<F>>, // indicates position in the array before hashing siblings leaf nodes
    _m: PhantomData<(NP, NPG)>,
}

impl<
        const N: usize,
        P: Config,
        F: PrimeField,
        PG: ConfigGadget<P, F, LeafDigest = FpVar<F>, InnerDigest = FpVar<F>>,
        NP: NAryConfig<N, P>,
        NPG: NAryConfigGadget<N, P, F, PG, NP>,
    > NAryPathVar<N, P, F, PG, NP, NPG>
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
        F: PrimeField,
        PG: ConfigGadget<P, F>,
        NP: NAryConfig<N, P>,
        NPG: NAryConfigGadget<N, P, F, PG, NP>,
    > AllocVar<NAryPath<N, P, NP>, F> for NAryPathVar<N, P, F, PG, NP, NPG>
{
    fn new_variable<T: std::borrow::Borrow<NAryPath<N, P, NP>>>(
        cs: impl Into<ark_relations::gr1cs::Namespace<F>>,
        f: impl FnOnce() -> Result<T, ark_relations::gr1cs::SynthesisError>,
        mode: ark_r1cs_std::prelude::AllocationMode,
    ) -> Result<Self, ark_relations::gr1cs::SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let NAryPath {
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
        Ok(NAryPathVar {
            leaf_siblings_hashes,
            auth_path,
            leaf_selectors,
            _m: PhantomData::<(NP, NPG)>,
        })
    }
}

type LeafParam<PG, P, F> = <<PG as ConfigGadget<P, F>>::LeafHash as CRHSchemeGadget<
    <P as Config>::LeafHash,
    F,
>>::ParametersVar;

type NToOneParam<const N: usize, P, F, PG, NP, NPG> =
    <<NPG as NAryConfigGadget<N, P, F, PG, NP>>::NToOneHash as CRHSchemeGadget<
        <NP as NAryConfig<N, P>>::NToOneHash,
        F,
    >>::ParametersVar;

impl<
        const N: usize,
        P: Config + Clone,
        F: PrimeField,
        PG: ConfigGadget<P, F, LeafDigest = FpVar<F>, InnerDigest = FpVar<F>>,
        NP: NAryConfig<N, P>,
        NPG: NAryConfigGadget<N, P, F, PG, NP>,
    > NAryPathVar<N, P, F, PG, NP, NPG>
{
    /// Calculate the root of the Merkle tree assuming that `leaf` is the leaf on the path defined by `self`.
    pub fn calculate_root(
        &self,
        cs: ConstraintSystemRef<F>,
        leaf_params: &LeafParam<PG, P, F>,
        n_to_one_params: &NToOneParam<N, P, F, PG, NP, NPG>,
        leaf: &PG::Leaf,
    ) -> Result<PG::InnerDigest, SynthesisError> {
        let claimed_leaf_hash = PG::LeafHash::evaluate(leaf_params, leaf)?;

        let leaf_node = NAryPathVar::<N, P, _, PG, NP, NPG>::get_node(
            cs.clone(),
            &self.leaf_siblings_hashes,
            &self.leaf_selectors,
            &claimed_leaf_hash,
        )?;

        let mut curr_hash = NPG::NToOneHash::evaluate(n_to_one_params, leaf_node.as_slice())?;

        // To traverse up a MT, we iterate over the path from bottom to top (i.e. in reverse)
        for step in (0..self.auth_path.len()).rev() {
            let node = NAryPathVar::<N, P, _, PG, NP, NPG>::get_node(
                cs.clone(),
                &self.auth_path[step].siblings,
                &self.auth_path[step].selectors,
                &curr_hash,
            )?;

            curr_hash = NPG::NToOneHash::evaluate(&n_to_one_params, node.as_slice())?;
        }

        Ok(curr_hash)
    }

    pub fn verify_membership(
        &self,
        cs: ConstraintSystemRef<F>,
        leaf_params: &LeafParam<PG, P, F>,
        two_to_one_params: &NToOneParam<N, P, F, PG, NP, NPG>,
        root: &PG::InnerDigest,
        leaf: &PG::Leaf,
    ) -> Result<Boolean<F>, SynthesisError> {
        let expected_root = self.calculate_root(cs, leaf_params, two_to_one_params, leaf)?;
        Ok(expected_root.is_eq(root)?)
    }
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ark_bn254::Fr;
    use ark_crypto_primitives::{
        crh::poseidon::constraints::{CRHGadget, CRHParametersVar, TwoToOneCRHGadget},
        merkle_tree::{constraints::ConfigGadget, IdentityDigestConverter},
        sponge::Absorb,
    };
    use ark_ff::PrimeField;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::Boolean, GR1CSVar};
    use ark_relations::gr1cs::{ConstraintSystem, ConstraintSystemRef};

    use crate::{
        tests::{
            initialize_poseidon_config, BinaryPoseidonTree, PoseidonTree, QuinaryPoseidonTree,
            TernaryPoseidonTree,
        },
        traits::{NAryConfig, NAryConfigGadget},
        NAryMerkleTree,
    };

    use super::NAryPathVar;

    pub struct PoseidonTreeGadget<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    pub struct BinaryPoseidonTreeGadget<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    pub struct TernaryPoseidonTreeGadget<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    pub struct QuinaryPoseidonTreeGadget<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb>
        NAryConfigGadget<2, PoseidonTree<F>, F, PoseidonTreeGadget<F>, BinaryPoseidonTree<F>>
        for BinaryPoseidonTreeGadget<F>
    {
        type NToOneHash = CRHGadget<F>;
    }

    impl<F: PrimeField + Absorb>
        NAryConfigGadget<3, PoseidonTree<F>, F, PoseidonTreeGadget<F>, TernaryPoseidonTree<F>>
        for TernaryPoseidonTreeGadget<F>
    {
        type NToOneHash = CRHGadget<F>;
    }

    impl<F: PrimeField + Absorb>
        NAryConfigGadget<5, PoseidonTree<F>, F, PoseidonTreeGadget<F>, QuinaryPoseidonTree<F>>
        for QuinaryPoseidonTreeGadget<F>
    {
        type NToOneHash = CRHGadget<F>;
    }

    impl<F: PrimeField + Absorb> ConfigGadget<PoseidonTree<F>, F> for PoseidonTreeGadget<F> {
        type Leaf = [FpVar<F>];
        type LeafDigest = FpVar<F>;
        type LeafInnerConverter = IdentityDigestConverter<FpVar<F>>;
        type InnerDigest = FpVar<F>;
        type LeafHash = CRHGadget<F>;
        type TwoToOneHash = TwoToOneCRHGadget<F>;
    }

    // idx indicates which leave should be one
    fn get_leaves(n_leaf_nodes: usize, idx: usize) -> Vec<[Fr; 1]> {
        let mut leaves = vec![[Fr::default()]; n_leaf_nodes];
        leaves[idx] = [Fr::from(1)];
        leaves
    }

    fn run_test<
        const N: usize,
        NP: NAryConfig<N, PoseidonTree<Fr>>,
        NPG: NAryConfigGadget<N, PoseidonTree<Fr>, Fr, PoseidonTreeGadget<Fr>, NP>,
    >(
        cs: ConstraintSystemRef<Fr>,
    ) {
        let values = vec![Fr::from(0); N - 1];
        let to_insert = Fr::from(1);
        let values_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(values)).unwrap();
        let to_insert_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(to_insert)).unwrap();
        for i in 0..N {
            let mut selector = vec![false; N];
            selector[i] = true;
            let selector_var =
                Vec::<Boolean<Fr>>::new_witness(cs.clone(), || Ok(selector)).unwrap();
            let node = NAryPathVar::<N, _, _, _, NP, NPG>::get_node(
                cs.clone(),
                &values_var.clone(),
                &selector_var,
                &to_insert_var.clone(),
            )
            .unwrap();
            let node_values = node.iter().map(|v| v.value().unwrap()).collect::<Vec<Fr>>();
            let node_sum: Fr = node_values.into_iter().sum();
            assert_eq!(node_sum, Fr::from(1)); // only one insertion
            assert_eq!(node[i].value().unwrap(), Fr::from(1)); // insertion at correct index
            assert_eq!(node.len(), N); // vector is of expected length
        }
    }

    #[test]
    pub fn test_get_node() {
        let poseidon_conf = initialize_poseidon_config::<Fr>();
        let cs = ConstraintSystem::<Fr>::new_ref();
        run_test::<2, BinaryPoseidonTree<Fr>, BinaryPoseidonTreeGadget<Fr>>(cs.clone());
        run_test::<3, TernaryPoseidonTree<Fr>, TernaryPoseidonTreeGadget<Fr>>(cs.clone());
        run_test::<5, QuinaryPoseidonTree<Fr>, QuinaryPoseidonTreeGadget<Fr>>(cs.clone());

        let cs = ConstraintSystem::<Fr>::new_ref();

        let poseidon_params_var =
            CRHParametersVar::new_constant(cs.clone(), poseidon_conf.clone()).unwrap();
        let leaf = FpVar::new_witness(cs.clone(), || Ok(Fr::from(1))).unwrap();

        // binary tree
        let n_leaf_nodes = 8;
        let leaves = get_leaves(n_leaf_nodes, 0);
        let mt2 = NAryMerkleTree::<2, PoseidonTree<Fr>, BinaryPoseidonTree<Fr>>::new(
            &poseidon_conf,
            &poseidon_conf,
            &leaves,
        )
        .unwrap();
        let proof = mt2.generate_proof(0).unwrap();
        let res = proof
            .verify(&poseidon_conf, &poseidon_conf, &mt2.root(), [Fr::from(1)])
            .unwrap();
        assert!(res);

        let proof_var = NAryPathVar::<
            2,
            PoseidonTree<Fr>,
            Fr,
            PoseidonTreeGadget<Fr>,
            BinaryPoseidonTree<Fr>,
            BinaryPoseidonTreeGadget<Fr>,
        >::new_witness(cs.clone(), || Ok(proof))
        .unwrap();
        let root = proof_var
            .calculate_root(
                cs.clone(),
                &poseidon_params_var,
                &poseidon_params_var,
                &[leaf.clone()],
            )
            .unwrap();
        assert_eq!(mt2.root(), root.value().unwrap());

        // quinary tree
        let n_leaf_nodes = 3125;
        let leaves = get_leaves(n_leaf_nodes, 0);
        let mt5 = NAryMerkleTree::<5, PoseidonTree<Fr>, QuinaryPoseidonTree<Fr>>::new(
            &poseidon_conf,
            &poseidon_conf,
            &leaves,
        )
        .unwrap();
        let proof = mt5.generate_proof(0).unwrap();
        let res = proof
            .verify(&poseidon_conf, &poseidon_conf, &mt5.root(), [Fr::from(1)])
            .unwrap();
        assert!(res);

        let proof_var = NAryPathVar::<
            5,
            PoseidonTree<Fr>,
            Fr,
            PoseidonTreeGadget<Fr>,
            QuinaryPoseidonTree<Fr>,
            QuinaryPoseidonTreeGadget<Fr>,
        >::new_witness(cs.clone(), || Ok(proof))
        .unwrap();
        let root = proof_var
            .calculate_root(cs, &poseidon_params_var, &poseidon_params_var, &[leaf])
            .unwrap();
        assert_eq!(mt5.root(), root.value().unwrap())
    }
}

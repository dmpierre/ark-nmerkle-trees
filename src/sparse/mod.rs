use ark_std::fmt::Debug;
use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet},
    marker::PhantomData,
};

use ark_crypto_primitives::{
    crh::{CRHScheme, TwoToOneCRHScheme},
    merkle_tree::{Config, DigestConverter, IdentityDigestConverter},
    sponge::Absorb,
    Error,
};
use ark_ff::PrimeField;

use crate::{
    convert_index_to_last_level, leaf_siblings, left_child, n_leaves, n_nodes, parent, siblings,
    sparse::traits::NArySparseConfig, tree_height, PathStep, Siblings,
};

pub mod constraints;
pub mod traits;

pub type LeafParam<P: Config> = <P::LeafHash as CRHScheme>::Parameters;
pub type NToOneParam<const N: usize, P: Config, SP: NArySparseConfig<N, P>> =
    <<SP as NArySparseConfig<N, P>>::NToOneHash as CRHScheme>::Parameters;

#[derive(Clone)]
pub struct NArySparsePath<const N: usize, P: Config, SP: NArySparseConfig<N, P>> {
    pub leaf_siblings_hashes: Vec<P::LeafDigest>,
    pub auth_path: Vec<PathStep<P>>,
    pub leaf_index: usize, // indicates position in the array before hashing siblings leaf nodes
    _m: PhantomData<SP>,
}

impl<const N: usize, P: Config, SP: NArySparseConfig<N, P>> Default for NArySparsePath<N, P, SP> {
    fn default() -> Self {
        let leaf_siblings_hashes = vec![P::LeafDigest::default(); N - 1];
        let leaf_index = 0;
        let auth_path = (0..SP::HEIGHT - 2)
            .map(|_| PathStep::<P>::new(0, vec![P::InnerDigest::default(); N - 1]))
            .collect();
        Self {
            leaf_siblings_hashes,
            auth_path,
            leaf_index,
            _m: PhantomData,
        }
    }
}

impl<const N: usize, P: Config, NP: NArySparseConfig<N, P>> NArySparsePath<N, P, NP> {
    pub fn new(
        leaf_siblings_hashes: Vec<P::LeafDigest>,
        auth_path: Vec<PathStep<P>>,
        leaf_index: usize,
    ) -> NArySparsePath<N, P, NP> {
        NArySparsePath {
            leaf_siblings_hashes,
            auth_path,
            leaf_index,
            _m: PhantomData::<NP> {},
        }
    }
}

pub struct NAryMerkleSparseTree<const N: usize, P: Config, SP: NArySparseConfig<N, P>> {
    pub tree: BTreeMap<usize, P::LeafDigest>,
    pub leaf_hash_param: <P::LeafHash as CRHScheme>::Parameters,
    pub n_to_one_hash_param: <SP::NToOneHash as CRHScheme>::Parameters,
    pub root: P::InnerDigest,
    pub empty_hashes: Vec<P::InnerDigest>,
}

pub fn gen_empty_hashes<
    const N: usize,
    F: PrimeField + Absorb,
    P: Config<InnerDigest = F, LeafDigest = F, LeafInnerDigestConverter = IdentityDigestConverter<F>>,
    SP: NArySparseConfig<N, P>,
>(
    leaf_hash_params: &<P::LeafHash as CRHScheme>::Parameters,
    n_to_one_hash_params: &<SP::NToOneHash as CRHScheme>::Parameters,
    empty_leaf: &<P as Config>::Leaf,
    height: u64,
) -> Result<Vec<P::InnerDigest>, Error> {
    let mut empty_hashes = Vec::with_capacity(height as usize);
    let empty_hash = P::LeafHash::evaluate(leaf_hash_params, empty_leaf)?;
    let mut empty_hash =
        <P::LeafInnerDigestConverter as DigestConverter<_, P::InnerDigest>>::convert(empty_hash)?;
    empty_hashes.push(empty_hash);
    for _ in 1..=height {
        empty_hash =
            <SP::NToOneHash as CRHScheme>::evaluate(n_to_one_hash_params, [empty_hash; N])?;
        empty_hashes.push(empty_hash);
    }
    Ok(empty_hashes)
}

impl<
        const N: usize,
        F: PrimeField + Absorb,
        P: Config<
            InnerDigest = F,
            LeafDigest = F,
            LeafInnerDigestConverter = IdentityDigestConverter<F>,
        >,
        SP: NArySparseConfig<N, P>,
    > NAryMerkleSparseTree<N, P, SP>
{
    /// obtain an empty tree
    pub fn blank(
        leaf_hash_params: &<P::LeafHash as CRHScheme>::Parameters,
        n_to_one_hash_params: &<SP::NToOneHash as CRHScheme>::Parameters,
        blank_leaf: &P::Leaf,
    ) -> Result<Self, Error> {
        let empty_hashes = gen_empty_hashes::<N, F, P, SP>(
            leaf_hash_params,
            n_to_one_hash_params,
            blank_leaf,
            SP::HEIGHT,
        )?;

        Ok(NAryMerkleSparseTree {
            tree: BTreeMap::new(),
            leaf_hash_param: leaf_hash_params.clone(),
            n_to_one_hash_param: n_to_one_hash_params.clone(),
            root: empty_hashes[(SP::HEIGHT - 1) as usize],
            empty_hashes,
        })
    }

    /// initialize a tree (with optional data)
    pub fn new(
        leaf_hash_params: &<P::LeafHash as CRHScheme>::Parameters,
        n_to_one_hash_params: &<SP::NToOneHash as CRHScheme>::Parameters,
        leaves: &BTreeMap<usize, P::Leaf>,
        empty_leaf: &<P as Config>::Leaf,
    ) -> Result<Self, Error>
    where
        <P as Config>::Leaf: Sized,
    {
        let num_leaves = n_leaves(SP::HEIGHT as u32, N);
        let tree_height = tree_height(N, num_leaves);
        assert!(tree_height <= SP::HEIGHT as usize);
        assert!(
            leaves.len() > 0,
            "can not initiate with empty leaves, use blank() instead"
        );

        let mut tree: BTreeMap<usize, P::InnerDigest> = BTreeMap::new();
        let empty_hashes = gen_empty_hashes::<N, F, P, SP>(
            leaf_hash_params,
            n_to_one_hash_params,
            empty_leaf,
            SP::HEIGHT,
        )?;

        // TODO: review what u32/u64/usize HEIGHT const should be
        let n_nodes = n_nodes(SP::HEIGHT as u32, N);
        // index of the first leaf within the tree
        let last_level_index = convert_index_to_last_level(n_nodes, num_leaves, 0);

        for (i, leaf) in leaves.iter() {
            tree.insert(
                last_level_index + *i,
                P::LeafHash::evaluate(leaf_hash_params, leaf)?,
            );
        }

        let mut middle_nodes: BTreeSet<usize> = BTreeSet::new();
        for i in leaves.keys() {
            middle_nodes.insert(parent(last_level_index + *i, N));
        }

        // Compute the hash values for every node in parts of the tree.
        for level in 0..SP::HEIGHT {
            // Iterate over the current level.
            for current_index in &middle_nodes {
                let left_index = left_child(*current_index, N);
                let rightmost_leaf_index = left_index + (N - 1);

                let empty_hash = empty_hashes[level as usize];

                let to_hash = (left_index..=rightmost_leaf_index)
                    .map(|i| tree.get(&i).copied().unwrap_or(empty_hash))
                    .collect::<Vec<P::InnerDigest>>();

                // Compute Hash(left || right).
                tree.insert(
                    *current_index,
                    SP::NToOneHash::evaluate(n_to_one_hash_params, to_hash)?,
                );
            }

            let tmp_middle_nodes = middle_nodes.clone();
            middle_nodes.clear();
            for i in tmp_middle_nodes {
                if !is_root(i) {
                    middle_nodes.insert(parent(i, N));
                }
            }
        }

        let root_hash = tree[&0];

        Ok(NAryMerkleSparseTree::<N, P, SP> {
            tree,
            leaf_hash_param: leaf_hash_params.clone(),
            n_to_one_hash_param: n_to_one_hash_params.clone(),
            root: root_hash,
            empty_hashes,
        })
    }

    #[inline]
    pub fn root(&self) -> P::InnerDigest {
        self.root
    }

    fn compute_auth_path(&self, index: usize) -> Vec<PathStep<P>> {
        let tree_height = SP::HEIGHT;
        let num_leaves = n_leaves(SP::HEIGHT as u32, N);
        let n_nodes = n_nodes(SP::HEIGHT as u32, N);
        let tree_index = convert_index_to_last_level(n_nodes, num_leaves, index);
        let mut path = Vec::<PathStep<P>>::with_capacity((tree_height - 2) as usize);
        let mut current_node = parent(tree_index as usize, N);

        for level in 1..SP::HEIGHT - 1 {
            let left_siblings = siblings(current_node, N, Siblings::Left);
            let right_siblings = siblings(current_node, N, Siblings::Right);

            let empty_hash = self.empty_hashes[level as usize];

            let siblings = left_siblings
                .into_iter()
                .chain(right_siblings)
                .map(|idx| self.tree.get(&idx).copied().unwrap_or(empty_hash))
                .collect::<Vec<P::InnerDigest>>();

            let step = PathStep::new((current_node - 1) % N, siblings);
            path.push(step);

            current_node = parent(current_node, N);
        }
        assert!(is_root(current_node));
        path
    }

    pub fn generate_proof(&self, index: usize) -> Result<NArySparsePath<N, P, SP>, Error> {
        let path = self.compute_auth_path(index);
        Ok(NArySparsePath::new(
            self.get_leaf_siblings_hashes(index as usize),
            path.into_iter().rev().collect(),
            (index as usize) % N,
        ))
    }

    pub fn get_leaf_siblings_hashes(&self, index: usize) -> Vec<P::LeafDigest> {
        let num_leaves = n_leaves(SP::HEIGHT as u32, N);
        let n_nodes = n_nodes(SP::HEIGHT as u32, N);
        let last_level_index = convert_index_to_last_level(n_nodes, num_leaves, 0);
        let left_siblings = leaf_siblings(index, N, Siblings::Left);
        let right_siblings = leaf_siblings(index, N, Siblings::Right);
        left_siblings
            .iter()
            .chain(&right_siblings)
            .map(|idx| {
                self.tree
                    .get(&(*idx + last_level_index))
                    .unwrap_or(&self.empty_hashes[0])
                    .clone()
            })
            .collect()
    }

    /// Given the index and new leaf, return the hash of leaf and an updated path in order from root to bottom non-leaf level.
    /// This does not mutate the underlying tree.
    fn updated_path<T: Borrow<P::Leaf>>(
        &self,
        index: usize,
        new_leaf: T,
    ) -> Result<(P::LeafDigest, Vec<P::InnerDigest>), crate::Error> {
        let num_leaves = n_leaves(SP::HEIGHT as u32, N);
        let n_nodes = n_nodes(SP::HEIGHT as u32, N);
        let last_level_index = convert_index_to_last_level(n_nodes, num_leaves, 0);

        // calculate the hash of leaf
        let new_leaf_hash: P::LeafDigest = P::LeafHash::evaluate(&self.leaf_hash_param, new_leaf)?;

        // calculate leaf sibling hash and locate its position (left or right)
        let left_siblings = leaf_siblings(index, N, Siblings::Left)
            .iter()
            .map(|idx| {
                self.tree
                    .get(&(*idx + last_level_index))
                    .unwrap_or(&self.empty_hashes[0])
                    .clone()
            })
            .collect();
        let right_siblings = leaf_siblings(index, N, Siblings::Right)
            .iter()
            .map(|idx| {
                self.tree
                    .get(&(*idx + last_level_index))
                    .unwrap_or(&self.empty_hashes[0])
                    .clone()
            })
            .collect();

        let to_hash = [left_siblings, vec![new_leaf_hash.clone()], right_siblings]
            .concat()
            .iter()
            .map(|ld| P::LeafInnerDigestConverter::convert(ld.clone()))
            .collect::<Result<
                Vec<<P::LeafInnerDigestConverter as DigestConverter<_, _>>::TargetType>,
                Error,
            >>()?;

        // calculate the updated hash at bottom non-leaf-level
        let mut path_bottom_to_top = Vec::with_capacity((SP::HEIGHT - 1) as usize);
        path_bottom_to_top.push(SP::NToOneHash::evaluate(
            &self.n_to_one_hash_param,
            to_hash,
        )?);

        // then calculate the updated hash from bottom to root
        let leaf_index_in_tree = convert_index_to_last_level(n_nodes, num_leaves, index);
        let mut prev_index = parent(leaf_index_in_tree, N);
        let mut level = 1; // NOTE: we need to keep track of level, since we have to provide
                           // empty hash value (main difference with dense merkle trees
                           // implem)

        while !is_root(prev_index) {
            let left_siblings = siblings(prev_index, N, Siblings::Left)
                .iter()
                .map(|idx| {
                    self.tree
                        .get(&(*idx))
                        .unwrap_or(&self.empty_hashes[level])
                        .clone()
                })
                .collect();
            let right_siblings = siblings(prev_index, N, Siblings::Right)
                .iter()
                .map(|idx| {
                    self.tree
                        .get(&(*idx))
                        .unwrap_or(&self.empty_hashes[level])
                        .clone()
                })
                .collect();
            let to_hash = [
                left_siblings,
                vec![path_bottom_to_top.last().unwrap().clone()],
                right_siblings,
            ]
            .concat();

            let evaluated = SP::NToOneHash::evaluate(&self.n_to_one_hash_param, to_hash)?;
            path_bottom_to_top.push(evaluated);
            prev_index = parent(prev_index, N);
            level += 1;
        }

        debug_assert_eq!(path_bottom_to_top.len(), (SP::HEIGHT - 1) as usize);
        let path_top_to_bottom: Vec<_> = path_bottom_to_top.into_iter().rev().collect();
        Ok((new_leaf_hash, path_top_to_bottom))
    }

    pub fn update(&mut self, index: usize, new_leaf: &P::Leaf) -> Result<(), crate::Error> {
        let num_leaves = n_leaves(SP::HEIGHT as u32, N);
        let n_nodes = n_nodes(SP::HEIGHT as u32, N);
        let leaf_index_in_tree = convert_index_to_last_level(n_nodes, num_leaves, index);

        let (updated_leaf_hash, mut updated_path) = self.updated_path(index, new_leaf)?;
        self.tree.insert(leaf_index_in_tree, updated_leaf_hash);
        let mut curr_index = convert_index_to_last_level(n_nodes, num_leaves, index);
        for _ in 0..SP::HEIGHT - 1 {
            curr_index = parent(curr_index, N);
            self.tree.insert(curr_index, updated_path.pop().unwrap());
        }
        self.root = self.tree[&0];
        Ok(())
    }

    /// Update the leaf and check if the updated root is equal to `asserted_new_root`.
    /// Tree will not be modified if the check fails.
    pub fn check_update(
        &mut self,
        index: usize,
        new_leaf: &P::Leaf,
        asserted_new_root: &P::InnerDigest,
    ) -> Result<bool, crate::Error> {
        let num_leaves = n_leaves(SP::HEIGHT as u32, N);
        let n_nodes = n_nodes(SP::HEIGHT as u32, N);
        let leaf_index_in_tree = convert_index_to_last_level(n_nodes, num_leaves, index);
        let (updated_leaf_hash, mut updated_path) = self.updated_path(index, new_leaf)?;
        if &updated_path[0] != asserted_new_root {
            return Ok(false);
        }
        self.tree.insert(leaf_index_in_tree, updated_leaf_hash);
        let mut curr_index = leaf_index_in_tree;
        for _ in 0..SP::HEIGHT - 1 {
            curr_index = parent(curr_index, N);
            self.tree.insert(curr_index, updated_path.pop().unwrap());
        }
        assert!(is_root(curr_index));
        self.root = self.tree[&0];
        Ok(true)
    }
}

impl<const N: usize, P: Config, SP: NArySparseConfig<N, P>> NArySparsePath<N, P, SP>
where
    Vec<<P as Config>::InnerDigest>: Borrow<<SP::NToOneHash as CRHScheme>::Input>,
    Vec<
        <<P as Config>::LeafInnerDigestConverter as DigestConverter<
            <P as Config>::LeafDigest,
            <<P as Config>::TwoToOneHash as TwoToOneCRHScheme>::Input,
        >>::TargetType,
    >: Borrow<<<SP as NArySparseConfig<N, P>>::NToOneHash as CRHScheme>::Input>,
{
    /// Verify that a leaf is at `self.index` of the merkle tree.
    /// * `leaf_size`: leaf size in number of bytes
    ///
    /// `verify` infers the tree height by setting `tree_height = self.auth_path.len() + 2`
    pub fn verify<L: Borrow<P::Leaf> + Debug>(
        &self,
        leaf_hash_params: &LeafParam<P>,
        n_to_one_params: &NToOneParam<N, P, SP>,
        root_hash: &P::InnerDigest,
        leaf: L,
    ) -> Result<bool, crate::Error>
    where
        <<P as Config>::LeafInnerDigestConverter as DigestConverter<
            <P as Config>::LeafDigest,
            <<P as Config>::TwoToOneHash as TwoToOneCRHScheme>::Input,
        >>::TargetType: Debug,
    {
        // calculate leaf hash
        let claimed_leaf_hash = P::LeafHash::evaluate(&leaf_hash_params, leaf)?;
        let mut leaves = self.leaf_siblings_hashes.clone();
        let leaf_index_in_array = self.leaf_index;
        leaves.insert(leaf_index_in_array as usize, claimed_leaf_hash);

        let to_hash = leaves
            .iter()
            .map(|ld| P::LeafInnerDigestConverter::convert(ld.clone()))
            .collect::<Result<
                Vec<<P::LeafInnerDigestConverter as DigestConverter<_, _>>::TargetType>,
                Error,
            >>()?;

        // check hash along the path from bottom to root
        let mut curr_path_node = SP::NToOneHash::evaluate(&n_to_one_params, to_hash)?;

        // Check levels between leaf level and root
        for level in (0..self.auth_path.len()).rev() {
            let step = &self.auth_path[level];
            let mut to_hash = step.siblings.clone();
            to_hash.insert(step.index as usize, curr_path_node);
            // check if path node at this level is left or right
            // update curr_path_node

            curr_path_node = SP::NToOneHash::evaluate(&n_to_one_params, to_hash)?;
        }

        //// check if final hash is root
        if &curr_path_node != root_hash {
            return Ok(false);
        }

        Ok(true)
    }
}

#[inline]
fn is_root(index: usize) -> bool {
    index == 0
}

#[cfg(test)]
pub mod tests {

    use std::{borrow::Borrow, collections::BTreeMap, marker::PhantomData};

    use ark_bn254::Fr;
    use ark_crypto_primitives::{
        crh::{
            poseidon::{TwoToOneCRH, CRH},
            CRHScheme,
        },
        merkle_tree::{Config, IdentityDigestConverter},
        sponge::{poseidon::PoseidonConfig, Absorb},
        Error,
    };
    use ark_ff::PrimeField;
    use ark_std::rand::Rng;

    use crate::{
        sparse::NAryMerkleSparseTree,
        tests::{
            initialize_poseidon_config, BinaryPoseidonTree, PoseidonTree, QuinaryPoseidonTree,
            TernaryPoseidonTree,
        },
        traits::NAryConfig,
        NAryMerkleTree,
    };

    use super::NArySparseConfig;

    impl NArySparseConfig<2, PoseidonTree<Fr>> for BinaryPoseidonTree<Fr> {
        const HEIGHT: u64 = 4;
        type NToOneHashParams = PoseidonConfig<Fr>;
        type NToOneHash = CRH<Fr>;
    }

    impl NArySparseConfig<3, PoseidonTree<Fr>> for TernaryPoseidonTree<Fr> {
        const HEIGHT: u64 = 4;

        type NToOneHashParams = PoseidonConfig<Fr>;
        type NToOneHash = CRH<Fr>;
    }

    impl NArySparseConfig<5, PoseidonTree<Fr>> for QuinaryPoseidonTree<Fr> {
        const HEIGHT: u64 = 4;
        type NToOneHashParams = PoseidonConfig<Fr>;
        type NToOneHash = CRH<Fr>;
    }

    pub struct NoArrayCRH<F> {
        _f: PhantomData<F>,
    }

    // NOTE: we also define different configs for testing sparse merkle trees, since leaves should
    // implement Sized, which is not the case when leaves are arrays.
    impl<F: PrimeField + Absorb> CRHScheme for NoArrayCRH<F> {
        type Input = F;
        type Output = F;
        type Parameters = PoseidonConfig<F>;

        fn setup<R: Rng>(_r: &mut R) -> Result<Self::Parameters, Error> {
            todo!()
        }

        fn evaluate<T: Borrow<Self::Input>>(
            parameters: &Self::Parameters,
            input: T,
        ) -> Result<Self::Output, Error> {
            let input = input.borrow();
            CRH::evaluate(parameters, [*input])
        }
    }

    // NOTE: we prefix it with `NoArray` to emphasize that leaves are not defined as arrays but as
    // a single field element, which is required by the trait
    #[derive(Clone)]
    pub struct NoArrayPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> Config for NoArrayPoseidonTree<F> {
        type Leaf = F;
        type LeafDigest = F;
        type LeafInnerDigestConverter = IdentityDigestConverter<F>;
        type InnerDigest = F;
        type LeafHash = NoArrayCRH<F>;
        type TwoToOneHash = TwoToOneCRH<F>;
    }

    pub struct NoArrayBinaryPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> NArySparseConfig<2, NoArrayPoseidonTree<F>>
        for NoArrayBinaryPoseidonTree<F>
    {
        type NToOneHashParams = PoseidonConfig<F>;
        type NToOneHash = CRH<F>;

        const HEIGHT: u64 = 4;
    }

    pub struct NoArrayTernaryPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> NArySparseConfig<3, NoArrayPoseidonTree<F>>
        for NoArrayTernaryPoseidonTree<F>
    {
        type NToOneHashParams = PoseidonConfig<F>;
        type NToOneHash = CRH<F>;

        const HEIGHT: u64 = 4;
    }

    pub struct NoArrayQuinaryPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> NArySparseConfig<5, NoArrayPoseidonTree<F>>
        for NoArrayQuinaryPoseidonTree<F>
    {
        type NToOneHashParams = PoseidonConfig<F>;
        type NToOneHash = CRH<F>;
        const HEIGHT: u64 = 4;
    }

    fn run_test<
        const N: usize,
        NP: NAryConfig<N, PoseidonTree<Fr>, NToOneHashParams = PoseidonConfig<Fr>>,
        SP: NArySparseConfig<N, NoArrayPoseidonTree<Fr>, NToOneHashParams = PoseidonConfig<Fr>>,
    >(
        n_leaf_nodes: usize,
        poseidon_conf: PoseidonConfig<Fr>,
        index_values: Vec<(usize, Fr)>,
    ) {
        // testing binary tree
        let mut leaves = vec![[Fr::default()]; n_leaf_nodes];
        let mut sparse_leaves = BTreeMap::<usize, Fr>::new();
        for (i, value) in index_values.clone() {
            leaves[i as usize] = [value];
            sparse_leaves.insert(i, value);
        }

        let mt =
            NAryMerkleTree::<N, PoseidonTree<Fr>, NP>::new(&poseidon_conf, &poseidon_conf, &leaves)
                .unwrap();
        let mut sparse_mt = NAryMerkleSparseTree::<N, NoArrayPoseidonTree<Fr>, SP>::new(
            &poseidon_conf,
            &poseidon_conf,
            &sparse_leaves,
            &Fr::default(),
        )
        .unwrap();

        assert_eq!(mt.root(), sparse_mt.root());

        for (i, value) in index_values.clone() {
            let proof_mt = mt.generate_proof(i as usize).unwrap();
            let proof_sparse_mt = sparse_mt.generate_proof(i as usize).unwrap();

            // check that path are equiv to dense implementation
            assert_eq!(proof_mt.auth_path.len(), proof_sparse_mt.auth_path.len());
            assert!(proof_mt
                .auth_path
                .into_iter()
                .zip(&proof_sparse_mt.auth_path)
                .all(|(step1, step2)| step1.siblings == step2.siblings));
            assert_eq!(
                proof_mt.leaf_siblings_hashes,
                proof_sparse_mt.leaf_siblings_hashes
            );

            // check that proof is verified
            assert!(proof_sparse_mt
                .verify(
                    &sparse_mt.leaf_hash_param,
                    &sparse_mt.n_to_one_hash_param,
                    &sparse_mt.root(),
                    value,
                )
                .unwrap());
        }

        // check update logic
        for (i, value) in index_values.clone() {
            let new_leaf = value + Fr::from(1000);
            let (_, updated_path) = sparse_mt.updated_path(i, new_leaf).unwrap();

            let is_updated = sparse_mt
                .check_update(i, &new_leaf, &updated_path[0])
                .unwrap();
            assert!(is_updated);
        }
    }

    #[test]
    fn test_nary_sparse_trees() {
        let poseidon_conf = initialize_poseidon_config::<Fr>();

        let index_values = vec![(0, Fr::from(42)), (4, Fr::from(24))];
        run_test::<2, BinaryPoseidonTree<Fr>, NoArrayBinaryPoseidonTree<Fr>>(
            8,
            poseidon_conf.clone(),
            index_values.clone(),
        );

        let index_values = vec![(0, Fr::from(42)), (4, Fr::from(24)), (25, Fr::from(42))];
        run_test::<3, TernaryPoseidonTree<Fr>, NoArrayTernaryPoseidonTree<Fr>>(
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
        run_test::<5, QuinaryPoseidonTree<Fr>, NoArrayQuinaryPoseidonTree<Fr>>(
            125,
            poseidon_conf.clone(),
            index_values,
        );
    }
}

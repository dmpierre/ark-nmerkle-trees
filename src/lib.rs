use std::borrow::Borrow;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::vec;

use ark_crypto_primitives::crh::{CRHScheme, TwoToOneCRHScheme};
use ark_crypto_primitives::merkle_tree::DigestConverter;
use ark_crypto_primitives::{merkle_tree::Config, Error};
use ark_ff::Zero;
use ark_std::{cfg_into_iter, cfg_iter_mut};
use traits::NAryConfig;

pub mod constraints;
pub mod sparse;
pub mod traits;

pub type LeafParam<P: Config> = <P::LeafHash as CRHScheme>::Parameters;
pub type NToOneParam<const N: usize, P: Config, NP: NAryConfig<N, P>> =
    <<NP as NAryConfig<N, P>>::NToOneHash as CRHScheme>::Parameters;

pub struct NAryMerkleTree<const N: usize, P: Config, NP: NAryConfig<N, P>> {
    /// stores the non-leaf nodes in level order. The first element is the root node.
    /// The ith nodes (starting at 1st) children are at indices `2*i`, `2*i+1`
    non_leaf_nodes: Vec<P::InnerDigest>,
    /// store the hash of leaf nodes from left to right
    leaf_nodes: Vec<P::LeafDigest>,
    /// Store the inner hash parameters
    n_to_one_hash_param: NToOneParam<N, P, NP>,
    /// Store the leaf hash parameters
    leaf_hash_param: <<P as Config>::LeafHash as CRHScheme>::Parameters,
    /// Stores the height of the MerkleTree
    height: usize,
}

#[derive(Debug, Clone)]
pub struct PathStep<P: Config> {
    index: usize, // indicates position in the array before hashing with siblings
    siblings: Vec<P::InnerDigest>,
}

#[derive(Default, Clone)]
pub struct NAryPath<const N: usize, P: Config, NP: NAryConfig<N, P>> {
    leaf_siblings_hashes: Vec<P::LeafDigest>,
    auth_path: Vec<PathStep<P>>,
    leaf_index: usize, // indicates position in the array before hashing siblings leaf nodes
    _m: PhantomData<NP>,
}

impl<const N: usize, P: Config, NP: NAryConfig<N, P>> NAryPath<N, P, NP> {
    pub fn new(
        leaf_siblings_hashes: Vec<P::LeafDigest>,
        auth_path: Vec<PathStep<P>>,
        leaf_index: usize,
    ) -> Self {
        Self {
            leaf_siblings_hashes,
            auth_path,
            leaf_index,
            _m: PhantomData::<NP>,
        }
    }
}

impl<P: Config> PathStep<P> {
    pub fn new(index: usize, siblings: Vec<P::InnerDigest>) -> Self {
        Self { index, siblings }
    }
}

impl<const N: usize, P: Config, NP: NAryConfig<N, P>> NAryMerkleTree<N, P, NP>
where
    Vec<<P as Config>::InnerDigest>: Borrow<<NP::NToOneHash as CRHScheme>::Input>,
    Vec<
        <<P as Config>::LeafInnerDigestConverter as DigestConverter<
            <P as Config>::LeafDigest,
            <<P as Config>::TwoToOneHash as TwoToOneCRHScheme>::Input,
        >>::TargetType,
    >: Borrow<<<NP as NAryConfig<N, P>>::NToOneHash as CRHScheme>::Input>,
{
    pub fn new<L: AsRef<P::Leaf> + Send>(
        leaf_hash_param: &LeafParam<P>,
        n_to_one_hash_param: &NToOneParam<N, P, NP>,
        #[cfg(not(feature = "parallel"))] leaves: impl IntoIterator<Item = L>,
        #[cfg(feature = "parallel")] leaves: impl IntoParallelIterator<Item = L>,
    ) -> Result<Self, Error> {
        let leaf_digests: Vec<_> = cfg_into_iter!(leaves)
            .map(|input| P::LeafHash::evaluate(leaf_hash_param, input.as_ref()))
            .collect::<Result<Vec<_>, _>>()?;

        Self::new_with_leaf_digest(leaf_hash_param, n_to_one_hash_param, leaf_digests)
    }

    pub fn new_with_leaf_digest(
        leaf_hash_param: &LeafParam<P>,
        n_to_one_hash_param: &NToOneParam<N, P, NP>,
        leaf_digests: Vec<P::LeafDigest>,
    ) -> Result<Self, Error> {
        let leaf_nodes_size = leaf_digests.len();
        let tree_height = tree_height(N, leaf_nodes_size);
        let non_leaf_nodes_size = n_non_leaf_nodes(N, leaf_nodes_size);

        // initialize the merkle tree as array of nodes in level order
        let hash_of_empty: P::InnerDigest = P::InnerDigest::default();

        // initialize the merkle tree as array of nodes in level order
        let mut non_leaf_nodes: Vec<P::InnerDigest> = cfg_into_iter!(0..non_leaf_nodes_size)
            .map(|_| hash_of_empty.clone())
            .collect();

        // Compute the starting indices for each non-leaf level of the tree
        let mut index = 0;
        let mut level_indices = Vec::with_capacity(tree_height - 1);
        for _ in 0..(tree_height - 1) {
            level_indices.push(index);
            index = left_child(index, N);
        }

        // compute the hash values for the non-leaf bottom layer
        {
            let start_index = level_indices.pop().unwrap();
            let upper_bound = left_child(start_index, N);

            cfg_iter_mut!(non_leaf_nodes[start_index..upper_bound])
                .enumerate()
                .try_for_each(|(i, n)| {
                    // `left_child(current_index)` and `right_child(current_index) returns the position of
                    // leaf in the whole tree (represented as a list in level order). We need to shift it
                    // by `-upper_bound` to get the index in `leaf_nodes` list.

                    // similarly, we need to rescale i by start_index
                    // to get the index outside the slice and in the level-ordered list of nodes
                    let current_index = i + start_index;
                    let left_leaf_index = left_child(current_index, N) - upper_bound;
                    let rightmost_leaf_index = left_leaf_index + (N - 1);
                    let converted_ld = leaf_digests[left_leaf_index..=rightmost_leaf_index]
                        .iter()
                        .map(|ld| P::LeafInnerDigestConverter::convert(ld.clone()))
                        .collect::<Result<
                            Vec<<P::LeafInnerDigestConverter as DigestConverter<_, _>>::TargetType>,
                            Error,
                        >>()?;
                    *n = NP::NToOneHash::evaluate(n_to_one_hash_param, converted_ld)?;

                    Ok::<(), crate::Error>(())
                })?;
        }

        // compute the hash values for nodes in every other layer in the tree
        level_indices.reverse();

        for &start_index in &level_indices {
            // The layer beginning `start_index` ends at `upper_bound` (exclusive).
            let upper_bound = left_child(start_index, N);

            let (nodes_at_level, nodes_at_prev_level) =
                non_leaf_nodes[..].split_at_mut(upper_bound);

            // Iterate over the nodes at the current level, and compute the hash of each node
            cfg_iter_mut!(nodes_at_level[start_index..])
                .enumerate()
                .try_for_each(|(i, n)| {
                    // `left_child(current_index)` and `right_child(current_index) returns the position of
                    // leaf in the whole tree (represented as a list in level order). We need to shift it
                    // by `-upper_bound` to get the index in `leaf_nodes` list.

                    // similarly, we need to rescale i by start_index
                    // to get the index outside the slice and in the level-ordered list of nodes
                    let current_index = i + start_index;
                    let left_leaf_index = left_child(current_index, N) - upper_bound;
                    let rightmost_leaf_index = left_leaf_index + (N - 1);

                    // need for unwrap as Box<Error> does not implement trait Send
                    *n = NP::NToOneHash::evaluate(
                        n_to_one_hash_param,
                        nodes_at_prev_level[left_leaf_index..=rightmost_leaf_index].to_vec(),
                    )?;
                    Ok::<_, crate::Error>(())
                })?;
        }

        Ok(NAryMerkleTree {
            leaf_nodes: leaf_digests,
            non_leaf_nodes,
            height: tree_height,
            leaf_hash_param: leaf_hash_param.clone(),
            n_to_one_hash_param: n_to_one_hash_param.clone(),
        })
    }

    /// Returns the root of the Merkle tree.
    pub fn root(&self) -> P::InnerDigest {
        self.non_leaf_nodes[0].clone()
    }

    /// Returns the height of the Merkle tree.
    pub fn height(&self) -> usize {
        self.height
    }

    /// Returns the authentication path from leaf at `index` to root, as a Vec of digests
    fn compute_auth_path(&self, index: usize) -> Vec<PathStep<P>> {
        // gather basic tree information
        let tree_height = tree_height(N, self.leaf_nodes.len());
        let n_nodes = n_nodes(tree_height as u32, N);

        // Get Leaf hash, and leaf sibling hash,
        let leaf_index_in_tree = convert_index_to_last_level(n_nodes, self.leaf_nodes.len(), index);

        // path.len() = `tree height - 2`, the two missing elements being the leaf sibling hash and the root
        let mut path = Vec::<PathStep<P>>::with_capacity(tree_height - 2);
        // Iterate from the bottom layer after the leaves, to the top, storing all sibling node's hash values.
        let mut current_node = parent(leaf_index_in_tree, N);
        while !is_root(current_node) {
            let left_siblings = siblings(current_node, N, Siblings::Left);
            let right_siblings = siblings(current_node, N, Siblings::Right);
            let siblings = left_siblings
                .iter()
                .chain(&right_siblings)
                .map(|idx| self.non_leaf_nodes[*idx].clone())
                .collect();
            let path_step = PathStep::new((current_node - 1) % N, siblings);
            path.push(path_step);
            current_node = parent(current_node, N);
        }

        debug_assert_eq!(path.len(), tree_height - 2);

        // we want to make path from root to bottom
        path.reverse();
        path
    }

    pub fn get_leaf_siblings_hashes(&self, index: usize) -> Vec<P::LeafDigest> {
        let left_siblings = leaf_siblings(index, N, Siblings::Left);
        let right_siblings = leaf_siblings(index, N, Siblings::Right);
        left_siblings
            .iter()
            .chain(&right_siblings)
            .map(|idx| self.leaf_nodes[*idx].clone())
            .collect()
    }

    pub fn generate_proof(&self, index: usize) -> Result<NAryPath<N, P, NP>, Error> {
        let path = self.compute_auth_path(index);
        Ok(NAryPath::new(
            self.get_leaf_siblings_hashes(index),
            path,
            index % N,
        ))
    }

    /// Given the index and new leaf, return the hash of leaf and an updated path in order from root to bottom non-leaf level.
    /// This does not mutate the underlying tree.
    fn updated_path<T: Borrow<P::Leaf>>(
        &self,
        index: usize,
        new_leaf: T,
    ) -> Result<(P::LeafDigest, Vec<P::InnerDigest>), crate::Error> {
        // calculate the hash of leaf
        let new_leaf_hash: P::LeafDigest = P::LeafHash::evaluate(&self.leaf_hash_param, new_leaf)?;

        // calculate leaf sibling hash and locate its position (left or right)
        let left_siblings = leaf_siblings(index, N, Siblings::Left)
            .iter()
            .map(|idx| self.leaf_nodes[*idx].clone())
            .collect();
        let right_siblings = leaf_siblings(index, N, Siblings::Right)
            .iter()
            .map(|idx| self.leaf_nodes[*idx].clone())
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
        let mut path_bottom_to_top = Vec::with_capacity(self.height - 1);
        {
            // PathStep::new(index, siblings)
            path_bottom_to_top.push(NP::NToOneHash::evaluate(
                &self.n_to_one_hash_param,
                to_hash,
            )?);
        }

        // then calculate the updated hash from bottom to root
        let n_nodes = n_nodes(self.height as u32, N);
        let leaf_index_in_tree = convert_index_to_last_level(n_nodes, self.leaf_nodes.len(), index);
        let mut prev_index = parent(leaf_index_in_tree, N);

        while !is_root(prev_index) {
            let left_siblings = siblings(prev_index, N, Siblings::Left)
                .iter()
                .map(|idx| self.non_leaf_nodes[*idx].clone())
                .collect();
            let right_siblings = siblings(prev_index, N, Siblings::Right)
                .iter()
                .map(|idx| self.non_leaf_nodes[*idx].clone())
                .collect();
            let to_hash = [
                left_siblings,
                vec![path_bottom_to_top.last().unwrap().clone()],
                right_siblings,
            ]
            .concat();

            let evaluated = NP::NToOneHash::evaluate(&self.n_to_one_hash_param, to_hash)?;
            path_bottom_to_top.push(evaluated);
            prev_index = parent(prev_index, N);
        }

        debug_assert_eq!(path_bottom_to_top.len(), self.height - 1);
        let path_top_to_bottom: Vec<_> = path_bottom_to_top.into_iter().rev().collect();
        Ok((new_leaf_hash, path_top_to_bottom))
    }

    pub fn update(&mut self, index: usize, new_leaf: &P::Leaf) -> Result<(), crate::Error> {
        assert!(index < self.leaf_nodes.len(), "index out of range");
        let (updated_leaf_hash, mut updated_path) = self.updated_path(index, new_leaf)?;
        self.leaf_nodes[index] = updated_leaf_hash;
        let mut curr_index = convert_index_to_last_level(
            n_nodes(self.height as u32, N),
            self.leaf_nodes.len(),
            index,
        );
        for _ in 0..self.height - 1 {
            curr_index = parent(curr_index, N);
            self.non_leaf_nodes[curr_index] = updated_path.pop().unwrap();
        }
        Ok(())
    }

    /// Update the leaf and check if the updated root is equal to `asserted_new_root`.
    ///
    /// Tree will not be modified if the check fails.
    pub fn check_update(
        &mut self,
        index: usize,
        new_leaf: &P::Leaf,
        asserted_new_root: &P::InnerDigest,
    ) -> Result<bool, crate::Error> {
        assert!(index < self.leaf_nodes.len(), "index out of range");
        let (updated_leaf_hash, mut updated_path) = self.updated_path(index, new_leaf)?;
        if &updated_path[0] != asserted_new_root {
            return Ok(false);
        }
        self.leaf_nodes[index] = updated_leaf_hash;
        let mut curr_index = convert_index_to_last_level(
            n_nodes(self.height as u32, N),
            self.leaf_nodes.len(),
            index,
        );
        for _ in 0..self.height - 1 {
            curr_index = parent(curr_index, N);
            self.non_leaf_nodes[curr_index] = updated_path.pop().unwrap();
        }
        Ok(true)
    }
}

impl<const N: usize, P: Config, NP: NAryConfig<N, P>> NAryPath<N, P, NP>
where
    Vec<<P as Config>::InnerDigest>: Borrow<<NP::NToOneHash as CRHScheme>::Input>,
    Vec<
        <<P as Config>::LeafInnerDigestConverter as DigestConverter<
            <P as Config>::LeafDigest,
            <<P as Config>::TwoToOneHash as TwoToOneCRHScheme>::Input,
        >>::TargetType,
    >: Borrow<<<NP as NAryConfig<N, P>>::NToOneHash as CRHScheme>::Input>,
{
    /// Verify that a leaf is at `self.index` of the merkle tree.
    /// * `leaf_size`: leaf size in number of bytes
    ///
    /// `verify` infers the tree height by setting `tree_height = self.auth_path.len() + 2`
    pub fn verify<L: Borrow<P::Leaf> + Debug>(
        &self,
        leaf_hash_params: &LeafParam<P>,
        n_to_one_params: &NToOneParam<N, P, NP>,
        root_hash: &P::InnerDigest,
        leaf: L,
    ) -> Result<bool, crate::Error> {
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
        let mut curr_path_node = NP::NToOneHash::evaluate(&n_to_one_params, to_hash)?;

        // Check levels between leaf level and root
        for level in (0..self.auth_path.len()).rev() {
            let step = &self.auth_path[level];
            let mut to_hash = step.siblings.clone();
            to_hash.insert(step.index as usize, curr_path_node);
            // check if path node at this level is left or right
            // update curr_path_node
            curr_path_node = NP::NToOneHash::evaluate(&n_to_one_params, to_hash)?;
        }

        //// check if final hash is root
        if &curr_path_node != root_hash {
            return Ok(false);
        }

        Ok(true)
    }
}

/// Returns true iff the index represents the root.
#[inline]
pub(crate) fn is_root(index: usize) -> bool {
    index == 0
}

pub(crate) fn tree_height(arity: usize, num_leaves: usize) -> usize {
    if num_leaves == 1 {
        return 1;
    }
    let mut num_leaves = num_leaves;
    let mut height = 1;
    while num_leaves != 1 {
        num_leaves /= arity;
        height += 1;
    }
    height
}

// root included
pub(crate) fn n_nodes(height: u32, arity: usize) -> usize {
    let mut n_nodes = 1;
    for i in 1..height {
        n_nodes += arity.pow(i);
    }
    n_nodes
}

pub(crate) fn n_leaves(height: u32, arity: usize) -> usize {
    arity.pow(height - 1)
}

// user provides index between 0 and N leaves, convert it to index in whole tree
#[inline]
pub(crate) fn convert_index_to_last_level(
    n_nodes: usize,
    n_nodes_last_layer: usize,
    leaf_idx: usize,
) -> usize {
    n_nodes - n_nodes_last_layer + leaf_idx
}

// index of parent node
// idx is position in the tree
#[inline]
pub(crate) fn parent(idx: usize, arity: usize) -> usize {
    if idx == 0 {
        return 0;
    }
    (idx - 1) / arity
}

pub(crate) enum Siblings {
    Left,
    Right,
}

pub(crate) fn leaf_siblings(idx: usize, arity: usize, siblings: Siblings) -> Vec<usize> {
    let offset = idx % arity;
    let siblings = match siblings {
        Siblings::Left => {
            // this is the leftmost leaf
            if offset.is_zero() {
                return vec![];
            }
            ((idx - offset)..idx).collect()
        }
        Siblings::Right => {
            // this is the rightmost leaf
            if offset == arity - 1 {
                return vec![];
            }
            ((idx + 1)..(idx + arity - offset)).collect()
        }
    };

    siblings
}

pub(crate) fn siblings(idx: usize, arity: usize, siblings: Siblings) -> Vec<usize> {
    // the root is in the list of non leaf nodes, we have to subtract one
    let offset = (idx - 1) % arity;
    let siblings = match siblings {
        Siblings::Left => {
            if offset.is_zero() {
                return vec![];
            }
            ((idx - offset)..idx).collect()
        }
        Siblings::Right => {
            if offset == arity - 1 {
                return vec![];
            }
            ((idx + 1)..(idx + arity - offset)).collect()
        }
    };

    siblings
}

/// Returns the index of the left child, given an index.
#[inline]
pub(crate) fn left_child(index: usize, arity: usize) -> usize {
    arity * index + 1
}

pub(crate) fn n_non_leaf_nodes(arity: usize, n_leaf_nodes: usize) -> usize {
    let tree_height = tree_height(arity, n_leaf_nodes);
    n_nodes(tree_height as u32, arity) - n_leaf_nodes
}

#[cfg(test)]
pub mod tests {

    use std::marker::PhantomData;

    use super::*;
    use ark_bn254::Fr;
    use ark_crypto_primitives::{
        crh::poseidon::{TwoToOneCRH, CRH},
        merkle_tree::{IdentityDigestConverter, MerkleTree},
        sponge::{
            poseidon::{find_poseidon_ark_and_mds, PoseidonConfig},
            Absorb,
        },
    };
    use ark_ff::PrimeField;

    #[inline]
    fn ark_tree_height(num_leaves: usize) -> usize {
        if num_leaves == 1 {
            return 1;
        }

        (ark_std::log2(num_leaves) as usize) + 1
    }

    #[test]
    fn utils() {
        // checking that it returns correct values for balanced binary tree
        assert_eq!(ark_tree_height(8), tree_height(2, 8));
        assert_eq!(ark_tree_height(16), tree_height(2, 16));

        assert_eq!(tree_height(5, 1), 1);
        assert_eq!(tree_height(5, 5), 2);
        assert_eq!(tree_height(5, 25), 3);
        assert_eq!(tree_height(5, 125), 4);

        assert_eq!(n_nodes(3, 3), 13);
        assert_eq!(n_nodes(3, 4), 21);
        assert_eq!(n_nodes(3, 5), 31);

        assert_eq!(parent(0, 3), 0);
        assert_eq!(parent(3, 3), 0);
        assert_eq!(parent(6, 3), 1);
        assert_eq!(parent(9, 3), 2);
        assert_eq!(parent(13, 3), 4);
        assert_eq!(parent(16, 3), 5);

        assert_eq!(siblings(5, 4, Siblings::Left), vec![]);
        assert_eq!(siblings(6, 4, Siblings::Left), vec![5]);
        assert_eq!(siblings(7, 4, Siblings::Left), vec![5, 6]);
        assert_eq!(siblings(8, 4, Siblings::Left), vec![5, 6, 7]);
        assert_eq!(siblings(5, 4, Siblings::Right), vec![6, 7, 8]);
        assert_eq!(siblings(6, 4, Siblings::Right), vec![7, 8]);
        assert_eq!(siblings(7, 4, Siblings::Right), vec![8]);
        assert_eq!(siblings(8, 4, Siblings::Right), vec![]);

        assert_eq!(siblings(4, 3, Siblings::Left), vec![]);
        assert_eq!(siblings(5, 3, Siblings::Left), vec![4]);
        assert_eq!(siblings(6, 3, Siblings::Left), vec![4, 5]);
        assert_eq!(siblings(4, 3, Siblings::Right), vec![5, 6]);
        assert_eq!(siblings(5, 3, Siblings::Right), vec![6]);
        assert_eq!(siblings(6, 3, Siblings::Right), vec![]);

        assert_eq!(n_non_leaf_nodes(2, 4), 3);
        assert_eq!(n_non_leaf_nodes(2, 16), 15);
        assert_eq!(n_non_leaf_nodes(3, 3), 1);
        assert_eq!(n_non_leaf_nodes(3, 9), 4);
        assert_eq!(n_non_leaf_nodes(4, 4), 1);
        assert_eq!(n_non_leaf_nodes(4, 16), 5);
    }

    #[derive(Clone)]
    pub struct PoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> Config for PoseidonTree<F> {
        type Leaf = [F];
        type LeafDigest = F;
        type LeafInnerDigestConverter = IdentityDigestConverter<F>;
        type InnerDigest = F;
        type LeafHash = CRH<F>;
        type TwoToOneHash = TwoToOneCRH<F>;
    }

    pub struct BinaryPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    pub struct TernaryPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    pub struct QuinaryPoseidonTree<F: PrimeField + Absorb> {
        _n: PhantomData<F>,
    }

    impl<F: PrimeField + Absorb> NAryConfig<2, PoseidonTree<F>> for BinaryPoseidonTree<F> {
        type NToOneHash = CRH<F>;
        type NToOneHashParams = PoseidonConfig<F>;
    }

    impl<F: PrimeField + Absorb> NAryConfig<3, PoseidonTree<F>> for TernaryPoseidonTree<F> {
        type NToOneHash = CRH<F>;
        type NToOneHashParams = PoseidonConfig<F>;
    }

    impl<F: PrimeField + Absorb> NAryConfig<5, PoseidonTree<F>> for QuinaryPoseidonTree<F> {
        type NToOneHash = CRH<F>;
        type NToOneHashParams = PoseidonConfig<F>;
    }

    pub fn initialize_poseidon_config<F: PrimeField>() -> PoseidonConfig<F> {
        let full_rounds = 8;
        let partial_rounds = 57;
        let alpha = 5; // fixed, don't use -1 or 3
        let rate = 2; // rate is at 2 for binary tree
        let (ark, mds) = find_poseidon_ark_and_mds::<F>(
            F::MODULUS_BIT_SIZE as u64,
            rate,
            full_rounds as u64,
            partial_rounds as u64,
            0,
        );
        PoseidonConfig::new(full_rounds, partial_rounds, alpha, mds, ark, rate, 1)
    }

    #[test]
    pub fn test_nary_merkle_tree() {
        // testing binary tree
        let n_leaf_nodes = 8;
        let poseidon_conf = initialize_poseidon_config::<Fr>();
        let leaves = vec![[Fr::default()]; n_leaf_nodes];
        let mt =
            MerkleTree::<PoseidonTree<Fr>>::new(&poseidon_conf, &poseidon_conf, &leaves).unwrap();
        let mut mt2 = NAryMerkleTree::<2, PoseidonTree<Fr>, BinaryPoseidonTree<Fr>>::new(
            &poseidon_conf,
            &poseidon_conf,
            &leaves,
        )
        .unwrap();
        assert_eq!(mt.root(), mt2.root());
        assert_eq!(mt2.non_leaf_nodes.len(), n_non_leaf_nodes(2, n_leaf_nodes));

        let expected_proof = mt.generate_proof(0).unwrap();
        let proof = mt2.generate_proof(0).unwrap();
        assert_eq!(expected_proof.auth_path.len(), proof.auth_path.len());
        for (p, expected_p) in expected_proof.auth_path.iter().zip(&proof.auth_path) {
            assert_eq!(*p, expected_p.siblings[0]);
        }
        assert_eq!(
            expected_proof.leaf_sibling_hash,
            proof.leaf_siblings_hashes[0]
        );

        for i in 0..mt2.leaf_nodes.len() {
            let proof = mt2.generate_proof(i).unwrap();

            assert!(proof
                .verify(&poseidon_conf, &poseidon_conf, &mt2.root(), [Fr::default()])
                .unwrap());
        }

        // udpated path binary tree
        for i in 0..mt2.leaf_nodes.len() {
            let new_leaf = [Fr::from(42)];
            let (updated_leaf_hash, updated_path) = mt2.updated_path(i, new_leaf).unwrap();
            let is_updated = mt2.check_update(i, &new_leaf, &updated_path[0]).unwrap();
            assert!(is_updated);
        }

        // testing ternary tree
        let n_leaf_nodes = 81;
        let leaves = vec![[Fr::default()]; n_leaf_nodes];
        let mut mt3 = NAryMerkleTree::<3, PoseidonTree<Fr>, TernaryPoseidonTree<Fr>>::new(
            &poseidon_conf,
            &poseidon_conf,
            &leaves,
        )
        .unwrap();
        assert_eq!(mt3.non_leaf_nodes.len(), n_non_leaf_nodes(3, n_leaf_nodes));
        assert_eq!(mt3.height(), tree_height(3, n_leaf_nodes));
        let expected_leaf_digest = CRH::evaluate(&poseidon_conf, vec![Fr::default()]).unwrap();
        let expected_last_layer =
            CRH::evaluate(&poseidon_conf, vec![expected_leaf_digest; 3]).unwrap();
        let expected_second_layer =
            CRH::evaluate(&poseidon_conf, vec![expected_last_layer; 3]).unwrap();
        let expected_first_layer =
            CRH::evaluate(&poseidon_conf, vec![expected_second_layer; 3]).unwrap();
        let expected_root = CRH::evaluate(&poseidon_conf, vec![expected_first_layer; 3]).unwrap();

        assert_eq!(*mt3.leaf_nodes.first().unwrap(), expected_leaf_digest);
        assert_eq!(mt3.non_leaf_nodes[1], expected_first_layer);
        assert_eq!(mt3.non_leaf_nodes[4], expected_second_layer);
        assert_eq!(mt3.non_leaf_nodes[13], expected_last_layer);
        assert_eq!(mt3.root(), expected_root);

        for i in 0..mt3.leaf_nodes.len() {
            let proof = mt3.generate_proof(i).unwrap();
            assert!(proof
                .verify(&poseidon_conf, &poseidon_conf, &mt3.root(), [Fr::default()])
                .unwrap());
        }

        for i in 0..mt3.leaf_nodes.len() {
            let new_leaf = [Fr::from(42)];
            let (_, updated_path) = mt3.updated_path(i, new_leaf).unwrap();
            let is_updated = mt3.check_update(i, &new_leaf, &updated_path[0]).unwrap();
            assert!(is_updated);
        }

        // testing quinary tree
        let n_leaf_nodes = 25;
        let leaves = vec![[Fr::default()]; n_leaf_nodes];
        let mut mt5 = NAryMerkleTree::<5, PoseidonTree<Fr>, QuinaryPoseidonTree<Fr>>::new(
            &poseidon_conf,
            &poseidon_conf,
            &leaves,
        )
        .unwrap();
        assert_eq!(mt5.non_leaf_nodes.len(), n_non_leaf_nodes(5, n_leaf_nodes));
        assert_eq!(mt5.height(), tree_height(5, n_leaf_nodes));
        for i in 0..mt5.leaf_nodes.len() {
            let proof = mt5.generate_proof(i).unwrap();
            assert!(proof
                .verify(&poseidon_conf, &poseidon_conf, &mt5.root(), [Fr::default()])
                .unwrap());
            // rejects correctly
            assert!(!proof
                .verify(&poseidon_conf, &poseidon_conf, &mt5.root(), [Fr::from(42)])
                .unwrap());
        }

        for i in 0..mt5.leaf_nodes.len() {
            let new_leaf = [Fr::from(42)];
            let (updated_leaf_hash, updated_path) = mt5.updated_path(i, new_leaf).unwrap();
            let is_updated = mt5.check_update(i, &new_leaf, &updated_path[0]).unwrap();
            assert!(is_updated);
        }
    }
}

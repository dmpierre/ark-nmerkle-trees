use std::borrow::Borrow;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::vec;

use ark_crypto_primitives::crh::{CRHScheme, TwoToOneCRHScheme};
use ark_crypto_primitives::merkle_tree::DigestConverter;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::{merkle_tree::Config, Error};
use ark_ff::{PrimeField, Zero};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::prelude::Boolean;
use ark_std::{cfg_into_iter, cfg_iter_mut};

pub mod sparse;

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
}

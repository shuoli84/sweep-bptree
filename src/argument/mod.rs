use crate::Key;

use std::borrow::Cow;

/// Augument trait, it is used to store augumentation, like 'size'
pub trait Argumentation<K: Key>: Clone + Default + std::fmt::Debug {
    /// create a new Argumentation from leaf node's key
    fn from_leaf(keys: &[K]) -> Self;

    /// create a new Argumentation from inner node and its argument
    /// e.g: take size as example.
    /// the root node's argument is created from its children's argument and keys
    /// the inner node with height 1's is created from leaf's keys
    ///                             [k3][9, 5]
    ///                [k2][5, 4]                  [k4][3, 2]
    ///         leaf[0] 5       leaf[1] 4      leaf[2] 3   leaf[2] 2
    fn from_inner(keys: &[K], arguments: &[Self]) -> Self;
}

/// Whether the argumentation able to locate element
pub trait SearchArgumentation<K: Key>: Argumentation<K> {
    type Query;

    /// locate the offset of the element in leaf node
    fn locate_in_leaf(query: Self::Query, keys: &[K]) -> Option<usize>;

    /// locate the child index of query in inner node, with new query
    fn locate_in_inner(
        query: Self::Query,
        keys: &[K],
        arguments: &[Self],
    ) -> Option<(usize, Self::Query)>;
}

/// Whether the argumentation able to rank element(like the index of key)
pub trait RankArgumentation<K: Key>: Argumentation<K> {
    type Rank: Default;

    /// Initial rank value, e.g: 0 for size
    /// it will be passed to the first call of `combine_rank`
    fn initial_value() -> Self::Rank;

    /// combine rank with all ranks for prev sibling arguments.
    /// The passed in argument slice doesn't contain the argument 'k' belongs
    /// The result will be passed to `fold_inner` for inner layer
    /// and finally to `fold_leaf`
    fn fold_inner(rank: Self::Rank, arguments: &[Self]) -> Self::Rank;

    /// Get rank of the key in leaf node
    /// Returns Ok(Rank) for existing key, Err(Rank) for non-existing key
    fn fold_leaf(
        rank: Self::Rank,
        slot: Result<usize, usize>,
        keys: &[K],
    ) -> Result<Self::Rank, Self::Rank>;
}

/// Unit is a dummy argumentation, it doesn't store any argument
impl<K: Key> Argumentation<K> for () {
    fn from_leaf(_: &[K]) -> Self {
        ()
    }

    fn from_inner(_: &[K], _: &[Self]) -> Self {
        ()
    }
}

/// Argumentation converts the tree to order statistic tree.
/// e.g: if each node stores a `ElementCount` size, then it can be used to
///      query the element at index `i` in the tree.
#[derive(Clone, Copy, Debug, Default)]
pub struct ElementCount(usize);

impl ElementCount {
    /// Get the count value
    pub fn count(&self) -> usize {
        self.0
    }
}

impl<K: Key> Argumentation<K> for ElementCount {
    fn from_leaf(keys: &[K]) -> Self {
        Self(keys.len())
    }

    fn from_inner(_keys: &[K], arguments: &[Self]) -> Self {
        Self(arguments.iter().map(|a| a.0).sum())
    }
}

impl<K: Key> SearchArgumentation<K> for ElementCount {
    /// Query for ElementCount is index
    type Query = usize;

    fn locate_in_leaf(idx: usize, keys: &[K]) -> Option<usize> {
        if idx < keys.len() {
            Some(idx)
        } else {
            None
        }
    }

    fn locate_in_inner(mut idx: usize, _keys: &[K], arguments: &[Self]) -> Option<(usize, usize)> {
        for (i, a) in arguments.iter().enumerate() {
            if idx >= a.0 {
                idx -= a.0;
            } else {
                return Some((i, idx));
            }
        }

        // offset is larger than the sum of all arguments
        None
    }
}

impl<K: Key> RankArgumentation<K> for ElementCount {
    /// The rank for ElementCount is index
    type Rank = usize;

    fn initial_value() -> Self::Rank {
        0
    }

    /// combine the rank of child and the rank of all prev siblings
    fn fold_inner(mut rank: Self::Rank, arguments: &[Self]) -> Self::Rank {
        for a in arguments {
            rank += a.0
        }
        rank
    }

    fn fold_leaf(
        rank: Self::Rank,
        slot: Result<usize, usize>,
        _keys: &[K],
    ) -> Result<Self::Rank, Self::Rank> {
        match slot {
            Ok(idx) => Ok(idx + rank),
            Err(idx) => Err(idx + rank),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct GroupCount<G: Clone + Ord + std::fmt::Debug> {
    min_group: G,
    max_group: G,
    pub count: usize,
}

pub trait FromRef<T> {
    fn from_ref(input: &T) -> Self;
}

impl<K, G> Argumentation<K> for Option<GroupCount<G>>
where
    K: Key,
    G: FromRef<K> + Clone + Ord + std::fmt::Debug,
{
    fn from_leaf(keys: &[K]) -> Self {
        let mut keys_iter = keys.iter();
        let first_group = G::from_ref(keys_iter.next()?);
        let mut group_count = 1;
        let mut last_group = Cow::Borrowed(&first_group);

        for key in keys_iter {
            let group = G::from_ref(key);
            if last_group.as_ref().ne(&group) {
                group_count += 1;
                last_group = Cow::Owned(group);
            }
        }
        let last_group = last_group.into_owned();
        Some(GroupCount {
            min_group: first_group,
            max_group: last_group,
            count: group_count,
        })
    }

    fn from_inner(_keys: &[K], arguments: &[Self]) -> Self {
        if arguments.is_empty() {
            return None;
        }

        let mut argument_iter = arguments.iter().flatten();
        let first_arguement = argument_iter.next().unwrap();
        let mut group_count = first_arguement.count;

        let mut last_group = &first_arguement.max_group;

        for m in argument_iter {
            if last_group.eq(&m.min_group) {
                // one group crossed two nodes
                group_count += m.count - 1;
            } else {
                group_count += m.count;
            }

            last_group = &m.max_group;
        }

        Some(GroupCount {
            min_group: first_arguement.min_group.clone(),
            max_group: last_group.clone(),
            count: group_count,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{BPlusTree, NodeStoreVec};

    use super::*;

    #[test]
    fn test_element_count() {
        let count = ElementCount::from_leaf(&[1, 2, 3]);
        assert_eq!(count.0, 3);

        let count = ElementCount::from_inner(&[1, 2, 3], &[count, count, count]);
        assert_eq!(count.0, 9);
    }

    #[test]
    fn test_element_count_in_tree() {
        let node_store = NodeStoreVec::<i64, u32, ElementCount>::new();
        let mut tree = BPlusTree::new(node_store);
        tree.insert(1, 101);
        assert_eq!(tree.root_argument().count(), 1);

        tree.remove(&1);
        assert_eq!(tree.root_argument().count(), 0);

        for i in 2..500 {
            tree.insert(i, i as u32 + 100);
        }

        let expected_size = 498;
        assert_eq!(tree.len(), expected_size);

        for i in 0..expected_size {
            assert_eq!(tree.get_by_argument(i).unwrap().1, &(100 + 2 + i as u32));
        }
        assert!(tree.get_by_argument(expected_size + 1).is_none());

        // 1 is not in the tree
        assert_eq!(tree.rank_by_argument(&1), Err(0));
        for i in 2..500 {
            assert_eq!(tree.rank_by_argument(&i), Ok(i as usize - 2));
        }
        assert_eq!(tree.rank_by_argument(&500), Err(expected_size));
    }

    #[test]
    fn test_group_count() {
        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
        struct G(u8);

        impl FromRef<u8> for G {
            fn from_ref(input: &u8) -> Self {
                Self(*input / 2 as u8)
            }
        }

        let argument = Option::<GroupCount<G>>::from_leaf(&[1, 2, 3]);
        assert_eq!(argument.unwrap().count, 2);

        let argument = Option::<GroupCount<G>>::from_inner(
            &[1, 2, 3],
            &[
                Some(GroupCount {
                    min_group: G(0),
                    max_group: G(1),
                    count: 2,
                }),
                Some(GroupCount {
                    min_group: G(1),
                    max_group: G(4),
                    count: 2,
                }),
                Some(GroupCount {
                    min_group: G(4),
                    max_group: G(10),
                    count: 3,
                }),
            ],
        );

        // 1 and 4 are dup groups in child, so we need to fix the double counting
        assert_eq!(argument.unwrap().count, 2 + 1 + 2);

        let argument = Option::<GroupCount<G>>::from_inner(
            &[1, 2, 3],
            &[
                Some(GroupCount {
                    min_group: G(0),
                    max_group: G(0),
                    count: 1,
                }),
                Some(GroupCount {
                    min_group: G(0),
                    max_group: G(0),
                    count: 1,
                }),
                Some(GroupCount {
                    min_group: G(0),
                    max_group: G(0),
                    count: 1,
                }),
            ],
        );
        assert_eq!(argument.unwrap().count, 1);
    }

    #[test]
    fn test_group_count_in_tree() {
        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        struct Group(u64);

        impl FromRef<(u64, u64)> for Group {
            fn from_ref(input: &(u64, u64)) -> Self {
                Group(input.0)
            }
        }

        let node_store = NodeStoreVec::<(u64, u64), i64, Option<GroupCount<Group>>>::new();
        let mut tree = BPlusTree::new(node_store);

        tree.insert((1, 1), 100);
        assert_eq!(tree.root_argument().as_ref().unwrap().count, 1);
        tree.remove(&(1, 1));
        assert!(tree.root_argument().is_none());

        tree.insert((1, 1), 100);
        tree.insert((1, 2), 100);
        assert_eq!(tree.root_argument().as_ref().unwrap().count, 1);

        tree.insert((1, 3), 100);
        tree.insert((2, 4), 100);
        assert_eq!(tree.root_argument().as_ref().unwrap().count, 2);
        tree.insert((3, 5), 100);
        tree.insert((4, 6), 100);
        assert_eq!(tree.root_argument().as_ref().unwrap().count, 4);
        tree.remove(&(4, 6));
        assert_eq!(tree.root_argument().as_ref().unwrap().count, 3);
    }
}

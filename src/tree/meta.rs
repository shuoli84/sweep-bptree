use std::borrow::Cow;

use crate::Key;

/// Augument trait, it is used to store augumentation, like 'size'
pub trait Argumentation<K: Key>: Clone + Default + std::fmt::Debug {
    /// create a new Argumentation from leaf node's key
    fn from_leaf(keys: &[K]) -> Self;

    /// create a new Argumentation from inner node and its meta
    /// e.g: take size as example.
    /// the root node's meta is created from its children's meta and keys
    /// the inner node with height 1's meta is created from leaf's keys
    ///                             [k3][9, 5]
    ///                [k2][5, 4]                  [k4][3, 2]
    ///         leaf[0] 5       leaf[1] 4      leaf[2] 3   leaf[2] 2
    fn from_inner(keys: &[K], meta: &[Self]) -> Self;
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
        meta: &[Self],
    ) -> Option<(usize, Self::Query)>;
}

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

    fn from_inner(_keys: &[K], meta: &[Self]) -> Self {
        Self(meta.iter().map(|m| m.0).sum())
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

    fn locate_in_inner(mut idx: usize, _keys: &[K], meta: &[Self]) -> Option<(usize, usize)> {
        for (i, m) in meta.iter().enumerate() {
            if idx >= m.0 {
                idx -= m.0;
            } else {
                return Some((i, idx));
            }
        }

        // offset is larger than the sum of all meta
        None
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

    fn from_inner(_keys: &[K], meta: &[Self]) -> Self {
        if meta.is_empty() {
            return None;
        }

        let mut meta_iter = meta.iter().flatten();
        let first_meta = meta_iter.next().unwrap();
        let mut group_count = first_meta.count;

        let mut last_group = &first_meta.max_group;

        for m in meta_iter {
            if last_group.eq(&m.min_group) {
                // one group crossed two nodes
                group_count += m.count - 1;
            } else {
                group_count += m.count;
            }

            last_group = &m.max_group;
        }

        Some(GroupCount {
            min_group: first_meta.min_group.clone(),
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
        let meta = ElementCount::from_leaf(&[1, 2, 3]);
        assert_eq!(meta.0, 3);

        let meta = ElementCount::from_inner(&[1, 2, 3], &[meta, meta, meta]);
        assert_eq!(meta.0, 9);
    }

    #[test]
    fn test_element_count_in_tree() {
        let node_store = NodeStoreVec::<i64, u32, 4, 5, 4, ElementCount>::new();
        let mut tree = BPlusTree::new(node_store);
        tree.insert(1, 101);
        assert_eq!(tree.root_meta.count(), 1);

        tree.remove(&1);
        assert_eq!(tree.root_meta.count(), 0);

        for i in 2..500 {
            tree.insert(i, i as u32 + 100);
        }

        let expected_size = 498;
        assert_eq!(tree.len(), expected_size);

        for i in 0..expected_size {
            assert_eq!(tree.get_by_argument(i).unwrap(), &(100 + 2 + i as u32));
        }
        assert!(tree.get_by_argument(expected_size + 1).is_none());
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

        let meta = Option::<GroupCount<G>>::from_leaf(&[1, 2, 3]);
        assert_eq!(meta.unwrap().count, 2);

        let meta = Option::<GroupCount<G>>::from_inner(
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
        assert_eq!(meta.unwrap().count, 2 + 1 + 2);

        let meta = Option::<GroupCount<G>>::from_inner(
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
        assert_eq!(meta.unwrap().count, 1);
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

        let node_store = NodeStoreVec::<(u64, u64), i64, 8, 9, 6, Option<GroupCount<Group>>>::new();
        let mut tree = BPlusTree::new(node_store);

        tree.insert((1, 1), 100);
        assert_eq!(tree.root_meta.as_ref().unwrap().count, 1);
        tree.remove(&(1, 1));
        assert!(tree.root_meta.is_none());

        tree.insert((1, 1), 100);
        tree.insert((1, 2), 100);
        assert_eq!(tree.root_meta.as_ref().unwrap().count, 1);

        tree.insert((1, 3), 100);
        tree.insert((2, 4), 100);
        assert_eq!(tree.root_meta.as_ref().unwrap().count, 2);
        tree.insert((3, 5), 100);
        tree.insert((4, 6), 100);
        assert_eq!(tree.root_meta.as_ref().unwrap().count, 4);
        tree.remove(&(4, 6));
        assert_eq!(tree.root_meta.as_ref().unwrap().count, 3);
    }
}

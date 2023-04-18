use std::borrow::Cow;

use crate::Key;

/// Meta trait, it is used to store recursive metadata, like 'size'
/// What is a proper name? 'Meta' is not a good name.
pub trait Meta<K: Key>: Clone {
    /// create a new meta from leaf node's key
    fn from_leaf(keys: &[K]) -> Self;

    /// create a new meta from inner node and its meta
    /// e.g: take size as example.
    /// the root node's meta is created from its children's meta and keys
    /// the inner node with height 1's meta is created from leaf's keys
    ///                             [k3][9, 5]
    ///                [k2][5, 4]                  [k4][3, 2]
    ///         leaf[0] 5       leaf[1] 4      leaf[2] 3   leaf[2] 2
    fn from_inner(keys: &[K], meta: &[Self]) -> Self;
}

/// A meta that can be used to search elements.
/// e.g: if each node stores a `ElementCount` size, then it can be used to
///      query the element at index `i` in the tree.
pub trait SearchableMeta<K: Key>: Meta<K> {
    /// locate the offset of the element in leaf node
    fn locate_in_leaf(&self, query: Self, keys: &[K]) -> Option<usize>;

    /// locate the child index of query in inner node, with new query
    fn locate_in_inner(&self, query: Self, keys: &[K], meta: &[Self]) -> Option<(usize, Self)>;
}

impl<K: Key> Meta<K> for () {
    fn from_leaf(_: &[K]) -> Self {
        ()
    }

    fn from_inner(_: &[K], _: &[Self]) -> Self {
        ()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ElementCount(usize);

impl<K: Key> Meta<K> for ElementCount {
    fn from_leaf(keys: &[K]) -> Self {
        Self(keys.len())
    }

    fn from_inner(_keys: &[K], meta: &[Self]) -> Self {
        Self(meta.iter().map(|m| m.0).sum())
    }
}

impl<K: Key> SearchableMeta<K> for ElementCount {
    fn locate_in_leaf(&self, query: Self, keys: &[K]) -> Option<usize> {
        let idx = query.0;
        if idx < keys.len() {
            Some(idx)
        } else {
            None
        }
    }

    fn locate_in_inner(&self, query: Self, _keys: &[K], meta: &[Self]) -> Option<(usize, Self)> {
        let mut offset = query.0;

        for (i, m) in meta.iter().enumerate() {
            if offset > m.0 {
                offset -= m.0;
            } else {
                return Some((i, Self(offset)));
            }
        }

        // offset is larger than the sum of all meta
        None
    }
}

#[derive(Clone, Copy, Debug)]
pub struct GroupCount<G: Clone + Ord> {
    min_group: G,
    max_group: G,
    group_count: usize,
}

pub trait FromRef<T> {
    fn from_ref(input: &T) -> Self;
}

impl<K, G> Meta<K> for GroupCount<G>
where
    K: Key,
    G: FromRef<K> + Clone + Ord,
{
    fn from_leaf(keys: &[K]) -> Self {
        let mut keys_iter = keys.iter();
        let first_group = G::from_ref(keys_iter.next().unwrap());
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
        Self {
            min_group: first_group,
            max_group: last_group,
            group_count,
        }
    }

    fn from_inner(_keys: &[K], meta: &[Self]) -> Self {
        let mut meta_iter = meta.iter();
        let first_meta = meta_iter.next().unwrap();
        let mut group_count = first_meta.group_count;

        let mut last_group = &first_meta.max_group;

        for m in meta_iter {
            if last_group.eq(&m.min_group) {
                // one group crossed two nodes
                group_count += m.group_count - 1;
            } else {
                group_count += m.group_count;
            }

            last_group = &m.max_group;
        }

        Self {
            min_group: first_meta.min_group.clone(),
            max_group: last_group.clone(),
            group_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_element_count() {
        let meta = ElementCount::from_leaf(&[1, 2, 3]);
        assert_eq!(meta.0, 3);

        let meta = ElementCount::from_inner(&[1, 2, 3], &[meta, meta, meta]);
        assert_eq!(meta.0, 9);
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

        let meta = GroupCount::<G>::from_leaf(&[1, 2, 3]);
        assert_eq!(meta.group_count, 2);

        let meta = GroupCount::<G>::from_inner(
            &[1, 2, 3],
            &[
                GroupCount {
                    min_group: G(0),
                    max_group: G(1),
                    group_count: 2,
                },
                GroupCount {
                    min_group: G(1),
                    max_group: G(4),
                    group_count: 2,
                },
                GroupCount {
                    min_group: G(4),
                    max_group: G(10),
                    group_count: 3,
                },
            ],
        );

        // 1 and 4 are dup groups in child, so we need to fix the double counting
        assert_eq!(meta.group_count, 2 + 1 + 2);

        let meta = GroupCount::<G>::from_inner(
            &[1, 2, 3],
            &[
                GroupCount {
                    min_group: G(0),
                    max_group: G(0),
                    group_count: 1,
                },
                GroupCount {
                    min_group: G(0),
                    max_group: G(0),
                    group_count: 1,
                },
                GroupCount {
                    min_group: G(0),
                    max_group: G(0),
                    group_count: 1,
                },
            ],
        );
        assert_eq!(meta.group_count, 1);
    }
}

use std::borrow::Cow;

use crate::Key;

use super::Argumentation;

/// Argument to count the number of groups in a set of keys
/// Note, the group must be ordered
#[derive(Clone, Copy, Debug)]
pub struct GroupCount<G: Clone + Ord + std::fmt::Debug> {
    min_group: G,
    max_group: G,
    /// how many groups for child
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
    fn test_group_count() {
        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
        struct Half(u8);

        impl FromRef<u8> for Half {
            fn from_ref(input: &u8) -> Self {
                Self(*input / 2 as u8)
            }
        }

        let argument = Option::<GroupCount<Half>>::from_leaf(&[1, 2, 3]);
        assert_eq!(argument.unwrap().count, 2);

        let argument = Option::<GroupCount<Half>>::from_inner(
            &[1, 2, 3],
            &[
                Some(GroupCount {
                    min_group: Half(0),
                    max_group: Half(1),
                    count: 2,
                }),
                Some(GroupCount {
                    min_group: Half(1),
                    max_group: Half(4),
                    count: 2,
                }),
                Some(GroupCount {
                    min_group: Half(4),
                    max_group: Half(10),
                    count: 3,
                }),
            ],
        );

        // 1 and 4 are dup groups in child, so we need to fix the double counting
        assert_eq!(argument.unwrap().count, 2 + 1 + 2);

        let argument = Option::<GroupCount<Half>>::from_inner(
            &[1, 2, 3],
            &[
                Some(GroupCount {
                    min_group: Half(0),
                    max_group: Half(0),
                    count: 1,
                }),
                Some(GroupCount {
                    min_group: Half(0),
                    max_group: Half(0),
                    count: 1,
                }),
                Some(GroupCount {
                    min_group: Half(0),
                    max_group: Half(0),
                    count: 1,
                }),
            ],
        );
        assert_eq!(argument.unwrap().count, 1);
    }

    #[test]
    fn test_group_count_in_tree() {
        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        struct First(u64);

        impl FromRef<(u64, u64)> for First {
            fn from_ref(input: &(u64, u64)) -> Self {
                First(input.0)
            }
        }

        let node_store = NodeStoreVec::<(u64, u64), i64, Option<GroupCount<First>>>::new();
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

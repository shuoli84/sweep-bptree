use crate::Key;

use super::{Argument, RankArgument, SearchArgument};

/// This argumentation keeps track of the number of elements in the child.
/// Basicly, it turns the tree to [Order Statistic Tree](https://en.wikipedia.org/wiki/Order_statistic_tree)
#[derive(Clone, Copy, Debug, Default)]
pub struct Count(usize);

impl Count {
    /// Get the count value
    pub fn count(&self) -> usize {
        self.0
    }
}

impl<K: Key> Argument<K> for Count {
    fn from_leaf(keys: &[K]) -> Self {
        Self(keys.len())
    }

    fn from_inner(_keys: &[K], arguments: &[Self]) -> Self {
        Self(arguments.iter().map(|a| a.0).sum())
    }
}

impl<K: Key> SearchArgument<K> for Count {
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

impl<K: Key> RankArgument<K> for Count {
    /// The rank for ElementCount is index
    type Rank = usize;

    fn initial_value() -> Self::Rank {
        0
    }

    /// combine the rank of child and the rank of all prev siblings
    fn fold_inner(_k: &K, mut rank: Self::Rank, arguments: &[Self]) -> Self::Rank {
        for a in arguments {
            rank += a.0
        }
        rank
    }

    fn fold_leaf(
        _k: &K,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BPlusTree, NodeStoreVec};

    #[test]
    fn test_element_count() {
        let count = Count::from_leaf(&[1, 2, 3]);
        assert_eq!(count.0, 3);

        let count = Count::from_inner(&[1, 2, 3], &[count, count, count]);
        assert_eq!(count.0, 9);
    }

    #[test]
    fn test_element_count_in_tree() {
        let node_store = NodeStoreVec::<i64, u32, Count>::new();
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
}

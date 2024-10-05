use sweep_bptree::augment::{RankAugmentation, SearchAugmentation};
use sweep_bptree::{augment::Augmentation, BPlusTree, NodeStoreVec};

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
pub struct Key {
    value: i64,
    count: usize,
}

/// Count Augmentation which aggregates key's count component
#[derive(Clone, Copy, Debug, Default)]
pub struct Count(usize);

impl Count {
    /// Get the count value
    pub fn count(&self) -> usize {
        self.0
    }
}

impl<V> Augmentation<Key, V> for Count {
    fn from_leaf(keys: &[Key], _: &[V]) -> Self {
        Self(keys.iter().map(|k| k.count).sum())
    }

    fn from_inner(_keys: &[Key], counts: &[Self]) -> Self {
        Self(counts.iter().map(|a| a.0).sum())
    }
}

impl<V> SearchAugmentation<Key, V> for Count {
    /// Query for ElementCount is index
    type Query = usize;

    fn locate_in_leaf(offset: usize, keys: &[Key]) -> Option<usize> {
        let mut accum = 0usize;

        for (idx, key) in keys.iter().enumerate() {
            if accum + key.count > offset {
                return Some(idx);
            }

            accum += key.count;
        }

        None
    }

    fn locate_in_inner(mut idx: usize, _keys: &[Key], counts: &[Self]) -> Option<(usize, usize)> {
        for (i, a) in counts.iter().enumerate() {
            if idx >= a.0 {
                idx -= a.0;
            } else {
                dbg!((idx, i));
                return Some((i, idx));
            }
        }

        // offset is larger than the sum of all counts
        None
    }
}

impl<V> RankAugmentation<Key, V> for Count {
    /// The rank for ElementCount is index
    type Rank = usize;

    fn initial_value() -> Self::Rank {
        0
    }

    /// combine the rank of child and the rank of all prev siblings
    fn fold_inner(_k: &Key, mut rank: Self::Rank, counts: &[Self]) -> Self::Rank {
        for a in counts {
            rank += a.0
        }
        rank
    }

    fn fold_leaf(
        _k: &Key,
        rank: Self::Rank,
        slot: Result<usize, usize>,
        keys: &[Key],
    ) -> Result<Self::Rank, Self::Rank> {
        match slot {
            Ok(idx) => {
                let idx: usize = keys[0..=idx].iter().map(|k| k.count).sum();
                Ok(idx + rank)
            }
            Err(idx) => {
                let idx: usize = keys[0..=idx].iter().map(|k| k.count).sum();
                Err(idx + rank)
            }
        }
    }
}

// insert key into tree, if it already exists, then increase count
fn insert(tree: &mut BPlusTree<NodeStoreVec<Key, (), Count>>, key: i64) {
    // find the right key to delete, actually we want to get the first key that not less than '(key, 0)'
    // and then check if key part matches.
    let existing_key = match tree.get_cursor(&Key {
        value: key,
        count: 0,
    }) {
        None => {
            tree.insert(
                Key {
                    value: key,
                    count: 1,
                },
                (),
            );
            return;
        }
        Some((cursor, _)) => match cursor.next(tree) {
            Some(next_cursor) if next_cursor.key().value == key => next_cursor.key().clone(),
            _ => {
                tree.insert(
                    Key {
                        value: key,
                        count: 1,
                    },
                    (),
                );
                return;
            }
        },
    };

    tree.remove(&existing_key);
    tree.insert(
        Key {
            value: key,
            count: existing_key.count + 1,
        },
        (),
    );
}

fn main() {
    // create a tree with the augment
    let mut tree = BPlusTree::new(NodeStoreVec::<Key, (), Count>::new());

    for _ in 0..100 {
        for i in 0..100 {
            insert(&mut tree, i);
        }
    }
    assert_eq!(tree.root_augmentation().0, 10000);

    for offset in 0..tree.root_augmentation().0 {
        let kv = tree.get_by_augmentation::<usize>(offset).unwrap();
        assert_eq!(kv.0.value, (offset / 100) as i64);
        dbg!((offset, kv));
    }
}

use sweep_bptree::augment::SearchAugmentation;
use sweep_bptree::Key;
use sweep_bptree::{augment::Augmentation, BPlusTree, NodeStoreVec};

#[derive(Debug, Copy, Clone, Default)]
pub struct Count(usize);

impl Count {
    /// Get the count value
    pub fn count(&self) -> usize {
        self.0
    }
}

impl<K: Key> Augmentation<K, usize> for Count {
    fn from_leaf(_: &[K], values: &[usize]) -> Self {
        Self(values.iter().sum())
    }

    fn from_inner(_keys: &[K], counts: &[Self]) -> Self {
        Self(counts.iter().map(|a| a.0).sum())
    }
}

impl<K: Key> SearchAugmentation<K, usize> for Count {
    /// Query for ElementCount is index
    type Query = usize;

    fn locate_in_leaf(offset: usize, keys: &[K], values: &[usize]) -> Option<usize> {
        let mut accum = 0usize;

        for (idx, (key, count)) in keys.iter().zip(values).enumerate() {
            if accum + count > offset {
                return Some(idx);
            }

            accum += count;
        }

        None
    }

    fn locate_in_inner(mut idx: usize, _keys: &[K], counts: &[Self]) -> Option<(usize, usize)> {
        for (i, a) in counts.iter().enumerate() {
            if idx >= a.0 {
                idx -= a.0;
            } else {
                return Some((i, idx));
            }
        }

        // offset is larger than the sum of all counts
        None
    }
}

// insert key into tree, if it already exists, then increase count
fn insert(tree: &mut BPlusTree<NodeStoreVec<i64, usize, Count>>, key: i64) {
    let prev_count = tree.get(&key).cloned().unwrap_or_default();
    tree.insert(key, prev_count + 1);
}

fn delete(tree: &mut BPlusTree<NodeStoreVec<i64, usize, Count>>, key: i64) {
    let prev_count = tree.get(&key).cloned().unwrap_or_default();
    if prev_count == 1 {
        tree.remove(&key);
    } else {
        tree.insert(key, prev_count - 1);
    }
}

fn main() {
    // create a tree with the augment
    let mut tree = BPlusTree::new(NodeStoreVec::<i64, usize, Count>::new());

    for _ in 0..100 {
        for i in 0..100 {
            insert(&mut tree, i);
        }
    }
    assert_eq!(tree.root_augmentation().0, 10000);

    for offset in 0..tree.root_augmentation().0 {
        let kv = tree.get_by_augmentation::<usize>(offset).unwrap();
        dbg!((offset, kv.0));
    }

    for _ in 0..100 {
        for i in 0..100 {
            delete(&mut tree, i);
        }
    }

    assert_eq!(tree.root_augmentation().0, 0);
    assert!(tree.get_by_augmentation::<usize>(0).is_none());
}

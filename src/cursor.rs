use crate::BPlusTree;
use crate::Key;
use crate::LNode;
use crate::LeafNodeId;
use crate::NodeStore;

#[derive(Debug)]
pub struct Cursor<K: Key> {
    k: K,
    leaf_id: LeafNodeId,
    offset_hint: usize,
}

impl<K: Key> Cursor<K> {
    /// Get the key of the cursor.
    pub fn key(&self) -> &K {
        &self.k
    }

    pub fn first<'a, 'b, S: NodeStore<K = K>>(tree: &'b BPlusTree<S>) -> Option<(Self, &'b S::V)> {
        let leaf_id = tree.first_leaf()?;
        let leaf = tree.node_store.get_leaf(leaf_id);

        let kv = leaf.data_at(0);

        Some((
            Self {
                k: kv.0.clone(),
                leaf_id,
                offset_hint: 0,
            },
            &kv.1,
        ))
    }

    pub fn last<'a, 'b, S: NodeStore<K = K>>(tree: &'b BPlusTree<S>) -> Option<(Self, &'b S::V)> {
        let leaf_id = tree.last_leaf()?;
        let leaf = tree.node_store.get_leaf(leaf_id);
        let kv = leaf.data_at(leaf.len() - 1);

        Some((
            Self {
                k: kv.0.clone(),
                leaf_id,
                offset_hint: leaf.len() - 1,
            },
            &kv.1,
        ))
    }

    pub fn prev<'a, 'b, S: NodeStore<K = K>>(&'a self, tree: &'b BPlusTree<S>) -> Option<Self> {
        self.prev_with_value(tree).map(|x| x.0)
    }

    pub fn prev_with_value<'a, 'b, S: NodeStore<K = K>>(
        &'a self,
        tree: &'b BPlusTree<S>,
    ) -> Option<(Self, &'b S::V)> {
        let (leaf_id, leaf) = self.locate_leaf(tree)?;

        let (offset, leaf) = match leaf.try_data_at(self.offset_hint) {
            Some(kv) if kv.0.eq(&self.k) => {
                if self.offset_hint > 0 {
                    (self.offset_hint - 1, leaf)
                } else if let Some(prev_id) = leaf.prev() {
                    let prev = tree.node_store.get_leaf(prev_id);
                    (prev.len() - 1, prev)
                } else {
                    return None;
                }
            }
            _ => {
                let (offset, _value) = leaf.locate_slot(&self.k);
                if offset > 0 {
                    (offset - 1, leaf)
                } else if let Some(prev_id) = leaf.prev() {
                    let prev = tree.node_store.get_leaf(prev_id);
                    (prev.len() - 1, prev)
                } else {
                    return None;
                }
            }
        };

        let kv = leaf.data_at(offset);
        Some((
            Self {
                k: kv.0,
                leaf_id,
                offset_hint: offset,
            },
            &kv.1,
        ))
    }

    pub fn next<'a, 'b, S: NodeStore<K = K>>(&'a self, tree: &'b BPlusTree<S>) -> Option<Self> {
        self.next_with_value(tree).map(|x| x.0)
    }

    pub fn next_with_value<'a, 'b, S: NodeStore<K = K>>(
        &'a self,
        tree: &'b BPlusTree<S>,
    ) -> Option<(Self, &'b S::V)> {
        let (leaf_id, leaf) = self.locate_leaf(tree)?;

        let next_offset = match leaf.try_data_at(self.offset_hint) {
            Some(kv) if kv.0.eq(&self.k) => self.offset_hint + 1,
            _ => {
                let (offset, value) = leaf.locate_slot(&self.k);
                match value {
                    Some(_) => offset + 1,
                    None => offset,
                }
            }
        };

        if next_offset < leaf.len() {
            let kv = leaf.data_at(next_offset);
            Some((
                Self {
                    k: kv.0,
                    leaf_id,
                    offset_hint: next_offset,
                },
                &kv.1,
            ))
        } else {
            let leaf_id = leaf.next()?;
            let leaf = tree.node_store.get_leaf(leaf_id);
            let kv = leaf.data_at(0);

            Some((
                Self {
                    k: kv.0,
                    leaf_id,
                    offset_hint: 0,
                },
                &kv.1,
            ))
        }
    }

    /// whether current cursor is still valid
    pub fn exists<'a, 'b, S: NodeStore<K = K>>(&'a self, tree: &'b BPlusTree<S>) -> bool {
        self.value(tree).is_some()
    }

    /// get the value attached to cursor, if the underlying key is deleted, this returns None
    pub fn value<'a, 'b, S: NodeStore<K = K>>(
        &'a self,
        tree: &'b BPlusTree<S>,
    ) -> Option<&'b S::V> {
        let (_, leaf) = self.locate_leaf(tree)?;

        match leaf.try_data_at(self.offset_hint) {
            Some(kv) if kv.0.eq(&self.k) => Some(&kv.1),
            _ => {
                // todo: consider update self?
                let (_, value) = leaf.locate_slot(&self.k);
                value.map(|kv| &kv.1)
            }
        }
    }

    fn locate_leaf<'a, 'b, S: NodeStore<K = K>>(
        &'a self,
        tree: &'b BPlusTree<S>,
    ) -> Option<(LeafNodeId, &'b S::LeafNode)> {
        let leaf_id = self.leaf_id;
        match tree.node_store.try_get_leaf(leaf_id) {
            Some(leaf) if range_contains(&leaf.key_range(), &self.k) => {
                // still valid
                Some((leaf_id, leaf))
            }
            _ => {
                // the leaf is modified, we need to do a search by key
                let leaf_id = tree.locate_leaf(&self.k)?;
                Some((leaf_id, tree.node_store.get_leaf(leaf_id)))
            }
        }
    }
}

fn range_contains<K: Ord + Eq>(range: &(K, K), k: &K) -> bool {
    range.0.le(k) && range.1.ge(k)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use rand::seq::SliceRandom;

    use crate::*;

    #[test]
    fn test_cursor_next() {
        let (mut tree, mut keys) = tests::create_test_tree::<2000>();
        let mut expected_count = keys.len();

        keys.shuffle(&mut rand::thread_rng());

        tree.node_store.debug();

        let mut keys = keys.into_iter();

        let (mut cursor_0, v_0) = Cursor::first(&tree).unwrap();

        let (cursor_1, _) = Cursor::first(&tree).unwrap();

        assert_eq!(cursor_0.k, 0);

        let mut value = vec![v_0.clone()];
        let mut keys_deleted = BTreeSet::new();
        while let Some((c, v)) = cursor_0.next_with_value(&tree) {
            println!("\n-------------------");
            println!("cursor {:?}", c);
            tree.node_store.debug();
            assert!(!keys_deleted.contains(&c.k));

            assert_eq!(c.value(&tree).unwrap(), v);
            value.push(v.clone());

            cursor_0 = c;

            // asserting that existing cursor's query also works
            if keys_deleted.contains(&cursor_1.k) {
                assert!(cursor_1.value(&tree).is_none());
            } else {
                assert!(cursor_1.value(&tree).is_some());
            }

            // just delete the key just passed, it should not affect the cursor
            let k = keys.next().unwrap();
            keys_deleted.insert(k);
            tree.remove(&k);
            if cursor_0.k < k {
                expected_count -= 1;
            }
        }

        assert_eq!(value.len(), expected_count);
        // cursor_1 still valid
        assert_eq!(cursor_1.k, 0);
    }

    #[test]
    fn test_cursor_prev() {
        let (mut tree, mut keys) = tests::create_test_tree::<500>();
        let mut expected_count = keys.len();

        keys.shuffle(&mut rand::thread_rng());
        // println!("{keys:?}");

        let mut keys = keys.into_iter();

        let mut values: Vec<i64> = vec![];
        let (mut cursor, _v) = Cursor::last(&tree).unwrap();
        values.push(cursor.k);

        while let Some((c, _v)) = cursor.prev_with_value(&tree) {
            values.push(c.k);
            cursor = c;
            let key = keys.next().unwrap();

            tree.remove(&key);
            if key < cursor.k {
                expected_count -= 1;
            }
        }

        assert_eq!(values.len(), expected_count);
    }
}

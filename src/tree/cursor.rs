use crate::tree::LNode;
use crate::tree::LeafNodeId;
use crate::BPlusTree;
use crate::Key;
use crate::NodeStore;

/// `Cursor` points to a key value pair in the tree. Not like Iterator, it can move to next or prev.
#[derive(Debug, Clone, Copy)]
pub struct Cursor<K: Key + 'static> {
    /// The key this cursor points to. It is possible the `k` doesn't exist in the tree.
    k: K,
    /// The leaf node id this cursor points to. This is a hint, which means it is possible the leaf
    /// for `k` is changed. In that case, the cursor will do a lookup first.
    leaf_id_hint: LeafNodeId,
    /// The offset this cursor points to inside the leaf. This is a hint, if the underlying tree is
    /// modified, then the offset may be invalid.
    offset_hint: usize,
}

impl<K: Key> Cursor<K> {
    /// Create a new cursor
    #[inline(always)]
    pub(crate) fn new(k: K, leaf_id: LeafNodeId, offset: usize) -> Self {
        Self {
            k,
            leaf_id_hint: leaf_id,
            offset_hint: offset,
        }
    }

    /// Get the key of the cursor.
    #[inline(always)]
    pub fn key(&self) -> &K {
        &self.k
    }

    /// Create a `Cursor` pointing to the first key-value pair in the tree.
    pub fn first<'b, S: NodeStore<K = K>>(tree: &'b BPlusTree<S>) -> Option<(Self, &'b S::V)> {
        let leaf_id = tree.first_leaf()?;
        let leaf = tree.node_store.get_leaf(leaf_id);

        let kv = leaf.data_at(0);

        Some((
            Self {
                k: kv.0.clone(),
                leaf_id_hint: leaf_id,
                offset_hint: 0,
            },
            &kv.1,
        ))
    }

    /// Create a `Cursor` pointing to the last key-value pair in the tree. If the key for `self` is deleted, then
    /// this returns the cursor for the key value pair just larger than the deleted key.
    pub fn last<'b, S: NodeStore<K = K>>(tree: &'b BPlusTree<S>) -> Option<(Self, &'b S::V)> {
        let leaf_id = tree.last_leaf()?;
        let leaf = tree.node_store.get_leaf(leaf_id);
        let kv = leaf.data_at(leaf.len() - 1);

        Some((
            Self {
                k: kv.0.clone(),
                leaf_id_hint: leaf_id,
                offset_hint: leaf.len() - 1,
            },
            &kv.1,
        ))
    }

    /// Get the `Cursor` points to the prev key-value pair. If the key for `self` is deleted, then
    /// this returns the cursor for the key value pair just under the deleted key.
    pub fn prev<'a, 'b, S: NodeStore<K = K>>(&'a self, tree: &'b BPlusTree<S>) -> Option<Self> {
        self.prev_with_value(tree).map(|x| x.0)
    }

    /// Get the `Cursor` points to the prev key-value pair, also with a reference to the value.
    /// This is faster than first `prev`, then `value`.
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
                let offset = match leaf.locate_slot(&self.k) {
                    Ok(offset) => offset,
                    Err(offset) => offset,
                };

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
                k: kv.0.clone(),
                leaf_id_hint: leaf_id,
                offset_hint: offset,
            },
            &kv.1,
        ))
    }

    /// Get the `Cursor` points to the next key-value pair. If the key for `self` is deleted, then
    /// this returns the cursor for the key value pair just larger than the deleted key.
    pub fn next<'a, 'b, S: NodeStore<K = K>>(&'a self, tree: &'b BPlusTree<S>) -> Option<Self> {
        self.next_with_value(tree).map(|x| x.0)
    }

    /// Get the `Cursor` points to the next key-value pair, also with a reference to the value.
    pub fn next_with_value<'a, 'b, S: NodeStore<K = K>>(
        &'a self,
        tree: &'b BPlusTree<S>,
    ) -> Option<(Self, &'b S::V)> {
        let (leaf_id, leaf) = self.locate_leaf(tree)?;

        let next_offset = match leaf.try_data_at(self.offset_hint) {
            Some(kv) if kv.0.eq(&self.k) => self.offset_hint + 1,
            _ => {
                let (offset, value) = leaf.locate_slot_with_value(&self.k);
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
                    k: kv.0.clone(),
                    leaf_id_hint: leaf_id,
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
                    k: kv.0.clone(),
                    leaf_id_hint: leaf_id,
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
                let (_, value) = leaf.locate_slot_with_value(&self.k);
                value
            }
        }
    }

    #[inline]
    fn locate_leaf<'a, 'b, S: NodeStore<K = K>>(
        &'a self,
        tree: &'b BPlusTree<S>,
    ) -> Option<(LeafNodeId, &'b S::LeafNode)> {
        let leaf_id = self.leaf_id_hint;
        if let Some(leaf) = tree.node_store.try_get_leaf(leaf_id) {
            if leaf.in_range(&self.k) {
                return Some((leaf_id, leaf));
            }
        }

        // no hint or hint outdated, need to do a search by key
        let leaf_id = tree.locate_leaf(&self.k)?;

        Some((leaf_id, tree.node_store.get_leaf(leaf_id)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{tree::tests, *};
    use rand::seq::SliceRandom;
    use std::collections::BTreeSet;

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

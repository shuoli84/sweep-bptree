use crate::*;

/// A borrowed iterator for BPlusTree
/// Borrowed, means the underlying tree won't change, so this is faster
/// compare to Cursor.
pub struct Iter<'a, S: NodeStore> {
    tree: &'a BPlusTree<S>,
    leaf: Option<&'a S::LeafNode>,
    leaf_offset: usize,
}

impl<'a, S: NodeStore> Iter<'a, S> {
    pub(crate) fn new(tree: &'a BPlusTree<S>) -> Self {
        let leaf = tree
            .first_leaf()
            .map(|leaf_id| tree.node_store.get_leaf(leaf_id));
        Self {
            tree,
            leaf,
            leaf_offset: 0,
        }
    }
}

impl<'a, S: NodeStore> Iterator for Iter<'a, S> {
    type Item = (&'a S::K, &'a S::V);

    fn next(&mut self) -> Option<Self::Item> {
        let leaf = self.leaf?;
        let offset = self.leaf_offset;
        let kv = leaf.data_at(offset);

        // move the position to next valid
        if offset + 1 < leaf.len() {
            self.leaf_offset = offset + 1;
            Some((&kv.0, &kv.1))
        } else {
            match leaf.next() {
                Some(next_id) => {
                    self.leaf = Some(self.tree.node_store.get_leaf(next_id));
                    self.leaf_offset = 0;
                }
                None => {
                    self.leaf = None;
                    self.leaf_offset = 0;
                }
            }
            Some((&kv.0, &kv.1))
        }
    }
}

pub struct IntoIter<S: NodeStore> {
    node_store: S,
    len: usize,
    /// current iterator pos
    pos: (LeafNodeId, usize),
    /// the end of the iterator
    end: (LeafNodeId, usize),
}

impl<S: NodeStore> IntoIter<S> {
    pub fn new(tree: BPlusTree<S>) -> Self {
        // the tree ensures there is at least one leaf
        let first_leaf_id = tree.first_leaf().unwrap();
        let last_leaf_id = tree.last_leaf().unwrap();

        let BPlusTree {
            len, node_store, ..
        } = tree;

        let last_leaf_size = node_store.get_leaf(last_leaf_id).len();

        Self {
            node_store,
            len,
            pos: (first_leaf_id, 0),
            end: (last_leaf_id, last_leaf_size),
        }
    }

    fn len(&self) -> usize {
        self.len
    }
}

impl<S: NodeStore> Iterator for IntoIter<S> {
    type Item = (S::K, S::V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len() == 0 {
            return None;
        }

        let (leaf_id, offset) = self.pos;
        let leaf = self.node_store.get_mut_leaf(leaf_id);

        if offset < leaf.len() {
            // book keeping current len
            self.len -= 1;
            // we should not call delete_at which internally memcpy, instead, use mark_uninit to take
            // the value out and leaves the memory uninit
            // safety: right after we called this, the pos moves to next.
            let kv = unsafe { leaf.take_data(offset) };
            self.pos = (leaf_id, offset + 1);
            return Some(kv);
        } else {
            // move to next leaf
            match leaf.next() {
                Some(next_id) => {
                    self.pos = (next_id, 0);
                    self.next()
                }
                None => {
                    // pos is the valid position, so it should not be the end
                    // we only reach here if len is mis counted
                    unreachable!()
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::tests::create_test_tree;

    #[derive(Clone)]
    struct TestValue {
        counter: Rc<std::sync::atomic::AtomicU64>,
    }

    impl TestValue {
        fn new(counter: Rc<std::sync::atomic::AtomicU64>) -> Self {
            Self { counter }
        }
    }

    impl Drop for TestValue {
        fn drop(&mut self) {
            self.counter
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }

    #[test]
    fn test_iter() {
        let (tree, _) = create_test_tree::<100>();
        let iter = Iter::new(&tree);
        let kvs = iter.collect::<Vec<_>>();
        assert_eq!(kvs.len(), tree.len());
    }

    #[test]
    fn test_into_iter() {
        let node_store = NodeStoreVec::<i64, TestValue, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);
    }
}

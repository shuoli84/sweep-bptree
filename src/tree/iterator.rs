use super::*;

/// A borrowed iterator for BPlusTree
/// Borrowed, means the underlying tree won't change, so this is faster
/// compare to Cursor.
pub struct Iter<'a, S: NodeStore> {
    tree: &'a BPlusTree<S>,
    len: usize,
    leaf: Option<&'a S::LeafNode>,
    leaf_offset: usize,

    end: Option<(&'a S::LeafNode, usize)>,
}

impl<'a, S: NodeStore> Iter<'a, S> {
    pub(crate) fn new(tree: &'a BPlusTree<S>) -> Self {
        let leaf = tree
            .first_leaf()
            .map(|leaf_id| tree.node_store.get_leaf(leaf_id));
        Self {
            tree,
            len: tree.len(),
            leaf,
            leaf_offset: 0,
            end: None,
        }
    }
}

impl<'a, S: NodeStore> Iterator for Iter<'a, S> {
    type Item = (&'a S::K, &'a S::V);

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let leaf = self.leaf?;
        let offset = self.leaf_offset;
        let kv = leaf.data_at(offset);

        // move the position to next valid
        if offset + 1 < leaf.len() {
            self.leaf_offset = offset + 1;
            self.len -= 1;
            Some(kv)
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

            self.len -= 1;
            Some(kv)
        }
    }
}

impl<'a, S: NodeStore> DoubleEndedIterator for Iter<'a, S> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        match self.end {
            Some((leaf, offset)) => {
                if offset > 0 {
                    let offset = offset - 1;
                    let kv = leaf.data_at(offset);
                    self.end = Some((leaf, offset));
                    Some(kv)
                } else {
                    // move to previous leaf
                    let prev_id = leaf.prev()?;
                    let leaf = self.tree.node_store.get_leaf(prev_id);
                    let offset = leaf.len() - 1;

                    self.end = Some((leaf, offset));
                    Some(leaf.data_at(offset))
                }
            }
            None => {
                let last_leaf_id = self.tree.last_leaf()?;
                let last_leaf = self.tree.node_store.get_leaf(last_leaf_id);
                let last_leaf_size = last_leaf.len();
                if last_leaf_size == 0 {
                    return None;
                }

                let offset = last_leaf_size - 1;

                self.end = Some((last_leaf, offset));
                Some(last_leaf.data_at(offset))
            }
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

        let (node_store, _root_id, len) = tree.into_parts();

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

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

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
}

impl<S: NodeStore> DoubleEndedIterator for IntoIter<S> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len() == 0 {
            return None;
        }

        let (leaf_id, offset) = self.end;
        let leaf = self.node_store.get_mut_leaf(leaf_id);

        if offset > 0 {
            // book keeping current len
            self.len -= 1;
            // we should not call delete_at which internally memcpy, instead, use mark_uninit to take
            // the value out and leaves the memory uninit
            // safety: right after we called this, the pos moves to next.
            let kv = unsafe { leaf.take_data(offset - 1) };
            self.end = (leaf_id, offset - 1);
            return Some(kv);
        } else {
            // move to prev leaf
            match leaf.prev() {
                Some(prev_id) => {
                    let prev_leaf = self.node_store.get_mut_leaf(prev_id);
                    self.end = (prev_id, prev_leaf.len());
                    self.next_back()
                }
                None => {
                    // we only reach here if len is mis counted
                    unreachable!()
                }
            }
        }
    }
}

impl<S: NodeStore> Drop for IntoIter<S> {
    fn drop(&mut self) {
        // drop all the remaining items
        while self.next().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::tree::tests::create_test_tree;

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
    fn test_iter_double_ended() {
        let (tree, _keys) = create_test_tree::<100>();
        let kvs = Iter::new(&tree).collect::<Vec<_>>();
        let rev_kvs = Iter::new(&tree).rev().collect::<Vec<_>>();

        assert_eq!(rev_kvs.len(), kvs.len());
        assert_eq!(rev_kvs, kvs.iter().rev().cloned().collect::<Vec<_>>());
    }

    #[test]
    fn test_into_iter_collect() {
        // test collect and drop
        let node_store = NodeStoreVec::<i64, TestValue, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);
        let counter = Rc::new(std::sync::atomic::AtomicU64::new(0));
        for i in 0..10 {
            tree.insert(i, TestValue::new(counter.clone()));
        }
        let iter = IntoIter::new(tree);
        let items = iter.collect::<Vec<_>>();
        assert_eq!(items.len(), 10);
        drop(items);

        assert_eq!(counter.load(std::sync::atomic::Ordering::Relaxed), 10);
    }

    #[test]
    fn test_into_iter_drop() {
        // test drop
        let node_store = NodeStoreVec::<i64, TestValue, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);
        let counter = Rc::new(std::sync::atomic::AtomicU64::new(0));
        for i in 0..10 {
            tree.insert(i, TestValue::new(counter.clone()));
        }
        let iter = IntoIter::new(tree);
        drop(iter);

        assert_eq!(counter.load(std::sync::atomic::Ordering::Relaxed), 10);
    }

    #[test]
    fn test_into_iter_double_ended() {
        let node_store = NodeStoreVec::<i64, TestValue, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);
        let counter = Rc::new(std::sync::atomic::AtomicU64::new(0));
        for i in 0..10 {
            tree.insert(i, TestValue::new(counter.clone()));
        }
        let items = IntoIter::new(tree)
            .rev()
            .map(|(k, _v)| k)
            .collect::<Vec<_>>();
        assert_eq!(items.len(), 10);
        assert_eq!(counter.load(std::sync::atomic::Ordering::Relaxed), 10);
        assert_eq!(items, (0..10).rev().collect::<Vec<_>>());
    }
}

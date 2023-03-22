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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::create_test_tree;

    #[test]
    fn test_iter() {
        let (tree, _) = create_test_tree::<100>();
        let iter = Iter::new(&tree);
        let kvs = iter.collect::<Vec<_>>();
        assert_eq!(kvs.len(), tree.len());
    }
}

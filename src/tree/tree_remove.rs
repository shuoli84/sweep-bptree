use super::{
    entry_ref::EntryRef, BPlusTree, InnerMergeResult, InnerNode, LeafDeleteResult, NodeStore,
};
use crate::argument::Argument;
use std::borrow::Borrow;

impl<S: NodeStore> BPlusTree<S> {
    pub(crate) fn remove_impl<Q>(&mut self, k: &Q) -> Option<(S::K, S::V)>
    where
        Q: ?Sized + Ord,
        S::K: Borrow<Q>,
    {
        let entry_ref = self.key_to_ref(k)?;
        let entry_ref_mut: EntryRef<&mut Self> = entry_ref.to_detached().to_ref(self);
        Self::remove_by_ref(entry_ref_mut)
    }

    pub(crate) fn remove_by_ref(entry_ref: EntryRef<&mut Self>) -> Option<(S::K, S::V)> {
        let EntryRef {
            tree,
            inner_stack: mut stack,
            leaf_id,
            offset,
        } = entry_ref;

        let mut r = {
            let leaf = tree.node_store.get_mut_leaf(leaf_id);

            match leaf.try_delete_at(offset) {
                LeafDeleteResult::Done(kv) => DeleteDescendResult::Done(kv),
                LeafDeleteResult::UnderSize(idx) => DeleteDescendResult::LeafUnderSize(idx),
            }
        };

        // pop visit stack and fix things up
        loop {
            match stack.pop() {
                Some((parent_id, child_idx, child_id)) => {
                    match r {
                        DeleteDescendResult::Done(_) => {
                            let child_argument =
                                Self::new_argument_for_id(&tree.node_store, child_id);
                            let inner_node = tree.node_store.get_mut_inner(parent_id);
                            inner_node.set_argument(child_idx, child_argument);
                        }
                        DeleteDescendResult::InnerUnderSize(kv) => {
                            // Safety: When mutating sub tree, this node is the root and won't be queried or mutated
                            //         so we can safely get a mut ptr to it.
                            let parent =
                                unsafe { &mut *tree.node_store.get_mut_inner_ptr(parent_id) };
                            r = tree.handle_inner_under_size(parent, child_idx, kv);
                        }
                        DeleteDescendResult::LeafUnderSize(idx) => {
                            // todo: remove this unsafe
                            let inner_node =
                                unsafe { &mut *tree.node_store.get_mut_inner_ptr(parent_id) };
                            r = tree.handle_leaf_under_size(inner_node, child_idx, idx);
                        }
                    }
                }
                None => {
                    // now process root
                    let r = match r {
                        DeleteDescendResult::Done(kv) => Some(kv),
                        DeleteDescendResult::InnerUnderSize(deleted_item) => {
                            let root = tree
                                .node_store
                                .get_mut_inner(unsafe { tree.root.inner_id_unchecked() });

                            if root.is_empty() {
                                tree.root = root.child_id(0);
                            }

                            Some(deleted_item)
                        }
                        DeleteDescendResult::LeafUnderSize(idx) => {
                            let leaf = tree
                                .node_store
                                .get_mut_leaf(unsafe { tree.root.leaf_id_unchecked() });
                            let item = leaf.delete_at(idx);
                            Some(item)
                        }
                    };

                    if r.is_some() {
                        tree.root_argument = Self::new_argument_for_id(&tree.node_store, tree.root);
                        tree.len -= 1;
                    }

                    return r;
                }
            }
        }
    }

    fn handle_inner_under_size(
        &mut self,
        node: &mut InnerNode<S::K, S::Argument>,
        child_idx: usize,
        deleted_item: (S::K, S::V),
    ) -> DeleteDescendResult<S::K, S::V> {
        if child_idx > 0
            && Self::try_rotate_right_for_inner_node(&mut self.node_store, node, child_idx - 1)
                .is_some()
        {
            self.st.rotate_right_inner += 1;
            return DeleteDescendResult::Done(deleted_item);
        }
        if child_idx < node.len()
            && Self::try_rotate_left_for_inner_node(&mut self.node_store, node, child_idx).is_some()
        {
            self.st.rotate_left_inner += 1;
            return DeleteDescendResult::Done(deleted_item);
        }

        let merge_slot = if child_idx > 0 {
            self.st.merge_with_left_inner += 1;
            child_idx - 1
        } else {
            self.st.merge_with_right_inner += 1;
            child_idx
        };

        match Self::merge_inner_node(&mut self.node_store, node, merge_slot) {
            InnerMergeResult::Done => DeleteDescendResult::Done(deleted_item),
            InnerMergeResult::UnderSize => DeleteDescendResult::InnerUnderSize(deleted_item),
        }
    }

    fn handle_leaf_under_size(
        &mut self,
        node: &mut InnerNode<S::K, S::Argument>,
        child_idx: usize,
        key_idx_in_child: usize,
    ) -> DeleteDescendResult<<S as NodeStore>::K, <S as NodeStore>::V> {
        let prev_sibling = if child_idx > 0 {
            Some(
                self.node_store
                    .get_leaf(unsafe { node.child_id(child_idx - 1).leaf_id_unchecked() }),
            )
        } else {
            None
        };
        let next_sibling = if child_idx < node.len() {
            Some(
                self.node_store
                    .get_leaf(unsafe { node.child_id(child_idx + 1).leaf_id_unchecked() }),
            )
        } else {
            None
        };

        let action: FixAction = match (prev_sibling, next_sibling) {
            (Some(p), Some(n)) => {
                if p.able_to_lend() {
                    if n.able_to_lend() {
                        if p.len() > n.len() {
                            FixAction::RotateRight
                        } else {
                            FixAction::RotateLeft
                        }
                    } else {
                        FixAction::RotateRight
                    }
                } else if n.able_to_lend() {
                    FixAction::RotateLeft
                } else {
                    FixAction::MergeLeft
                }
            }
            (Some(p), None) => {
                if p.able_to_lend() {
                    FixAction::RotateRight
                } else {
                    FixAction::MergeLeft
                }
            }
            (None, Some(n)) => {
                if n.able_to_lend() {
                    FixAction::RotateLeft
                } else {
                    FixAction::MergeRight
                }
            }
            _ => unreachable!(),
        };

        match action {
            FixAction::RotateRight => {
                let deleted = Self::rotate_right_for_leaf(
                    &mut self.node_store,
                    node,
                    child_idx - 1,
                    key_idx_in_child,
                );
                self.st.rotate_right_leaf += 1;
                DeleteDescendResult::Done(deleted)
            }
            FixAction::RotateLeft => {
                let deleted = Self::rotate_left_for_leaf(
                    &mut self.node_store,
                    node,
                    child_idx,
                    key_idx_in_child,
                );
                self.st.rotate_left_leaf += 1;
                DeleteDescendResult::Done(deleted)
            }
            FixAction::MergeLeft => {
                self.st.merge_with_left_leaf += 1;
                // merge with prev node

                Self::merge_leaf_node_left(
                    &mut self.node_store,
                    node,
                    child_idx - 1,
                    key_idx_in_child,
                )
            }
            FixAction::MergeRight => {
                self.st.merge_with_right_leaf += 1;
                // merge with next node

                Self::merge_leaf_node_with_right(
                    &mut self.node_store,
                    node,
                    child_idx,
                    key_idx_in_child,
                )
            }
        }
    }

    fn try_rotate_right_for_inner_node(
        node_store: &mut S,
        node: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
    ) -> Option<()> {
        //     1    3  5
        //      ..2  4
        // rotate right
        //     1    2   5
        //       ..   3,4
        let right_child_id = unsafe { node.child_id(slot + 1).inner_id_unchecked() };
        let left_child_id = unsafe { node.child_id(slot).inner_id_unchecked() };

        let prev_node = node_store.get_mut_inner(left_child_id);
        if prev_node.able_to_lend() {
            let (k, c, a) = prev_node.pop();
            let left_argument = S::Argument::from_inner(prev_node.keys(), prev_node.arguments());

            let slot_key = node.set_key(slot, k);
            let right = node_store.get_mut_inner(right_child_id);
            right.push_front(slot_key, c, a);
            let right_argument = S::Argument::from_inner(right.keys(), right.arguments());

            node.set_argument(slot, left_argument);
            node.set_argument(slot + 1, right_argument);

            Some(())
        } else {
            None
        }
    }

    fn try_rotate_left_for_inner_node(
        node_store: &mut S,
        node: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
    ) -> Option<()> {
        //     1  3  5
        //       2  4..
        // rotate right
        //     1   4   5
        //      2,3  ..
        let right_child_id = unsafe { node.child_id(slot + 1).inner_id_unchecked() };
        let left_child_id = unsafe { node.child_id(slot).inner_id_unchecked() };

        let right = node_store.get_mut_inner(right_child_id);
        if right.able_to_lend() {
            let (k, c, m) = right.pop_front();

            let right_argument = S::Argument::from_inner(right.keys(), right.arguments());

            let slot_key = node.set_key(slot, k);
            let left = node_store.get_mut_inner(left_child_id);
            left.push(slot_key, c, m);

            let left_argument = S::Argument::from_inner(left.keys(), left.arguments());

            node.set_argument(slot, left_argument);
            node.set_argument(slot + 1, right_argument);

            Some(())
        } else {
            None
        }
    }

    fn merge_inner_node(
        node_store: &mut S,
        node: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
    ) -> InnerMergeResult {
        //     1  3  5
        //       2  4
        //  merge 3
        //     1        5
        //       2,3,4
        debug_assert!(slot < node.len());

        let left_child_id = unsafe { node.child_id(slot).inner_id_unchecked() };
        let right_child_id = unsafe { node.child_id(slot + 1).inner_id_unchecked() };

        let (result, slot_key) = node.remove_slot_with_right(slot);

        // merge right into left
        let mut right = node_store.take_inner(right_child_id);
        let left = node_store.get_mut_inner(left_child_id);
        left.merge_next(slot_key, &mut right);

        let argument = S::Argument::from_inner(left.keys(), left.arguments());
        node.set_argument(slot, argument);

        result
    }

    fn rotate_right_for_leaf(
        node_store: &mut S,
        node: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
        delete_idx: usize,
    ) -> (S::K, S::V) {
        let left_id = unsafe { node.child_id(slot).leaf_id_unchecked() };
        let right_id = unsafe { node.child_id(slot + 1).leaf_id_unchecked() };

        let left = node_store.get_mut_leaf(left_id);
        debug_assert!(left.able_to_lend());

        let kv = left.pop();
        node.set_argument(slot, S::Argument::from_leaf(left.keys()));

        let new_slot_key = kv.0.clone();
        let right = node_store.get_mut_leaf(right_id);
        let deleted = right.delete_with_push_front(delete_idx, kv);
        node.set_argument(slot + 1, S::Argument::from_leaf(right.keys()));

        node_store.cache_leaf(right_id);

        // the prev key is dropped here
        let _ = node.set_key(slot, new_slot_key);

        deleted
    }

    fn rotate_left_for_leaf(
        node_store: &mut S,
        parent: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
        delete_idx: usize,
    ) -> (S::K, S::V) {
        let left_id = unsafe { parent.child_id(slot).leaf_id_unchecked() };
        let right_id = unsafe { parent.child_id(slot + 1).leaf_id_unchecked() };

        let right = node_store.get_mut_leaf(right_id);
        debug_assert!(right.able_to_lend());

        let kv = right.pop_front();
        parent.set_argument(slot + 1, S::Argument::from_leaf(right.keys()));

        let new_slot_key = right.data_at(0).0.clone();
        let left = node_store.get_mut_leaf(left_id);
        let deleted = left.delete_with_push(delete_idx, kv);
        parent.set_argument(slot, S::Argument::from_leaf(left.keys()));

        // the prev key is dropped here
        let _ = parent.set_key(slot, new_slot_key);

        node_store.cache_leaf(left_id);
        deleted
    }

    fn merge_leaf_node_left(
        node_store: &mut S,
        parent: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
        delete_idx: usize,
    ) -> DeleteDescendResult<S::K, S::V> {
        let left_leaf_id = unsafe { parent.child_id(slot).leaf_id_unchecked() };
        let right_leaf_id = unsafe { parent.child_id(slot + 1).leaf_id_unchecked() };

        let mut right = node_store.take_leaf(right_leaf_id);
        let left = node_store.get_mut_leaf(left_leaf_id);
        let kv = left.merge_right_delete_first(delete_idx, &mut right);
        parent.set_argument(slot, S::Argument::from_leaf(left.keys()));

        if let Some(next) = left.next() {
            node_store.get_mut_leaf(next).set_prev(Some(left_leaf_id));
        }

        let r = match parent.remove_slot_with_right(slot) {
            (InnerMergeResult::Done, _removed_k) => DeleteDescendResult::Done(kv),
            (InnerMergeResult::UnderSize, _removed_k) => DeleteDescendResult::InnerUnderSize(kv),
        };

        node_store.cache_leaf(left_leaf_id);
        r
    }

    fn merge_leaf_node_with_right(
        node_store: &mut S,
        parent: &mut InnerNode<S::K, S::Argument>,
        slot: usize,
        delete_idx: usize,
    ) -> DeleteDescendResult<S::K, S::V> {
        let left_leaf_id = unsafe { parent.child_id(slot).leaf_id_unchecked() };
        let right_leaf_id = unsafe { parent.child_id(slot + 1).leaf_id_unchecked() };

        let mut right = node_store.take_leaf(right_leaf_id);
        let left = node_store.get_mut_leaf(left_leaf_id);
        let kv = left.delete_at(delete_idx);
        left.merge_right(&mut right);

        parent.set_argument(slot, S::Argument::from_leaf(left.keys()));

        if let Some(next) = left.next() {
            node_store.get_mut_leaf(next).set_prev(Some(left_leaf_id));
        }

        // the merge on inner, it could propagate
        let r = match parent.remove_slot_with_right(slot) {
            (InnerMergeResult::Done, _removed_k) => DeleteDescendResult::Done(kv),
            (InnerMergeResult::UnderSize, _removed_k) => DeleteDescendResult::InnerUnderSize(kv),
        };
        node_store.cache_leaf(left_leaf_id);
        r
    }
}

/// Fix action
#[derive(Debug)]
enum FixAction {
    RotateRight,
    RotateLeft,
    MergeLeft,
    MergeRight,
}

#[derive(Debug)]
enum DeleteDescendResult<K, V> {
    Done((K, V)),
    /// Inner node under size, the index and node_id to remove
    InnerUnderSize((K, V)),
    /// Leaf node under size
    LeafUnderSize(usize),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{tree::LeafNodeId, NodeStoreVec};

    #[test]
    fn test_merge() {
        let mut node_store = NodeStoreVec::<i64, i64>::new();
        let parent_id = node_store.new_empty_inner();
        let child_0 = node_store.new_empty_inner();
        let child_1 = node_store.new_empty_inner();
        let child_2 = node_store.new_empty_inner();
        let child_3 = node_store.new_empty_inner();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);
        node_store
            .get_mut_inner(child_1)
            .set_data([10, 11], [LeafNodeId(1), LeafNodeId(2), LeafNodeId(3)]);
        node_store
            .get_mut_inner(child_2)
            .set_data([40], [LeafNodeId(5), LeafNodeId(6)]);

        let mut parent = node_store.take_inner(parent_id);
        let _result = BPlusTree::merge_inner_node(&mut node_store, &mut parent, 1);
        node_store.put_back_inner(parent_id, parent);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.len(), 2);
            assert_eq!(parent.key(1).clone(), 50);
            assert_eq!(
                parent.child_id_vec(),
                vec![child_0.into(), child_1.into(), child_3.into(),]
            );
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.len(), 4);
            assert_eq!(child_1.key_vec(), vec![10, 11, 30, 40]);
            assert_eq!(
                child_1.child_id_vec(),
                vec![
                    LeafNodeId(1).into(),
                    LeafNodeId(2).into(),
                    LeafNodeId(3).into(),
                    LeafNodeId(5).into(),
                    LeafNodeId(6).into(),
                ]
            );
        }

        {
            assert!(node_store.try_get_inner(child_2).is_none());
        }
    }

    #[test]
    fn test_merge_leaf_with_right() {
        let mut node_store = NodeStoreVec::<i64, i64>::new();
        let parent_id = node_store.new_empty_inner();
        let (child_0, _) = node_store.new_empty_leaf();
        let (child_1, _) = node_store.new_empty_leaf();
        let (child_2, _) = node_store.new_empty_leaf();
        let (child_3, _) = node_store.new_empty_leaf();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);
        node_store
            .get_mut_leaf(child_1)
            .set_data([(10, 1), (11, 1)].into_iter());
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1)].into_iter());

        let mut parent = node_store.take_inner(parent_id);
        let _result = BPlusTree::merge_leaf_node_with_right(&mut node_store, &mut parent, 1, 0);
        node_store.put_back_inner(parent_id, parent);
        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 50);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(child_1.data_vec(), vec![(11, 1), (39, 1), (40, 1),]);
        }

        assert!(node_store.try_get_leaf(child_2).is_none());
    }

    #[test]
    fn test_merge_leaf_with_left() {
        let mut node_store = NodeStoreVec::<i64, i64>::new();
        let parent_id = node_store.new_empty_inner();
        let (child_0, _) = node_store.new_empty_leaf();
        let (child_1, _) = node_store.new_empty_leaf();
        let (child_2, _) = node_store.new_empty_leaf();
        let (child_3, _) = node_store.new_empty_leaf();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);
        node_store
            .get_mut_leaf(child_1)
            .set_data([(10, 1), (11, 1)].into_iter());
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1)].into_iter());

        let mut parent = node_store.take_inner(parent_id);
        let _result = BPlusTree::merge_leaf_node_left(&mut node_store, &mut parent, 1, 0);
        node_store.put_back_inner(parent_id, parent);
        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 50);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(child_1.data_vec(), vec![(10, 1), (11, 1), (40, 1),]);
        }

        assert!(node_store.try_get_leaf(child_2).is_none());
    }
}

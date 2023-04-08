mod inner_node;
mod utils;
use std::mem::ManuallyDrop;

pub use inner_node::*;
mod leaf_node;
pub use leaf_node::*;
mod node_id;
pub use node_id::*;
mod cursor;
pub use cursor::*;
mod iterator;
pub use iterator::*;
mod node_stores;
pub use node_stores::*;
mod bulk_load;

/// B plus tree implementation, with following considerations:
///
/// 1. Performance critical, for sweep like algo, the sweepline's searching and updating is on hot path
/// 2. Cursor support, after one search, it should be fairly easy to move next or prev without another search
/// 3. Memory efficient, reduce mem alloc
///
/// # Example
/// ```rust
/// use sweep_bptree::{BPlusTree, NodeStoreVec};
///
/// // create a node_store with `u64` as key, `(f64, f64)` as value, inner node size 64, child size 65, leaf node size 64
/// let mut node_store = NodeStoreVec::<u64, (f64, f64), 64, 65, 64>::new();
/// let mut tree = BPlusTree::new(node_store);
///
/// // insert new value
/// assert!(tree.insert(3, (0., 0.)).is_none());
///
/// // update by insert again
/// assert_eq!(tree.insert(3, (1., 1.)).unwrap(), (0., 0.));
///
/// // remove the value
/// assert_eq!(tree.remove(&3).unwrap(), (1.0, 1.0));
///
/// assert!(tree.is_empty());
/// ```
///
/// # Example
/// Create multiple owned cursors
///
/// ``` rust
/// use sweep_bptree::{BPlusTree, NodeStoreVec};
/// let mut node_store = NodeStoreVec::<u64, (f64, f64), 64, 65, 64>::new();
/// let mut tree = BPlusTree::new(node_store);
///
/// for i in 0..100 {
///     tree.insert(i, (i as f64, i as f64));
/// }
///
/// let cursor_0 = tree.cursor_first().unwrap();
/// let cursor_1 = tree.cursor_first().unwrap();
///
/// // remove the key 0
/// tree.remove(&0);
///
/// // cursor's value should be empty now
/// assert!(cursor_0.value(&tree).is_none());
///
/// // move to next
/// let cursor_next = cursor_0.next(&tree).unwrap();
/// assert_eq!(*cursor_next.key(), 1);
/// assert_eq!(cursor_next.value(&tree).unwrap().0, 1.);
///
/// // insert a new value to key 0
/// tree.insert(0, (100., 100.));
/// // now cursor_1 should retrieve the new value
/// assert_eq!(cursor_1.value(&tree).unwrap().0, 100.);
/// ```
#[derive(Clone)]
pub struct BPlusTree<S: NodeStore> {
    root: NodeId,
    len: usize,
    node_store: ManuallyDrop<S>,
    st: Statistic,
}

impl<S> BPlusTree<S>
where
    S: NodeStore,
{
    /// Create a new `BPlusTree` with the given `NodeStore`.
    pub fn new(mut node_store: S) -> Self {
        let (root_id, _) = node_store.new_empty_leaf();
        Self {
            root: NodeId::Leaf(root_id),
            node_store: ManuallyDrop::new(node_store),
            len: 0,

            st: Statistic::default(),
        }
    }

    /// Create a new `BPlusTree` from existing parts
    fn new_from_parts(node_store: S, root: NodeId, len: usize) -> Self {
        let me = Self {
            root,
            node_store: ManuallyDrop::new(node_store),
            len,

            st: Statistic::default(),
        };

        #[cfg(test)]
        me.validate();

        me
    }

    /// Gets a reference to the `NodeStore` that this `BPlusTree` was created with.
    pub fn node_store(&self) -> &S {
        &self.node_store
    }

    /// Returns the number of elements in the tree.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the tree contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Insert a new key-value pair into the tree.
    pub fn insert(&mut self, k: S::K, v: S::V) -> Option<S::V> {
        // quick check if the last accessed leaf is the one to insert
        if let Some(leaf_id) = self.node_store.try_cache(&k) {
            let leaf = self.node_store.get_mut_leaf(leaf_id);
            if !leaf.is_full() {
                let result = match leaf.try_upsert(k, v) {
                    LeafUpsertResult::Inserted => {
                        self.len += 1;
                        // no need to update cache, it doesn't changed
                        None
                    }
                    LeafUpsertResult::Updated(v) => Some(v),
                    LeafUpsertResult::IsFull(_, _) => unreachable!(),
                };

                #[cfg(test)]
                self.validate();

                return result;
            }
        }

        let node_id = self.root;

        let result = match self.descend_insert(node_id, k, v) {
            DescendInsertResult::Inserted => None,
            DescendInsertResult::Updated(prev_v) => Some(prev_v),
            DescendInsertResult::Split(k, new_child_id) => {
                let new_root = S::InnerNode::new([k], [node_id, new_child_id]);
                let new_root_id = self.node_store.add_inner(new_root);
                self.root = new_root_id.into();
                None
            }
        };

        if result.is_none() {
            self.len += 1;
        }

        #[cfg(test)]
        self.validate();

        result
    }

    /// consume self and return the parts. This is useful when implementing `IntoIter`
    fn into_parts(self) -> (S, NodeId, usize) {
        let mut me = ManuallyDrop::new(self);
        (
            unsafe { ManuallyDrop::take(&mut me.node_store) },
            me.root,
            me.len,
        )
    }

    pub fn statistic(&self) -> &Statistic {
        &self.st
    }

    fn descend_insert_inner(
        &mut self,
        id: InnerNodeId,
        k: S::K,
        v: S::V,
    ) -> DescendInsertResult<S::K, S::V> {
        let node = self.node_store.get_inner(id);
        let (child_idx, child_id) = node.locate_child(&k);
        match self.descend_insert(child_id, k, v) {
            DescendInsertResult::Inserted => DescendInsertResult::Inserted,
            DescendInsertResult::Split(key, right_child) => {
                // child splited
                let inner_node = self.node_store.get_mut_inner(id);

                if !inner_node.is_full() {
                    let slot = child_idx;
                    inner_node.insert_at(slot, key, right_child);
                    DescendInsertResult::Inserted
                } else {
                    let (prompt_k, new_node) = inner_node.split(child_idx, key, right_child);

                    let new_node_id = self.node_store.add_inner(new_node);
                    DescendInsertResult::Split(prompt_k, NodeId::Inner(new_node_id))
                }
            }
            r => r,
        }
    }

    fn descend_insert(
        &mut self,
        node_id: NodeId,
        k: S::K,
        v: S::V,
    ) -> DescendInsertResult<S::K, S::V> {
        match node_id {
            NodeId::Inner(node_id) => self.descend_insert_inner(node_id, k, v),
            NodeId::Leaf(leaf_id) => self.insert_leaf(leaf_id, k, v),
        }
    }

    fn insert_leaf(&mut self, id: LeafNodeId, k: S::K, v: S::V) -> DescendInsertResult<S::K, S::V> {
        let leaf_node = self.node_store.get_mut_leaf(id);
        match leaf_node.try_upsert(k, v) {
            LeafUpsertResult::Inserted => {
                self.node_store.cache_leaf(id);
                DescendInsertResult::Inserted
            }
            LeafUpsertResult::Updated(v) => DescendInsertResult::Updated(v),
            LeafUpsertResult::IsFull(idx, v) => {
                let right_id = self.node_store.reserve_leaf();

                let l_leaf = self.node_store.get_mut_leaf(id);
                let r_leaf = l_leaf.split_new_leaf(idx, (k, v), right_id, id);
                let slot_key: S::K = *r_leaf.data_at(0).0;

                let updated_id = if idx >= S::leaf_n() as usize / 2 {
                    right_id
                } else {
                    id
                };
                self.node_store.cache_leaf(updated_id);

                // fix r_leaf's next's prev
                if let Some(next) = r_leaf.next() {
                    self.node_store.get_mut_leaf(next).set_prev(Some(right_id));
                }
                self.node_store.assign_leaf(right_id, r_leaf);

                DescendInsertResult::Split(slot_key, NodeId::Leaf(right_id))
            }
        }
    }

    /// Get reference to value identified by key.
    pub fn get(&self, k: &S::K) -> Option<&S::V> {
        if let Some(leaf_id) = self.node_store.try_cache(k) {
            // cache hit
            return self.find_in_leaf(leaf_id, k);
        }

        self.find_descend(self.root, k)
    }

    /// Get mutable reference to value identified by key.
    pub fn get_mut(&mut self, k: &S::K) -> Option<&mut S::V> {
        let mut cache_leaf_id: Option<LeafNodeId> = None;
        if let Some(leaf_id) = self.node_store.try_cache(k) {
            // cache hit
            cache_leaf_id = Some(leaf_id);
        }

        if let Some(leaf_id) = cache_leaf_id {
            return self.find_in_leaf_mut(leaf_id, k);
        }

        self.find_descend_mut(self.root, k)
    }

    #[inline]
    fn find_descend(&self, mut node_id: NodeId, k: &S::K) -> Option<&S::V> {
        loop {
            match node_id {
                NodeId::Inner(inner_id) => {
                    let inner_node = self.node_store.get_inner(inner_id);
                    let (_, child_id) = inner_node.locate_child(k);
                    node_id = child_id;
                    continue;
                }
                NodeId::Leaf(leaf_id) => return self.find_in_leaf_and_cache_it(leaf_id, k),
            }
        }
    }

    fn find_in_leaf(&self, leaf_id: LeafNodeId, k: &S::K) -> Option<&S::V> {
        let leaf_node = self.node_store.get_leaf(leaf_id);
        let (_, kv) = leaf_node.locate_slot_with_value(k);
        kv
    }

    fn find_descend_mut(&mut self, node_id: NodeId, k: &S::K) -> Option<&mut S::V> {
        match node_id {
            NodeId::Inner(inner_id) => {
                let inner_node = self.node_store.get_inner(inner_id);
                let (_, child_id) = inner_node.locate_child(k);
                self.find_descend_mut(child_id, k)
            }
            NodeId::Leaf(leaf_id) => self.find_in_leaf_mut_and_cache_it(leaf_id, k),
        }
    }

    fn find_in_leaf_mut(&mut self, leaf_id: LeafNodeId, k: &S::K) -> Option<&mut S::V> {
        let leaf_node = self.node_store.get_mut_leaf(leaf_id);
        let (_, v) = leaf_node.locate_slot_mut(k);
        v
    }

    fn find_in_leaf_mut_and_cache_it(
        &mut self,
        leaf_id: LeafNodeId,
        k: &S::K,
    ) -> Option<&mut S::V> {
        self.node_store.cache_leaf(leaf_id);
        let leaf_node = self.node_store.get_mut_leaf(leaf_id);
        let (_, kv) = leaf_node.locate_slot_mut(k);
        kv
    }

    /// Find the key in leaf, and cache leaf, this method only called when
    /// cache miss
    fn find_in_leaf_and_cache_it(&self, leaf_id: LeafNodeId, k: &S::K) -> Option<&S::V> {
        self.node_store.cache_leaf(leaf_id);
        let leaf = self.node_store.get_leaf(leaf_id);
        let (_, v) = leaf.locate_slot_with_value(k);
        v
    }

    /// delete element identified by K
    pub fn remove(&mut self, k: &S::K) -> Option<S::V> {
        // quick check if the last accessed leaf is the one to remove
        if let Some(cache_leaf_id) = self.node_store.try_cache(k) {
            let leaf = self.node_store.get_mut_leaf(cache_leaf_id);
            if leaf.able_to_lend() {
                let result = match leaf.try_delete(k) {
                    LeafDeleteResult::Done(v) => {
                        self.len -= 1;
                        Some(v.1)
                    }
                    LeafDeleteResult::NotFound => None,
                    LeafDeleteResult::UnderSize(_) => unreachable!(),
                };

                #[cfg(test)]
                self.validate();

                return result;
            }
        }

        let root_id = self.root;
        let r = match root_id {
            NodeId::Inner(inner_id) => match self.remove_inner(inner_id, k) {
                DeleteDescendResult::Done(kv) => Some(kv),
                DeleteDescendResult::None => None,
                DeleteDescendResult::InnerUnderSize(deleted_item) => {
                    let root = self.node_store.get_mut_inner(inner_id);

                    if root.is_empty() {
                        self.root = root.child_id(0);
                    }

                    Some(deleted_item)
                }
            },
            NodeId::Leaf(leaf_id) => {
                let leaf = self.node_store.get_mut_leaf(leaf_id);
                match leaf.try_delete(k) {
                    LeafDeleteResult::Done(kv) => Some(kv),
                    LeafDeleteResult::NotFound => None,
                    LeafDeleteResult::UnderSize(idx) => {
                        let item = leaf.delete_at(idx);
                        Some(item)
                    }
                }
            }
        };

        if r.is_some() {
            self.len -= 1;
        }

        r.map(|kv| kv.1)
    }

    fn remove_inner(&mut self, node_id: InnerNodeId, k: &S::K) -> DeleteDescendResult<S::K, S::V> {
        // Safety: When mutating sub tree, this node is the root and won't be queried or mutated
        //         so we can safely get a mutable ptr to it.
        let inner_node = unsafe { &mut *self.node_store.get_mut_inner_ptr(node_id) };
        let (child_idx, child_id) = inner_node.locate_child(k);
        let r = match child_id {
            NodeId::Inner(inner_id) => match self.remove_inner(inner_id, k) {
                DeleteDescendResult::Done(kv) => DeleteDescendResult::Done(kv),
                DeleteDescendResult::InnerUnderSize(deleted_item) => {
                    self.handle_inner_under_size(inner_node, child_idx, deleted_item)
                }
                DeleteDescendResult::None => DeleteDescendResult::None,
            },
            NodeId::Leaf(leaf_id) => {
                let leaf = self.node_store.get_mut_leaf(leaf_id);
                match leaf.try_delete(k) {
                    LeafDeleteResult::Done(kv) => DeleteDescendResult::Done(kv),
                    LeafDeleteResult::NotFound => DeleteDescendResult::None,
                    LeafDeleteResult::UnderSize(idx) => {
                        self.handle_leaf_under_size(inner_node, child_idx, idx)
                    }
                }
            }
        };

        r
    }

    fn handle_inner_under_size(
        &mut self,
        node: &mut S::InnerNode,
        child_idx: usize,
        deleted_item: (S::K, S::V),
    ) -> DeleteDescendResult<S::K, S::V> {
        if child_idx > 0 {
            if Self::try_rotate_right_for_inner_node(&mut self.node_store, node, child_idx - 1)
                .is_some()
            {
                self.st.rotate_right_inner += 1;
                return DeleteDescendResult::Done(deleted_item);
            }
        }
        if child_idx < node.size() {
            if Self::try_rotate_left_for_inner_node(&mut self.node_store, node, child_idx).is_some()
            {
                self.st.rotate_left_inner += 1;
                return DeleteDescendResult::Done(deleted_item);
            }
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
        node: &mut S::InnerNode,
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
        let next_sibling = if child_idx < node.size() {
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
                let result = Self::merge_leaf_node_left(
                    &mut self.node_store,
                    node,
                    child_idx - 1,
                    key_idx_in_child,
                );
                result
            }
            FixAction::MergeRight => {
                self.st.merge_with_right_leaf += 1;
                // merge with next node
                let result = Self::merge_leaf_node_with_right(
                    &mut self.node_store,
                    node,
                    child_idx,
                    key_idx_in_child,
                );

                result
            }
        }
    }

    fn try_rotate_right_for_inner_node(
        node_store: &mut S,
        node: &mut S::InnerNode,
        slot: usize,
    ) -> Option<()> {
        //     1    3  5
        //      ..2  4
        // rotate right
        //     1 2     5
        //     ..  3,4
        let right_child_id = unsafe { node.child_id(slot + 1).inner_id_unchecked() };
        let left_child_id = unsafe { node.child_id(slot).inner_id_unchecked() };
        let slot_key = *node.key(slot);

        let prev_node = node_store.get_mut_inner(left_child_id);
        if prev_node.able_to_lend() {
            let (k, c) = prev_node.pop();
            let child = node_store.get_mut_inner(right_child_id);
            child.push_front(slot_key, c);

            node.set_key(slot, k);

            Some(())
        } else {
            None
        }
    }

    fn try_rotate_left_for_inner_node(
        node_store: &mut S,
        node: &mut S::InnerNode,
        slot: usize,
    ) -> Option<()> {
        //     1  3  5
        //       2  4..
        // rotate right
        //     1   4   5
        //      2,3  ..
        let right_child_id = unsafe { node.child_id(slot + 1).inner_id_unchecked() };
        let left_child_id = unsafe { node.child_id(slot).inner_id_unchecked() };
        let slot_key = node.key(slot).clone();

        let right = node_store.get_mut_inner(right_child_id);
        if right.able_to_lend() {
            let (k, c) = right.pop_front();
            let left = node_store.get_mut_inner(left_child_id);
            left.push(slot_key, c);

            node.set_key(slot, k);

            Some(())
        } else {
            None
        }
    }

    fn merge_inner_node(
        node_store: &mut S,
        node: &mut S::InnerNode,
        slot: usize,
    ) -> InnerMergeResult {
        //     1  3  5
        //       2  4
        //  merge 3
        //     1        5
        //       2,3,4
        debug_assert!(slot < node.size());

        let left_child_id = unsafe { node.child_id(slot).inner_id_unchecked() };
        let right_child_id = unsafe { node.child_id(slot + 1).inner_id_unchecked() };
        let slot_key = node.key(slot).clone();

        // merge right into left
        let mut right = node_store.take_inner(right_child_id);
        let left = node_store.get_mut_inner(left_child_id);

        left.merge_next(slot_key, &mut right);

        node.merge_child(slot)
    }

    fn rotate_right_for_leaf(
        node_store: &mut S,
        node: &mut S::InnerNode,
        slot: usize,
        delete_idx: usize,
    ) -> (S::K, S::V) {
        let left_id = unsafe { node.child_id(slot).leaf_id_unchecked() };
        let right_id = unsafe { node.child_id(slot + 1).leaf_id_unchecked() };

        let left = node_store.get_mut_leaf(left_id);
        debug_assert!(left.able_to_lend());

        let kv = left.pop();
        let new_slot_key = kv.0;
        let right = node_store.get_mut_leaf(right_id);
        let deleted = right.delete_with_push_front(delete_idx, kv);

        node_store.cache_leaf(right_id);

        node.set_key(slot, new_slot_key);

        deleted
    }

    fn rotate_left_for_leaf(
        node_store: &mut S,
        parent: &mut S::InnerNode,
        slot: usize,
        delete_idx: usize,
    ) -> (S::K, S::V) {
        let left_id = unsafe { parent.child_id(slot).leaf_id_unchecked() };
        let right_id = unsafe { parent.child_id(slot + 1).leaf_id_unchecked() };

        let right = node_store.get_mut_leaf(right_id);
        debug_assert!(right.able_to_lend());

        let kv = right.pop_front();
        let new_slot_key = *right.data_at(0).0;
        let left = node_store.get_mut_leaf(left_id);
        let deleted = left.delete_with_push(delete_idx, kv);

        parent.set_key(slot, new_slot_key);

        node_store.cache_leaf(left_id);
        deleted
    }

    fn merge_leaf_node_left(
        node_store: &mut S,
        parent: &mut S::InnerNode,
        slot: usize,
        delete_idx: usize,
    ) -> DeleteDescendResult<S::K, S::V> {
        let left_leaf_id = unsafe { parent.child_id(slot).leaf_id_unchecked() };
        let right_leaf_id = unsafe { parent.child_id(slot + 1).leaf_id_unchecked() };

        let mut right = node_store.take_leaf(right_leaf_id);
        let left = node_store.get_mut_leaf(left_leaf_id);
        let kv = left.merge_right_delete_first(delete_idx, &mut right);

        if let Some(next) = left.next() {
            node_store.get_mut_leaf(next).set_prev(Some(left_leaf_id));
        }

        let r = match parent.merge_child(slot) {
            InnerMergeResult::Done => DeleteDescendResult::Done(kv),
            InnerMergeResult::UnderSize => DeleteDescendResult::InnerUnderSize(kv),
        };

        node_store.cache_leaf(left_leaf_id);
        r
    }

    fn merge_leaf_node_with_right(
        node_store: &mut S,
        parent: &mut S::InnerNode,
        slot: usize,
        delete_idx: usize,
    ) -> DeleteDescendResult<S::K, S::V> {
        let left_leaf_id = unsafe { parent.child_id(slot).leaf_id_unchecked() };
        let right_leaf_id = unsafe { parent.child_id(slot + 1).leaf_id_unchecked() };

        let mut right = node_store.take_leaf(right_leaf_id);
        let left = node_store.get_mut_leaf(left_leaf_id);
        let kv = left.delete_at(delete_idx);
        left.merge_right(&mut right);

        if let Some(next) = left.next() {
            node_store.get_mut_leaf(next).set_prev(Some(left_leaf_id));
        }

        // the merge on inner, it could propagate
        let r = match parent.merge_child(slot) {
            InnerMergeResult::Done => DeleteDescendResult::Done(kv),
            InnerMergeResult::UnderSize => DeleteDescendResult::InnerUnderSize(kv),
        };
        node_store.cache_leaf(left_leaf_id);
        r
    }

    /// get the first leaf_id if exists
    pub fn first_leaf(&self) -> Option<LeafNodeId> {
        match self.root {
            NodeId::Inner(inner_id) => {
                let mut result = None;

                self.descend_visit_inner(inner_id, |inner_node| {
                    let first_child_id = inner_node.child_id(0);
                    match first_child_id {
                        NodeId::Inner(inner_id) => Some(inner_id),
                        NodeId::Leaf(leaf_id) => {
                            result = Some(leaf_id);
                            None
                        }
                    }
                });

                result
            }
            NodeId::Leaf(leaf_id) => Some(leaf_id),
        }
    }

    /// get the last leaf_id if exists
    pub fn last_leaf(&self) -> Option<LeafNodeId> {
        match self.root {
            NodeId::Inner(inner_id) => {
                let mut result = None;

                self.descend_visit_inner(inner_id, |inner_node| {
                    let child_id = inner_node.child_id(inner_node.size());
                    match child_id {
                        NodeId::Inner(inner_id) => Some(inner_id),
                        NodeId::Leaf(leaf_id) => {
                            result = Some(leaf_id);
                            None
                        }
                    }
                });

                result
            }
            NodeId::Leaf(leaf_id) => Some(leaf_id),
        }
    }

    /// Locate the leaf node for `k`.
    /// Returns the leaf whose range contains `k`.
    /// User should query the leaf and check key existance.
    pub(crate) fn locate_leaf(&self, k: &S::K) -> Option<LeafNodeId> {
        if let Some(leaf_id) = self.node_store.try_cache(k) {
            return Some(leaf_id);
        }

        let leaf_id = match self.root {
            NodeId::Inner(inner_id) => {
                let mut result = None;
                self.descend_visit_inner(inner_id, |inner_node| {
                    let (_idx, node_id) = inner_node.locate_child(k);
                    match node_id {
                        NodeId::Inner(inner_node) => Some(inner_node),
                        NodeId::Leaf(leaf_id) => {
                            result = Some(leaf_id);
                            None
                        }
                    }
                });
                result
            }
            NodeId::Leaf(leaf_id) => Some(leaf_id),
        }?;

        Some(leaf_id)
    }

    fn descend_visit_inner(
        &self,
        mut node_id: InnerNodeId,
        mut f: impl FnMut(&S::InnerNode) -> Option<InnerNodeId>,
    ) -> Option<()> {
        loop {
            let inner = self.node_store.get_inner(node_id);
            match f(inner) {
                None => {
                    return None;
                }
                Some(id_to_visit) => node_id = id_to_visit,
            }
        }
    }

    /// Create an iterator on (&K, &V) pairs
    pub fn iter(&self) -> iterator::Iter<S> {
        iterator::Iter::new(self)
    }

    /// Consume the tree and create an iterator on (K, &V) pairs
    pub fn into_iter(self) -> iterator::IntoIter<S> {
        iterator::IntoIter::new(self)
    }

    /// Create an cursor from first elem
    pub fn cursor_first(&self) -> Option<Cursor<S::K>> {
        Cursor::first(self).map(|c| c.0)
    }

    /// Create an cursor for k
    pub fn get_cursor(&self, k: &S::K) -> Option<(Cursor<S::K>, Option<&S::V>)> {
        let node_id = self.root;
        let leaf_id = match node_id {
            NodeId::Inner(inner_id) => {
                let mut result = None;
                self.descend_visit_inner(inner_id, |inner_node| {
                    let (_idx, node_id) = inner_node.locate_child(k);
                    match node_id {
                        NodeId::Inner(inner_node) => Some(inner_node),
                        NodeId::Leaf(leaf_id) => {
                            result = Some(leaf_id);
                            None
                        }
                    }
                });
                result
            }
            NodeId::Leaf(leaf_id) => Some(leaf_id),
        }?;

        let leaf = self.node_store.get_leaf(leaf_id);
        let (idx, v) = leaf.locate_slot_with_value(k);
        Some((Cursor::new(*k, leaf_id, idx), v))
    }

    /// Clear the tree
    pub fn clear(&mut self) {
        // todo: should we keep the node_store's capacity?
        std::mem::drop(std::mem::replace(self, Self::new(S::default())));
    }

    #[cfg(test)]
    fn validate(&self) {
        let Some(mut leaf_id) = self.first_leaf() else { return; };
        let mut last_leaf_id: Option<LeafNodeId> = None;

        // ensures all prev and next are correct
        loop {
            let leaf = self.node_store.get_leaf(leaf_id);

            let p = leaf.prev();
            let n = leaf.next();

            if let Some(last_leaf_id) = last_leaf_id {
                assert_eq!(last_leaf_id, p.unwrap());
            }

            if n.is_none() {
                break;
            }

            last_leaf_id = Some(leaf_id);
            leaf_id = n.unwrap();
        }
    }
}

impl<S: NodeStore> Drop for BPlusTree<S> {
    fn drop(&mut self) {
        unsafe { drop(std::ptr::read(self).into_iter()) }
    }
}

/// Statistic data used to guide the perf tuning
#[derive(Default, Debug, Clone)]
pub struct Statistic {
    pub rotate_right_inner: u64,
    pub rotate_left_inner: u64,

    pub merge_with_left_inner: u64,
    pub merge_with_right_inner: u64,

    pub rotate_right_leaf: u64,
    pub rotate_left_leaf: u64,

    pub merge_with_left_leaf: u64,
    pub merge_with_right_leaf: u64,
}

/// Fix action
enum FixAction {
    RotateRight,
    RotateLeft,
    MergeLeft,
    MergeRight,
}

enum DescendInsertResult<K, V> {
    /// Update existing value, V is the previous value
    Updated(V),
    /// Inserted, and not split
    Inserted,
    /// need to split
    Split(K, NodeId),
}

#[derive(Debug)]
enum DeleteDescendResult<K, V> {
    None,
    Done((K, V)),
    /// Inner node under size, the index and node_id to remove
    InnerUnderSize((K, V)),
}

/// NodeStore is the node storage for tree, responsible for
/// define node types, manage node memory, and provide node access
pub trait NodeStore: Default {
    /// Key type for the tree
    type K: Key;
    /// Value type for the tree
    type V;

    /// InnerNode type
    type InnerNode: INode<Self::K>;
    /// LeafNode type
    type LeafNode: LNode<Self::K, Self::V>;

    /// Get the max number of keys inner node can hold
    fn inner_n() -> u16;
    /// Get the max number of elements leaf node can hold
    fn leaf_n() -> u16;

    /// Create an empty inner node and returns its id
    #[cfg(test)]
    fn new_empty_inner(&mut self) -> InnerNodeId;

    /// Add the inner node to the store and returns its id
    fn add_inner(&mut self, node: Box<Self::InnerNode>) -> InnerNodeId;

    /// Get the inner node
    /// # Panics
    /// if id is invalid or the node is already removed, panic
    fn get_inner(&self, id: InnerNodeId) -> &Self::InnerNode;

    /// Get the inner node
    /// if id is invalid or the node already removed, remove None
    fn try_get_inner(&self, id: InnerNodeId) -> Option<&Self::InnerNode>;

    /// Get a mut reference to the `InnerNode`
    fn get_mut_inner(&mut self, id: InnerNodeId) -> &mut Self::InnerNode;

    /// Get a mut pointer to inner node.
    /// User must ensure there is non shared reference to the node co-exists
    unsafe fn get_mut_inner_ptr(&mut self, id: InnerNodeId) -> *mut Self::InnerNode;

    /// Take the inner node out of the store
    fn take_inner(&mut self, id: InnerNodeId) -> Box<Self::InnerNode>;

    /// Put back the inner node
    fn put_back_inner(&mut self, id: InnerNodeId, node: Box<Self::InnerNode>);

    /// Create a new empty leaf node and returns its id
    fn new_empty_leaf(&mut self) -> (LeafNodeId, &mut Self::LeafNode);

    /// Reserve a leaf node, it must be assigned later
    fn reserve_leaf(&mut self) -> LeafNodeId;

    /// Get a refernce to leaf node
    /// Panics if id is invalid or the node is taken
    fn get_leaf(&self, id: LeafNodeId) -> &Self::LeafNode;

    /// Get a reference to leaf node
    /// Returns None if id is invalid or the node is taken
    fn try_get_leaf(&self, id: LeafNodeId) -> Option<&Self::LeafNode>;

    /// Get a mut reference to leaf node
    /// Panics if id is invalid or the node is taken
    fn get_mut_leaf(&mut self, id: LeafNodeId) -> &mut Self::LeafNode;

    /// Take the leaf out of store
    fn take_leaf(&mut self, id: LeafNodeId) -> Box<Self::LeafNode>;

    /// Assign the leaf to the id, the id must exists
    fn assign_leaf(&mut self, id: LeafNodeId, leaf: Box<Self::LeafNode>);

    /// cache leaf
    fn cache_leaf(&self, leaf_id: LeafNodeId);

    /// try cache for k
    fn try_cache(&self, k: &Self::K) -> Option<LeafNodeId>;

    #[cfg(test)]
    fn debug(&self)
    where
        Self::K: std::fmt::Debug,
        Self::V: std::fmt::Debug + Clone;
}

/// Key trait
pub trait Key: Copy + Clone + Ord + PartialOrd + Eq + PartialEq + 'static {}

impl<T> Key for T where T: Copy + Clone + Ord + PartialOrd + Eq + PartialEq + 'static {}

/// Inner node trait
pub trait INode<K: Key> {
    /// Create a new inner node with `slot_keys` and `child_id`.
    fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) -> Box<Self>;

    /// Create a new inner node from Iterators.
    /// Note: the count for keys must less than `IN`, and count for childs must be keys's count plus 1.
    /// Otherwise this method will panic!
    fn new_from_iter(
        keys: impl Iterator<Item = K>,
        childs: impl Iterator<Item = NodeId>,
    ) -> Box<Self>;

    /// Get the number of keys
    fn size(&self) -> usize;

    /// Check if the node is empty
    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Get the key at `slot`
    fn key(&self, slot: usize) -> &K;

    /// Set the key at `slot`
    fn set_key(&mut self, slot: usize, key: K);

    /// Get the child id at `idx`
    fn child_id(&self, idx: usize) -> NodeId;

    /// Locate child index and `NodeId` for `k`
    fn locate_child(&self, k: &K) -> (usize, NodeId);

    /// Check if the node is full
    fn is_full(&self) -> bool;

    /// Check if the node is able to lend a key to its sibling
    fn able_to_lend(&self) -> bool;

    /// Insert a key and the right child id at `slot`
    fn insert_at(&mut self, slot: usize, key: K, right_child: NodeId);

    /// Split the node at `child_idx` and return the key to be inserted to parent
    fn split(&mut self, child_idx: usize, k: K, new_child_id: NodeId) -> (K, Box<Self>);

    /// Remove the last key and its right child id
    fn pop(&mut self) -> (K, NodeId);

    /// Remove the first key and its left child id
    fn pop_front(&mut self) -> (K, NodeId);

    /// Insert a key and its right child id at the end
    fn push(&mut self, k: K, child: NodeId);

    /// Insert a key and its left child id at the front
    fn push_front(&mut self, k: K, child: NodeId);

    /// Merge the key and its right child id at `slot` with its right sibling
    fn merge_next(&mut self, slot_key: K, right: &mut Self);

    /// Merge children at slot
    fn merge_child(&mut self, slot: usize) -> InnerMergeResult;
}

/// Leaf node trait
/// This is not supposed to be implemented by user
pub trait LNode<K: Key, V> {
    /// Create an empty LeafNode
    fn new() -> Box<Self>;

    /// Returns size of the leaf
    fn len(&self) -> usize;

    /// Returns prev `LeafNodeId` if exists
    fn prev(&self) -> Option<LeafNodeId>;

    /// Set prev to `LeafNodeId`
    fn set_prev(&mut self, id: Option<LeafNodeId>);

    /// Returns next `LeafNodeId` if exists
    fn next(&self) -> Option<LeafNodeId>;

    /// Set next to `LeafNodeId`
    fn set_next(&mut self, id: Option<LeafNodeId>);

    fn set_data(&mut self, data: impl IntoIterator<Item = (K, V)>);
    fn data_at(&self, slot: usize) -> (&K, &V);
    fn try_data_at(&self, idx: usize) -> Option<(&K, &V)>;

    /// this takes data at `slot` out, makes original storage `uinit`.
    /// This should never called for same slot, or double free will happen.
    unsafe fn take_data(&mut self, slot: usize) -> (K, V);

    fn in_range(&self, k: &K) -> bool;
    fn key_range(&self) -> (Option<K>, Option<K>);
    fn is_full(&self) -> bool;
    fn able_to_lend(&self) -> bool;
    fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<V>;
    fn split_new_leaf(
        &mut self,
        insert_idx: usize,
        item: (K, V),
        new_leaf_id: LeafNodeId,
        self_leaf_id: LeafNodeId,
    ) -> Box<Self>;
    fn locate_slot(&self, k: &K) -> Result<usize, usize>;
    fn locate_slot_with_value(&self, k: &K) -> (usize, Option<&V>);

    fn locate_slot_mut(&mut self, k: &K) -> (usize, Option<&mut V>);
    fn try_delete(&mut self, k: &K) -> LeafDeleteResult<K, V>;
    fn delete_at(&mut self, idx: usize) -> (K, V);
    fn delete_with_push_front(&mut self, idx: usize, item: (K, V)) -> (K, V);
    fn delete_with_push(&mut self, idx: usize, item: (K, V)) -> (K, V);
    fn merge_right_delete_first(&mut self, delete_idx_in_next: usize, right: &mut Self) -> (K, V);
    fn merge_right(&mut self, right: &mut Self);
    fn pop(&mut self) -> (K, V);
    fn pop_front(&mut self) -> (K, V);
}

/// ensure NodeStoreVec is send for send v
fn _ensure_send<V: Send>() {
    fn _assert_send<T: Send>() {}
    _assert_send::<BPlusTree<NodeStoreVec<u64, V, 4, 5, 4>>>();
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use rand::seq::SliceRandom;

    use super::*;

    #[test]
    fn test_round_trip_100() {
        for _ in 0..100 {
            round_trip_one::<4, 5, 4>();
            round_trip_one::<5, 6, 5>();
        }
    }

    #[test]
    fn test_round_trip_one() {
        round_trip_one::<4, 5, 4>();
        round_trip_one::<5, 6, 5>();
    }

    fn round_trip_one<const N: usize, const C: usize, const L: usize>() {
        let node_store = NodeStoreVec::<i64, i64, N, C, L>::new();
        let mut tree = BPlusTree::new(node_store);

        let size: i64 = 500;

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        for i in keys {
            tree.insert(i, i % 13);
        }

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());
        for i in keys {
            assert_eq!(*tree.get(&i).unwrap(), i % 13);
        }

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        for i in keys {
            let k = i;

            let delete_result = tree.remove(&k);
            assert!(delete_result.is_some());
        }

        assert!(tree.is_empty());

        // call clear on empty tree
        tree.clear();
    }

    #[test]
    fn test_tree_clear() {
        let (mut tree, keys) = create_test_tree::<100>();
        tree.clear();
        assert!(tree.is_empty());

        // insert after clear
        for k in keys.clone() {
            tree.insert(k, k % 13);
        }
        assert_eq!(tree.len(), keys.len());
    }

    #[test]
    fn test_first_leaf() {
        let node_store = NodeStoreVec::<i64, i64, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);
        let size: i64 = 500;
        let keys = (0..size).collect::<Vec<_>>();
        for i in keys {
            tree.insert(i, i % 13);
        }

        let first_leaf_id = tree.first_leaf().unwrap();
        let first_leaf = tree.node_store.get_leaf(first_leaf_id);
        assert_eq!(first_leaf.data_at(0).0.clone(), 0);
    }

    #[test]
    fn test_rotate_right() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
        let parent_id = node_store.new_empty_inner();
        let child_0 = node_store.new_empty_inner();
        let child_1 = node_store.new_empty_inner();
        let child_2 = node_store.new_empty_inner();
        let child_3 = node_store.new_empty_inner();

        let parent_node = node_store.get_mut_inner(parent_id);
        parent_node.set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);

        node_store.get_mut_inner(child_1).set_data(
            [10, 11, 12, 13],
            [
                LeafNodeId(1),
                LeafNodeId(2),
                LeafNodeId(3),
                LeafNodeId(4),
                LeafNodeId(5),
            ],
        );

        node_store
            .get_mut_inner(child_2)
            .set_data([40, 41], [LeafNodeId(6), LeafNodeId(7), LeafNodeId(8)]);

        let mut parent = node_store.take_inner(parent_id);
        assert!(
            BPlusTree::try_rotate_right_for_inner_node(&mut node_store, &mut parent, 1).is_some()
        );
        node_store.put_back_inner(parent_id, parent);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 13);
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.size(), 3);
            assert_eq!(child_1.key_vec(), vec![10, 11, 12]);
            assert_eq!(
                child_1.child_id_vec(),
                vec![
                    LeafNodeId(1).into(),
                    LeafNodeId(2).into(),
                    LeafNodeId(3).into(),
                    LeafNodeId(4).into(),
                ]
            );
        }

        {
            let child_2 = node_store.get_inner(child_2);

            assert_eq!(child_2.size(), 3);

            assert_eq!(child_2.key_vec(), vec![30, 40, 41]);
            assert_eq!(
                child_2.child_id_vec(),
                vec![
                    LeafNodeId(5).into(),
                    LeafNodeId(6).into(),
                    LeafNodeId(7).into(),
                    LeafNodeId(8).into(),
                ]
            );
        }
    }

    #[test]
    fn test_rotate_left() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
        let parent_id = node_store.new_empty_inner();
        let child_0 = node_store.new_empty_inner();
        let child_1 = node_store.new_empty_inner();
        let child_2 = node_store.new_empty_inner();
        let child_3 = node_store.new_empty_inner();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);

        node_store.get_mut_inner(child_1).set_data(
            [10, 11, 12],
            [LeafNodeId(1), LeafNodeId(2), LeafNodeId(3), LeafNodeId(4)],
        );

        node_store.get_mut_inner(child_2).set_data(
            [39, 40, 41],
            [LeafNodeId(5), LeafNodeId(6), LeafNodeId(7), LeafNodeId(8)],
        );

        let mut parent = node_store.take_inner(parent_id);
        assert!(
            BPlusTree::try_rotate_left_for_inner_node(&mut node_store, &mut parent, 1).is_some()
        );
        node_store.put_back_inner(parent_id, parent);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 39);
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.size(), 4);
            assert_eq!(child_1.key_vec(), vec![10, 11, 12, 30]);
            assert_eq!(
                child_1.child_id_vec(),
                vec![
                    LeafNodeId(1).into(),
                    LeafNodeId(2).into(),
                    LeafNodeId(3).into(),
                    LeafNodeId(4).into(),
                    LeafNodeId(5).into(),
                ]
            );
        }

        {
            let child_2 = node_store.get_inner(child_2);

            assert_eq!(child_2.size(), 2);

            assert_eq!(child_2.key_vec(), vec![40, 41]);
            assert_eq!(
                child_2.child_id_vec(),
                vec![
                    LeafNodeId(6).into(),
                    LeafNodeId(7).into(),
                    LeafNodeId(8).into(),
                ]
            );
        }
    }

    #[test]
    fn test_merge() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
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
            assert_eq!(parent.size(), 2);
            assert_eq!(parent.key(1).clone(), 50);
            assert_eq!(
                parent.child_id_vec(),
                vec![child_0.into(), child_1.into(), child_3.into(),]
            );
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.size(), 4);
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
    fn test_rotate_right_for_leaf() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
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
            .set_data([(10, 1), (11, 1), (12, 1), (13, 1)]);

        node_store
            .get_mut_leaf(child_2)
            .set_data([(40, 1), (41, 1)]);

        let mut parent = node_store.take_inner(parent_id);
        BPlusTree::rotate_right_for_leaf(&mut node_store, &mut parent, 1, 0);
        node_store.put_back_inner(parent_id, parent);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 13);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(child_1.data_vec(), vec![(10, 1), (11, 1), (12, 1)]);
        }

        {
            let child_2 = node_store.get_leaf(child_2);
            assert_eq!(child_2.len(), 2);

            assert_eq!(child_2.data_vec(), vec![(13, 1), (41, 1)]);
        }
    }

    #[test]
    fn test_rotate_left_for_leaf() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
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
            .set_data([(10, 1), (11, 1), (12, 1)]);
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1), (41, 1)]);

        let mut parent = node_store.take_inner(parent_id);
        let result = BPlusTree::rotate_left_for_leaf(&mut node_store, &mut parent, 1, 0);
        node_store.put_back_inner(parent_id, parent);
        assert_eq!(result.0, 10);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 40);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(child_1.data_vec(), vec![(11, 1), (12, 1), (39, 1),]);
        }

        {
            let child_2 = node_store.get_leaf(child_2);
            assert_eq!(child_2.len(), 2);

            assert_eq!(child_2.data_vec(), vec![(40, 1), (41, 1)]);
        }
    }

    #[test]
    fn test_merge_leaf_with_right() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
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
            .set_data([(10, 1), (11, 1)]);
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1)]);

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
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
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
            .set_data([(10, 1), (11, 1)]);
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1)]);

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

    #[test]
    fn test_modify_value() {
        let (mut tree, _) = create_test_tree::<30>();
        let v = tree.get_mut(&1).unwrap();
        *v = 100;
        assert_eq!(tree.get(&1).unwrap().clone(), 100);
    }

    #[test]
    fn test_cursor() {
        let (mut tree, _) = create_test_tree::<30>();

        let (cursor, _kv) = tree.get_cursor(&10).unwrap();
        assert_eq!(cursor.key().clone(), 10);
        assert_eq!(cursor.value(&tree).unwrap().clone(), 10);

        {
            let prev = cursor.prev(&tree).unwrap();
            assert_eq!(prev.key().clone(), 9);

            let next = cursor.next(&tree).unwrap();
            assert_eq!(next.key().clone(), 11);
        }

        tree.remove(&10);

        {
            assert_eq!(cursor.key().clone(), 10);
            assert!(cursor.value(&tree).is_none());

            let prev = cursor.prev(&tree).unwrap();
            assert_eq!(prev.key().clone(), 9);

            let next = cursor.next(&tree).unwrap();
            assert_eq!(next.key().clone(), 11);
        }

        let (cursor, kv) = tree.get_cursor(&10).unwrap();
        assert_eq!(cursor.key().clone(), 10);
        assert!(kv.is_none());
    }

    pub fn create_test_tree<const N: usize>(
    ) -> (BPlusTree<NodeStoreVec<i64, i64, 8, 9, 6>>, Vec<i64>) {
        let node_store = NodeStoreVec::<i64, i64, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);

        let size: i64 = N as i64;

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        // println!("{:?}", keys);

        for i in keys.iter() {
            tree.insert(*i, i % 13);
        }

        assert_eq!(tree.len(), N);

        (tree, keys)
    }

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
    fn test_drop() {
        // test drop
        let node_store = NodeStoreVec::<i64, TestValue, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);
        let counter = Rc::new(std::sync::atomic::AtomicU64::new(0));
        for i in 0..10 {
            tree.insert(i, TestValue::new(counter.clone()));
        }
        drop(tree);

        assert_eq!(counter.load(std::sync::atomic::Ordering::Relaxed), 10);
    }
}
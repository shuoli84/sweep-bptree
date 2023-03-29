mod inner_node;
use std::{cell::RefCell, marker::PhantomData};

pub use inner_node::*;
mod leaf_node;
pub use leaf_node::*;
mod node_id;
pub use node_id::*;
mod cursor;
pub use cursor::*;
mod iterator;
pub use iterator::*;

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
    root: Option<NodeId>,
    len: usize,
    node_store: S,
    /// store last accessed leaf, and it's key range
    leaf_cache: RefCell<Option<(S::K, S::K, LeafNodeId)>>,
}

impl<S> BPlusTree<S>
where
    S: NodeStore,
{
    pub fn new(node_store: S) -> Self {
        Self {
            root: None,
            node_store,
            leaf_cache: RefCell::new(None),
            len: 0,
        }
    }

    /// Gets a reference to the `NodeStore` that this `BPlusTree` was created with.
    pub fn node_store(&self) -> &S {
        &self.node_store
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn insert(&mut self, k: S::K, v: S::V) -> Option<S::V> {
        let result = match self.root {
            Some(node_id) => match self.descend_insert(node_id, k, v) {
                DescendInsertResult::Inserted => None,
                DescendInsertResult::Updated(prev_v) => Some(prev_v),
                DescendInsertResult::Split(k, new_child_id) => {
                    let new_root = S::InnerNode::new([k], [node_id, new_child_id]);
                    let new_root_id = self.node_store.add_inner(new_root);
                    self.root = Some(new_root_id.into());
                    None
                }
            },
            None => {
                // empty tree, create new leaf as root
                let (id, node) = self.node_store.create_leaf();
                node.set_data([(k, v)]);
                self.root = Some(NodeId::Leaf(id));
                None
            }
        };

        #[cfg(test)]
        self.validate();

        if result.is_none() {
            self.len += 1;
        }

        result
    }

    fn descend_insert(
        &mut self,
        node_id: NodeId,
        k: S::K,
        v: S::V,
    ) -> DescendInsertResult<S::K, S::V> {
        match node_id {
            NodeId::Inner(node_id) => {
                let node = self.node_store.get_inner(node_id);
                let (child_idx, child_id) = node.locate_child(&k);
                match self.descend_insert(child_id, k, v) {
                    DescendInsertResult::Inserted => DescendInsertResult::Inserted,
                    DescendInsertResult::Split(key, right_child) => {
                        // child splited
                        let inner_node = self.node_store.get_mut_inner(node_id);

                        if !inner_node.is_full() {
                            let slot = child_idx;
                            inner_node.insert_at(slot, key, right_child);
                            DescendInsertResult::Inserted
                        } else {
                            let (prompt_k, new_node) =
                                inner_node.split(child_idx, key, right_child);

                            let new_node_id = self.node_store.add_inner(new_node);
                            DescendInsertResult::Split(prompt_k, NodeId::Inner(new_node_id))
                        }
                    }
                    r => r,
                }
            }
            NodeId::Leaf(leaf_id) => {
                let leaf_node = self.node_store.get_mut_leaf(leaf_id);
                match leaf_node.try_upsert(k, v) {
                    LeafUpsertResult::Inserted => DescendInsertResult::Inserted,
                    LeafUpsertResult::Updated(v) => DescendInsertResult::Updated(v),
                    LeafUpsertResult::IsFull(idx) => {
                        let (new_leaf_id, _) = self.node_store.create_leaf();

                        let l_leaf = self.node_store.get_mut_leaf(leaf_id);
                        let r_leaf = l_leaf.split_new_leaf(idx, (k, v), new_leaf_id, leaf_id);
                        let slot_key: S::K = r_leaf.data_at(0).0;

                        if k >= slot_key {
                            self.set_cache(new_leaf_id, r_leaf.key_range());
                        } else {
                            let l_leaf_key = l_leaf.key_range();
                            self.set_cache(leaf_id, l_leaf_key);
                        }

                        // fix r_leaf's next's prev
                        if let Some(next) = r_leaf.next() {
                            self.node_store
                                .get_mut_leaf(next)
                                .set_prev(Some(new_leaf_id));
                        }
                        *self.node_store.get_mut_leaf(new_leaf_id) = r_leaf;

                        DescendInsertResult::Split(slot_key, NodeId::Leaf(new_leaf_id))
                    }
                }
            }
        }
    }

    fn set_cache(&self, id: LeafNodeId, key_range: (S::K, S::K)) {
        *self.leaf_cache.borrow_mut() = Some((key_range.0, key_range.1, id));
    }

    fn clear_cache(&self) {
        *self.leaf_cache.borrow_mut() = None;
    }

    pub fn get(&self, k: &S::K) -> Option<&S::V> {
        if let Some(cache) = self.leaf_cache.borrow().as_ref() {
            if cache.0 <= *k && cache.1 >= *k {
                // cache hit
                return self.find_in_leaf(cache.2, k);
            }
        }

        self.find_descend(self.root?, k)
    }

    /// Get mutable reference to value identified by key.
    pub fn get_mut(&mut self, k: &S::K) -> Option<&mut S::V> {
        let mut cache_leaf_id: Option<LeafNodeId> = None;
        if let Some(cache) = self.leaf_cache.borrow_mut().as_ref() {
            if cache.0 <= *k && cache.1 >= *k {
                // cache hit
                cache_leaf_id = Some(cache.2);
            }
        }

        if let Some(leaf_id) = cache_leaf_id {
            return self.find_in_leaf_mut(leaf_id, k);
        }

        self.find_descend_mut(self.root?, k)
    }

    fn find_descend(&self, node_id: NodeId, k: &S::K) -> Option<&S::V> {
        match node_id {
            NodeId::Inner(inner_id) => {
                let inner_node = self.node_store.get_inner(inner_id);
                let (_, child_id) = inner_node.locate_child(k);
                self.find_descend(child_id, k)
            }
            NodeId::Leaf(leaf_id) => self.find_in_leaf_and_cache_it(leaf_id, k),
        }
    }

    fn find_in_leaf(&self, leaf_id: LeafNodeId, k: &S::K) -> Option<&S::V> {
        let leaf_node = self.node_store.get_leaf(leaf_id);
        let (_, kv) = leaf_node.locate_slot(k);
        kv.map(|kv| &kv.1)
    }

    fn find_descend_mut(&mut self, node_id: NodeId, k: &S::K) -> Option<&mut S::V> {
        match node_id {
            NodeId::Inner(inner_id) => {
                let inner_node = self.node_store.get_inner(inner_id);
                let (_, child_id) = inner_node.locate_child(k);
                self.find_descend_mut(child_id, k)
            }
            NodeId::Leaf(leaf_id) => self.find_in_leaf_mut(leaf_id, k),
        }
    }

    fn find_in_leaf_mut(&mut self, leaf_id: LeafNodeId, k: &S::K) -> Option<&mut S::V> {
        let leaf_node = self.node_store.get_mut_leaf(leaf_id);
        let (_, kv) = leaf_node.locate_slot_mut(k);
        kv
    }

    fn find_in_leaf_and_cache_it(&self, leaf_id: LeafNodeId, k: &S::K) -> Option<&S::V> {
        let leaf_node = self.node_store.get_leaf(leaf_id);
        self.set_cache(leaf_id, leaf_node.key_range());
        let (_, kv) = leaf_node.locate_slot(k);
        kv.map(|kv| &kv.1)
    }

    /// delete element identified by K
    pub fn remove(&mut self, k: &S::K) -> Option<S::V> {
        let root_id = self.root?;
        let r = match self.delete_descend(root_id, k) {
            DeleteDescendResult::Done(kv) => Some(kv),
            DeleteDescendResult::None => None,
            DeleteDescendResult::LeafUnderSize(idx) => {
                let item = self
                    .node_store
                    .get_mut_leaf(root_id.leaf_id().unwrap())
                    .delete_at(idx);
                Some(item)
            }
            DeleteDescendResult::InnerUnderSize(deleted_item) => {
                let root = self.node_store.get_mut_inner(root_id.inner_id().unwrap());
                if root.is_empty() {
                    self.root = Some(root.child_id_at(0));
                }

                Some(deleted_item)
            }
        };

        if r.is_some() {
            self.len -= 1;
        }

        // clear cache for remove
        self.clear_cache();
        r.map(|kv| kv.1)
    }

    fn delete_descend(&mut self, node_id: NodeId, k: &S::K) -> DeleteDescendResult<S::K, S::V> {
        let r = match node_id {
            NodeId::Inner(inner_id) => {
                let inner_node = self.node_store.get_inner(inner_id);
                let inner_node_size = inner_node.size();
                debug_assert!(inner_node_size > 0);

                let (child_idx, child_id) = inner_node.locate_child(k);
                match self.delete_descend(child_id, k) {
                    DeleteDescendResult::Done(kv) => DeleteDescendResult::Done(kv),
                    DeleteDescendResult::LeafUnderSize(key_idx_in_child) => {
                        // child not modified yet. Prefer lend from prev, pop_back operation is faster
                        // than pop_front
                        if child_idx > 0 {
                            if let Some(deleted) = Self::try_rotate_right_for_leaf_node(
                                &mut self.node_store,
                                inner_id,
                                child_idx - 1,
                                key_idx_in_child,
                            ) {
                                return DeleteDescendResult::Done(deleted);
                            }
                        }

                        // try borrow from next
                        if child_idx < inner_node_size {
                            if let Some(deleted) = Self::try_rotate_left_for_leaf_node(
                                &mut self.node_store,
                                inner_id,
                                child_idx,
                                key_idx_in_child,
                            ) {
                                return DeleteDescendResult::Done(deleted);
                            }
                        }

                        // neither prev nor next able to lend us, so merge
                        if child_idx > 0 {
                            // merge with prev node
                            Self::merge_leaf_node_left(
                                &mut self.node_store,
                                inner_id,
                                child_idx - 1,
                                key_idx_in_child,
                            )
                        } else {
                            // merge with next node
                            Self::merge_leaf_node_with_right(
                                &mut self.node_store,
                                inner_id,
                                child_idx,
                                key_idx_in_child,
                            )
                        }
                    }
                    DeleteDescendResult::InnerUnderSize(deleted_item) => {
                        if child_idx > 0 {
                            if Self::try_rotate_right_for_inner_node(
                                &mut self.node_store,
                                inner_id,
                                child_idx - 1,
                            )
                            .is_some()
                            {
                                return DeleteDescendResult::Done(deleted_item);
                            }
                        }
                        if child_idx < inner_node_size {
                            if Self::try_rotate_left_for_inner_node(
                                &mut self.node_store,
                                inner_id,
                                child_idx,
                            )
                            .is_some()
                            {
                                return DeleteDescendResult::Done(deleted_item);
                            }
                        }
                        let merge_slot = if child_idx > 0 {
                            child_idx - 1
                        } else {
                            child_idx
                        };

                        match Self::merge_inner_node(&mut self.node_store, inner_id, merge_slot) {
                            InnerMergeResult::Done => {
                                return DeleteDescendResult::Done(deleted_item);
                            }
                            InnerMergeResult::UnderSize => {
                                return DeleteDescendResult::InnerUnderSize(deleted_item)
                            }
                        }
                    }
                    DeleteDescendResult::None => DeleteDescendResult::None,
                }
            }
            NodeId::Leaf(leaf_id) => {
                let leaf = self.node_store.get_mut_leaf(leaf_id);
                match leaf.try_delete(k) {
                    LeafDeleteResult::Done(kv) => DeleteDescendResult::Done(kv),
                    LeafDeleteResult::None => DeleteDescendResult::None,
                    LeafDeleteResult::UnderSize(idx) => DeleteDescendResult::LeafUnderSize(idx),
                }
            }
        };

        r
    }

    fn try_rotate_right_for_inner_node(
        node_store: &mut S,
        parent_node_id: InnerNodeId,
        slot: usize,
    ) -> Option<()> {
        //     1    3  5
        //      ..2  4
        // rotate right
        //     1 2     5
        //     ..  3,4
        let node = node_store.get_inner(parent_node_id);
        let right_child_id = node.child_id_at(slot + 1).inner_id().unwrap();
        let left_child_id = node.child_id_at(slot).inner_id().unwrap();
        let slot_key = *node.key(slot);

        let prev_node = node_store.get_mut_inner(left_child_id);
        if prev_node.able_to_lend() {
            let (k, c) = prev_node.pop();
            let child = node_store.get_mut_inner(right_child_id);
            child.push_front(slot_key, c);

            let node = node_store.get_mut_inner(parent_node_id);
            node.set_key(slot, k);

            Some(())
        } else {
            None
        }
    }

    fn try_rotate_left_for_inner_node(
        node_store: &mut S,
        parent_node_id: InnerNodeId,
        slot: usize,
    ) -> Option<()> {
        //     1  3  5
        //       2  4..
        // rotate right
        //     1   4   5
        //      2,3  ..
        let node = node_store.get_inner(parent_node_id);
        let right_child_id = node.child_id_at(slot + 1).inner_id().unwrap();
        let left_child_id = node.child_id_at(slot).inner_id().unwrap();
        let slot_key = node.key(slot).clone();

        let right = node_store.get_mut_inner(right_child_id);
        if right.able_to_lend() {
            let (k, c) = right.pop_front();
            let left = node_store.get_mut_inner(left_child_id);
            left.push(slot_key, c);

            let node = node_store.get_mut_inner(parent_node_id);
            node.set_key(slot, k);

            Some(())
        } else {
            None
        }
    }

    fn merge_inner_node(
        node_store: &mut S,
        parent_id: InnerNodeId,
        slot: usize,
    ) -> InnerMergeResult {
        //     1  3  5
        //       2  4
        //  merge 3
        //     1        5
        //       2,3,4
        let node = node_store.get_inner(parent_id);
        debug_assert!(slot < node.size());

        let left_child_id = node.child_id_at(slot).inner_id().unwrap();
        let right_child_id = node.child_id_at(slot + 1).inner_id().unwrap();
        let slot_key = node.key(slot).clone();

        // merge right into left
        let right = node_store.take_inner(right_child_id);
        let left = node_store.get_mut_inner(left_child_id);

        debug_assert!(!right.able_to_lend());
        debug_assert!(!left.able_to_lend());

        left.merge_next(slot_key, &right);

        let node = node_store.get_mut_inner(parent_id);
        node.merge_child(slot)
    }

    fn try_rotate_right_for_leaf_node(
        node_store: &mut S,
        parent_id: InnerNodeId,
        slot: usize,
        delete_idx: usize,
    ) -> Option<(S::K, S::V)> {
        let parent = node_store.get_inner(parent_id);

        let left_id = parent.child_id_at(slot).leaf_id().unwrap();
        let right_id = parent.child_id_at(slot + 1).leaf_id().unwrap();

        let left = node_store.get_mut_leaf(left_id);
        if !left.able_to_lend() {
            return None;
        }

        let kv = left.pop();
        let new_slot_key = kv.0;
        let right = node_store.get_mut_leaf(right_id);
        let deleted = right.delete_with_push_front(delete_idx, kv);

        node_store
            .get_mut_inner(parent_id)
            .set_key(slot, new_slot_key);

        Some(deleted)
    }

    fn try_rotate_left_for_leaf_node(
        node_store: &mut S,
        parent_id: InnerNodeId,
        slot: usize,
        delete_idx: usize,
    ) -> Option<(S::K, S::V)> {
        let parent = node_store.get_inner(parent_id);

        let left_id = parent.child_id_at(slot).leaf_id().unwrap();
        let right_id = parent.child_id_at(slot + 1).leaf_id().unwrap();

        let right = node_store.get_mut_leaf(right_id);
        if !right.able_to_lend() {
            return None;
        }

        let kv = right.pop_front();
        let new_slot_key = right.data_at(0).0;
        let left = node_store.get_mut_leaf(left_id);
        let deleted = left.delete_with_push(delete_idx, kv);

        node_store
            .get_mut_inner(parent_id)
            .set_key(slot, new_slot_key);

        Some(deleted)
    }

    fn merge_leaf_node_left(
        node_store: &mut S,
        parent_id: InnerNodeId,
        slot: usize,
        delete_idx: usize,
    ) -> DeleteDescendResult<S::K, S::V> {
        let parent = node_store.get_inner(parent_id);
        let left_leaf_id = parent.child_id_at(slot).leaf_id().unwrap();
        let right_leaf_id = parent.child_id_at(slot + 1).leaf_id().unwrap();

        let mut right = node_store.take_leaf(right_leaf_id);
        let left = node_store.get_mut_leaf(left_leaf_id);
        let kv = left.merge_right_delete_first(delete_idx, &mut right);
        if let Some(next) = left.next() {
            node_store.get_mut_leaf(next).set_prev(Some(left_leaf_id));
        }

        let parent = node_store.get_mut_inner(parent_id);

        match parent.merge_child(slot) {
            InnerMergeResult::Done => DeleteDescendResult::Done(kv),
            InnerMergeResult::UnderSize => DeleteDescendResult::InnerUnderSize(kv),
        }
    }

    fn merge_leaf_node_with_right(
        node_store: &mut S,
        parent_id: InnerNodeId,
        slot: usize,
        delete_idx: usize,
    ) -> DeleteDescendResult<S::K, S::V> {
        let parent = node_store.get_inner(parent_id);
        let left_leaf_id = parent.child_id_at(slot).leaf_id().unwrap();
        let right_leaf_id = parent.child_id_at(slot + 1).leaf_id().unwrap();

        let right = node_store.take_leaf(right_leaf_id);
        let left = node_store.get_mut_leaf(left_leaf_id);
        let kv = left.delete_at(delete_idx);
        left.merge_right(&right);
        if let Some(next) = left.next() {
            node_store.get_mut_leaf(next).set_prev(Some(left_leaf_id));
        }

        let parent = node_store.get_mut_inner(parent_id);
        // the merge on inner, it could propagate
        match parent.merge_child(slot) {
            InnerMergeResult::Done => {
                return DeleteDescendResult::Done(kv);
            }
            InnerMergeResult::UnderSize => return DeleteDescendResult::InnerUnderSize(kv),
        }
    }

    /// get the first leaf_id if exists
    pub fn first_leaf(&self) -> Option<LeafNodeId> {
        match self.root? {
            NodeId::Inner(inner_id) => {
                let mut result = None;

                self.descend_visit_inner(inner_id, |inner_node| {
                    let first_child_id = inner_node.child_id_at(0);
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
        match self.root? {
            NodeId::Inner(inner_id) => {
                let mut result = None;

                self.descend_visit_inner(inner_id, |inner_node| {
                    let child_id = inner_node.child_id_at(inner_node.size());
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
    pub fn locate_leaf(&self, k: &S::K) -> Option<LeafNodeId> {
        // todo: check cache first?
        let leaf_id = match self.root? {
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
        node_id: InnerNodeId,
        mut f: impl FnMut(&S::InnerNode) -> Option<InnerNodeId>,
    ) -> Option<()> {
        let inner = self.node_store.get_inner(node_id);
        match f(inner) {
            None => {
                return None;
            }
            Some(id_to_visit) => self.descend_visit_inner(id_to_visit, f),
        }
    }

    /// Create an iterator on (&K, &V) pairs
    pub fn iter(&self) -> iterator::Iter<S> {
        iterator::Iter::new(self)
    }

    /// Create an cursor from first elem
    pub fn cursor_first(&self) -> Option<Cursor<S::K>> {
        Cursor::first(self).map(|c| c.0)
    }

    /// Create an cursor for k
    pub fn get_cursor(&self, k: &S::K) -> Option<Cursor<S::K>> {
        let node_id = self.root?;
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
        let (idx, _v) = leaf.locate_slot(k);
        Some(Cursor::new(*k, leaf_id, idx))
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
    /// Leaf under size
    LeafUnderSize(usize),
    /// Inner node under size, the index and node_id to remove
    InnerUnderSize((K, V)),
}

pub trait NodeStore: Clone {
    type K: Key;
    type V: Value;

    type InnerNode: INode<Self::K>;
    type LeafNode: LNode<Self::K, Self::V>;

    fn debug(&self);

    fn new_empty_inner(&mut self) -> InnerNodeId;
    fn add_inner(&mut self, node: Self::InnerNode) -> InnerNodeId;
    fn get_inner(&self, id: InnerNodeId) -> &Self::InnerNode;
    fn get_mut_inner(&mut self, id: InnerNodeId) -> &mut Self::InnerNode;
    fn take_inner(&mut self, id: InnerNodeId) -> Self::InnerNode;

    fn create_leaf(&mut self) -> (LeafNodeId, &mut Self::LeafNode);
    fn get_leaf(&self, id: LeafNodeId) -> &Self::LeafNode;
    fn try_get_leaf(&self, id: LeafNodeId) -> Option<&Self::LeafNode>;
    fn get_mut_leaf(&mut self, id: LeafNodeId) -> &mut Self::LeafNode;
    /// take the LeafNode
    fn take_leaf(&mut self, id: LeafNodeId) -> Self::LeafNode;
}

pub trait Key:
    std::fmt::Debug + Copy + Clone + Ord + PartialOrd + Eq + PartialEq + 'static
{
}
impl<T> Key for T where
    T: std::fmt::Debug + Copy + Clone + Ord + PartialOrd + Eq + PartialEq + 'static
{
}

pub trait Value: std::fmt::Debug + Copy + Clone {}
impl<T> Value for T where T: std::fmt::Debug + Copy + Clone {}

/// Inner node trait
pub trait INode<K: Key>: Clone + Default {
    /// Create a new inner node with `slot_keys` and `child_id`.
    fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) -> Self;

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
    fn child_id_at(&self, idx: usize) -> NodeId;

    /// Locate child index and `NodeId` for `k`
    fn locate_child(&self, k: &K) -> (usize, NodeId);

    /// Check if the node is full
    fn is_full(&self) -> bool;

    /// Check if the node is able to lend a key to its sibling
    fn able_to_lend(&self) -> bool;

    /// Insert a key and the right child id at `slot`
    fn insert_at(&mut self, slot: usize, key: K, right_child: NodeId);

    /// Split the node at `child_idx` and return the key to be inserted to parent
    fn split(&mut self, child_idx: usize, k: K, new_child_id: NodeId) -> (K, Self);

    /// Remove the last key and its right child id
    fn pop(&mut self) -> (K, NodeId);

    /// Remove the first key and its left child id
    fn pop_front(&mut self) -> (K, NodeId);

    /// Insert a key and its right child id at the end
    fn push(&mut self, k: K, child: NodeId);

    /// Insert a key and its left child id at the front
    fn push_front(&mut self, k: K, child: NodeId);

    /// Merge the key and its right child id at `slot` with its right sibling
    fn merge_next(&mut self, slot_key: K, right: &Self);

    /// Merge children at slot
    fn merge_child(&mut self, slot: usize) -> InnerMergeResult;

    /// Create an iterator over the keys
    fn iter_key<'a>(&'a self) -> Box<dyn Iterator<Item = &K> + 'a>;

    /// Create an iterator over the child ids
    fn iter_child<'a>(&'a self) -> Box<dyn Iterator<Item = NodeId> + 'a>;

    /// Set the data of the node
    fn set_data<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        &mut self,
        slot_keys: [K; N1],
        child_id: [I; C1],
    );
}

/// Leaf node trait
pub trait LNode<K: Key, V: Value>: Clone + Default {
    /// Returns size of the leaf
    fn len(&self) -> usize;

    fn prev(&self) -> Option<LeafNodeId>;
    fn set_prev(&mut self, id: Option<LeafNodeId>);
    fn next(&self) -> Option<LeafNodeId>;
    fn set_data<const N1: usize>(&mut self, data: [(K, V); N1]);
    fn data_at(&self, slot: usize) -> &(K, V);
    fn try_data_at(&self, idx: usize) -> Option<&(K, V)>;
    fn key_range(&self) -> (K, K);
    fn is_full(&self) -> bool;
    fn able_to_lend(&self) -> bool;
    fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<V>;
    fn split_new_leaf(
        &mut self,
        insert_idx: usize,
        item: (K, V),
        new_leaf_id: LeafNodeId,
        self_leaf_id: LeafNodeId,
    ) -> Self;
    fn locate_slot(&self, k: &K) -> (usize, Option<&(K, V)>);
    fn locate_slot_mut(&mut self, k: &K) -> (usize, Option<&mut V>);
    fn try_delete(&mut self, k: &K) -> LeafDeleteResult<K, V>;
    fn delete_at(&mut self, idx: usize) -> (K, V);
    fn delete_with_push_front(&mut self, idx: usize, item: (K, V)) -> (K, V);
    fn delete_with_push(&mut self, idx: usize, item: (K, V)) -> (K, V);
    fn merge_right_delete_first(&mut self, delete_idx_in_next: usize, right: &mut Self) -> (K, V);
    fn merge_right(&mut self, right: &Self);
    fn pop(&mut self) -> (K, V);
    fn pop_front(&mut self) -> (K, V);

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &(K, V)> + 'a>;
}

#[derive(Debug, Clone)]
pub struct NodeStoreVec<K: Key, V: Value, const IN: usize, const IC: usize, const LN: usize> {
    inner_nodes: Vec<InnerNode<K, IN, IC>>,
    leaf_nodes: Vec<LeafNode<K, V, LN>>,
    _ph: PhantomData<(K, V)>,
}

impl<K: Key, V: Value, const IN: usize, const IC: usize, const LN: usize>
    NodeStoreVec<K, V, IN, IC, LN>
{
    pub fn new() -> Self {
        Self {
            inner_nodes: Vec::with_capacity(32),
            leaf_nodes: Vec::with_capacity(128),
            _ph: Default::default(),
        }
    }

    pub fn print(&self) {
        for (idx, inner) in self.inner_nodes.iter().enumerate() {
            println!(
                "inner: {idx} s:{} key: {:?} child: {:?}",
                inner.size(),
                inner.iter_key().collect::<Vec<_>>(),
                inner.iter_child().collect::<Vec<_>>()
            );
        }

        for (idx, leaf) in self.leaf_nodes.iter().enumerate() {
            println!(
                "leaf: {idx} p:{:?} n:{:?} items:{:?}",
                leaf.prev()
                    .map(|l| l.as_usize().to_string())
                    .unwrap_or("-".to_string()),
                leaf.next()
                    .map(|l| l.as_usize().to_string())
                    .unwrap_or("-".to_string()),
                leaf.iter().map(|kv| kv.0).collect::<Vec<_>>()
            );
        }
    }
}

impl<K: Key, V: Value, const IN: usize, const IC: usize, const LN: usize> NodeStore
    for NodeStoreVec<K, V, IN, IC, LN>
{
    type K = K;
    type V = V;
    type InnerNode = InnerNode<K, IN, IC>;
    type LeafNode = LeafNode<K, V, LN>;

    fn new_empty_inner(&mut self) -> InnerNodeId {
        let id = InnerNodeId::from_usize(self.inner_nodes.len());
        let node = Self::InnerNode::default();
        self.inner_nodes.push(node);
        id
    }

    fn add_inner(&mut self, node: Self::InnerNode) -> InnerNodeId {
        let id = InnerNodeId::from_usize(self.inner_nodes.len());
        self.inner_nodes.push(node);
        id
    }

    fn get_inner(&self, id: InnerNodeId) -> &Self::InnerNode {
        &self.inner_nodes[id.as_usize()]
    }

    fn get_mut_inner(&mut self, id: InnerNodeId) -> &mut Self::InnerNode {
        &mut self.inner_nodes[id.as_usize()]
    }

    fn create_leaf(&mut self) -> (LeafNodeId, &mut Self::LeafNode) {
        let id = LeafNodeId::from_u32(self.leaf_nodes.len());
        let node = Self::LeafNode::default();
        self.leaf_nodes.push(node);
        (id, &mut self.leaf_nodes[id.as_usize()])
    }

    fn get_leaf(&self, id: LeafNodeId) -> &Self::LeafNode {
        &self.leaf_nodes[id.as_usize()]
    }

    fn try_get_leaf(&self, id: LeafNodeId) -> Option<&Self::LeafNode> {
        let leaf_node = self.leaf_nodes.get(id.as_usize())?;
        if leaf_node.len() == 0 {
            None
        } else {
            Some(leaf_node)
        }
    }

    fn get_mut_leaf(&mut self, id: LeafNodeId) -> &mut Self::LeafNode {
        &mut self.leaf_nodes[id.as_usize()]
    }

    fn debug(&self) {
        self.print()
    }

    fn take_leaf(&mut self, id: LeafNodeId) -> Self::LeafNode {
        std::mem::take(&mut self.leaf_nodes[id.as_usize()])
    }

    fn take_inner(&mut self, id: InnerNodeId) -> Self::InnerNode {
        std::mem::take(&mut self.inner_nodes[id.as_usize()])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_trip_100() {
        for _ in 0..100 {
            test_round_trip();
        }
    }

    #[test]
    fn test_round_trip() {
        use rand::seq::SliceRandom;

        let node_store = NodeStoreVec::<i64, i64, 8, 9, 6>::new();
        let mut tree = BPlusTree::new(node_store);

        let size: i64 = 50;

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        for i in keys {
            tree.insert(i, i % 13);
        }
        tree.node_store.debug();

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
        assert_eq!(first_leaf.data_at(0).0, 0);
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

        assert!(
            BPlusTree::try_rotate_right_for_inner_node(&mut node_store, parent_id, 1).is_some()
        );

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 13);
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.size(), 3);
            assert_eq!(
                child_1.iter_key().cloned().collect::<Vec<_>>(),
                vec![10, 11, 12]
            );
            assert_eq!(
                child_1.iter_child().collect::<Vec<_>>(),
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

            assert_eq!(
                child_2.iter_key().cloned().collect::<Vec<_>>(),
                vec![30, 40, 41]
            );
            assert_eq!(
                child_2.iter_child().collect::<Vec<_>>(),
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

        assert!(BPlusTree::try_rotate_left_for_inner_node(&mut node_store, parent_id, 1).is_some());

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 39);
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.size(), 4);
            assert_eq!(
                child_1.iter_key().cloned().collect::<Vec<_>>(),
                vec![10, 11, 12, 30]
            );
            assert_eq!(
                child_1.iter_child().collect::<Vec<_>>(),
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

            assert_eq!(
                child_2.iter_key().cloned().collect::<Vec<_>>(),
                vec![40, 41]
            );
            assert_eq!(
                child_2.iter_child().collect::<Vec<_>>(),
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

        let _result = BPlusTree::merge_inner_node(&mut node_store, parent_id, 1);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.size(), 2);
            assert_eq!(parent.key(1).clone(), 50);
            assert_eq!(
                parent.iter_child().collect::<Vec<_>>(),
                vec![child_0.into(), child_1.into(), child_3.into(),]
            );
        }

        {
            let child_1 = node_store.get_inner(child_1);
            assert_eq!(child_1.size(), 4);
            assert_eq!(
                child_1.iter_key().cloned().collect::<Vec<_>>(),
                vec![10, 11, 30, 40]
            );
            assert_eq!(
                child_1.iter_child().collect::<Vec<_>>(),
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
            let child_2 = node_store.get_inner(child_2);
            assert_eq!(child_2.size(), 0);
        }
    }

    #[test]
    fn test_rotate_right_for_leaf() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
        let parent_id = node_store.new_empty_inner();
        let (child_0, _) = node_store.create_leaf();
        let (child_1, _) = node_store.create_leaf();
        let (child_2, _) = node_store.create_leaf();
        let (child_3, _) = node_store.create_leaf();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);

        node_store
            .get_mut_leaf(child_1)
            .set_data([(10, 1), (11, 1), (12, 1), (13, 1)]);

        node_store
            .get_mut_leaf(child_2)
            .set_data([(40, 1), (41, 1)]);

        assert!(
            BPlusTree::try_rotate_right_for_leaf_node(&mut node_store, parent_id, 1, 0).is_some()
        );

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 13);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(
                child_1.iter().cloned().collect::<Vec<_>>(),
                vec![(10, 1), (11, 1), (12, 1)]
            );
        }

        {
            let child_2 = node_store.get_leaf(child_2);
            assert_eq!(child_2.len(), 2);

            assert_eq!(
                child_2.iter().cloned().collect::<Vec<_>>(),
                vec![(13, 1), (41, 1)]
            );
        }
    }

    #[test]
    fn test_rotate_left_for_leaf() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
        let parent_id = node_store.new_empty_inner();
        let (child_0, _) = node_store.create_leaf();
        let (child_1, _) = node_store.create_leaf();
        let (child_2, _) = node_store.create_leaf();
        let (child_3, _) = node_store.create_leaf();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);
        node_store
            .get_mut_leaf(child_1)
            .set_data([(10, 1), (11, 1), (12, 1)]);
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1), (41, 1)]);

        let result =
            BPlusTree::try_rotate_left_for_leaf_node(&mut node_store, parent_id, 1, 0).unwrap();
        assert_eq!(result.0, 10);

        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 40);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(
                child_1.iter().cloned().collect::<Vec<_>>(),
                vec![(11, 1), (12, 1), (39, 1),]
            );
        }

        {
            let child_2 = node_store.get_leaf(child_2);
            assert_eq!(child_2.len(), 2);

            assert_eq!(
                child_2.iter().cloned().collect::<Vec<_>>(),
                vec![(40, 1), (41, 1)]
            );
        }
    }

    #[test]
    fn test_merge_leaf_with_right() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
        let parent_id = node_store.new_empty_inner();
        let (child_0, _) = node_store.create_leaf();
        let (child_1, _) = node_store.create_leaf();
        let (child_2, _) = node_store.create_leaf();
        let (child_3, _) = node_store.create_leaf();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);
        node_store
            .get_mut_leaf(child_1)
            .set_data([(10, 1), (11, 1)]);
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1)]);

        let _result = BPlusTree::merge_leaf_node_with_right(&mut node_store, parent_id, 1, 0);
        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 50);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(
                child_1.iter().cloned().collect::<Vec<_>>(),
                vec![(11, 1), (39, 1), (40, 1),]
            );
        }

        {
            let child_2 = node_store.get_leaf(child_2);
            assert_eq!(child_2.len(), 0);
        }
    }

    #[test]
    fn test_merge_leaf_with_left() {
        let mut node_store = NodeStoreVec::<i64, i64, 4, 5, 4>::new();
        let parent_id = node_store.new_empty_inner();
        let (child_0, _) = node_store.create_leaf();
        let (child_1, _) = node_store.create_leaf();
        let (child_2, _) = node_store.create_leaf();
        let (child_3, _) = node_store.create_leaf();

        node_store
            .get_mut_inner(parent_id)
            .set_data([10, 30, 50], [child_0, child_1, child_2, child_3]);
        node_store
            .get_mut_leaf(child_1)
            .set_data([(10, 1), (11, 1)]);
        node_store
            .get_mut_leaf(child_2)
            .set_data([(39, 1), (40, 1)]);

        let _result = BPlusTree::merge_leaf_node_left(&mut node_store, parent_id, 1, 0);
        {
            let parent = node_store.get_inner(parent_id);
            assert_eq!(parent.key(1).clone(), 50);
        }

        {
            let child_1 = node_store.get_leaf(child_1);
            assert_eq!(child_1.len(), 3);
            assert_eq!(
                child_1.iter().cloned().collect::<Vec<_>>(),
                vec![(10, 1), (11, 1), (40, 1),]
            );
        }

        {
            let child_2 = node_store.get_leaf(child_2);
            assert_eq!(child_2.len(), 0);
        }
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

        let cursor = tree.get_cursor(&10).unwrap();
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
    }

    pub fn create_test_tree<const N: usize>(
    ) -> (BPlusTree<NodeStoreVec<i64, i64, 8, 9, 6>>, Vec<i64>) {
        use rand::seq::SliceRandom;

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
}

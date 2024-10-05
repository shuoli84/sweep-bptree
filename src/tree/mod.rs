mod inner_node;
mod slice_utils;
use std::{borrow::Borrow, mem::ManuallyDrop};

mod consts;

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

pub mod visit;

mod bulk_load;
pub use crate::augment::*;

use self::entry_ref::{EntryRef, VisitStack};
mod entry_ref;

mod tree_remove;

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
/// // create a node_store with `u64` as key, `(f64, f64)` as value
/// let mut node_store = NodeStoreVec::<u64, (f64, f64)>::new();
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
/// let mut node_store = NodeStoreVec::<u64, (f64, f64)>::new();
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
    root_augmentation: S::Augmentation,
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
            root_augmentation: S::Augmentation::default(),
            node_store: ManuallyDrop::new(node_store),
            len: 0,

            st: Statistic::default(),
        }
    }

    /// Create a new `BPlusTree` from existing parts
    fn new_from_parts(node_store: S, root: NodeId, len: usize) -> Self {
        let augmentation = if len > 0 {
            Self::new_augmentation_for_id(&node_store, root)
        } else {
            S::Augmentation::default()
        };

        let me = Self {
            root,
            root_augmentation: augmentation,
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

    /// Returns a reference to root augment
    pub fn root_augmentation(&self) -> &S::Augmentation {
        &self.root_augmentation
    }

    /// Insert a new key-value pair into the tree.
    pub fn insert(&mut self, k: S::K, v: S::V) -> Option<S::V> {
        let node_id = self.root;

        let result = match self.descend_insert(node_id, k, v) {
            DescendInsertResult::Inserted => {
                self.root_augmentation = Self::new_augmentation_for_id(&self.node_store, node_id);
                None
            }
            DescendInsertResult::Updated(prev_v) => Some(prev_v),
            DescendInsertResult::Split(k, new_child_id) => {
                let prev_root_augmentation =
                    Self::new_augmentation_for_id(&self.node_store, node_id);
                let new_augmentation =
                    Self::new_augmentation_for_id(&self.node_store, new_child_id);

                let new_root = InnerNode::<S::K, S::Augmentation>::new(
                    [k],
                    [node_id, new_child_id],
                    [prev_root_augmentation, new_augmentation],
                );
                let new_root_augmentation =
                    S::Augmentation::from_inner(new_root.keys(), new_root.augmentations());

                let new_root_id = self.node_store.add_inner(new_root);
                self.root = new_root_id.into();
                self.root_augmentation = new_root_augmentation;
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

    fn descend_insert(
        &mut self,
        node_id: NodeId,
        k: S::K,
        v: S::V,
    ) -> DescendInsertResult<S::K, S::V> {
        match node_id {
            NodeId::Inner(id) => self.insert_inner(id, k, v),
            NodeId::Leaf(leaf_id) => self.insert_leaf(leaf_id, k, v),
        }
    }

    fn insert_inner(
        &mut self,
        mut id: InnerNodeId,
        k: S::K,
        v: S::V,
    ) -> DescendInsertResult<S::K, S::V> {
        let mut stack = VisitStack::new();
        let mut r = loop {
            let node = self.node_store.get_inner(id);
            let (child_idx, child_id) = node.locate_child(&k);
            stack.push(id, child_idx, child_id);

            match child_id {
                NodeId::Inner(child_inner) => {
                    id = child_inner;
                    continue;
                }
                NodeId::Leaf(leaf_id) => break self.insert_leaf(leaf_id, k, v),
            }
        };

        loop {
            // ascend process. Need to process split and update augment
            match stack.pop() {
                Some((id, child_idx, child_id)) => match r {
                    DescendInsertResult::Split(key, right_child) => {
                        let right_child_augmentation =
                            Self::new_augmentation_for_id(&self.node_store, right_child);
                        let child_augmentation =
                            Self::new_augmentation_for_id(&self.node_store, child_id);

                        let inner_node = self.node_store.get_mut_inner(id);
                        // it's easier to update augment here, the split logic handles augmentations split
                        // too.
                        inner_node.set_augmentation(child_idx, child_augmentation);

                        if !inner_node.is_full() {
                            let slot = child_idx;
                            inner_node.insert_at(slot, key, right_child, right_child_augmentation);
                            r = DescendInsertResult::Inserted;
                        } else {
                            let (prompt_k, new_node) = inner_node.split(
                                child_idx,
                                key,
                                right_child,
                                right_child_augmentation,
                            );
                            let new_node_id = self.node_store.add_inner(new_node);
                            r = DescendInsertResult::Split(prompt_k, NodeId::Inner(new_node_id));
                        }
                    }
                    DescendInsertResult::Inserted => {
                        let child_augmentation =
                            Self::new_augmentation_for_id(&self.node_store, child_id);
                        let inner_node = self.node_store.get_mut_inner(id);
                        inner_node.set_augmentation(child_idx, child_augmentation);

                        continue;
                    }
                    DescendInsertResult::Updated(_) => {
                        // the key didn't change, so does the augment
                        continue;
                    }
                },
                None => return r,
            }
        }
    }

    fn new_augmentation_for_id(node_store: &S, id: NodeId) -> S::Augmentation {
        match id {
            NodeId::Inner(inner) => {
                let inner = node_store.get_inner(inner);
                S::Augmentation::from_inner(inner.keys(), inner.augmentations())
            }
            NodeId::Leaf(leaf) => {
                let leaf = node_store.get_leaf(leaf);
                S::Augmentation::from_leaf(leaf.keys())
            }
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
            LeafUpsertResult::IsFull(idx, k, v) => {
                let right_id = self.node_store.reserve_leaf();

                let l_leaf = self.node_store.get_mut_leaf(id);
                let r_leaf = l_leaf.split_new_leaf(idx, (k, v), right_id, id);
                let slot_key: S::K = r_leaf.data_at(0).0.clone();

                // fix r_leaf's next's prev
                if let Some(next) = r_leaf.next() {
                    self.node_store.get_mut_leaf(next).set_prev(Some(right_id));
                }
                self.node_store.assign_leaf(right_id, r_leaf);

                let updated_id = if idx >= S::leaf_n() as usize / 2 {
                    right_id
                } else {
                    id
                };
                self.node_store.cache_leaf(updated_id);
                DescendInsertResult::Split(slot_key, NodeId::Leaf(right_id))
            }
        }
    }

    /// Get reference to value identified by key.
    pub fn get<Q: ?Sized + Ord>(&self, k: &Q) -> Option<&S::V>
    where
        S::K: Borrow<Q>,
    {
        if let Some(leaf_id) = self.node_store.try_cache(k) {
            // cache hit
            return self.find_in_leaf(leaf_id, k);
        }

        self.find_descend(self.root, k)
    }

    /// Get mutable reference to value identified by key.
    pub fn get_mut<Q: ?Sized + Ord>(&mut self, k: &Q) -> Option<&mut S::V>
    where
        S::K: Borrow<Q>,
    {
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

    /// Returns first key-value pair in the map.
    pub fn first(&self) -> Option<(&S::K, &S::V)> {
        if self.is_empty() {
            return None;
        }

        let mut node_id = self.root;
        loop {
            match node_id {
                NodeId::Inner(inner_id) => {
                    let inner_node = self.node_store.get_inner(inner_id);
                    node_id = inner_node.child_id(0);
                    continue;
                }
                NodeId::Leaf(leaf_id) => {
                    let leaf_node = self.node_store.get_leaf(leaf_id);
                    return Some(leaf_node.data_at(0));
                }
            }
        }
    }

    /// Returns last key-value pair in the map.
    pub fn last(&self) -> Option<(&S::K, &S::V)> {
        if self.is_empty() {
            return None;
        }

        let mut node_id = self.root;
        loop {
            match node_id {
                NodeId::Inner(inner_id) => {
                    let inner_node = self.node_store.get_inner(inner_id);
                    node_id = inner_node.child_id(inner_node.len());
                    continue;
                }
                NodeId::Leaf(leaf_id) => {
                    let leaf_node = self.node_store.get_leaf(leaf_id);
                    return Some(leaf_node.data_at(leaf_node.len() - 1));
                }
            }
        }
    }

    fn find_descend<Q: ?Sized + Ord>(&self, mut node_id: NodeId, k: &Q) -> Option<&S::V>
    where
        S::K: Borrow<Q>,
    {
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

    fn find_in_leaf<Q: ?Sized + Ord>(&self, leaf_id: LeafNodeId, k: &Q) -> Option<&S::V>
    where
        S::K: Borrow<Q>,
    {
        let leaf_node = self.node_store.get_leaf(leaf_id);
        let (_, kv) = leaf_node.locate_slot_with_value(k);
        kv
    }

    fn find_descend_mut<Q: ?Sized + Ord>(&mut self, node_id: NodeId, k: &Q) -> Option<&mut S::V>
    where
        S::K: Borrow<Q>,
    {
        match node_id {
            NodeId::Inner(inner_id) => {
                let inner_node = self.node_store.get_inner(inner_id);
                let (_, child_id) = inner_node.locate_child(k);
                self.find_descend_mut(child_id, k)
            }
            NodeId::Leaf(leaf_id) => self.find_in_leaf_mut_and_cache_it(leaf_id, k),
        }
    }

    fn find_in_leaf_mut<Q: ?Sized + Ord>(&mut self, leaf_id: LeafNodeId, k: &Q) -> Option<&mut S::V>
    where
        S::K: Borrow<Q>,
    {
        let leaf_node = self.node_store.get_mut_leaf(leaf_id);
        let (_, v) = leaf_node.locate_slot_mut(k);
        v
    }

    fn find_in_leaf_mut_and_cache_it<Q: ?Sized + Ord>(
        &mut self,
        leaf_id: LeafNodeId,
        k: &Q,
    ) -> Option<&mut S::V>
    where
        S::K: Borrow<Q>,
    {
        self.node_store.cache_leaf(leaf_id);
        let leaf_node = self.node_store.get_mut_leaf(leaf_id);
        let (_, kv) = leaf_node.locate_slot_mut(k);
        kv
    }

    /// Find the key in leaf, and cache leaf, this method only called when
    /// cache miss
    fn find_in_leaf_and_cache_it<Q: ?Sized + Ord>(
        &self,
        leaf_id: LeafNodeId,
        k: &Q,
    ) -> Option<&S::V>
    where
        S::K: Borrow<Q>,
    {
        self.node_store.cache_leaf(leaf_id);
        let leaf = self.node_store.get_leaf(leaf_id);
        let (_, v) = leaf.locate_slot_with_value(k);
        v
    }

    /// delete element identified by K
    pub fn remove<Q>(&mut self, k: &Q) -> Option<S::V>
    where
        Q: ?Sized + Ord,
        S::K: Borrow<Q>,
    {
        self.remove_impl(k).map(|kv| kv.1)
    }

    fn key_to_ref<Q>(&self, k: &Q) -> Option<EntryRef<&Self>>
    where
        Q: ?Sized + Ord,
        S::K: Borrow<Q>,
    {
        let mut inner_stack = VisitStack::new();
        let mut node_id = self.root;
        loop {
            match node_id {
                NodeId::Inner(inner_id) => {
                    let inner_node = self.node_store.get_inner(inner_id);
                    let (child_offset, child_id) = inner_node.locate_child(k);
                    inner_stack.push(inner_id, child_offset, child_id);

                    node_id = child_id;
                }
                NodeId::Leaf(leaf_id) => {
                    let leaf = self.node_store.get_leaf(leaf_id);

                    match leaf.locate_slot(k) {
                        Ok(idx) => return Some(EntryRef::new(self, inner_stack, leaf_id, idx)),
                        Err(_) => return None,
                    };
                }
            }
        }
    }

    /// get the first leaf_id if exists
    pub(crate) fn first_leaf(&self) -> Option<LeafNodeId> {
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
    pub(crate) fn last_leaf(&self) -> Option<LeafNodeId> {
        match self.root {
            NodeId::Inner(inner_id) => {
                let mut result = None;

                self.descend_visit_inner(inner_id, |inner_node| {
                    let child_id = inner_node.child_id(inner_node.len());
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
        mut f: impl FnMut(&InnerNode<S::K, S::Augmentation>) -> Option<InnerNodeId>,
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

    /// Create a `Cursor` from first elem if exists
    ///
    pub fn cursor_first(&self) -> Option<Cursor<S::K>> {
        Cursor::first(self).map(|c| c.0)
    }

    /// Create a cursor and value for k if k exists.
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
        Some((Cursor::new(k.clone(), leaf_id, idx), v))
    }

    /// Clear the tree
    pub fn clear(&mut self) {
        // todo: should we keep the node_store's capacity?
        std::mem::drop(std::mem::replace(self, Self::new(S::default())));
    }

    /// get by augment
    fn get_ref_by_augmentation<Q>(&self, mut query: Q) -> Option<EntryRef<&Self>>
    where
        S::Augmentation: SearchAugmentation<S::K, S::V, Query = Q>,
    {
        let mut node_id = self.root;
        let mut stack = VisitStack::new();

        loop {
            match node_id {
                NodeId::Inner(inner_id) => {
                    let inner = self.node_store.get_inner(inner_id);
                    let (offset, new_query) =
                        <S::Augmentation as SearchAugmentation<_, _>>::locate_in_inner(
                            query,
                            inner.keys(),
                            inner.augmentations(),
                        )?;
                    node_id = inner.child_id(offset);

                    stack.push(inner_id, offset, node_id);
                    query = new_query;
                }
                NodeId::Leaf(leaf_id) => {
                    let leaf = self.node_store.get_leaf(leaf_id);
                    let slot = <S::Augmentation as SearchAugmentation<_, _>>::locate_in_leaf(
                        query,
                        leaf.keys(),
                    )?;

                    return Some(EntryRef::new(self, stack, leaf_id, slot));
                }
            }
        }
    }

    /// get by augment
    pub fn get_by_augmentation<Q>(&self, query: Q) -> Option<(&S::K, &S::V)>
    where
        S::Augmentation: SearchAugmentation<S::K, S::V, Query = Q>,
    {
        let entry_ref = self.get_ref_by_augmentation(query)?;
        Self::get_by_ref(entry_ref)
    }

    /// get mut reference to value by augmentation Query
    pub fn get_mut_by_augmentation<Q>(&mut self, query: Q) -> Option<&mut S::V>
    where
        S::Augmentation: SearchAugmentation<S::K, S::V, Query = Q>,
    {
        let entry_ref = self.get_ref_by_augmentation(query)?;
        Some(Self::get_mut_by_ref(
            entry_ref.into_detached().into_ref(self),
        ))
    }

    /// Get rank for augment
    pub fn rank_by_augmentation<R>(&self, k: &S::K) -> Result<R, R>
    where
        S::Augmentation: RankAugmentation<S::K, S::V, Rank = R>,
    {
        let mut node_id = self.root;
        let mut rank = <S::Augmentation as RankAugmentation<S::K, S::V>>::initial_value();

        loop {
            match node_id {
                NodeId::Inner(inner_id) => {
                    let inner = self.node_store.get_inner(inner_id);
                    let (child_idx, child_id) = inner.locate_child(k);
                    node_id = child_id;
                    let augmentations = &inner.augmentations()[0..child_idx];
                    rank = <S::Augmentation as RankAugmentation<S::K, S::V>>::fold_inner(
                        k,
                        rank,
                        augmentations,
                    );
                }
                NodeId::Leaf(leaf_id) => {
                    let leaf = self.node_store.get_leaf(leaf_id);
                    let slot = leaf.locate_slot(k);
                    return <S::Augmentation as RankAugmentation<_, _>>::fold_leaf(
                        k,
                        rank,
                        slot,
                        leaf.keys(),
                    );
                }
            }
        }
    }

    /// remove by augment
    pub fn remove_by_augmentation<Q>(&mut self, query: Q) -> Option<(S::K, S::V)>
    where
        S::Augmentation: SearchAugmentation<S::K, S::V, Query = Q>,
    {
        let entry_ref = self.get_ref_by_augmentation(query)?;
        Self::remove_by_ref(entry_ref.into_detached().into_ref(self))
    }

    /// Get the (&K, &V) pair for `EntryRef`
    fn get_by_ref(entry_ref: EntryRef<&Self>) -> Option<(&S::K, &S::V)> {
        let leaf = entry_ref.tree.node_store.get_leaf(entry_ref.leaf_id);
        let slot = entry_ref.offset;
        Some(leaf.data_at(slot))
    }

    /// Get the &mut V for reference
    fn get_mut_by_ref(entry_ref: EntryRef<&mut Self>) -> &mut S::V {
        let EntryRef {
            tree,
            leaf_id,
            offset,
            ..
        } = entry_ref;

        let leaf = tree.node_store.get_mut_leaf(leaf_id);
        let slot = offset;
        leaf.value_at_mut(slot)
    }

    #[cfg(test)]
    fn validate(&self) {
        let Some(mut leaf_id) = self.first_leaf() else {
            return;
        };
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

impl<S: NodeStore> IntoIterator for BPlusTree<S> {
    type Item = (S::K, S::V);
    type IntoIter = IntoIter<S>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
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

enum DescendInsertResult<K, V> {
    /// Update existing value, V is the previous value
    Updated(V),
    /// Inserted, and not split
    Inserted,
    /// need to split
    Split(K, NodeId),
}

/// NodeStore is the node storage for tree, responsible for
/// define node types, manage node memory, and provide node access
pub trait NodeStore: Default {
    /// Key type for the tree
    type K: Key;
    /// Value type for the tree
    type V;

    /// The Augmentation type
    type Augmentation: Augmentation<Self::K, Self::V>;

    /// Get the max number of keys inner node can hold
    fn inner_n() -> u16;
    /// Get the max number of elements leaf node can hold
    fn leaf_n() -> u16;

    /// Create an empty inner node and returns its id
    #[cfg(test)]
    fn new_empty_inner(&mut self) -> InnerNodeId;

    /// Add the inner node to the store and returns its id
    fn add_inner(&mut self, node: Box<InnerNode<Self::K, Self::Augmentation>>) -> InnerNodeId;

    /// Get the inner node
    /// # Panics
    /// if id is invalid or the node is already removed, panic
    fn get_inner(&self, id: InnerNodeId) -> &InnerNode<Self::K, Self::Augmentation>;

    /// Get the inner node
    /// if id is invalid or the node already removed, remove None
    fn try_get_inner(&self, id: InnerNodeId) -> Option<&InnerNode<Self::K, Self::Augmentation>>;

    /// Get a mut reference to the `InnerNode`
    fn get_mut_inner(&mut self, id: InnerNodeId) -> &mut InnerNode<Self::K, Self::Augmentation>;

    /// Get a mut pointer to inner node.
    ///
    /// # Safety
    /// User must ensure there is non shared reference to the node co-exists
    unsafe fn get_mut_inner_ptr(
        &mut self,
        id: InnerNodeId,
    ) -> *mut InnerNode<Self::K, Self::Augmentation>;

    /// Take the inner node out of the store
    fn take_inner(&mut self, id: InnerNodeId) -> Box<InnerNode<Self::K, Self::Augmentation>>;

    /// Put back the inner node
    fn put_back_inner(
        &mut self,
        id: InnerNodeId,
        node: Box<InnerNode<Self::K, Self::Augmentation>>,
    );

    /// Create a new empty leaf node and returns its id
    fn new_empty_leaf(&mut self) -> (LeafNodeId, &mut LeafNode<Self::K, Self::V>);

    /// Reserve a leaf node, it must be assigned later
    fn reserve_leaf(&mut self) -> LeafNodeId;

    /// Get a refernce to leaf node
    /// Panics if id is invalid or the node is taken
    fn get_leaf(&self, id: LeafNodeId) -> &LeafNode<Self::K, Self::V>;

    /// Get a reference to leaf node
    /// Returns None if id is invalid or the node is taken
    fn try_get_leaf(&self, id: LeafNodeId) -> Option<&LeafNode<Self::K, Self::V>>;

    /// Get a mut reference to leaf node
    /// Panics if id is invalid or the node is taken
    fn get_mut_leaf(&mut self, id: LeafNodeId) -> &mut LeafNode<Self::K, Self::V>;

    /// Take the leaf out of store
    fn take_leaf(&mut self, id: LeafNodeId) -> Box<LeafNode<Self::K, Self::V>>;

    /// Assign the leaf to the id, the id must exists
    fn assign_leaf(&mut self, id: LeafNodeId, leaf: Box<LeafNode<Self::K, Self::V>>);

    /// cache leaf
    fn cache_leaf(&self, leaf_id: LeafNodeId);

    /// try cache for k
    fn try_cache<Q>(&self, k: &Q) -> Option<LeafNodeId>
    where
        Q: ?Sized + Ord,
        Self::K: Borrow<Q>;

    #[cfg(test)]
    fn debug(&self)
    where
        Self::K: std::fmt::Debug,
        Self::V: std::fmt::Debug + Clone,
        Self::Augmentation: std::fmt::Debug;
}

/// Key trait
/// `Clone` is required since Inner Node may dup the key.
pub trait Key: Clone + Ord {}

impl<T> Key for T where T: Clone + Ord {}

/// ensure NodeStoreVec is send for send v
fn _ensure_send<V: Send>() {
    fn _assert_send<T: Send>() {}
    _assert_send::<BPlusTree<NodeStoreVec<u64, V>>>();
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use rand::seq::SliceRandom;

    use crate::augment::count::Count;

    use super::*;

    #[test]
    fn test_round_trip_one() {
        round_trip_one();
    }

    fn round_trip_one() {
        let node_store = NodeStoreVec::<i64, i64, Count>::new();
        let mut tree = BPlusTree::new(node_store);

        let size: i64 = 100000;

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        for i in keys {
            tree.insert(i, i % 13);
            assert_eq!(tree.root_augmentation.count(), tree.len());
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
            assert_eq!(tree.root_augmentation.count(), tree.len());
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
        let node_store = NodeStoreVec::<i64, i64>::new();
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
    fn test_get_mut() {
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

    pub fn create_test_tree<const N: usize>() -> (BPlusTree<NodeStoreVec<i64, i64>>, Vec<i64>) {
        let node_store = NodeStoreVec::<i64, i64>::new();
        let mut tree = BPlusTree::new(node_store);

        let size: i64 = N as i64;

        let mut keys = (0..size).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        for i in keys.iter() {
            tree.insert(*i, i % 13);
        }

        assert_eq!(tree.len(), N);

        (tree, keys)
    }

    struct TestKey {
        key: i32,
        counter: Rc<std::sync::atomic::AtomicU64>,
        panic_flag: Rc<std::sync::atomic::AtomicU64>,
    }

    impl Ord for TestKey {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.key.cmp(&other.key)
        }
    }

    impl PartialOrd for TestKey {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.key.partial_cmp(&other.key)
        }
    }

    impl PartialEq for TestKey {
        fn eq(&self, other: &Self) -> bool {
            self.key == other.key
        }
    }

    impl Eq for TestKey {}

    impl Clone for TestKey {
        fn clone(&self) -> Self {
            self.counter
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Self {
                key: self.key,
                panic_flag: self.panic_flag.clone(),
                counter: self.counter.clone(),
            }
        }
    }

    impl TestKey {
        fn new(
            key: i32,
            counter: Rc<std::sync::atomic::AtomicU64>,
            panic_flag: Rc<std::sync::atomic::AtomicU64>,
        ) -> Self {
            counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Self {
                key,
                counter,
                panic_flag,
            }
        }
    }

    impl Drop for TestKey {
        fn drop(&mut self) {
            self.panic_flag
                .fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
            self.counter
                .fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
        }
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
        let count: u64 = 16000;
        // test drop
        let node_store = NodeStoreVec::<TestKey, TestValue>::new();
        let mut tree = BPlusTree::new(node_store);
        let drop_counter = Rc::new(std::sync::atomic::AtomicU64::new(0));
        let key_counter = Rc::new(std::sync::atomic::AtomicU64::new(0));
        let panic_flag = Rc::new(std::sync::atomic::AtomicU64::new(0));

        macro_rules! get {
            ($id: ident) => {
                $id.load(std::sync::atomic::Ordering::Relaxed)
            };
        }

        for i in 0..count {
            tree.insert(
                TestKey::new(i as i32, key_counter.clone(), panic_flag.clone()),
                TestValue::new(drop_counter.clone()),
            );
        }

        {
            let key_count_inserted = key_counter.load(std::sync::atomic::Ordering::Relaxed);
            let another_tree = tree.clone();
            let key_count_cloned = get!(key_counter);
            assert_eq!(key_count_cloned, key_count_inserted * 2);
            drop(another_tree);

            let key_count_drop_clone = key_counter.load(std::sync::atomic::Ordering::Relaxed);
            assert_eq!(key_count_drop_clone, key_count_inserted);
        }

        {
            let keys = tree.iter().map(|(k, _v)| k.clone()).collect::<Vec<_>>();
            for k in keys {
                panic_flag.store(1, std::sync::atomic::Ordering::Relaxed);

                let prev = get!(key_counter);
                assert!(tree.remove(&k).is_some());
                let delta = prev - get!(key_counter);
                if delta > 3 {
                    panic!();
                }

                // one for k
                panic_flag.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }

        drop(tree);

        assert_eq!(
            drop_counter.load(std::sync::atomic::Ordering::Relaxed),
            count * 2,
        );
        assert_eq!(key_counter.load(std::sync::atomic::Ordering::Relaxed), 0);
    }
}

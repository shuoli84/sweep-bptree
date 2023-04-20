use super::*;
use std::alloc::alloc;
use std::slice::SliceIndex;
use std::{
    alloc::Layout,
    mem::{self, MaybeUninit},
};

const N: usize = 64;
const C: usize = N + 1;

/// Tree's inner node, it contains a list of keys and a list of child node id
/// `N` is the maximum number of keys in a node
/// `C` is the maximum child node id in a node
#[derive(Debug)]
pub struct InnerNode<K: Key, A: Argumentation<K>> {
    size: u16,

    slot_key: [MaybeUninit<K>; N],
    child_id: [MaybeUninit<NodeId>; C],
    /// The Argument for each Child
    arguments: [MaybeUninit<A>; C],
}

impl<K: Key, A: Argumentation<K>> Drop for InnerNode<K, A> {
    fn drop(&mut self) {
        // Satefy: The keys in range ..self.len() is initialized
        unsafe {
            for k in self.key_area_mut(..self.len()) {
                k.assume_init_drop();
            }

            for m in self.arguments_area_mut(..self.len() + 1) {
                m.assume_init_drop();
            }
        }
    }
}

impl<K: Key, A: Argumentation<K>> Clone for InnerNode<K, A> {
    fn clone(&self) -> Self {
        // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
        let mut new_key = unsafe { MaybeUninit::<[MaybeUninit<K>; N]>::uninit().assume_init() };

        for i in 0..self.len() {
            unsafe {
                *new_key.get_unchecked_mut(i) =
                    MaybeUninit::new(self.key_area(i).assume_init_ref().clone());
            };
        }

        // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
        let mut new_arguments =
            unsafe { MaybeUninit::<[MaybeUninit<A>; C]>::uninit().assume_init() };

        for i in 0..self.len() + 1 {
            unsafe {
                *new_arguments.get_unchecked_mut(i) =
                    MaybeUninit::new(self.argument_area(i).assume_init_ref().clone());
            };
        }

        Self {
            size: self.size.clone(),
            slot_key: new_key,
            child_id: self.child_id.clone(),
            arguments: new_arguments,
        }
    }
}

impl<K: Key, A: Argumentation<K>> InnerNode<K, A> {
    /// Size of keys in inner node
    pub fn len(&self) -> usize {
        self.size as usize
    }

    /// Max key capacity
    pub const fn max_capacity() -> u16 {
        N as u16
    }

    /// The size of the origin node after split
    pub const fn split_origin_size() -> usize {
        N / 2
    }

    /// The size of the new node after split
    pub const fn split_new_size() -> usize {
        N - Self::split_origin_size()
    }

    /// Minimum size of a node, if the size is less than this, then the node need to be merged
    const fn minimum_size() -> usize {
        if N / 4 == 0 {
            1
        } else {
            N / 4
        }
    }

    /// whether this node is able to lend a key to its sibling
    pub fn able_to_lend(&self) -> bool {
        self.size > Self::minimum_size() as u16
    }

    /// whether this node is full, if yes, then the next insert need to split
    pub fn is_full(&self) -> bool {
        self.size == N as u16
    }

    /// Create an empty inner node
    pub(crate) fn empty() -> Box<Self> {
        // not sure how to do a constrain in compile time, just put a debug assert here.
        debug_assert!(C == N + 1);

        let layout = Layout::new::<mem::MaybeUninit<Self>>();
        let ptr: *mut Self = unsafe { alloc(layout).cast() };
        let mut this = unsafe { Box::from_raw(ptr) };
        this.size = 0;
        this
    }

    /// Create a new inner node from keys and childs
    pub(crate) fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
        arguments: [A; C1],
    ) -> Box<Self> {
        // not sure how to do a constrain in compile time, just put a debug assert here.
        debug_assert!(C == N + 1);
        Self::new_from_iter(slot_keys, child_id.map(|c| c.into()), arguments)
    }

    /// Create a new inner node from keys and childs iterator
    fn new_from_iter(
        keys: impl IntoIterator<Item = K>,
        childs: impl IntoIterator<Item = NodeId>,
        arguments: impl IntoIterator<Item = A>,
    ) -> Box<Self> {
        let mut node = Self::empty();

        let keys = keys.into_iter();
        let childs = childs.into_iter();
        let arguments = arguments.into_iter();

        let mut key_size = 0;
        for (idx, k) in keys.enumerate() {
            node.slot_key[idx] = MaybeUninit::new(k);
            key_size += 1;
        }

        let mut child_size = 0;
        for (idx, c) in childs.enumerate() {
            node.child_id[idx] = MaybeUninit::new(c);
            child_size += 1;
        }
        for (idx, m) in arguments.enumerate() {
            node.arguments[idx] = MaybeUninit::new(m);
        }

        assert!(key_size + 1 == child_size);
        node.size = key_size;

        node
    }

    fn keys(&self) -> &[K] {
        unsafe {
            {
                let slice: &[MaybeUninit<K>] =
                    self.slot_key.get_unchecked(..usize::from(self.size));
                // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees that
                // `slice` is initialized, and `MaybeUninit` is guaranteed to have the same layout as `T`.
                // The pointer obtained is valid since it refers to memory owned by `slice` which is a
                // reference and thus guaranteed to be valid for reads.
                &*(slice as *const [MaybeUninit<K>] as *const [K])
            }
        }
    }

    fn arguments(&self) -> &[A] {
        unsafe {
            {
                let slice: &[MaybeUninit<A>] =
                    self.arguments.get_unchecked(..usize::from(self.size + 1));
                // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees that
                // `slice` is initialized, and `MaybeUninit` is guaranteed to have the same layout as `T`.
                // The pointer obtained is valid since it refers to memory owned by `slice` which is a
                // reference and thus guaranteed to be valid for reads.
                &*(slice as *const [MaybeUninit<A>] as *const [A])
            }
        }
    }

    /// Update the argument at index. The previous argument will be dropped.
    fn set_argument(&mut self, idx: usize, a: A) {
        // Safety: the caller must ensure that the index is valid
        unsafe {
            std::mem::replace(self.arguments_area_mut(idx), MaybeUninit::new(a)).assume_init_drop()
        }
    }

    /// returns the child index for k
    #[inline]
    pub(crate) fn locate_child<Q: ?Sized>(&self, k: &Q) -> (usize, NodeId)
    where
        K: std::borrow::Borrow<Q>,
        Q: Ord,
    {
        match self.keys().binary_search_by_key(&k, |f| f.borrow()) {
            Err(idx) => {
                // the idx is the place where a matching element could be inserted while maintaining
                // sorted order. go to left child
                (idx, self.child_id(idx))
            }
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (idx + 1, self.child_id(idx + 1))
            }
        }
    }

    /// Insert `key` and its `right_child` to `slot`
    pub(crate) fn insert_at(
        &mut self,
        slot: usize,
        key: K,
        right_child: NodeId,
        right_child_argument: A,
    ) {
        debug_assert!(slot <= self.len());
        debug_assert!(!self.is_full());

        let new_size = self.size as usize + 1;
        let new_child_size = self.size as usize + 2;

        // SAFETY: we have checked the slot is valid
        //         this method is called only when the node is not full
        unsafe {
            utils::slice_insert(self.key_area_mut(..new_size), slot, key);
            utils::slice_insert(self.child_area_mut(..new_child_size), slot + 1, right_child);
            utils::slice_insert(
                self.arguments_area_mut(..new_child_size),
                slot + 1,
                right_child_argument,
            );
        }

        self.size += 1;
    }

    /// Split the node
    /// modified node, it contains smaller half
    /// new node, it contains larger half
    /// new key, it is the key need to propagate to parent
    pub(crate) fn split(
        &mut self,
        child_idx: usize,
        k: K,
        new_child_id: NodeId,
        new_child_argument: A,
    ) -> (K, Box<Self>) {
        debug_assert!(self.is_full());

        let mut new_node = Self::empty();
        new_node.size = Self::split_new_size() as u16;

        let new_key: K;

        let split_origin_size = Self::split_origin_size();
        let split_new_size = Self::split_new_size();

        self.size = split_origin_size as u16;

        if child_idx < split_origin_size {
            // take node_size 4 as example
            // new key 2, new node n
            //      1, 3, 4, 5
            //     a, b, c, d, e
            // =>        3
            //     1, 2      4, 5
            //    a  b  n   c   d  e

            new_key = unsafe { self.key_area(split_origin_size - 1).assume_init_read() };

            unsafe {
                utils::move_to_slice(
                    self.key_area_mut(split_origin_size..N),
                    new_node.key_area_mut(..split_new_size),
                );
                utils::move_to_slice(
                    self.child_area_mut(split_origin_size..N + 1),
                    new_node.child_area_mut(..split_new_size + 1),
                );
                utils::move_to_slice(
                    self.arguments_area_mut(split_origin_size..N + 1),
                    new_node.arguments_area_mut(..split_new_size + 1),
                );

                utils::slice_insert(self.key_area_mut(..self.size as usize + 1), child_idx, k);
                utils::slice_insert(
                    self.child_area_mut(..self.size as usize + 2),
                    child_idx + 1,
                    new_child_id,
                );
                utils::slice_insert(
                    self.arguments_area_mut(..self.size as usize + 2),
                    child_idx + 1,
                    new_child_argument,
                );
            };
        } else if child_idx > split_origin_size {
            // new key 4, new node n
            //      1, 2, 3, 5
            //     a, b, c, d, e
            // =>        3
            //     1, 2      4, 5
            //    a  b  c   d   n  e

            let prompt_key_index = split_origin_size;
            new_key = unsafe { self.key_area(prompt_key_index).assume_init_read() };

            let new_slot_idx = child_idx - 1 - split_origin_size;
            let new_child_idx = child_idx - split_origin_size;

            unsafe {
                utils::move_to_slice(
                    self.key_area_mut(prompt_key_index + 1..prompt_key_index + new_slot_idx + 1),
                    new_node.key_area_mut(..new_slot_idx),
                );
                utils::move_to_slice(
                    self.child_area_mut(
                        split_origin_size + 1..split_origin_size + 1 + new_child_idx,
                    ),
                    new_node.child_area_mut(0..new_child_idx),
                );
                utils::move_to_slice(
                    self.arguments_area_mut(
                        split_origin_size + 1..split_origin_size + 1 + new_child_idx,
                    ),
                    new_node.arguments_area_mut(0..new_child_idx),
                );

                *new_node.key_area_mut(new_slot_idx) = MaybeUninit::new(k);
                *new_node.child_area_mut(new_child_idx) = MaybeUninit::new(new_child_id);
                *new_node.arguments_area_mut(new_child_idx) = MaybeUninit::new(new_child_argument);

                utils::move_to_slice(
                    self.key_area_mut(prompt_key_index + new_slot_idx + 1..N),
                    new_node.key_area_mut(new_slot_idx + 1..split_new_size),
                );
                utils::move_to_slice(
                    self.child_area_mut(split_origin_size + 1 + new_child_idx..N + 1),
                    new_node.child_area_mut(new_child_idx + 1..split_new_size + 1),
                );
                utils::move_to_slice(
                    self.arguments_area_mut(split_origin_size + 1 + new_child_idx..N + 1),
                    new_node.arguments_area_mut(new_child_idx + 1..split_new_size + 1),
                );
            };
        } else {
            // new key 3, new node n
            //      1, 2, 4, 5
            //     a, b, c, d, e
            // =>        3
            //     1, 2      4, 5
            //    a  b  c   n   d  e
            new_key = k;

            unsafe {
                utils::move_to_slice(
                    self.key_area_mut(split_origin_size..N),
                    new_node.key_area_mut(..split_new_size),
                );
                utils::move_to_slice(
                    self.child_area_mut(split_origin_size + 1..N + 1),
                    new_node.child_area_mut(1..split_new_size + 1),
                );
                utils::move_to_slice(
                    self.arguments_area_mut(split_origin_size + 1..N + 1),
                    new_node.arguments_area_mut(1..split_new_size + 1),
                );

                *new_node.child_area_mut(0) = MaybeUninit::new(new_child_id);
                *new_node.arguments_area_mut(0) = MaybeUninit::new(new_child_argument);
            };
        }

        (new_key, new_node)
    }

    /// remove key at `slot` and it's right child. This method is used when the children of slot
    /// is merged.
    pub(crate) fn remove_slot_with_right(&mut self, slot: usize) -> (InnerMergeResult, K) {
        let k = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.size as usize), slot);
            utils::slice_remove(self.child_area_mut(..self.size as usize + 1), slot + 1);
            utils::slice_remove(self.arguments_area_mut(..self.size as usize + 1), slot + 1);
            k
        };
        self.size -= 1;

        if self.size >= Self::minimum_size() as u16 {
            (InnerMergeResult::Done, k)
        } else {
            // the undersized inner node will be fixed by parent node
            (InnerMergeResult::UnderSize, k)
        }
    }

    pub(crate) fn merge_next(&mut self, slot_key: K, right: &mut Self) {
        unsafe {
            *self.key_area_mut(self.size as usize) = MaybeUninit::new(slot_key);
            self.size += 1;

            let self_size = self.size as usize;
            let right_size = right.len();

            debug_assert!(self.len() + right_size <= N);

            utils::move_to_slice(
                right.key_area_mut(..right_size),
                self.key_area_mut(self_size..self_size + right_size),
            );
            utils::move_to_slice(
                right.child_area_mut(..right_size + 1),
                self.child_area_mut(self_size..self_size + right_size + 1),
            );
            utils::move_to_slice(
                right.arguments_area_mut(..right_size + 1),
                self.arguments_area_mut(self_size..self_size + right_size + 1),
            );
            self.size += right.size;
            right.size = 0;
        }
    }

    /// pop the last key and right child
    pub(crate) fn pop(&mut self) -> (K, NodeId, A) {
        let k = std::mem::replace(
            unsafe { self.key_area_mut(self.size as usize - 1) },
            MaybeUninit::uninit(),
        );
        let child = std::mem::replace(
            unsafe { self.child_area_mut(self.size as usize) },
            MaybeUninit::uninit(),
        );
        let argument = std::mem::replace(
            unsafe { self.arguments_area_mut(self.size as usize) },
            MaybeUninit::uninit(),
        );
        self.size -= 1;
        unsafe {
            (
                k.assume_init_read(),
                child.assume_init_read(),
                argument.assume_init_read(),
            )
        }
    }

    pub(crate) fn pop_front(&mut self) -> (K, NodeId, A) {
        let (k, left_c, left_m) = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.size as usize), 0);
            let left_c = utils::slice_remove(self.child_area_mut(..self.size as usize + 1), 0);
            let left_m = utils::slice_remove(self.arguments_area_mut(..self.size as usize + 1), 0);
            (k, left_c, left_m)
        };
        self.size -= 1;

        (k, left_c, left_m)
    }

    pub fn push(&mut self, k: K, child: NodeId, argument: A) {
        unsafe {
            *self.key_area_mut(self.size as usize) = MaybeUninit::new(k);
            *self.child_area_mut(self.size as usize + 1) = MaybeUninit::new(child);
            *self.arguments_area_mut(self.size as usize + 1) = MaybeUninit::new(argument);
        };
        self.size += 1;
    }

    pub(crate) fn push_front(&mut self, k: K, child: NodeId, argument: A) {
        unsafe {
            utils::slice_insert(self.key_area_mut(0..self.size as usize + 1), 0, k);
            utils::slice_insert(self.child_area_mut(0..self.size as usize + 2), 0, child);
            utils::slice_insert(
                self.arguments_area_mut(0..self.size as usize + 2),
                0,
                argument,
            );
        }
        self.size += 1;
    }

    #[cfg(test)]
    fn iter_key(&self) -> impl Iterator<Item = &K> {
        unsafe { self.key_area(..self.size as usize) }
            .iter()
            .map(|s| unsafe { s.assume_init_ref() })
    }

    #[cfg(test)]
    fn iter_child(&self) -> impl Iterator<Item = NodeId> + '_ {
        let slice = if self.size > 0 {
            &self.child_id[0..self.len() + 1]
        } else {
            &self.child_id[..0]
        };

        slice.iter().map(|s| unsafe { s.assume_init_read() })
    }

    #[cfg(test)]
    fn iter_argument(&self) -> impl Iterator<Item = A> + '_ {
        let slice = if self.size > 0 {
            &self.arguments[0..self.len() + 1]
        } else {
            &self.arguments[..0]
        };

        slice.iter().map(|s| unsafe { s.assume_init_read() })
    }

    /// get slot_key vec, used in test
    #[cfg(test)]
    pub(crate) fn key_vec(&self) -> Vec<K> {
        self.iter_key().cloned().collect()
    }

    /// get child_id vec, used in test
    #[cfg(test)]
    pub(crate) fn child_id_vec(&self) -> Vec<NodeId> {
        self.iter_child().collect()
    }

    #[cfg(test)]
    pub(crate) fn argument_vec(&self) -> Vec<A> {
        self.iter_argument().collect()
    }

    fn key(&self, idx: usize) -> &K {
        unsafe { self.key_area(idx).assume_init_ref() }
    }

    pub(crate) fn set_key(&mut self, idx: usize, key: K) -> K {
        unsafe {
            std::mem::replace(self.key_area_mut(idx), MaybeUninit::new(key)).assume_init_read()
        }
    }

    fn child_id(&self, idx: usize) -> NodeId {
        unsafe { self.child_area(idx).assume_init_read() }
    }

    unsafe fn key_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<K>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.slot_key.as_mut_slice().get_unchecked_mut(index) }
    }

    unsafe fn key_area<I, Output: ?Sized>(&self, index: I) -> &Output
    where
        I: SliceIndex<[MaybeUninit<K>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.slot_key.as_slice().get_unchecked(index) }
    }

    unsafe fn argument_area<I, Output: ?Sized>(&self, index: I) -> &Output
    where
        I: SliceIndex<[MaybeUninit<A>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.arguments.as_slice().get_unchecked(index) }
    }

    unsafe fn arguments_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<A>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.arguments.as_mut_slice().get_unchecked_mut(index) }
    }

    unsafe fn child_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<NodeId>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.child_id.as_mut_slice().get_unchecked_mut(index) }
    }

    unsafe fn child_area<I, Output: ?Sized>(&self, index: I) -> &Output
    where
        I: SliceIndex<[MaybeUninit<NodeId>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.child_id.as_slice().get_unchecked(index) }
    }

    #[cfg(test)]
    pub(crate) fn set_data<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        &mut self,
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) {
        assert!(N1 + 1 == C1);
        assert!(N1 <= N);
        self.size = N1 as u16;
        for i in 0..N1 {
            self.slot_key[i] = MaybeUninit::new(slot_keys[i].clone());
        }

        for c in 0..C1 {
            self.child_id[c] = MaybeUninit::new(child_id[c].into());
        }
    }
}

impl<K: Key, A: Argumentation<K>> super::INode<K, A> for InnerNode<K, A> {
    fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
        arguments: [A; C1],
    ) -> Box<Self> {
        Self::new(slot_keys, child_id, arguments)
    }

    fn new_from_iter(
        keys: impl Iterator<Item = K>,
        childs: impl Iterator<Item = NodeId>,
        argument: impl Iterator<Item = A>,
    ) -> Box<Self> {
        Self::new_from_iter(keys, childs, argument)
    }

    fn len(&self) -> usize {
        self.size as usize
    }

    fn key(&self, idx: usize) -> &K {
        Self::key(self, idx)
    }

    fn set_key(&mut self, idx: usize, key: K) -> K {
        Self::set_key(self, idx, key)
    }

    fn child_id(&self, idx: usize) -> NodeId {
        Self::child_id(self, idx)
    }

    fn locate_child<Q: ?Sized>(&self, k: &Q) -> (usize, NodeId)
    where
        Q: Ord,
        K: std::borrow::Borrow<Q>,
    {
        Self::locate_child(self, k)
    }

    fn is_full(&self) -> bool {
        Self::is_full(self)
    }

    fn able_to_lend(&self) -> bool {
        Self::able_to_lend(self)
    }

    fn insert_at(&mut self, slot: usize, key: K, right_child: NodeId, right_child_argument: A) {
        Self::insert_at(self, slot, key, right_child, right_child_argument)
    }

    fn split(
        &mut self,
        child_idx: usize,
        k: K,
        new_child_id: NodeId,
        new_child_argument: A,
    ) -> (K, Box<Self>) {
        Self::split(self, child_idx, k, new_child_id, new_child_argument)
    }

    fn pop(&mut self) -> (K, NodeId, A) {
        Self::pop(self)
    }

    fn pop_front(&mut self) -> (K, NodeId, A) {
        Self::pop_front(self)
    }

    fn push(&mut self, k: K, child: NodeId, argument: A) {
        Self::push(self, k, child, argument)
    }

    fn push_front(&mut self, k: K, child: NodeId, argument: A) {
        Self::push_front(self, k, child, argument)
    }

    fn merge_next(&mut self, slot_key: K, right: &mut Self) {
        Self::merge_next(self, slot_key, right)
    }

    fn remove_slot_with_right(&mut self, slot: usize) -> (InnerMergeResult, K) {
        Self::remove_slot_with_right(self, slot)
    }

    fn keys(&self) -> &[K] {
        Self::keys(self)
    }

    fn arguments(&self) -> &[A] {
        Self::arguments(self)
    }

    fn set_argument(&mut self, idx: usize, argument: A) {
        Self::set_argument(self, idx, argument)
    }
}

/// Merge result, returns the nodeid needs to drop
pub enum InnerMergeResult {
    Done,
    UnderSize,
}

#[cfg(test)]
mod tests {
    use super::*;
    type InnerNode45 = InnerNode<usize, ()>;

    fn new_test_node() -> Box<InnerNode<usize, ()>> {
        let mut slot_keys = [0; N];
        for i in 0..N {
            slot_keys[i] = i * 2;
        }
        let mut child_ids = [InnerNodeId(0); C];
        for i in 0..C {
            child_ids[i] = InnerNodeId(i * 10);
        }
        InnerNode::new(slot_keys, child_ids, [(); C])
    }

    #[test]
    fn test_inner_split_new_key_in_origin_even() {
        let mut inner_node = new_test_node();

        let test_key = 3;
        let test_child = InnerNodeId(333);

        let (k, new_node) = inner_node.split(1, test_key, test_child.into(), ());
        assert_eq!(k, 2);
        assert_eq!(inner_node.key_vec(), vec![0, test_key]);
        assert_eq!(
            &inner_node.child_id_vec(),
            &[
                NodeId::Inner(InnerNodeId(0)),
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(test_child),
            ]
        );
        assert_eq!(new_node.key_vec(), vec![4, 6]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
                NodeId::Inner(InnerNodeId(40)),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_in_origin_odd() {
        let mut inner_node = new_test_node();

        let test_key = 3;
        let test_child = InnerNodeId(333);

        let (k, new_node) = inner_node.split(1, test_key, test_child.into(), ());
        assert_eq!(k, 2);
        assert_eq!(inner_node.key_vec(), vec![0, test_key]);
        assert_eq!(
            &inner_node.child_id_vec(),
            &[
                NodeId::Inner(InnerNodeId(0)),
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(test_child),
            ]
        );
        assert_eq!(new_node.key_vec(), vec![4, 6, 8]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(InnerNodeId(50)),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_in_new_last_even() {
        let mut inner_node = new_test_node();

        //   0 2  4  6
        // 0 10 20 30 40

        let test_idx = 4;
        let test_key = 7;
        let test_child = InnerNodeId(333);

        let (k, new_node) = inner_node.split(test_idx, test_key, NodeId::Inner(test_child), ());
        assert_eq!(new_node.len(), InnerNode45::split_new_size());
        assert_eq!(inner_node.len(), InnerNode45::split_origin_size());
        assert_eq!(k, 4);
        assert_eq!(inner_node.key_vec(), vec![0, 2]);
        assert_eq!(
            inner_node.child_id_vec(),
            vec![
                NodeId::Inner(InnerNodeId(0)),
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
            ]
        );
        assert_eq!(new_node.key_vec().as_slice(), &[6, 7]);
        assert_eq!(
            new_node.child_id_vec(),
            vec![
                NodeId::Inner(InnerNodeId(30)),
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(test_child),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_in_new_last_odd() {
        let mut inner_node = new_test_node();

        //  0  2  4  6  8
        // 0 10 20 30 40 50

        let (k, new_node) = inner_node.split(5, 9, NodeId::Inner(InnerNodeId(100)), ());
        assert_eq!(inner_node.len(), 2);
        assert_eq!(new_node.len(), 3);
        assert_eq!(k, 4);
        assert_eq!(inner_node.key_vec(), vec![0, 2]);
        assert_eq!(
            inner_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(0)),
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
            ]
        );
        assert_eq!(new_node.key_vec().as_slice(), &[6, 8, 9]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(30)),
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(InnerNodeId(50)),
                NodeId::Inner(InnerNodeId(100)),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_in_new() {
        let mut inner_node = InnerNode45::new(
            [1, 2, 3, 5],
            [
                InnerNodeId(10),
                InnerNodeId(20),
                InnerNodeId(30),
                InnerNodeId(40),
                InnerNodeId(50),
            ],
            [Default::default(); 5],
        );

        // child_idx is 1
        let (k, new_node) = inner_node.split(3, 4, NodeId::Inner(InnerNodeId(100)), ());
        assert_eq!(inner_node.len(), InnerNode45::split_origin_size());
        assert_eq!(new_node.len(), InnerNode45::split_new_size());
        assert_eq!(k, 3);
        assert_eq!(inner_node.key_vec().as_slice(), &[1, 2]);
        assert_eq!(
            inner_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
            ]
        );
        assert_eq!(new_node.key_vec().as_slice(), &[4, 5]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(InnerNodeId(100)),
                NodeId::Inner(InnerNodeId(50)),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_is_the_prompt_key() {
        let mut inner_node = InnerNode45::new(
            [1, 2, 4, 5],
            [
                InnerNodeId(10),
                InnerNodeId(20),
                InnerNodeId(30),
                InnerNodeId(40),
                InnerNodeId(50),
            ],
            [Default::default(); 5],
        );

        // child_idx is 1
        let (k, new_node) = inner_node.split(2, 3, NodeId::Inner(InnerNodeId(100)), ());
        assert_eq!(inner_node.len(), InnerNode45::split_origin_size());
        assert_eq!(k, 3);
        assert_eq!(inner_node.key_vec().as_slice(), &[1, 2]);
        assert_eq!(
            inner_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
            ]
        );
        assert_eq!(new_node.key_vec(), &[4, 5]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(100)),
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(InnerNodeId(50)),
            ]
        );
    }
}

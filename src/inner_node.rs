use crate::*;
use std::alloc::alloc;
use std::slice::SliceIndex;
use std::{
    alloc::Layout,
    mem::{self, MaybeUninit},
};

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct InnerNode<K: Key, const N: usize, const C: usize> {
    size: u16,

    slot_key: [MaybeUninit<K>; N],
    child_id: [MaybeUninit<NodeId>; C],
}

impl<K: Key, const N: usize, const C: usize> InnerNode<K, N, C> {
    pub const fn split_origin_size() -> usize {
        N / 2
    }

    pub const fn split_new_size() -> usize {
        N - Self::split_origin_size()
    }

    const fn minimum_size() -> usize {
        if N / 4 == 0 {
            1
        } else {
            N / 4
        }
    }

    pub fn able_to_lend(&self) -> bool {
        self.size > Self::minimum_size() as u16
    }

    /// whether this node is full, if yes, then the next insert need to split
    pub fn is_full(&self) -> bool {
        self.size == N as u16
    }

    pub(crate) fn empty() -> Box<Self> {
        // not sure how to do a constrain in compile time, just put a debug assert here.
        debug_assert!(C == N + 1);

        let layout = Layout::new::<mem::MaybeUninit<Self>>();
        let ptr: *mut Self = unsafe { alloc(layout).cast() };
        let mut this = unsafe { Box::from_raw(ptr) };
        this.size = 0;
        this
    }

    pub(crate) fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) -> Box<Self> {
        // not sure how to do a constrain in compile time, just put a debug assert here.
        debug_assert!(C == N + 1);

        let layout = Layout::new::<mem::MaybeUninit<Self>>();
        let ptr: *mut Self = unsafe { alloc(layout).cast() };
        let mut this = unsafe { Box::from_raw(ptr) };

        this.set_data(slot_keys, child_id);

        this
    }

    pub(crate) fn set_data<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        &mut self,
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) {
        assert!(N1 + 1 == C1);
        assert!(N1 <= N);
        self.size = N1 as u16;
        for i in 0..N1 {
            self.slot_key[i] = MaybeUninit::new(slot_keys[i]);
        }

        for c in 0..C1 {
            self.child_id[c] = MaybeUninit::new(child_id[c].into());
        }
    }

    const fn binary_search_threshold() -> usize {
        128 / std::mem::size_of::<K>()
    }

    /// returns the child index for k
    #[inline]
    pub(crate) fn locate_child(&self, k: &K) -> (usize, NodeId) {
        if self.size > Self::binary_search_threshold() as u16 {
            match unsafe { self.key_area(0..self.size as usize) }
                .binary_search_by_key(&k, |f| unsafe { f.assume_init_ref() })
            {
                Err(idx) => {
                    // the idx is the place where a matching element could be inserted while maintaining
                    // sorted order. go to left child
                    (idx, self.child_id_at(idx))
                }
                Ok(idx) => {
                    // exact match, go to right child.
                    // if the child split, then the new key should inserted idx + 1
                    (idx + 1, self.child_id_at(idx + 1))
                }
            }
        } else {
            unsafe { self.key_area(..self.size()) }
                .iter()
                .enumerate()
                .find_map(|(i, s)| {
                    let cmp = unsafe { s.assume_init_ref() }.cmp(k);
                    if cmp == std::cmp::Ordering::Less {
                        None
                    } else if cmp == std::cmp::Ordering::Greater {
                        Some((i, self.child_id_at(i)))
                    } else {
                        Some((i + 1, self.child_id_at(i + 1)))
                    }
                })
                .unwrap_or_else(|| (self.size as usize, self.child_id_at(self.size as usize)))
        }
    }

    pub(crate) fn iter_key(&self) -> impl Iterator<Item = &K> {
        unsafe { self.key_area(..self.size as usize) }
            .iter()
            .map(|s| unsafe { s.assume_init_ref() })
    }

    pub(crate) fn iter_child(&self) -> impl Iterator<Item = NodeId> + '_ {
        let slice = if self.size > 0 {
            &self.child_id[0..self.size() + 1]
        } else {
            &self.child_id[..0]
        };

        slice.iter().map(|s| unsafe { s.assume_init_read() })
    }

    /// Insert `key` and its `right_child` to `slot`
    pub(crate) fn insert_at(&mut self, slot: usize, key: K, right_child: NodeId) {
        debug_assert!(slot <= self.size());

        let new_size = self.size as usize + 1;
        let new_child_size = self.size as usize + 2;

        unsafe { utils::slice_insert(self.key_area_mut(..new_size), slot, key) };
        unsafe {
            utils::slice_insert(self.child_area_mut(..new_child_size), slot + 1, right_child)
        };

        self.size += 1;
    }

    /// Split the node
    /// modified node, it contains smaller half
    /// new node, it contains larger half
    /// new key, it is the key need to propagate to parent
    pub(crate) fn split(&mut self, child_idx: usize, k: K, new_child_id: NodeId) -> (K, Box<Self>) {
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
                    self.child_area_mut(split_new_size..N + 1),
                    new_node.child_area_mut(..split_new_size + 1),
                );

                utils::slice_insert(self.key_area_mut(..self.size as usize + 1), child_idx, k);
                utils::slice_insert(
                    self.child_area_mut(..self.size as usize + 2),
                    child_idx + 1,
                    new_child_id,
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
            let new_child_idx = child_idx - split_new_size;

            unsafe {
                utils::move_to_slice(
                    self.key_area_mut(prompt_key_index + 1..prompt_key_index + new_slot_idx + 1),
                    new_node.key_area_mut(..new_slot_idx),
                );

                utils::move_to_slice(
                    self.child_area_mut(split_new_size + 1..split_new_size + 1 + new_child_idx),
                    new_node.child_area_mut(0..new_child_idx),
                );

                *new_node.key_area_mut(new_slot_idx) = MaybeUninit::new(k);
                *new_node.child_area_mut(new_child_idx) = MaybeUninit::new(new_child_id);

                utils::move_to_slice(
                    self.key_area_mut(prompt_key_index + new_slot_idx + 1..N),
                    new_node.key_area_mut(new_slot_idx + 1..split_new_size),
                );

                utils::move_to_slice(
                    self.child_area_mut(split_new_size + 1 + new_child_idx..N + 1),
                    new_node.child_area_mut(new_child_idx + 1..split_new_size + 1),
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
                    self.key_area_mut(split_new_size..N),
                    new_node.key_area_mut(..split_new_size),
                );

                utils::move_to_slice(
                    self.child_area_mut(split_new_size + 1..N + 1),
                    new_node.child_area_mut(1..split_new_size + 1),
                );

                *new_node.child_area_mut(0) = MaybeUninit::new(new_child_id);
            };
        }

        (new_key, new_node)
    }

    /// merge child identified by `smaller_idx` and `smaller_idx + 1`
    pub(crate) fn merge_child(&mut self, slot: usize) -> InnerMergeResult {
        unsafe {
            utils::slice_remove(self.key_area_mut(..self.size as usize), slot);
            utils::slice_remove(self.child_area_mut(..self.size as usize + 1), slot + 1);
        };
        self.size -= 1;

        if self.size >= Self::minimum_size() as u16 {
            InnerMergeResult::Done
        } else {
            // the undersized inner node will be fixed by parent node
            InnerMergeResult::UnderSize
        }
    }

    pub(crate) fn merge_next(&mut self, slot_key: K, right: &mut Self) {
        unsafe {
            *self.key_area_mut(self.size as usize) = MaybeUninit::new(slot_key);
            self.size += 1;

            let self_size = self.size as usize;
            let right_size = right.size();

            debug_assert!(self.size() + right_size <= N);

            utils::move_to_slice(
                right.key_area_mut(..right_size),
                self.key_area_mut(self_size..self_size + right_size),
            );
            utils::move_to_slice(
                right.child_area_mut(..right_size + 1),
                self.child_area_mut(self_size..self_size + right_size + 1),
            );
            self.size += right.size;
        }
    }

    /// pop the last key and right child
    pub(crate) fn pop(&mut self) -> (K, NodeId) {
        let k = std::mem::replace(
            unsafe { self.key_area_mut(self.size as usize - 1) },
            MaybeUninit::uninit(),
        );
        let child = std::mem::replace(
            unsafe { self.child_area_mut(self.size as usize) },
            MaybeUninit::uninit(),
        );
        self.size -= 1;
        unsafe { (k.assume_init_read(), child.assume_init_read()) }
    }

    pub(crate) fn pop_front(&mut self) -> (K, NodeId) {
        let (k, left_c) = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.size as usize), 0);
            let left_c = utils::slice_remove(self.child_area_mut(..self.size as usize + 1), 0);
            (k, left_c)
        };
        self.size -= 1;

        (k, left_c)
    }

    pub fn push(&mut self, k: K, child: NodeId) {
        unsafe {
            *self.key_area_mut(self.size as usize) = MaybeUninit::new(k);
            *self.child_area_mut(self.size as usize + 1) = MaybeUninit::new(child);
        };
        self.size += 1;
    }

    /// get slot_key vec, used in test
    #[cfg(test)]
    fn slot_key_vec(&self) -> Vec<K> {
        self.iter_key().cloned().collect()
    }

    /// get child_id vec, used in test
    #[cfg(test)]
    fn child_id_vec(&self) -> Vec<NodeId> {
        self.iter_child().collect()
    }

    fn key(&self, idx: usize) -> &K {
        unsafe { self.key_area(idx).assume_init_ref() }
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
}

impl<K: Key, const N: usize, const C: usize> super::INode<K> for InnerNode<K, N, C> {
    fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) -> Box<Self> {
        Self::new(slot_keys, child_id)
    }

    fn size(&self) -> usize {
        self.size as usize
    }

    fn key(&self, idx: usize) -> &K {
        Self::key(self, idx)
    }

    fn set_key(&mut self, idx: usize, key: K) {
        unsafe {
            *self.key_area_mut(idx) = MaybeUninit::new(key);
        }
    }

    fn child_id_at(&self, idx: usize) -> NodeId {
        unsafe { self.child_area(idx).assume_init_read() }
    }

    fn locate_child(&self, k: &K) -> (usize, NodeId) {
        Self::locate_child(self, k)
    }

    fn is_full(&self) -> bool {
        Self::is_full(self)
    }

    fn able_to_lend(&self) -> bool {
        Self::able_to_lend(self)
    }

    fn insert_at(&mut self, slot: usize, key: K, right_child: NodeId) {
        Self::insert_at(self, slot, key, right_child)
    }

    fn split(&mut self, child_idx: usize, k: K, new_child_id: NodeId) -> (K, Box<Self>) {
        Self::split(self, child_idx, k, new_child_id)
    }

    fn pop(&mut self) -> (K, NodeId) {
        Self::pop(self)
    }

    fn pop_front(&mut self) -> (K, NodeId) {
        Self::pop_front(self)
    }

    fn push(&mut self, k: K, child: NodeId) {
        Self::push(self, k, child)
    }

    fn push_front(&mut self, k: K, child: NodeId) {
        unsafe {
            utils::slice_insert(self.key_area_mut(0..self.size as usize + 1), 0, k);
            utils::slice_insert(self.child_area_mut(0..self.size as usize + 2), 0, child);
        }
        self.size += 1;
    }

    fn merge_next(&mut self, slot_key: K, right: &mut Self) {
        Self::merge_next(self, slot_key, right)
    }

    fn merge_child(&mut self, slot: usize) -> InnerMergeResult {
        Self::merge_child(self, slot)
    }

    fn set_data<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        &mut self,
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) {
        InnerNode::set_data(self, slot_keys, child_id)
    }

    fn iter_key<'a>(&'a self) -> Box<dyn Iterator<Item = &K> + 'a> {
        Box::new(InnerNode::iter_key(&self))
    }

    fn iter_child<'a>(&'a self) -> Box<dyn Iterator<Item = NodeId> + 'a> {
        Box::new(InnerNode::iter_child(&self))
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
    type InnerNode = super::InnerNode<usize, 4, 5>;

    #[test]
    fn test_inner_split_new_key_in_origin() {
        let mut inner_node = InnerNode::new(
            [1, 3, 4, 5],
            [
                InnerNodeId(10),
                InnerNodeId(20),
                InnerNodeId(30),
                InnerNodeId(40),
                InnerNodeId(50),
            ],
        );

        // child_idx is 1
        let (k, new_node) = inner_node.split(1, 2, NodeId::Inner(InnerNodeId(100)));
        assert_eq!(k, 3);
        assert_eq!(inner_node.slot_key_vec(), vec![1, 2]);
        assert_eq!(
            &inner_node.child_id_vec(),
            &[
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(100)),
            ]
        );
        assert_eq!(new_node.slot_key_vec(), vec![4, 5]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(30)),
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(InnerNodeId(50)),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_in_new_last() {
        let mut inner_node = InnerNode::new(
            [1, 2, 3, 4],
            [
                InnerNodeId(10),
                InnerNodeId(20),
                InnerNodeId(30),
                InnerNodeId(40),
                InnerNodeId(50),
            ],
        );

        // child_idx is 1
        let (k, new_node) = inner_node.split(4, 5, NodeId::Inner(InnerNodeId(100)));
        assert_eq!(new_node.size(), InnerNode::split_new_size());
        assert_eq!(inner_node.size(), InnerNode::split_origin_size());
        assert_eq!(k, 3);
        assert_eq!(inner_node.slot_key_vec(), vec![1, 2,]);
        assert_eq!(
            inner_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
            ]
        );
        assert_eq!(new_node.slot_key_vec().as_slice(), &[4, 5]);
        assert_eq!(
            new_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(40)),
                NodeId::Inner(InnerNodeId(50)),
                NodeId::Inner(InnerNodeId(100)),
            ]
        );
    }

    #[test]
    fn test_inner_split_new_key_in_new() {
        let mut inner_node = InnerNode::new(
            [1, 2, 3, 5],
            [
                InnerNodeId(10),
                InnerNodeId(20),
                InnerNodeId(30),
                InnerNodeId(40),
                InnerNodeId(50),
            ],
        );

        // child_idx is 1
        let (k, new_node) = inner_node.split(3, 4, NodeId::Inner(InnerNodeId(100)));
        assert_eq!(inner_node.size(), InnerNode::split_origin_size());
        assert_eq!(new_node.size(), InnerNode::split_new_size());
        assert_eq!(k, 3);
        assert_eq!(inner_node.slot_key_vec().as_slice(), &[1, 2]);
        assert_eq!(
            inner_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
            ]
        );
        assert_eq!(new_node.slot_key_vec().as_slice(), &[4, 5]);
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
        let mut inner_node = InnerNode::new(
            [1, 2, 4, 5],
            [
                InnerNodeId(10),
                InnerNodeId(20),
                InnerNodeId(30),
                InnerNodeId(40),
                InnerNodeId(50),
            ],
        );

        // child_idx is 1
        let (k, new_node) = inner_node.split(2, 3, NodeId::Inner(InnerNodeId(100)));
        assert_eq!(inner_node.size(), InnerNode::split_origin_size());
        assert_eq!(k, 3);
        assert_eq!(inner_node.slot_key_vec().as_slice(), &[1, 2]);
        assert_eq!(
            inner_node.child_id_vec().as_slice(),
            &[
                NodeId::Inner(InnerNodeId(10)),
                NodeId::Inner(InnerNodeId(20)),
                NodeId::Inner(InnerNodeId(30)),
            ]
        );
        assert_eq!(new_node.slot_key_vec(), &[4, 5]);
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

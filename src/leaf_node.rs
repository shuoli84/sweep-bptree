use crate::*;
use std::{
    alloc::{alloc, Layout},
    mem::{self, MaybeUninit},
    slice::SliceIndex,
};

#[derive(Debug)]
#[repr(C)]
pub struct LeafNode<K: Key, V: Value, const N: usize> {
    /// how many data items
    size: u16,
    slot_key: [MaybeUninit<K>; N],
    slot_value: [MaybeUninit<V>; N],

    prev: Option<LeafNodeId>,
    next: Option<LeafNodeId>,
}

impl<K: Key, V: Value, const N: usize> Clone for LeafNode<K, V, N> {
    fn clone(&self) -> Self {
        // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
        let mut new_value = unsafe { MaybeUninit::<[MaybeUninit<V>; N]>::uninit().assume_init() };

        for i in 0..self.len() {
            unsafe {
                *new_value.get_unchecked_mut(i) =
                    MaybeUninit::new(self.value_area(i).assume_init_read().clone());
            };
        }

        Self {
            size: self.size.clone(),
            slot_key: self.slot_key.clone(),
            slot_value: new_value,
            prev: self.prev.clone(),
            next: self.next.clone(),
        }
    }
}

impl<K: Key, V: Value, const N: usize> LeafNode<K, V, N> {
    pub(crate) fn new() -> Box<Self> {
        let layout = Layout::new::<mem::MaybeUninit<Self>>();
        let ptr: *mut Self = unsafe { alloc(layout).cast() };
        let mut this = unsafe { Box::from_raw(ptr) };

        this.prev = None;
        this.next = None;
        this.size = 0;

        this
    }

    const fn split_origin_size() -> u16 {
        (N / 2) as u16
    }

    /// the minimum size for Leaf Node, if the node size lower than this, then
    /// it is under sized
    const fn minimum_size() -> u16 {
        let s = (N / 4) as u16;
        if s == 0 {
            1
        } else {
            s
        }
    }

    pub fn is_full(&self) -> bool {
        self.size == N as u16
    }

    pub fn able_to_lend(&self) -> bool {
        self.size > Self::minimum_size()
    }

    pub fn in_range(&self, k: &K) -> bool {
        debug_assert!(self.len() > 0);

        let (start, end) = self.key_range();
        match (start, end) {
            (Some(start), Some(end)) => k >= &start && k <= &end,
            (Some(start), None) => k >= &start,
            (None, Some(end)) => k <= &end,
            (None, None) => true,
        }
    }

    pub fn key_range(&self) -> (Option<K>, Option<K>) {
        debug_assert!(self.len() > 0);
        let start = match self.prev {
            Some(_) => Some(unsafe { self.key_area(0).assume_init_read() }),
            None => None,
        };
        let end = match self.next {
            Some(_) => Some(unsafe { self.key_area(self.len() - 1).assume_init_read() }),
            None => None,
        };
        (start, end)
    }

    pub fn is_size_minimum(&self) -> bool {
        self.size == Self::minimum_size()
    }

    pub fn set_prev(&mut self, id: Option<LeafNodeId>) {
        self.prev = id;
    }

    pub fn set_next(&mut self, id: Option<LeafNodeId>) {
        self.next = id;
    }

    fn set_data<const N1: usize>(&mut self, data: [(K, V); N1]) {
        assert!(N1 <= N);
        self.size = N1 as u16;
        for i in 0..N1 {
            unsafe {
                *self.key_area_mut(i) = MaybeUninit::new(data[i].0);
                *self.value_area_mut(i) = MaybeUninit::new(data[i].1.clone());
            }
        }
    }

    fn set_data_by_iter(&mut self, data: &mut impl Iterator<Item = (K, V)>) {
        for i in 0..N {
            if let Some((k, v)) = data.next() {
                unsafe {
                    *self.key_area_mut(i) = MaybeUninit::new(k);
                    *self.value_area_mut(i) = MaybeUninit::new(v);
                }
                self.size += 1;
            } else {
                break;
            }
        }
    }

    fn data_at(&self, slot: usize) -> (&K, &V) {
        unsafe {
            (
                self.key_area(slot).assume_init_ref(),
                self.value_area(slot).assume_init_ref(),
            )
        }
    }

    pub fn try_data_at(&self, idx: usize) -> Option<(&K, &V)> {
        if idx >= self.size as usize {
            return None;
        }
        Some(unsafe {
            (
                self.key_area(idx).assume_init_ref(),
                self.value_area(idx).assume_init_ref(),
            )
        })
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        unsafe { self.key_area(..self.size as usize) }
            .iter()
            .zip(unsafe { self.value_area(..self.size as usize) })
            .map(|item| unsafe { (item.0.assume_init_ref(), item.1.assume_init_ref()) })
    }

    #[cfg(test)]
    pub(crate) fn data_vec(&self) -> Vec<(K, V)> {
        self.iter().map(|(k, v)| (*k, v.clone())).collect()
    }

    /// insert / update (k, v), if node is full, then returns `LeafUpsertResult::IsFull`
    pub(crate) fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<V> {
        match self.locate_child_idx(&k) {
            Ok(idx) => {
                // update existing item
                let prev_v =
                    std::mem::replace(unsafe { self.value_area_mut(idx) }, MaybeUninit::new(v));
                LeafUpsertResult::Updated(unsafe { prev_v.assume_init() })
            }

            Err(idx) => {
                if !self.is_full() {
                    let new_len = self.len() + 1;
                    unsafe { utils::slice_insert(self.key_area_mut(..new_len), idx, k) };
                    unsafe { utils::slice_insert(self.value_area_mut(..new_len), idx, v) };
                    self.size = new_len as u16;
                    LeafUpsertResult::Inserted
                } else {
                    LeafUpsertResult::IsFull(idx, v)
                }
            }
        }
    }

    fn split_new_leaf(
        &mut self,
        insert_idx: usize,
        item: (K, V),
        new_leaf_id: LeafNodeId,
        self_leaf_id: LeafNodeId,
    ) -> Box<Self> {
        let split_origin_size = Self::split_origin_size() as usize;
        let split_new_size = N - split_origin_size as usize;

        let mut new_node = Self::new();
        new_node.prev = Some(self_leaf_id);
        new_node.next = self.next;

        unsafe {
            utils::move_to_slice(
                self.key_area_mut(split_origin_size..N),
                new_node.key_area_mut(..split_new_size as usize),
            );
            utils::move_to_slice(
                self.value_area_mut(split_origin_size..N),
                new_node.value_area_mut(..split_new_size as usize),
            );
        };

        if insert_idx < split_origin_size {
            let new_size = split_origin_size as usize + 1;
            unsafe {
                utils::slice_insert(self.key_area_mut(..new_size), insert_idx, item.0);
                utils::slice_insert(self.value_area_mut(..new_size), insert_idx, item.1);
            };
            self.size = new_size as u16;

            new_node.size = split_new_size as u16;
        } else {
            // data insert to new/right
            let insert_idx = insert_idx - split_origin_size;

            unsafe {
                utils::slice_insert(
                    new_node.key_area_mut(..split_new_size + 1),
                    insert_idx,
                    item.0,
                );
                utils::slice_insert(
                    new_node.value_area_mut(..split_new_size + 1),
                    insert_idx,
                    item.1,
                );
            }

            self.size = split_origin_size as u16;
            new_node.size = split_new_size as u16 + 1;
        };

        self.next = Some(new_leaf_id);

        new_node
    }

    /// Delete an item from LeafNode
    pub(crate) fn delete(&mut self, k: &K) -> LeafDeleteResult<K, V> {
        match self.locate_child_idx(k) {
            Ok(idx) => {
                if self.able_to_lend() {
                    let result = unsafe {
                        let k = utils::slice_remove(self.key_area_mut(..self.size as usize), idx);
                        let v = utils::slice_remove(self.value_area_mut(..self.size as usize), idx);
                        (k, v)
                    };
                    self.size -= 1;
                    LeafDeleteResult::Done(result)
                } else {
                    LeafDeleteResult::UnderSize(idx)
                }
            }
            _ => LeafDeleteResult::NotFound,
        }
    }

    #[inline]
    pub(crate) fn locate_child_idx(&self, k: &K) -> Result<usize, usize> {
        unsafe { self.key_area(..self.len()) }
            .binary_search_by_key(&k, |f| unsafe { f.assume_init_ref() })
    }

    pub(crate) fn locate_child(&self, k: &K) -> (usize, Option<&V>) {
        match self.locate_child_idx(k) {
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (idx, {
                    let v = unsafe { self.value_area(idx).assume_init_ref() };
                    Some(&v)
                })
            }

            Err(idx) => {
                // the idx is the place where a matching element could be inserted while maintaining
                // sorted order. go to left child
                (idx, None)
            }
        }
    }

    pub(crate) fn locate_child_mut(&mut self, k: &K) -> (usize, Option<&mut V>) {
        match self.locate_child_idx(k) {
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (
                    idx,
                    Some(unsafe { self.value_area_mut(idx).assume_init_mut() }),
                )
            }

            Err(idx) => {
                // the idx is the place where a matching element could be inserted while maintaining
                // sorted order. go to left child
                (idx, None)
            }
        }
    }

    /// pop the last item, this is used when next sibling undersize
    pub(crate) fn pop(&mut self) -> (K, V) {
        debug_assert!(self.able_to_lend());
        let last_idx = self.size as usize - 1;
        let result = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.len()), last_idx);
            let v = utils::slice_remove(self.value_area_mut(..self.len()), last_idx);
            (k, v)
        };
        self.size -= 1;
        result
    }

    pub(crate) fn pop_front(&mut self) -> (K, V) {
        debug_assert!(self.able_to_lend());
        let result = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.size as usize), 0);
            let v = utils::slice_remove(self.value_area_mut(..self.size as usize), 0);
            (k, v)
        };
        self.size -= 1;
        result
    }

    // delete the item at idx and append the item to last
    pub(crate) fn delete_with_push(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        let result = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.size as usize), idx);
            let v = utils::slice_remove(self.value_area_mut(..self.size as usize), idx);
            (k, v)
        };
        unsafe {
            *self.key_area_mut(self.size as usize - 1) = MaybeUninit::new(item.0);
            *self.value_area_mut(self.size as usize - 1) = MaybeUninit::new(item.1);
        }
        result
    }

    // delete the item at idx and append the item to last
    pub(crate) fn delete_with_push_front(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        let k = std::mem::replace(&mut self.slot_key[idx], MaybeUninit::uninit());
        let v = std::mem::replace(&mut self.slot_value[idx], MaybeUninit::uninit());

        unsafe {
            utils::slice_insert(self.key_area_mut(..idx + 1), 0, item.0);
            utils::slice_insert(self.value_area_mut(..idx + 1), 0, item.1);
        }

        unsafe { (k.assume_init_read(), v.assume_init_read()) }
    }

    /// Delete the item at idx, then merge with right
    pub(crate) fn merge_with_right_with_delete(
        &mut self,
        delete_idx: usize,
        right: &mut Self,
    ) -> (K, V) {
        let k = std::mem::replace(
            unsafe { right.key_area_mut(delete_idx) },
            MaybeUninit::uninit(),
        );
        let v = std::mem::replace(
            unsafe { right.value_area_mut(delete_idx) },
            MaybeUninit::uninit(),
        );

        {
            let head = unsafe {
                (
                    right
                        .slot_key
                        .as_mut_slice()
                        .get_unchecked_mut(..delete_idx),
                    right
                        .slot_value
                        .as_mut_slice()
                        .get_unchecked_mut(..delete_idx),
                )
            };
            self.extend(head);
        }

        {
            let right_len = right.len();
            let tail = unsafe {
                (
                    right
                        .slot_key
                        .as_mut_slice()
                        .get_unchecked_mut(delete_idx + 1..right_len),
                    right
                        .slot_value
                        .as_mut_slice()
                        .get_unchecked_mut(delete_idx + 1..right_len),
                )
            };
            self.extend(tail);
        }

        self.next = right.next;

        unsafe { (k.assume_init_read(), v.assume_init_read()) }
    }

    /// Delete the item at idx, then merge with right
    pub(crate) fn merge_right(&mut self, right: &mut Self) {
        let right_len = right.len();
        let data = unsafe {
            // safety: right.len() is checked against right.len()
            (
                right.slot_key.as_mut_slice().get_unchecked_mut(..right_len),
                right
                    .slot_value
                    .as_mut_slice()
                    .get_unchecked_mut(..right_len),
            )
        };
        self.extend(data);

        self.next = right.next;
    }

    /// This should never called with same slot
    unsafe fn take_data(&mut self, slot: usize) -> (K, V) {
        debug_assert!(slot < self.len());

        // safety: slot is checked against self.len()
        unsafe {
            let k = self.key_area(slot).clone();
            let v = std::mem::replace(self.value_area_mut(slot), MaybeUninit::uninit());
            // special care must be taken to avoid double drop
            (k.assume_init_read(), v.assume_init_read())
        }
    }

    fn extend(&mut self, (keys, values): (&mut [MaybeUninit<K>], &mut [MaybeUninit<V>])) {
        unsafe {
            utils::move_to_slice(keys, self.key_area_mut(self.len()..self.len() + keys.len()));
            utils::move_to_slice(
                values,
                self.value_area_mut(self.len()..self.len() + values.len()),
            );
        }
        self.size += keys.len() as u16;
    }

    pub(crate) fn delete_at(&mut self, idx: usize) -> (K, V) {
        let result = unsafe {
            let k = utils::slice_remove(self.key_area_mut(..self.size as usize), idx);
            let v = utils::slice_remove(self.value_area_mut(..self.size as usize), idx);
            (k, v)
        };
        self.size -= 1;
        result
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

    unsafe fn value_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<V>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the value slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.slot_value.as_mut_slice().get_unchecked_mut(index) }
    }

    unsafe fn value_area<I, Output: ?Sized>(&self, index: I) -> &Output
    where
        I: SliceIndex<[MaybeUninit<V>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the value slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.slot_value.as_slice().get_unchecked(index) }
    }
}

pub enum LeafUpsertResult<V> {
    Inserted,
    Updated(V),
    IsFull(usize, V),
}

pub enum LeafDeleteResult<K, V> {
    /// Item not exists
    NotFound,
    /// Succeeded deleted
    Done((K, V)),
    /// Item exists, but not able to delete because a merge is required
    UnderSize(usize),
}

impl<K: Key, V: Value, const N: usize> super::LNode<K, V> for LeafNode<K, V, N> {
    fn new() -> Box<Self> {
        Self::new()
    }

    fn len(&self) -> usize {
        self.size as usize
    }

    fn prev(&self) -> Option<LeafNodeId> {
        self.prev
    }

    fn set_prev(&mut self, id: Option<LeafNodeId>) {
        Self::set_prev(self, id)
    }

    fn next(&self) -> Option<LeafNodeId> {
        self.next
    }

    fn set_next(&mut self, id: Option<LeafNodeId>) {
        Self::set_next(self, id)
    }

    fn set_data<const N1: usize>(&mut self, data: [(K, V); N1]) {
        Self::set_data(self, data)
    }

    fn data_at(&self, slot: usize) -> (&K, &V) {
        Self::data_at(self, slot)
    }

    fn is_full(&self) -> bool {
        LeafNode::is_full(self)
    }

    fn able_to_lend(&self) -> bool {
        LeafNode::able_to_lend(self)
    }

    fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<V> {
        LeafNode::try_upsert(self, k, v)
    }

    fn split_new_leaf(
        &mut self,
        insert_idx: usize,
        item: (K, V),
        new_leaf_id: LeafNodeId,
        self_leaf_id: LeafNodeId,
    ) -> Box<Self> {
        LeafNode::split_new_leaf(self, insert_idx, item, new_leaf_id, self_leaf_id)
    }

    fn try_data_at(&self, idx: usize) -> Option<(&K, &V)> {
        Self::try_data_at(self, idx)
    }

    fn locate_slot_with_value(&self, k: &K) -> (usize, Option<&V>) {
        Self::locate_child(self, k)
    }

    fn locate_slot(&self, k: &K) -> Result<usize, usize> {
        Self::locate_child_idx(&self, k)
    }

    fn locate_slot_mut(&mut self, k: &K) -> (usize, Option<&mut V>) {
        Self::locate_child_mut(self, k)
    }

    fn try_delete(&mut self, k: &K) -> LeafDeleteResult<K, V> {
        Self::delete(self, k)
    }

    fn delete_at(&mut self, idx: usize) -> (K, V) {
        Self::delete_at(self, idx)
    }

    fn delete_with_push_front(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        Self::delete_with_push_front(self, idx, item)
    }

    fn delete_with_push(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        Self::delete_with_push(self, idx, item)
    }

    fn merge_right_delete_first(&mut self, delete_idx_in_next: usize, right: &mut Self) -> (K, V) {
        Self::merge_with_right_with_delete(self, delete_idx_in_next, right)
    }

    fn merge_right(&mut self, right: &mut Self) {
        Self::merge_right(self, right)
    }

    fn pop(&mut self) -> (K, V) {
        Self::pop(self)
    }

    fn pop_front(&mut self) -> (K, V) {
        Self::pop_front(self)
    }

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = (&K, &V)> + 'a> {
        Box::new(LeafNode::iter(self))
    }

    #[inline(always)]
    fn in_range(&self, k: &K) -> bool {
        Self::in_range(self, k)
    }

    #[inline(always)]
    fn key_range(&self) -> (Option<K>, Option<K>) {
        Self::key_range(self)
    }

    unsafe fn take_data(&mut self, slot: usize) -> (K, V) {
        Self::take_data(self, slot)
    }

    fn set_data_by_iter(&mut self, data: &mut impl Iterator<Item = (K, V)>) {
        Self::set_data_by_iter(self, data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_leaf() {
        {
            let mut leaf = LeafNode::<i64, i64, 4>::new();
            leaf.set_data([(1, 0), (2, 0), (3, 0), (4, 0)]);

            let new_leaf = leaf.split_new_leaf(0, (0, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec(), vec![(0, 0), (1, 0), (2, 0)]);
            assert_eq!(new_leaf.data_vec(), vec![(3, 0), (4, 0)]);
        }

        {
            let mut leaf = LeafNode::<i64, i64, 4>::new();
            leaf.set_data([(0, 0), (2, 0), (3, 0), (4, 0)]);

            let new_leaf = leaf.split_new_leaf(1, (1, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec(), vec![(0, 0), (1, 0), (2, 0)]);
            assert_eq!(new_leaf.data_vec(), vec![(3, 0), (4, 0)]);
        }

        {
            let mut leaf = LeafNode::<i64, i64, 4>::new();
            leaf.set_data([(0, 0), (1, 0), (3, 0), (4, 0)]);

            let new_leaf = leaf.split_new_leaf(2, (2, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec(), vec![(0, 0), (1, 0)]);
            assert_eq!(new_leaf.data_vec(), vec![(2, 0), (3, 0), (4, 0)]);
        }

        {
            let mut leaf = LeafNode::<i64, i64, 4>::new();
            leaf.set_data([(0, 0), (1, 0), (2, 0), (4, 0)]);

            let new_leaf = leaf.split_new_leaf(3, (3, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec(), vec![(0, 0), (1, 0)]);
            assert_eq!(new_leaf.data_vec(), vec![(2, 0), (3, 0), (4, 0)]);
        }

        {
            let mut leaf = LeafNode::<i64, i64, 4>::new();
            leaf.set_data([(0, 0), (1, 0), (2, 0), (3, 0)]);

            let new_leaf = leaf.split_new_leaf(4, (4, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec(), vec![(0, 0), (1, 0)]);
            assert_eq!(new_leaf.data_vec(), vec![(2, 0), (3, 0), (4, 0)]);
        }
    }
}

use super::*;
use std::{
    alloc::{alloc, Layout},
    borrow::Borrow,
    mem::{self, MaybeUninit},
    slice::SliceIndex,
};

const N: usize = 64;

#[derive(Debug)]
pub struct LeafNode<K, V> {
    /// how many data items
    size: u16,
    slot_key: [MaybeUninit<K>; N],
    slot_value: [MaybeUninit<V>; N],

    prev: Option<LeafNodeId>,
    next: Option<LeafNodeId>,
}

impl<K: Key, V> Clone for LeafNode<K, V>
where
    V: Clone,
{
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
        let mut new_value = unsafe { MaybeUninit::<[MaybeUninit<V>; N]>::uninit().assume_init() };

        for i in 0..self.len() {
            unsafe {
                *new_value.get_unchecked_mut(i) =
                    MaybeUninit::new(self.value_area(i).assume_init_ref().clone());
            };
        }

        Self {
            size: self.size.clone(),
            slot_key: new_key,
            slot_value: new_value,
            prev: self.prev.clone(),
            next: self.next.clone(),
        }
    }
}

impl<K: Key, V> LeafNode<K, V> {
    pub fn new() -> Box<Self> {
        let layout = Layout::new::<mem::MaybeUninit<Self>>();
        let ptr: *mut Self = unsafe { alloc(layout).cast() };
        let mut this = unsafe { Box::from_raw(ptr) };

        this.prev = None;
        this.next = None;
        this.size = 0;

        this
    }

    pub fn len(&self) -> usize {
        self.size as usize
    }

    const fn split_origin_size() -> u16 {
        (N / 2) as u16
    }

    /// Returns the maximum capacity of the leaf node
    pub const fn max_capacity() -> u16 {
        N as u16
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

    pub fn in_range<Q: ?Sized>(&self, k: &Q) -> bool
    where
        Q: Ord,
        K: std::borrow::Borrow<Q>,
    {
        let is_lt_start = match self.prev {
            Some(_) => k.lt(unsafe { self.key_area(0).assume_init_ref().borrow() }),
            None => false,
        };
        if is_lt_start {
            return false;
        }
        let is_gt_end = match self.next {
            Some(_) => k.gt(unsafe { self.key_area(self.len() - 1).assume_init_ref().borrow() }),
            None => false,
        };
        !is_gt_end
    }

    pub fn key_range(&self) -> (Option<K>, Option<K>) {
        debug_assert!(self.len() > 0);
        let start = match self.prev {
            Some(_) => Some(unsafe { self.key_area(0).assume_init_ref().clone() }),
            None => None,
        };
        let end = match self.next {
            Some(_) => Some(unsafe { self.key_area(self.len() - 1).assume_init_ref().clone() }),
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

    pub fn prev(&self) -> Option<LeafNodeId> {
        self.prev
    }

    pub fn set_next(&mut self, id: Option<LeafNodeId>) {
        self.next = id;
    }

    pub fn next(&self) -> Option<LeafNodeId> {
        self.next
    }

    pub fn set_data(&mut self, data: impl IntoIterator<Item = (K, V)>) {
        let mut data = data.into_iter();
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

    pub fn data_at(&self, slot: usize) -> (&K, &V) {
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

    #[cfg(test)]
    fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        unsafe { self.key_area(..self.size as usize) }
            .iter()
            .zip(unsafe { self.value_area(..self.size as usize) })
            .map(|item| unsafe { (item.0.assume_init_ref(), item.1.assume_init_ref()) })
    }

    #[cfg(test)]
    pub(crate) fn data_vec(&self) -> Vec<(K, V)>
    where
        V: Clone,
    {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }

    /// insert / update (k, v), if node is full, then returns `LeafUpsertResult::IsFull`
    pub(crate) fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<K, V> {
        match self.locate_slot(&k) {
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
                    LeafUpsertResult::IsFull(idx, k, v)
                }
            }
        }
    }

    pub(crate) fn split_new_leaf(
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
    pub(crate) fn try_delete<Q: ?Sized + Ord>(&mut self, k: &Q) -> LeafDeleteResult<K, V>
    where
        K: Borrow<Q>,
    {
        match self.locate_slot(k) {
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
    pub fn locate_slot<Q: ?Sized>(&self, k: &Q) -> Result<usize, usize>
    where
        Q: Ord,
        K: std::borrow::Borrow<Q>,
    {
        self.keys().binary_search_by_key(&k, |f| f.borrow())
    }

    #[inline(always)]
    pub fn locate_slot_with_value<Q: ?Sized>(&self, k: &Q) -> (usize, Option<&V>)
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        match self.locate_slot(k) {
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

    pub(crate) fn locate_slot_mut<Q: ?Sized>(&mut self, k: &Q) -> (usize, Option<&mut V>)
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        match self.locate_slot(k) {
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
    pub(crate) fn merge_right_delete_first(
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
        right.size = 0;

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
        right.size = 0;
    }

    /// This should never called with same slot
    pub unsafe fn take_data(&mut self, slot: usize) -> (K, V) {
        debug_assert!(slot < self.len());

        // safety: slot is checked against self.len()
        unsafe {
            let k = std::mem::replace(self.key_area_mut(slot), MaybeUninit::uninit());
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

    pub fn keys(&self) -> &[K] {
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

pub enum LeafUpsertResult<K, V> {
    Inserted,
    Updated(V),
    IsFull(usize, K, V),
}

pub enum LeafDeleteResult<K, V> {
    /// Item not exists
    NotFound,
    /// Succeeded deleted
    Done((K, V)),
    /// Item exists, but not able to delete because a merge is required
    UnderSize(usize),
}

#[cfg(test)]
mod tests {
    use super::*;

    /// create a leaf with data [2, 4, 6..]
    fn test_leaf() -> Box<LeafNode<i64, i64>> {
        let mut leaf = LeafNode::<i64, i64>::new();
        leaf.set_data((0..N as i64).map(|i| ((i + 1) * 2, 0)).collect::<Vec<_>>());
        leaf
    }

    fn assert_ascend(data: Vec<(i64, i64)>) {
        for i in 0..data.len() - 1 {
            assert!(data[i].0 < data[i + 1].0);
        }
    }

    fn assert_ascend_2(mut data_0: Vec<(i64, i64)>, data_1: Vec<(i64, i64)>) {
        data_0.extend(data_1);
        assert_ascend(data_0);
    }

    #[test]
    fn test_split_leaf() {
        let split_left_size = LeafNode::<i64, i64>::split_origin_size() as usize;

        {
            let mut leaf = test_leaf();
            let new_leaf = leaf.split_new_leaf(0, (0, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec().len(), N / 2 + 1);
            assert_eq!(new_leaf.data_vec().len(), N / 2);
            assert_ascend_2(leaf.data_vec(), new_leaf.data_vec());
        }

        {
            let mut leaf = test_leaf();
            let new_leaf = leaf.split_new_leaf(1, (3, 0), LeafNodeId(2), LeafNodeId(1));

            assert_eq!(leaf.data_vec().len(), N / 2 + 1);
            assert_eq!(new_leaf.data_vec().len(), N / 2);
            assert_ascend_2(leaf.data_vec(), new_leaf.data_vec());
        }

        {
            let mut leaf = test_leaf();
            let new_leaf = leaf.split_new_leaf(
                split_left_size,
                (split_left_size as i64 * 2 + 1, 0),
                LeafNodeId(2),
                LeafNodeId(1),
            );

            assert_eq!(leaf.data_vec().len(), N / 2);
            assert_eq!(new_leaf.data_vec().len(), N / 2 + 1);
            assert_ascend_2(leaf.data_vec(), new_leaf.data_vec());
        }

        {
            // split at left half's last element
            let mut leaf = test_leaf();
            let new_leaf = leaf.split_new_leaf(
                split_left_size - 1,
                ((split_left_size - 1) as i64 * 2 + 1, 0),
                LeafNodeId(2),
                LeafNodeId(1),
            );

            assert_eq!(leaf.data_vec().len(), N / 2 + 1);
            assert_eq!(new_leaf.data_vec().len(), N / 2);
            assert_ascend_2(leaf.data_vec(), new_leaf.data_vec());
        }

        {
            // split at last
            let mut leaf = test_leaf();
            let new_leaf = leaf.split_new_leaf(
                N - 1,
                ((N as i64 - 1) * 2 + 1, 0),
                LeafNodeId(2),
                LeafNodeId(1),
            );

            assert_eq!(leaf.data_vec().len(), N / 2);
            assert_eq!(new_leaf.data_vec().len(), N / 2 + 1);
            assert_ascend_2(leaf.data_vec(), new_leaf.data_vec());
        }
    }
    #[test]
    fn test_in_range() {
        let mut leaf = test_leaf();
        // prev and next both none, so all keys should considered in range
        assert!(leaf.in_range(&0));
        assert!(leaf.in_range(&(129)));

        leaf.set_prev(Some(LeafNodeId(1)));
        // now had prev, so all keys less than min should be out of range
        assert!(!leaf.in_range(&0));
        assert!(leaf.in_range(&129));

        leaf.set_next(Some(LeafNodeId(2)));
        assert!(!leaf.in_range(&0));
        assert!(!leaf.in_range(&129));
    }
}

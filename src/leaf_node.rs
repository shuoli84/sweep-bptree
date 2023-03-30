use crate::*;
use std::{
    alloc::{alloc, Layout},
    mem::{self, MaybeUninit},
};

#[derive(Debug, Clone)]
pub struct LeafNode<K: Key, V: Value, const N: usize> {
    /// how many data items
    size: u16,
    slot_data: [MaybeUninit<(K, V)>; N],

    prev: Option<LeafNodeId>,
    next: Option<LeafNodeId>,
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

    pub fn is_full(&self) -> bool {
        self.size == N as u16
    }

    pub fn able_to_lend(&self) -> bool {
        self.size > Self::split_origin_size() as u16
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.slot_data[0..self.size as usize]
            .iter()
            .map(|item| unsafe { item.assume_init_ref() })
    }

    #[cfg(test)]
    pub(crate) fn data_vec(&self) -> Vec<(K, V)> {
        self.iter().cloned().collect()
    }

    /// insert / update (k, v), if node is full, then returns `LeafUpsertResult::IsFull`
    pub(crate) fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<V> {
        let size = self.size as usize;
        match self.slot_data[..size].binary_search_by_key(&k, |f| unsafe { f.assume_init_ref() }.0)
        {
            Ok(idx) => {
                // update existing item
                let prev_v = std::mem::replace(
                    unsafe { self.slot_data.as_mut_slice().get_unchecked_mut(idx) },
                    MaybeUninit::new((k, v)),
                );
                LeafUpsertResult::Updated(unsafe { prev_v.assume_init() }.1)
            }

            Err(idx) => {
                if !self.is_full() {
                    self.slot_data.copy_within(idx..size, idx + 1);
                    self.slot_data[idx] = MaybeUninit::new((k, v));
                    self.size += 1;
                    LeafUpsertResult::Inserted
                } else {
                    LeafUpsertResult::IsFull(idx)
                }
            }
        }
    }

    // todo: Self => Box
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
        let new_slot_data = &mut new_node.slot_data;

        new_slot_data[..split_new_size as usize]
            .copy_from_slice(&self.slot_data[split_origin_size..N]);

        let new_leaf_size = if insert_idx < split_origin_size {
            self.slot_data
                .copy_within(insert_idx..split_origin_size, insert_idx + 1);
            self.slot_data[insert_idx] = MaybeUninit::new(item);
            self.size = (split_origin_size + 1) as u16;

            split_new_size
        } else {
            // data insert to new/right
            let insert_idx = insert_idx - split_origin_size;

            new_slot_data.copy_within(insert_idx..split_new_size, insert_idx + 1);
            new_slot_data[insert_idx] = MaybeUninit::new(item);

            self.size = split_origin_size as u16;

            split_new_size + 1
        };

        self.next = Some(new_leaf_id);
        new_node.size = new_leaf_size as u16;

        new_node
    }

    /// Delete an item from LeafNode
    pub(crate) fn delete(&mut self, k: &K) -> LeafDeleteResult<K, V> {
        match self.locate_child_idx(k) {
            Ok(idx) => {
                if self.size > Self::split_origin_size() {
                    let result = std::mem::replace(&mut self.slot_data[idx], MaybeUninit::uninit());
                    self.slot_data.copy_within(idx + 1..self.size as usize, idx);
                    self.size -= 1;
                    LeafDeleteResult::Done(unsafe { result.assume_init() })
                } else {
                    LeafDeleteResult::UnderSize(idx)
                }
            }
            _ => LeafDeleteResult::NotFound,
        }
    }

    pub(crate) fn locate_child_idx(&self, k: &K) -> Result<usize, usize> {
        self.slot_data[0..self.len()].binary_search_by_key(k, |f| unsafe { f.assume_init_ref() }.0)
    }

    pub(crate) fn locate_child(&self, k: &K) -> (usize, Option<(&K, &V)>) {
        match self.slot_data[0..self.len()]
            .binary_search_by_key(k, |f| unsafe { f.assume_init_ref() }.0)
        {
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (idx, {
                    let kv = unsafe { self.slot_data[idx].assume_init_ref() };
                    Some((&kv.0, &kv.1))
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
        match self.slot_data[0..self.len()]
            .binary_search_by_key(k, |f| unsafe { f.assume_init_ref() }.0)
        {
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (
                    idx,
                    Some(unsafe { &mut self.slot_data[idx].assume_init_mut().1 }),
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
        assert!(self.size > Self::split_origin_size());
        let result = std::mem::replace(&mut self.slot_data[self.len() - 1], MaybeUninit::uninit());
        self.size -= 1;
        unsafe { result.assume_init() }
    }

    pub(crate) fn pop_front(&mut self) -> (K, V) {
        assert!(self.size > Self::split_origin_size());

        let result = std::mem::replace(&mut self.slot_data[0], MaybeUninit::uninit());
        self.slot_data.copy_within(1..self.size as usize, 0);
        self.size -= 1;
        unsafe { result.assume_init() }
    }

    // delete the item at idx and append the item to last
    pub(crate) fn delete_with_push(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        let result = std::mem::replace(&mut self.slot_data[idx], MaybeUninit::uninit());
        self.slot_data.copy_within(idx + 1..self.size as usize, idx);
        self.slot_data[self.len() - 1] = MaybeUninit::new(item);
        unsafe { result.assume_init() }
    }

    // delete the item at idx and append the item to last
    pub(crate) fn delete_with_push_front(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        // only called when this node is fit
        debug_assert!(self.size == Self::split_origin_size());

        let result = std::mem::replace(&mut self.slot_data[idx], MaybeUninit::uninit());
        self.slot_data.copy_within(0..idx, 1);
        self.slot_data[0] = MaybeUninit::new(item);
        unsafe { result.assume_init() }
    }

    pub(crate) fn split_at_idx(
        &mut self,
        idx: usize,
    ) -> (&[MaybeUninit<(K, V)>], (K, V), &[MaybeUninit<(K, V)>]) {
        let kv = std::mem::replace(&mut self.slot_data[idx], MaybeUninit::uninit());
        let head = &self.slot_data[0..idx];
        let tail = &self.slot_data[idx + 1..self.len()];

        (head, unsafe { kv.assume_init() }, tail)
    }

    /// Delete the item at idx, then merge with right
    pub(crate) fn merge_with_right_with_delete(
        &mut self,
        delete_idx: usize,
        right: &mut Self,
    ) -> (K, V) {
        let (head, kv, tail) = right.split_at_idx(delete_idx);
        self.extend(head);
        self.extend(tail);
        self.next = right.next;
        kv
    }

    /// Delete the item at idx, then merge with right
    pub(crate) fn merge_right(&mut self, right: &Self) {
        self.extend(right.data());
        self.next = right.next;
    }

    pub(crate) fn data(&self) -> &[MaybeUninit<(K, V)>] {
        &self.slot_data[0..self.len()]
    }

    pub(crate) fn extend(&mut self, data: &[MaybeUninit<(K, V)>]) {
        self.slot_data[self.size as usize..self.size as usize + data.len()].copy_from_slice(data);
        self.size += data.len() as u16;
    }

    pub(crate) fn delete_at(&mut self, idx: usize) -> (K, V) {
        let result = std::mem::replace(&mut self.slot_data[idx], MaybeUninit::uninit());
        self.slot_data.copy_within(idx + 1..self.size as usize, idx);
        self.size -= 1;
        unsafe { result.assume_init() }
    }
}

pub enum LeafUpsertResult<V> {
    Inserted,
    Updated(V),
    IsFull(usize),
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
    fn len(&self) -> usize {
        self.size as usize
    }

    fn prev(&self) -> Option<LeafNodeId> {
        self.prev
    }

    fn set_prev(&mut self, id: Option<LeafNodeId>) {
        self.prev = id;
    }

    fn next(&self) -> Option<LeafNodeId> {
        self.next
    }

    fn set_data<const N1: usize>(&mut self, data: [(K, V); N1]) {
        assert!(N1 <= N);
        self.size = N1 as u16;
        for i in 0..N1 {
            self.slot_data[i] = MaybeUninit::new(data[i]);
        }
    }

    fn data_at(&self, slot: usize) -> &(K, V) {
        unsafe { self.slot_data[slot].assume_init_ref() }
    }

    fn is_full(&self) -> bool {
        self.size == N as u16
    }

    fn able_to_lend(&self) -> bool {
        self.size > Self::split_origin_size()
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

    fn try_data_at(&self, idx: usize) -> Option<&(K, V)> {
        if idx >= self.size as usize {
            return None;
        }
        Some(unsafe { self.slot_data[idx].assume_init_ref() })
    }

    fn locate_slot_with_value(&self, k: &K) -> (usize, Option<(&K, &V)>) {
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

    fn merge_right(&mut self, right: &Self) {
        Self::merge_right(self, right)
    }

    fn pop(&mut self) -> (K, V) {
        Self::pop(self)
    }

    fn pop_front(&mut self) -> (K, V) {
        Self::pop_front(self)
    }

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &(K, V)> + 'a> {
        Box::new(LeafNode::iter(self))
    }

    fn key_range(&self) -> Option<(K, K)> {
        if self.size == 0 {
            return None;
        }
        Some((
            unsafe { self.slot_data[0].assume_init_ref() }.0,
            unsafe { self.slot_data[self.len() - 1].assume_init_ref() }.0,
        ))
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

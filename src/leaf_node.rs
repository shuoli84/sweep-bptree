use crate::*;

#[derive(Debug, Clone)]
pub struct LeafNode<K: Key, V: Value, const N: usize> {
    prev: Option<LeafNodeId>,
    next: Option<LeafNodeId>,
    /// how many data items
    size: usize,
    slot_data: [Option<(K, V)>; N],
}

impl<K: Key, V: Value, const N: usize> Default for LeafNode<K, V, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key, V: Value, const N: usize> LeafNode<K, V, N> {
    pub(crate) fn new() -> Self {
        LeafNode {
            prev: None,
            next: None,
            size: 0,
            slot_data: [None; N],
        }
    }

    const fn split_origin_size() -> usize {
        N / 2
    }

    pub fn is_full(&self) -> bool {
        self.size == N
    }

    pub fn able_to_lend(&self) -> bool {
        self.size > Self::split_origin_size()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.slot_data[0..self.size]
            .iter()
            .map(|item| item.as_ref().unwrap())
    }

    #[cfg(test)]
    pub(crate) fn data_vec(&self) -> Vec<(K, V)> {
        self.iter().cloned().collect()
    }

    /// insert / update (k, v), if node is full, then returns `LeafUpsertResult::IsFull`
    pub(crate) fn try_upsert(&mut self, k: K, v: V) -> LeafUpsertResult<V> {
        match self.slot_data[..self.size].binary_search_by_key(&k, |f| f.unwrap().0) {
            Ok(idx) => {
                // update existing item
                let prev_v = std::mem::replace(&mut self.slot_data[idx], Some((k, v)));
                LeafUpsertResult::Updated(prev_v.unwrap().1)
            }

            Err(idx) => {
                if !self.is_full() {
                    self.slot_data.copy_within(idx..self.size, idx + 1);
                    self.slot_data[idx] = Some((k, v));
                    self.size += 1;
                    LeafUpsertResult::Inserted
                } else {
                    LeafUpsertResult::IsFull(idx)
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
    ) -> Self {
        let split_origin_size = Self::split_origin_size();
        let split_new_size = N - split_origin_size;

        let prev_next = self.next;

        if insert_idx < split_origin_size {
            // data insert to origin/left
            let mut new_slot_data = [None; N];

            new_slot_data[..split_new_size].copy_from_slice(&self.slot_data[split_origin_size..N]);

            self.slot_data
                .copy_within(insert_idx..split_origin_size, insert_idx + 1);
            self.slot_data[insert_idx] = Some(item);
            self.size = split_origin_size + 1;
            self.next = Some(new_leaf_id);

            Self {
                prev: Some(self_leaf_id),
                next: prev_next,
                slot_data: new_slot_data,
                size: split_new_size,
            }
        } else {
            // data insert to new/right
            let insert_idx = insert_idx - split_origin_size;

            let mut new_slot_data = [None; N];
            new_slot_data[0..insert_idx].copy_from_slice(
                &self.slot_data[split_origin_size..split_origin_size + insert_idx],
            );
            new_slot_data[insert_idx] = Some(item);
            if insert_idx < split_new_size {
                new_slot_data[insert_idx + 1..split_new_size + 1]
                    .copy_from_slice(&self.slot_data[split_origin_size + insert_idx..N]);
            }

            self.next = Some(new_leaf_id);
            self.size = split_origin_size;

            Self {
                prev: Some(self_leaf_id),
                next: prev_next,
                slot_data: new_slot_data,
                size: N - split_origin_size + 1,
            }
        }
    }

    /// Delete an item from LeafNode
    pub(crate) fn delete(&mut self, k: &K) -> LeafDeleteResult<K, V> {
        let (idx, value) = self.locate_child(k);
        // return if k not exists
        if value.is_none() {
            return LeafDeleteResult::None;
        }

        let split_origin_size = Self::split_origin_size();
        if self.size > split_origin_size {
            let result = self.slot_data[idx].unwrap();
            self.slot_data.copy_within(idx + 1..self.size, idx);
            self.size -= 1;
            LeafDeleteResult::Done(result)
        } else {
            LeafDeleteResult::UnderSize(idx)
        }
    }

    pub(crate) fn locate_child(&self, k: &K) -> (usize, Option<&(K, V)>) {
        match self.slot_data[0..self.size].binary_search_by_key(k, |f| f.unwrap().0) {
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (idx, self.slot_data[idx].as_ref())
            }

            Err(idx) => {
                // the idx is the place where a matching element could be inserted while maintaining
                // sorted order. go to left child
                (idx, None)
            }
        }
    }

    pub(crate) fn locate_child_mut(&mut self, k: &K) -> (usize, Option<&mut V>) {
        match self.slot_data[0..self.size].binary_search_by_key(k, |f| f.unwrap().0) {
            Ok(idx) => {
                // exact match, go to right child.
                // if the child split, then the new key should inserted idx + 1
                (idx, self.slot_data[idx].as_mut().map(|x| &mut x.1))
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
        let result = std::mem::take(&mut self.slot_data[self.size - 1]).unwrap();
        self.size -= 1;
        result
    }

    pub(crate) fn pop_front(&mut self) -> (K, V) {
        assert!(self.size > Self::split_origin_size());

        let result = self.slot_data[0].unwrap();
        self.slot_data.copy_within(1..self.size, 0);
        self.size -= 1;
        result
    }

    // delete the item at idx and append the item to last
    pub(crate) fn delete_with_push(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        let result = self.slot_data[idx].unwrap();
        self.slot_data.copy_within(idx + 1..self.size, idx);
        self.slot_data[self.size - 1] = Some(item);
        result
    }

    // delete the item at idx and append the item to last
    pub(crate) fn delete_with_push_front(&mut self, idx: usize, item: (K, V)) -> (K, V) {
        // only called when this node is fit
        debug_assert!(self.size == Self::split_origin_size());

        let result = self.slot_data[idx].unwrap();
        self.slot_data.copy_within(0..idx, 1);
        self.slot_data[0] = Some(item);
        result
    }

    pub(crate) fn split_at_idx(
        &self,
        idx: usize,
    ) -> (&[Option<(K, V)>], (K, V), &[Option<(K, V)>]) {
        let head = &self.slot_data[0..idx];
        let tail = &self.slot_data[idx + 1..self.size];
        let kv = self.slot_data[idx].unwrap();

        (head, kv, tail)
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

    pub(crate) fn data(&self) -> &[Option<(K, V)>] {
        &self.slot_data[0..self.size]
    }

    pub(crate) fn extend(&mut self, data: &[Option<(K, V)>]) {
        self.slot_data[self.size..self.size + data.len()].copy_from_slice(data);
        self.size += data.len();
    }

    pub(crate) fn delete_at(&mut self, idx: usize) -> (K, V) {
        let result = self.slot_data[idx].unwrap();
        self.slot_data.copy_within(idx + 1..self.size, idx);
        self.size -= 1;
        result
    }
}

pub enum LeafUpsertResult<V> {
    Inserted,
    Updated(V),
    IsFull(usize),
}

pub enum LeafDeleteResult<K, V> {
    /// Item not exists
    None,
    /// Succeeded deleted
    Done((K, V)),
    /// Item exists, but not able to delete because a merge is required
    UnderSize(usize),
}

impl<K: Key, V: Value, const N: usize> super::LNode<K, V> for LeafNode<K, V, N> {
    fn len(&self) -> usize {
        self.size
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
        self.size = N1;
        for i in 0..N1 {
            self.slot_data[i] = Some(data[i]);
        }
    }

    fn data_at(&self, slot: usize) -> &(K, V) {
        self.slot_data[slot].as_ref().unwrap()
    }

    fn is_full(&self) -> bool {
        self.size == N
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
    ) -> Self {
        LeafNode::split_new_leaf(self, insert_idx, item, new_leaf_id, self_leaf_id)
    }

    fn try_data_at(&self, idx: usize) -> Option<&(K, V)> {
        if idx >= self.size {
            return None;
        }
        self.slot_data[idx].as_ref()
    }

    fn locate_slot(&self, k: &K) -> (usize, Option<&(K, V)>) {
        Self::locate_child(self, k)
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

    fn key_range(&self) -> (K, K) {
        (
            self.slot_data[0].as_ref().unwrap().0,
            self.slot_data[self.size - 1].as_ref().unwrap().0,
        )
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

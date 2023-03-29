use crate::*;

#[derive(Debug, Clone, Copy)]
pub struct InnerNode<K: Key, const N: usize, const C: usize> {
    size: usize,

    slot_key: [Option<K>; N],
    child_id: [Option<NodeId>; C],
}

impl<K: Key, const N: usize, const C: usize> Default for InnerNode<K, N, C> {
    fn default() -> Self {
        Self {
            size: 0,
            slot_key: [None; N],
            child_id: [None; C],
        }
    }
}

impl<K: Key, const N: usize, const C: usize> InnerNode<K, N, C> {
    pub const fn split_origin_size() -> usize {
        N / 2
    }

    pub const fn split_new_size() -> usize {
        N - Self::split_origin_size()
    }

    pub(crate) fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) -> Self {
        // not sure how to do a constrain in compile time, just put a debug assert here.
        debug_assert!(C == N + 1);

        let mut result = Self::default();
        result.set_data(slot_keys, child_id);
        result
    }

    pub(crate) fn set_data<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        &mut self,
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) {
        assert!(N1 + 1 == C1);
        assert!(N1 <= N);
        self.size = N1;
        for i in 0..N1 {
            self.slot_key[i] = Some(slot_keys[i]);
        }

        for c in 0..C1 {
            self.child_id[c] = Some(child_id[c].into());
        }
    }

    /// whether this node is full, if yes, then the next insert need to split
    pub fn is_full(&self) -> bool {
        self.size == N
    }

    /// whether this node able to lend
    pub fn able_to_lend(&self) -> bool {
        self.size > Self::split_origin_size()
    }

    const fn binary_search_threshold() -> usize {
        128 / std::mem::size_of::<K>()
    }

    /// returns the child index for k
    pub(crate) fn locate_child(&self, k: &K) -> (usize, NodeId) {
        if self.size > Self::binary_search_threshold() {
            match self.slot_key[0..self.size].binary_search_by_key(k, |f| f.unwrap()) {
                Err(idx) => {
                    // the idx is the place where a matching element could be inserted while maintaining
                    // sorted order. go to left child
                    (idx, self.child_id[idx].unwrap())
                }
                Ok(idx) => {
                    // exact match, go to right child.
                    // if the child split, then the new key should inserted idx + 1
                    (idx + 1, self.child_id[idx + 1].unwrap())
                }
            }
        } else {
            assert!(self.size <= N);

            for i in 0..self.size {
                match self.slot_key[i].unwrap().cmp(k) {
                    std::cmp::Ordering::Less => continue,
                    std::cmp::Ordering::Equal => return (i + 1, self.child_id[i + 1].unwrap()),
                    std::cmp::Ordering::Greater => return (i, self.child_id[i].unwrap()),
                }
            }
            return (self.size, self.child_id[self.size].unwrap());
        }
    }

    pub(crate) fn iter_key(&self) -> impl Iterator<Item = &K> {
        self.slot_key[0..self.size]
            .iter()
            .map(|s| s.as_ref().unwrap())
    }

    pub(crate) fn iter_child(&self) -> impl Iterator<Item = NodeId> + '_ {
        let slice = if self.size > 0 {
            &self.child_id[0..self.size + 1]
        } else {
            &self.child_id[..0]
        };

        slice.iter().map(|s| s.unwrap())
    }

    /// Insert `key` and its `right_child` to `slot`
    pub(crate) fn insert_at(&mut self, slot: usize, key: K, right_child: NodeId) {
        debug_assert!(slot <= self.size);

        // insert_at may insert right at last item
        if slot < self.size {
            self.slot_key.copy_within(slot..self.size, slot + 1);
            self.child_id.copy_within(slot + 1..self.size + 1, slot + 2);
        }

        self.slot_key[slot] = Some(key);
        self.child_id[slot + 1] = Some(right_child);
        self.size += 1;
    }

    /// Split the node
    /// modified node, it contains smaller half
    /// new node, it contains larger half
    /// new key, it is the key need to propagate to parent
    pub(crate) fn split(&mut self, child_idx: usize, k: K, new_child_id: NodeId) -> (K, Self) {
        debug_assert!(self.is_full());

        let mut new_slot_keys = [None; N];
        let mut new_child_ids = [None; C];
        let new_key: K;

        let split_origin_size = Self::split_origin_size();
        let split_new_size = Self::split_new_size();

        self.size = split_origin_size;

        if child_idx < split_origin_size {
            // take node_size 4 as example
            // new key 2, new node n
            //      1, 3, 4, 5
            //     a, b, c, d, e
            // =>        3
            //     1, 2      4, 5
            //    a  b  n   c   d  e

            new_key = self.slot_key[split_origin_size - 1].unwrap();

            new_slot_keys[0..split_new_size].copy_from_slice(&self.slot_key[split_origin_size..N]);
            new_child_ids[0..split_new_size + 1]
                .copy_from_slice(&self.child_id[split_new_size..N + 1]);

            // assign the key to slot
            self.slot_key
                .copy_within(child_idx..self.size, child_idx + 1);
            self.slot_key[child_idx] = Some(k);
            self.child_id
                .copy_within(child_idx + 1..self.size + 2, child_idx + 2);
            self.child_id[child_idx + 1] = Some(new_child_id);
        } else if child_idx > split_origin_size {
            // new key 4, new node n
            //      1, 2, 3, 5
            //     a, b, c, d, e
            // =>        3
            //     1, 2      4, 5
            //    a  b  c   d   n  e

            let prompt_key_index = split_origin_size;
            new_key = self.slot_key[prompt_key_index].unwrap();

            let new_slot_idx = child_idx - 1 - split_origin_size;
            let new_child_idx = child_idx - split_new_size;

            new_slot_keys[0..new_slot_idx].copy_from_slice(
                &self.slot_key[prompt_key_index + 1..prompt_key_index + new_slot_idx + 1],
            );
            new_child_ids[0..new_child_idx].copy_from_slice(
                &self.child_id[split_new_size + 1..split_new_size + 1 + new_child_idx],
            );
            new_slot_keys[new_slot_idx] = Some(k);
            new_child_ids[new_child_idx] = Some(new_child_id);

            new_slot_keys[new_slot_idx + 1..split_new_size]
                .copy_from_slice(&self.slot_key[prompt_key_index + new_slot_idx + 1..N]);
            new_child_ids[new_child_idx + 1..split_new_size + 1]
                .copy_from_slice(&self.child_id[split_new_size + 1 + new_child_idx..N + 1]);
        } else {
            // new key 3, new node n
            //      1, 2, 4, 5
            //     a, b, c, d, e
            // =>        3
            //     1, 2      4, 5
            //    a  b  c   n   d  e
            new_key = k;

            new_slot_keys[0..split_new_size].copy_from_slice(&self.slot_key[split_new_size..N]);
            new_child_ids[1..split_new_size + 1]
                .copy_from_slice(&self.child_id[split_new_size + 1..N + 1]);
            new_child_ids[0] = Some(new_child_id);
        }

        (
            new_key,
            Self {
                slot_key: new_slot_keys,
                child_id: new_child_ids,
                size: Self::split_new_size(),
            },
        )
    }

    /// merge child identified by `smaller_idx` and `smaller_idx + 1`
    pub(crate) fn merge_child(&mut self, slot: usize) -> InnerMergeResult {
        self.slot_key.copy_within(slot + 1..self.size, slot);
        self.child_id.copy_within(slot + 2..self.size + 1, slot + 1);
        self.size -= 1;

        if self.size >= Self::split_origin_size() {
            InnerMergeResult::Done
        } else {
            // the undersized inner node will be fixed by parent node
            InnerMergeResult::UnderSize
        }
    }

    pub(crate) fn merge_next(&mut self, slot_key: K, right: &Self) {
        self.slot_key[self.size] = Some(slot_key);
        self.size += 1;
        self.slot_key[self.size..N].copy_from_slice(&right.slot_key[..right.size]);
        self.child_id[self.size..N + 1].copy_from_slice(&right.child_id[..right.size + 1]);
        self.size += right.size;
    }

    pub(crate) fn shift_left(&mut self) {
        self.slot_key.copy_within(1..self.size, 0);
        self.child_id.copy_within(1..self.size + 1, 0);
    }

    /// pop the last key and right child
    pub(crate) fn pop(&mut self) -> (K, NodeId) {
        let k = self.slot_key[self.size - 1].unwrap();
        let child = self.child_id[self.size].unwrap();
        self.size -= 1;
        (k, child)
    }

    pub(crate) fn pop_front(&mut self) -> (K, NodeId) {
        let k = self.slot_key[0].unwrap();
        let child = self.child_id[0].unwrap();
        self.shift_left();
        self.size -= 1;
        (k, child)
    }

    pub fn push(&mut self, k: K, child: NodeId) {
        self.slot_key[self.size] = Some(k);
        self.child_id[self.size + 1] = Some(child);
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
}

impl<K: Key, const N: usize, const C: usize> super::INode<K> for InnerNode<K, N, C> {
    fn new<I: Into<NodeId> + Copy + Clone, const N1: usize, const C1: usize>(
        slot_keys: [K; N1],
        child_id: [I; C1],
    ) -> Self {
        Self::new(slot_keys, child_id)
    }

    fn size(&self) -> usize {
        self.size
    }

    fn key(&self, idx: usize) -> &K {
        self.slot_key[idx].as_ref().unwrap()
    }

    fn set_key(&mut self, idx: usize, key: K) {
        self.slot_key[idx] = Some(key);
    }

    fn child_id_at(&self, idx: usize) -> NodeId {
        self.child_id[idx].unwrap()
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

    fn split(&mut self, child_idx: usize, k: K, new_child_id: NodeId) -> (K, Self) {
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
        self.slot_key.copy_within(0..self.size, 1);
        self.child_id.copy_within(0..self.size + 1, 1);
        self.slot_key[0] = Some(k);
        self.child_id[0] = Some(child);
        self.size += 1;
    }

    fn merge_next(&mut self, slot_key: K, right: &Self) {
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
        let mut inner_node = InnerNode::default();

        inner_node.set_data(
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
        assert_eq!(new_node.slot_key, [Some(4), Some(5), None, None]);
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
        let mut inner_node = InnerNode::default();

        inner_node.set_data(
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
        assert_eq!(new_node.size, InnerNode::split_new_size());
        assert_eq!(inner_node.size, InnerNode::split_origin_size());
        assert_eq!(k, 3);
        assert_eq!(inner_node.slot_key, [Some(1), Some(2), None, None]);
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
        let mut inner_node = InnerNode::default();

        inner_node.set_data(
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
        assert_eq!(inner_node.size, InnerNode::split_origin_size());
        assert_eq!(new_node.size, InnerNode::split_new_size());
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
        let mut inner_node = InnerNode::default();

        inner_node.set_data(
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
        assert_eq!(inner_node.size, InnerNode::split_origin_size());
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

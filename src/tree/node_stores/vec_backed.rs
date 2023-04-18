use crate::tree::{
    visit_stack::VisitStack, InnerNode, InnerNodeId, Key, LeafNode, LeafNodeId, NodeStore,
};

#[derive(Debug)]
pub struct NodeStoreVec<K: Key, V, const IN: usize, const IC: usize, const LN: usize> {
    inner_nodes: Vec<Option<Box<InnerNode<K, usize, IN, IC>>>>,
    leaf_nodes: Vec<Option<Box<LeafNode<K, V, LN>>>>,

    cached_leaf: std::sync::atomic::AtomicUsize,
}

impl<K: Key, V: Clone, const IN: usize, const IC: usize, const LN: usize> Clone
    for NodeStoreVec<K, V, IN, IC, LN>
{
    fn clone(&self) -> Self {
        Self {
            inner_nodes: self.inner_nodes.clone(),
            leaf_nodes: self.leaf_nodes.clone(),
            cached_leaf: std::sync::atomic::AtomicUsize::new(
                self.cached_leaf.load(std::sync::atomic::Ordering::Relaxed),
            ),
        }
    }
}

impl<K: Key, V, const IN: usize, const IC: usize, const LN: usize> Default
    for NodeStoreVec<K, V, IN, IC, LN>
{
    fn default() -> Self {
        assert!(IN == IC - 1);

        Self {
            inner_nodes: Default::default(),
            leaf_nodes: Default::default(),
            cached_leaf: std::sync::atomic::AtomicUsize::new(usize::MAX),
        }
    }
}

impl<K: Key, V, const IN: usize, const IC: usize, const LN: usize> NodeStoreVec<K, V, IN, IC, LN> {
    /// Create a new `NodeStoreVec`
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new `NodeStoreVec` with capacity
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            inner_nodes: Vec::with_capacity(cap),
            leaf_nodes: Vec::with_capacity(cap),
            ..Self::default()
        }
    }

    /// Print nodes, used in test only
    #[cfg(test)]
    pub fn print(&self)
    where
        K: std::fmt::Debug,
        V: std::fmt::Debug + Clone,
    {
        use crate::tree::{INode, LNode};

        for (idx, inner) in self.inner_nodes.iter().flatten().enumerate() {
            println!(
                "inner: {idx} s:{} key: {:?} child: {:?}",
                inner.len(),
                inner.key_vec(),
                inner.child_id_vec()
            );
        }

        for (idx, leaf) in self.leaf_nodes.iter().flatten().enumerate() {
            println!(
                "leaf: {idx} p:{:?} n:{:?} items:{:?}",
                leaf.prev()
                    .map(|l| l.as_usize().to_string())
                    .unwrap_or("-".to_string()),
                leaf.next()
                    .map(|l| l.as_usize().to_string())
                    .unwrap_or("-".to_string()),
                leaf.data_vec()
                    .iter()
                    .map(|kv| kv.0.clone())
                    .collect::<Vec<_>>()
            );
        }
    }
}

impl<K: Key, V, const IN: usize, const IC: usize, const LN: usize> NodeStore
    for NodeStoreVec<K, V, IN, IC, LN>
{
    type K = K;
    type V = V;
    type InnerNode = InnerNode<K, usize, IN, IC>;
    type LeafNode = LeafNode<K, V, LN>;
    type VisitStack = VisitStack<64>; // use 64 as default, which is the maximum possible value

    fn inner_n() -> u16 {
        IN as u16
    }

    fn leaf_n() -> u16 {
        LN as u16
    }

    #[cfg(test)]
    fn debug(&self)
    where
        K: std::fmt::Debug,
        V: std::fmt::Debug + Clone,
    {
        self.print()
    }

    #[cfg(test)]
    fn new_empty_inner(&mut self) -> InnerNodeId {
        let id = InnerNodeId::from_usize(self.inner_nodes.len());
        let node = Self::InnerNode::empty();
        self.inner_nodes.push(Some(node));
        id
    }

    fn new_empty_leaf(&mut self) -> (LeafNodeId, &mut Self::LeafNode) {
        let id = LeafNodeId::from_usize(self.leaf_nodes.len());
        let node = Self::LeafNode::new();
        self.leaf_nodes.push(Some(node));
        (id, self.get_mut_leaf(id))
    }

    fn add_inner(&mut self, node: Box<Self::InnerNode>) -> InnerNodeId {
        let id = InnerNodeId::from_usize(self.inner_nodes.len());
        self.inner_nodes.push(Some(node));
        id
    }

    #[inline(always)]
    fn get_inner(&self, id: InnerNodeId) -> &Self::InnerNode {
        // need to ensure the output assmebly are two ldr only, the two unsafe is the only way to do it.

        // SAFETY: id is only used in btree impl, and it is always valid
        unsafe {
            self.inner_nodes
                .get_unchecked(id.as_usize())
                .as_ref()
                .unwrap_or_else(|| std::hint::unreachable_unchecked())
        }
    }

    fn try_get_inner(&self, id: InnerNodeId) -> Option<&Self::InnerNode> {
        let node = self.inner_nodes.get(id.as_usize())?.as_ref()?;
        Some(node)
    }

    #[inline(always)]
    fn get_mut_inner(&mut self, id: InnerNodeId) -> &mut Self::InnerNode {
        // need to ensure the output assmebly are two ldr only, the two unsafe is the only way to do it.

        // SAFETY: id is only used in btree impl, and it is always valid
        unsafe {
            self.inner_nodes
                .get_unchecked_mut(id.as_usize())
                .as_mut()
                .unwrap_or_else(|| std::hint::unreachable_unchecked())
        }
    }

    fn take_inner(&mut self, id: InnerNodeId) -> Box<Self::InnerNode> {
        std::mem::take(&mut self.inner_nodes[id.as_usize()]).unwrap()
    }

    fn put_back_inner(&mut self, id: InnerNodeId, node: Box<Self::InnerNode>) {
        self.inner_nodes[id.as_usize()] = Some(node);
    }

    fn reserve_leaf(&mut self) -> LeafNodeId {
        let id = LeafNodeId::from_usize(self.leaf_nodes.len());
        self.leaf_nodes.push(None);
        id
    }

    #[inline(always)]
    fn get_leaf(&self, id: LeafNodeId) -> &Self::LeafNode {
        // need to ensure the output assmebly are two ldr only, the two unsafe is the only way to do it.

        // SAFETY: id is only used in btree impl, we need to ensure that the id is valid.
        unsafe {
            self.leaf_nodes
                .get_unchecked(id.as_usize())
                .as_ref()
                .unwrap_or_else(|| std::hint::unreachable_unchecked())
        }
    }

    fn try_get_leaf(&self, id: LeafNodeId) -> Option<&Self::LeafNode> {
        let leaf_node = self.leaf_nodes.get(id.as_usize())?.as_ref()?;
        Some(leaf_node)
    }

    #[inline(always)]
    fn get_mut_leaf(&mut self, id: LeafNodeId) -> &mut Self::LeafNode {
        // SAFETY: id is only used in btree impl, we need to ensure that the id is valid.
        unsafe {
            self.leaf_nodes
                .get_unchecked_mut(id.as_usize())
                .as_mut()
                .unwrap_or_else(|| std::hint::unreachable_unchecked())
        }
    }

    fn take_leaf(&mut self, id: LeafNodeId) -> Box<Self::LeafNode> {
        std::mem::take(&mut self.leaf_nodes[id.as_usize()]).unwrap()
    }

    fn assign_leaf(&mut self, id: LeafNodeId, leaf: Box<Self::LeafNode>) {
        self.leaf_nodes[id.as_usize()] = Some(leaf);
    }

    #[inline(always)]
    unsafe fn get_mut_inner_ptr(&mut self, id: InnerNodeId) -> *mut Self::InnerNode {
        // need to ensure the output assmebly are two ldr only, the two unsafe is the only way to do it.

        // SAFETY: id is only used in btree impl, we need to ensure that the id is valid.
        unsafe {
            self.inner_nodes
                .get_unchecked_mut(id.as_usize())
                .as_mut()
                .unwrap_or_else(|| std::hint::unreachable_unchecked())
                .as_mut() as *mut Self::InnerNode
        }
    }

    fn cache_leaf(&self, leaf_id: LeafNodeId) {
        self.cached_leaf
            .store(leaf_id.as_usize(), std::sync::atomic::Ordering::Relaxed);
    }

    fn try_cache<Q: ?Sized>(&self, k: &Q) -> Option<LeafNodeId>
    where
        Q: Ord,
        Self::K: std::borrow::Borrow<Q>,
    {
        let leaf_id = self.cached_leaf.load(std::sync::atomic::Ordering::Relaxed);
        let leaf_id = LeafNodeId(leaf_id);
        // try_get_leaf returns None for usize:MAX, so we don't need to handle it explicitly
        if self
            .try_get_leaf(leaf_id)
            .map(|l| l.in_range(k))
            .unwrap_or_default()
        {
            Some(leaf_id)
        } else {
            None
        }
    }
}

/// ensure NodeStoreVec is send for send v
fn _ensure_send<V: Send>() {
    fn _assert_send<T: Send>() {}
    _assert_send::<NodeStoreVec<u64, V, 4, 5, 4>>();
}

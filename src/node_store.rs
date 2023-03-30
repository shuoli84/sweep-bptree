use crate::{INode, InnerNode, InnerNodeId, Key, LNode, LeafNode, LeafNodeId, NodeStore, Value};

#[derive(Debug, Clone)]
pub struct NodeStoreVec<K: Key, V: Value, const IN: usize, const IC: usize, const LN: usize> {
    inner_nodes: Vec<Option<Box<InnerNode<K, IN, IC>>>>,
    leaf_nodes: Vec<Option<Box<LeafNode<K, V, LN>>>>,
}

impl<K: Key, V: Value, const IN: usize, const IC: usize, const LN: usize>
    NodeStoreVec<K, V, IN, IC, LN>
{
    /// Create a new `NodeStoreVec`
    pub fn new() -> Self {
        Self {
            inner_nodes: Vec::with_capacity(128),
            leaf_nodes: Vec::with_capacity(128),
        }
    }

    pub fn print(&self) {
        for (idx, inner) in self.inner_nodes.iter().flatten().enumerate() {
            println!(
                "inner: {idx} s:{} key: {:?} child: {:?}",
                inner.size(),
                inner.iter_key().collect::<Vec<_>>(),
                inner.iter_child().collect::<Vec<_>>()
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
        let node = Self::InnerNode::empty();
        self.inner_nodes.push(Some(node));
        id
    }

    fn add_inner(&mut self, node: Box<Self::InnerNode>) -> InnerNodeId {
        let id = InnerNodeId::from_usize(self.inner_nodes.len());
        self.inner_nodes.push(Some(node));
        id
    }

    fn get_inner(&self, id: InnerNodeId) -> &Self::InnerNode {
        &self.inner_nodes[id.as_usize()].as_ref().unwrap()
    }

    fn try_get_inner(&self, id: InnerNodeId) -> Option<&Self::InnerNode> {
        let node = self.inner_nodes.get(id.as_usize())?.as_ref()?;
        Some(node)
    }

    fn get_mut_inner(&mut self, id: InnerNodeId) -> &mut Self::InnerNode {
        self.inner_nodes[id.as_usize()].as_mut().unwrap()
    }

    fn reserve_leaf(&mut self) -> LeafNodeId {
        let id = LeafNodeId::from_u32(self.leaf_nodes.len());
        self.leaf_nodes.push(None);
        id
    }

    fn create_leaf(&mut self) -> (LeafNodeId, &mut Self::LeafNode) {
        let id = LeafNodeId::from_u32(self.leaf_nodes.len());
        let node = Self::LeafNode::new();
        self.leaf_nodes.push(Some(node));
        (id, self.get_mut_leaf(id))
    }

    fn get_leaf(&self, id: LeafNodeId) -> &Self::LeafNode {
        &self.leaf_nodes[id.as_usize()].as_ref().unwrap()
    }

    fn try_get_leaf(&self, id: LeafNodeId) -> Option<&Self::LeafNode> {
        let leaf_node = self.leaf_nodes.get(id.as_usize())?.as_ref()?;
        if leaf_node.len() == 0 {
            None
        } else {
            Some(leaf_node)
        }
    }

    fn get_mut_leaf(&mut self, id: LeafNodeId) -> &mut Self::LeafNode {
        self.leaf_nodes[id.as_usize()].as_mut().unwrap()
    }

    fn debug(&self) {
        self.print()
    }

    fn take_leaf(&mut self, id: LeafNodeId) -> Box<Self::LeafNode> {
        std::mem::take(&mut self.leaf_nodes[id.as_usize()]).unwrap()
    }

    fn assign_leaf(&mut self, id: LeafNodeId, leaf: Box<Self::LeafNode>) {
        self.leaf_nodes[id.as_usize()] = Some(leaf);
    }

    fn take_inner(&mut self, id: InnerNodeId) -> Box<Self::InnerNode> {
        std::mem::take(&mut self.inner_nodes[id.as_usize()]).unwrap()
    }
}

use crate::NodeStore;

pub enum DescendVisitResult<R> {
    /// Go down to index
    GoDown(usize),
    Cancel,
    /// The visit is completed, R will be returned
    /// This is used in cases that the result can be determined by inner layer.
    Complete(R),
}

/// This kind visit is used to visit the tree from root to leaf, each layer visit one node.
/// Mainly used as search like visit. Each inner node will returns at most one child to visit.
/// Time complexity for this visit is log(n)
pub trait DescendVisit<K, V, A> {
    type Result;

    fn visit_inner(&mut self, keys: &[K], arguments: &[A]) -> DescendVisitResult<Self::Result>;
    fn visit_leaf(&mut self, keys: &[K], values: &[V]) -> Option<Self::Result>;
}

impl<S: NodeStore> super::BPlusTree<S> {
    pub fn descend_visit<V>(&self, mut v: V) -> Option<V::Result>
    where
        V: DescendVisit<S::K, S::V, S::Argument>,
    {
        let mut node_id = self.root;
        loop {
            match node_id {
                super::NodeId::Inner(inner_id) => {
                    let inner = self.node_store.get_inner(inner_id);

                    match v.visit_inner(inner.keys(), inner.arguments()) {
                        DescendVisitResult::GoDown(child_idx) => {
                            if child_idx >= inner.len() + 1 {
                                panic!("invalid index");
                            }
                            let child_id = inner.child_id(child_idx);

                            node_id = child_id;
                        }
                        DescendVisitResult::Cancel => {
                            return None;
                        }
                        DescendVisitResult::Complete(r) => {
                            return Some(r);
                        }
                    }
                }
                super::NodeId::Leaf(leaf_id) => {
                    let leaf = self.node_store.get_leaf(leaf_id);
                    return v.visit_leaf(leaf.keys(), leaf.values());
                }
            }
        }
    }
}

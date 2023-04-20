use super::{Argumentation, INode, LeafNode, LeafNodeId, NodeId, NodeStore};

impl<S: NodeStore> crate::BPlusTree<S> {
    /// bulk load data into a new `BPlusTree`, the loaded tree's leaf with fill rate 1.0
    pub fn bulk_load(data: Vec<(S::K, S::V)>) -> Self {
        let mut node_store = S::default();

        if !data.is_empty() {
            let item_count = data.len();
            let leaf_count = item_count / S::leaf_n() as usize
                + (item_count % S::leaf_n() as usize != 0) as usize;
            let leaf_ids = (0..leaf_count)
                .map(|_| node_store.reserve_leaf())
                .collect::<Vec<LeafNodeId>>();

            let mut data_iter = data.into_iter();
            let mut nodes: Vec<(NodeId, (Option<S::K>, Option<S::K>), S::Argument)> =
                Vec::with_capacity(leaf_ids.len());

            for (idx, leaf_id) in leaf_ids.iter().enumerate() {
                let prev_id = if idx > 0 {
                    Some(leaf_ids[idx - 1])
                } else {
                    None
                };
                let next_id = if idx < leaf_ids.len() - 1 {
                    Some(leaf_ids[idx + 1])
                } else {
                    None
                };

                let mut leaf = LeafNode::<S::K, S::V>::new();

                leaf.set_data(&mut data_iter);
                leaf.set_prev(prev_id);
                leaf.set_next(next_id);

                nodes.push((
                    NodeId::Leaf(*leaf_id),
                    leaf.key_range(),
                    S::Argument::from_leaf(leaf.keys()),
                ));

                node_store.assign_leaf(*leaf_id, leaf);
            }

            let root_id = Self::build_inner_layer(&mut node_store, nodes);

            Self::new_from_parts(node_store, root_id, item_count)
        } else {
            Self::new(node_store)
        }
    }

    /// build an inner node layer for all `nodes`
    /// Returns the root id
    fn build_inner_layer(
        node_store: &mut S,
        nodes: Vec<(NodeId, (Option<S::K>, Option<S::K>), S::Argument)>,
    ) -> NodeId {
        assert!(!nodes.is_empty());

        if nodes.len() == 1 {
            return nodes[0].0;
        }

        let child_n = S::inner_n() as usize + 1;

        // each node is a child
        let node_num = nodes.len() / child_n + (nodes.len() % child_n > 0) as usize;

        let mut chunk_iter = nodes.chunks(child_n);

        let mut nodes: Vec<(NodeId, (Option<S::K>, Option<S::K>), S::Argument)> =
            Vec::with_capacity(node_num);

        for _ in 0..node_num {
            let childs = chunk_iter.next().unwrap();
            let start_key = childs[0].1 .0.clone();
            let end_key = childs[childs.len() - 1].1 .0.clone();

            let keys_iter = childs.iter().skip(1).map(|(_, (start_key, _), _)| {
                start_key.clone().expect("the first leaf is skipped")
            });
            let childs_iter = childs.iter().map(|(child, _, _)| *child);
            let child_argument_iter = childs.iter().map(|(_, _, m)| m.clone());

            let inner = S::InnerNode::new_from_iter(keys_iter, childs_iter, child_argument_iter);
            let argument = S::Argument::from_inner(inner.keys(), inner.arguments());
            let node_id = node_store.add_inner(inner);

            nodes.push((NodeId::Inner(node_id), (start_key, end_key), argument));
        }

        Self::build_inner_layer(node_store, nodes)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_bulk_load() {
        type Tree = BPlusTree<NodeStoreVec<i32, i32, 4, 5>>;
        let data = (0..400).map(|i| (i, i * 2)).collect::<Vec<_>>();
        let loaded_tree = Tree::bulk_load(data.clone());
        let mut inserted_tree = Tree::new(NodeStoreVec::default());
        for (k, v) in data.clone().into_iter() {
            inserted_tree.insert(k, v);
        }
        assert_eq!(loaded_tree.len(), inserted_tree.len());

        for (k, v) in &data {
            assert_eq!(loaded_tree.get(k).unwrap(), v);
        }

        let loaded_kvs = loaded_tree.into_iter().collect::<Vec<_>>();
        let inserted_kvs = inserted_tree.into_iter().collect::<Vec<_>>();
        assert_eq!(loaded_kvs, inserted_kvs);
    }

    #[test]
    fn test_bulk_load_string() {
        type Tree = BPlusTree<NodeStoreVec<String, i32, 4, 5>>;
        let data = (0..400)
            .map(|i| (format!("{i:010}"), i * 2))
            .collect::<Vec<_>>();
        let loaded_tree = Tree::bulk_load(data.clone());
        let mut inserted_tree = Tree::new(NodeStoreVec::default());
        for (k, v) in data.clone().into_iter() {
            inserted_tree.insert(k, v);
        }
        assert_eq!(loaded_tree.len(), inserted_tree.len());

        for (k, v) in &data {
            assert_eq!(loaded_tree.get(k).unwrap(), v);
        }

        let loaded_kvs = loaded_tree.into_iter().collect::<Vec<_>>();
        let inserted_kvs = inserted_tree.into_iter().collect::<Vec<_>>();
        assert_eq!(loaded_kvs, inserted_kvs);
    }
}

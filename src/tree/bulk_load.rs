use crate::tree::InnerNode;

use super::{Argument, LeafNode, LeafNodeId, NodeId, NodeStore};

impl<S: NodeStore> crate::BPlusTree<S> {
    /// bulk load data into a new `BPlusTree`, the loaded tree's leaf with fill rate 1.0
    /// It requires data sorted by `S::K`
    pub fn bulk_load(data: Vec<(S::K, S::V)>) -> Self {
        // todo: now the last leaf maybe undersized, which should be easily fixed by
        //       shifting some items from prev leaf.
        let mut node_store = S::default();
        if data.is_empty() {
            return Self::new(node_store);
        }

        let mut item_count = 0usize;

        let mut data_iter = data.into_iter().dedup_keep_last(|l, r| l.0.eq(&r.0));
        let mut nodes: Vec<(NodeId, (Option<S::K>, Option<S::K>), S::Argument)> = Vec::new();

        let mut prev_id: Option<LeafNodeId> = None;

        loop {
            let mut leaf = LeafNode::<S::K, S::V>::new();
            leaf.set_data(&mut data_iter);

            if leaf.len() == 0 {
                // there is no data left
                break;
            }

            let leaf_id = node_store.reserve_leaf();
            leaf.set_prev(prev_id);

            // fix the prev leaf's next pointer
            if let Some(prev_id) = prev_id {
                node_store.get_mut_leaf(prev_id).set_next(Some(leaf_id));
            }

            prev_id = Some(leaf_id);

            nodes.push((
                NodeId::Leaf(leaf_id),
                leaf.key_range(),
                S::Argument::from_leaf(leaf.keys()),
            ));
            item_count += leaf.len();

            node_store.assign_leaf(leaf_id, leaf);
        }

        let root_id = Self::build_inner_layer(&mut node_store, nodes);

        Self::new_from_parts(node_store, root_id, item_count)
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

            let inner = InnerNode::<S::K, S::Argument>::new_from_iter(
                keys_iter,
                childs_iter,
                child_argument_iter,
            );
            let argument = S::Argument::from_inner(inner.keys(), inner.arguments());
            let node_id = node_store.add_inner(inner);

            nodes.push((NodeId::Inner(node_id), (start_key, end_key), argument));
        }

        Self::build_inner_layer(node_store, nodes)
    }
}

/// Dedup, keeps the last item for same key
struct DeDupKeepLast<I, F>
where
    I: Iterator,
{
    iter: I,
    current_item: Option<I::Item>,
    same_bucket: F,
}

impl<I, F> Iterator for DeDupKeepLast<I, F>
where
    I: Iterator,
    F: Fn(&I::Item, &I::Item) -> bool,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        for item in self.iter.by_ref() {
            match self.current_item.as_ref() {
                Some(current_item) if !(self.same_bucket)(current_item, &item) => {
                    let prev_item = std::mem::replace(&mut self.current_item, Some(item));
                    return prev_item;
                }
                _ => {
                    self.current_item = Some(item);
                }
            }
        }
        std::mem::take(&mut self.current_item)
    }
}

trait DedupByExt: Iterator {
    fn dedup_keep_last<F>(self, same_bucket: F) -> DeDupKeepLast<Self, F>
    where
        Self: Sized,
        F: Fn(&Self::Item, &Self::Item) -> bool,
    {
        DeDupKeepLast {
            iter: self,
            current_item: None,
            same_bucket,
        }
    }
}

impl<I: Iterator> DedupByExt for I {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn test_bulk_load() {
        type Tree = BPlusTree<NodeStoreVec<i32, i32, argument::count::Count>>;
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

        // verify argument is same for both
        assert_eq!(
            loaded_tree.root_argument().count(),
            inserted_tree.root_argument().count()
        );

        let loaded_kvs = loaded_tree.into_iter().collect::<Vec<_>>();
        let inserted_kvs = inserted_tree.into_iter().collect::<Vec<_>>();
        assert_eq!(loaded_kvs, inserted_kvs);
    }

    #[test]
    fn test_bulk_load_with_dup_items() {
        type Tree = BPlusTree<NodeStoreVec<i32, i32, argument::count::Count>>;
        // i / 2, so there are two keys for one value
        let data = (0..400).map(|i| (i / 2, i * 2)).collect::<Vec<_>>();
        let loaded_tree = Tree::bulk_load(data.clone());
        let mut inserted_tree = Tree::new(NodeStoreVec::default());
        for (k, v) in data.clone().into_iter() {
            inserted_tree.insert(k, v);
        }
        assert_eq!(loaded_tree.len(), inserted_tree.len());

        // verify argument is same for both
        assert_eq!(
            loaded_tree.root_argument().count(),
            inserted_tree.root_argument().count()
        );

        let loaded_kvs = loaded_tree.into_iter().collect::<Vec<_>>();
        let inserted_kvs = inserted_tree.into_iter().collect::<Vec<_>>();
        assert_eq!(loaded_kvs, inserted_kvs);
    }

    #[test]
    fn test_bulk_load_string() {
        type Tree = BPlusTree<NodeStoreVec<String, i32>>;
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

    #[test]
    fn test_dedup() {
        let mut data = vec![];
        for i in 0..4 {
            data.push((i, i * 10));
            data.push((i, i * 10 + 1));
        }

        let dedupped = data
            .iter()
            .cloned()
            .dedup_keep_last(|a, b| a.0 == b.0)
            .collect::<Vec<_>>();
        assert_eq!(dedupped, vec![(0, 1), (1, 11), (2, 21), (3, 31)]);
    }
}

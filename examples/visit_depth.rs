use sweep_bptree::{tree::visit::DescendVisit, BPlusTreeMap};

/// This is a dummy visitor that counts the depth of the tree
#[derive(Default)]
struct GetTreeDepth {
    depth: usize,
}

impl<K, V, A> DescendVisit<K, V, A> for GetTreeDepth {
    type Result = usize;

    fn visit_inner(
        &mut self,
        _keys: &[K],
        _augmentations: &[A],
    ) -> sweep_bptree::tree::visit::DescendVisitResult<Self::Result> {
        self.depth += 1;

        // always down to first child, b+tree is balanced, so it doesn't matter
        // which child we choose
        sweep_bptree::tree::visit::DescendVisitResult::GoDown(0)
    }

    fn visit_leaf(&mut self, _keys: &[K], _values: &[V]) -> Option<Self::Result> {
        self.depth += 1;

        // leaf is the last layer, return the depth
        Some(self.depth)
    }
}

fn main() {
    let tree = (0..10000)
        .map(|i| (i, i * 10))
        .collect::<BPlusTreeMap<_, _>>();

    println!("tree size: {}", tree.len());

    // ceil(log(10000, 64)) == 3
    assert_eq!(tree.descend_visit(GetTreeDepth::default()), Some(3));
}

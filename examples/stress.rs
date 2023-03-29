mod utils;
use rand::seq::SliceRandom;
use utils::*;

use sweep_bptree::{BPlusTree, NodeStoreVec};

type NodeStore = NodeStoreVec<Point, Value, 64, 65, 64>;

#[inline(never)]
fn create_tree() -> BPlusTree<NodeStore> {
    let node_store = NodeStore::new();
    let mut tree = BPlusTree::new(node_store);

    let mut keys = (0..1000).collect::<Vec<_>>();
    keys.shuffle(&mut rand::thread_rng());

    for i in keys {
        let k = Point {
            x: i as f64,
            y: i as f64,
        };
        tree.insert(k, Value::default());
    }

    println!("{}", tree.len());
    tree
}

#[inline(never)]
fn delete_tree(tree: &mut BPlusTree<NodeStore>) {
    let mut keys = tree.iter().map(|(k, _)| k).cloned().collect::<Vec<_>>();
    keys.shuffle(&mut rand::thread_rng());

    for k in keys.iter() {
        tree.remove(k);
    }
    println!("{}", tree.len());
}

fn main() {
    let mut tree = create_tree();
    // tree.node_store().print();
    delete_tree(&mut tree);
}

mod utils;
use utils::*;

use sweep_bptree::{BPlusTree, NodeStoreVec};

type NodeStore = NodeStoreVec<Point, Value, 64, 65, 64>;

#[inline(never)]
fn create_tree() -> BPlusTree<NodeStore> {
    let node_store = NodeStore::new();
    let mut tree = BPlusTree::new(node_store);

    for i in 0..1000000 {
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
    for i in 0..1000000 {
        let k = Point {
            x: i as f64,
            y: i as f64,
        };
        tree.remove(&k);
    }
    println!("{}", tree.len());
}

fn main() {
    let mut tree = create_tree();
    delete_tree(&mut tree);
}

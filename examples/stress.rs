mod utils;
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
use utils::*;

use sweep_bptree::BPlusTreeMap;

const RAND_SEED: u64 = 123;

#[inline(never)]
fn create_bptree() -> BPlusTreeMap<Point, Value> {
    let mut tree = BPlusTreeMap::new();

    let mut keys = (0..100000).collect::<Vec<_>>();
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
fn delete_bptree(tree: &mut BPlusTreeMap<Point, Value>) {
    let mut keys = tree.iter().map(|(k, _)| k).cloned().collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for k in keys.iter() {
        tree.remove(k);
    }
    println!("{}", tree.len());
}

fn main() {
    let mut tree = create_bptree();
    delete_bptree(&mut tree);
}

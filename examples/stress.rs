mod utils;
use std::collections::BTreeMap;

use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
use utils::*;

use sweep_bptree::BPlusTreeMap;

const RAND_SEED: u64 = 123;

#[derive(PartialEq, PartialOrd, Eq, Ord)]
struct StringWrapper(String);

impl From<String> for StringWrapper {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl Clone for StringWrapper {
    #[inline(never)]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[inline(never)]
fn create_bptree(keys: Vec<StringWrapper>) -> BPlusTreeMap<StringWrapper, Value> {
    let mut tree = BPlusTreeMap::new();

    for i in keys {
        tree.insert(i, Value::default());
    }

    println!("tree len: {}", tree.len());
    tree
}

#[inline(never)]
fn find_all_bptree(tree: &BPlusTreeMap<StringWrapper, Value>, keys: &[StringWrapper]) {
    let mut count = 0;
    for k in keys {
        count += if tree.get(k).is_some() { 2 } else { 0 }
    }
    println!("find_all_bptree: count {count}");
}

#[inline(never)]
fn delete_bptree(tree: &mut BPlusTreeMap<StringWrapper, Value>) {
    let mut keys = tree.iter().map(|(k, _)| k).cloned().collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for k in keys.iter() {
        assert!(tree.remove(k).is_some());
    }
    println!("tree len after delete: {}", tree.len());
}

#[inline(never)]
fn create_btree(keys: Vec<StringWrapper>) -> BTreeMap<StringWrapper, Value> {
    let mut tree = BTreeMap::new();

    for i in keys {
        tree.insert(i, Value::default());
    }

    println!("tree len: {}", tree.len());
    tree
}

#[inline(never)]
fn find_all_btree(tree: &BTreeMap<StringWrapper, Value>, keys: &[StringWrapper]) {
    let mut count = 0;
    for k in keys {
        count += if tree.get(k).is_some() { 2 } else { 0 }
    }
    println!("find_all_bptree: count {count}");
}

#[inline(never)]
fn delete_btree(tree: &mut BTreeMap<StringWrapper, Value>) {
    let mut keys = tree.iter().map(|(k, _)| k).cloned().collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for k in keys.iter() {
        tree.remove(k);
    }
    println!("tree len after delete {}", tree.len());
}

fn main() {
    for _ in 0..200 {
        let mut keys = (0..10000).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        let keys = keys
            .into_iter()
            .map(|i| format!("{i:030}").into())
            .collect::<Vec<_>>();

        let mut tree = create_bptree(keys.clone());
        find_all_bptree(&tree, &keys);
        delete_bptree(&mut tree);

        let mut tree = create_btree(keys.clone());
        find_all_btree(&tree, &keys);
        delete_btree(&mut tree);
    }
}

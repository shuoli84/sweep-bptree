use sweep_bptree::{argument::Argument, BPlusTreeMap};

/// An argumentation that counts even numbers
#[derive(Default, Clone, Debug)]
struct EvenCount(usize);

impl Argument<i64> for EvenCount {
    fn from_leaf(keys: &[i64]) -> Self {
        // For leafs, we count all keys that are even
        Self(keys.iter().filter(|k| *k % 2 == 0).count())
    }

    fn from_inner(_keys: &[i64], arguments: &[Self]) -> Self {
        // For inner nodes, we aggregate all the EvenCount
        Self(arguments.iter().map(|a| a.0).sum::<usize>())
    }
}

fn main() {
    // create a tree with the argument
    let mut tree = BPlusTreeMap::<i64, i64, EvenCount>::new();

    // insert 100000 numbers
    for i in 0..100000 {
        tree.insert(i, i);
    }

    // check we get the correct count
    assert_eq!(dbg!(tree.root_argument()).0, 50000);

    // then remove some keys
    for i in 0..100 {
        tree.remove(&(i * 2));
    }
    assert_eq!(dbg!(tree.root_argument()).0, 49900);

    // remove odd numbers should not affect the even count
    for i in 0..100 {
        tree.remove(&(i * 2 + 1));
    }
    assert_eq!(dbg!(tree.root_argument()).0, 49900);
}

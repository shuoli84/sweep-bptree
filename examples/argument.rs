use sweep_bptree::{argument::Argumentation, BPlusTreeMap};

#[derive(Default, Clone, Debug)]
struct EvenCount(usize);

impl Argumentation<i64> for EvenCount {
    fn from_leaf(keys: &[i64]) -> Self {
        EvenCount(keys.iter().filter(|k| *k % 2 == 0).count())
    }

    fn from_inner(_keys: &[i64], arguments: &[Self]) -> Self {
        Self(arguments.iter().map(|a| a.0).sum::<usize>())
    }
}

fn main() {
    let mut tree = BPlusTreeMap::<i64, i64, EvenCount>::new();

    for i in 0..100000 {
        tree.insert(i, i);
    }

    assert_eq!(dbg!(tree.root_argument()).0, 50000);

    for i in 0..100 {
        tree.remove(&(i * 2));
    }

    assert_eq!(dbg!(tree.root_argument()).0, 49900);
}

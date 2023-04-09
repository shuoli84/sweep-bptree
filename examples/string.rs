use sweep_bptree::BPlusTreeSet;

fn main() {
    let mut set = BPlusTreeSet::<String>::new();
    set.insert("hello");
    set.insert("world");

    assert!(set.contains("hello"));
}

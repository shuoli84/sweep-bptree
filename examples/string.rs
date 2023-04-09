use std::borrow::Cow;

use sweep_bptree::BPlusTreeSet;

fn main() {
    let mut set = BPlusTreeSet::<Cow<'_, str>>::new();
    set.insert("hello");
    set.insert("world");

    assert!(set.contains("hello"));
}

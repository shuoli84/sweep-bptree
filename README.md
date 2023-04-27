# Sweep-bptree(under development)

In memory augmentable b+ tree.

## Features

* Augmented search tree, e.g, you can use `Count` Argment to turn the tree into order statistic tree. Or create your own argument to support more advanced usage.
* Performance, comparable to std::collections::BTreeMap.

## Install

```toml
[dependencies]
sweep-bptree = "0.4"
```

## Example

### Map

as a plain Map/Set

``` rust
use sweep_bptree::BPlusTreeMap;

let mut map = BPlusTreeMap::<i32, i32>::new();
map.insert(1, 2);

assert_eq!(map.get(&1).unwrap(), &2);
assert!(map.get(&2).is_none());
```

### Order statistic tree

Or enhaunced with `Argument`

```rust
use sweep_bptree::BPlusTreeMap;
use sweep_bptree::argument::count::Count;

// use Count as Argument to create a order statistic tree
let mut map = BPlusTreeMap::<i32, i32, Count>::new();
map.insert(1, 2);
map.insert(2, 3);
map.insert(3, 4);

// get by order, time complexity is log(n)
assert_eq!(map.get_by_argument(0), Some((&1, &2)));
assert_eq!(map.get_by_argument(1), Some((&2, &3)));

// get the offset for key

// 0 does not exists
assert_eq!(map.rank_by_argument(&0), Err(0));

assert_eq!(map.rank_by_argument(&1), Ok(0));
assert_eq!(map.rank_by_argument(&2), Ok(1));
assert_eq!(map.rank_by_argument(&3), Ok(2));

// 4 does not exists
assert_eq!(map.rank_by_argument(&4), Err(3));
```

### Two layered key

Another example of augemented tree. With built in `GroupCount` argument, the tree can
support two layer key, e.g, (year, date), (section, row) etc.

```rust
use sweep_bptree::BPlusTreeMap;
use sweep_bptree::argument::group::{GroupCount, Tuple2};

// Tuple2 use pair's first element as group value
let mut tree = BPlusTreeMap::<_, _, GroupCount<Tuple2<_>>>::new();

// group count is 0 for empty tree
assert_eq!(tree.root_argument().group_count(), 0);

tree.insert((1, 1), 100);
assert_eq!(tree.root_argument().group_count(), 1);
tree.remove(&(1, 1));
assert_eq!(tree.root_argument().group_count(), 0);

tree.insert((1, 1), 100);
tree.insert((1, 2), 101);
assert_eq!(tree.root_argument().group_count(), 1);

// get group size for Tuple2(1)
assert_eq!(
    tree.descend_visit(ExtractGroupSize::new(Tuple2(1))),
    Some(2)
);

// get (k, v) by (group, offset)
assert_eq!(tree.get_by_argument((Tuple2(1), 0)).unwrap().1, &100);

// or get the (group, offset) tuple by key
assert_eq!(tree.rank_by_argument(&(1, 0)), Err(Some((Tuple2(1), 0))));
```

## Unsafe

This crate utilize unsafe code to improve performance. Mostly for memory initialize, copy and move operations. It is tested with fuzzy testing.

## Contribution

Contributions are welcome! Please open an issue or a PR. Currently, documentation, feature parity with `std::collections::BTreeMap`, and performance improvements are the main areas of interest.

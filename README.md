# Sweep-bptree(under development)

In memory general purpose b+ tree.

## Features(Why use this)

* Inspired by splaytree, maintains last accessed leaf node. Quite performant for ordered/local access. (Check out benchmark)
* Owned version of cursor, so you can keep a cursor around and modify the tree underlying.
* Bulk load, currently the most performant way to build a tree. (Check out benchmark)
* Faster iteration than `std::collections::BTreeMap`, mostly because it has large leaf node and don't need to visit inner node.
* Friendlier to non-trivial keys. `std::collections::BTreeMap`'s in-node key searching use a for loop, which has better performance for trivial cmp keys. But it issues more cmp operations. (TODO: add numbers)

## Install

```toml
[dependencies]
sweep-bptree = "0.3"
```

## Example

### Map

``` rust
use sweep_bptree::BPlusTreeMap;

let mut map = BPlusTreeMap::<i32, i32>::new();
map.insert(1, 2);

assert_eq!(map.get(&1).unwrap(), &2);
assert!(map.get(&2).is_none());
```

### Set

```rust
use sweep_bptree::BPlusTreeSet;

let mut set = BPlusTreeSet::<i32>::new();
set.insert(1);
assert!(set.contains(&1));
set.remove(&1);
assert!(!set.contains(&1));
```

### Tree

For adanced usage, use `BPlusTree` directly.

#### crud

```rust
use sweep_bptree::{BPlusTree, NodeStoreVec};

// create a node_store with `u64` as key, `(f64, f64)` as value, inner node size 64, child size 65, leaf node size 64
let mut node_store = NodeStoreVec::<u64, (f64, f64), 64, 65, 64>::new();
let mut tree = BPlusTree::new(node_store);

// insert new value
assert!(tree.insert(3, (0., 0.)).is_none());

// update by insert again
assert_eq!(tree.insert(3, (1., 1.)).unwrap(), (0., 0.));

// remove the value
assert_eq!(tree.remove(&3).unwrap(), (1.0, 1.0));

assert!(tree.is_empty());
```

#### Create multiple owned cursors

``` rust
use sweep_bptree::{BPlusTree, NodeStoreVec};
let mut node_store = NodeStoreVec::<u64, (f64, f64), 64, 65, 64>::new();
let mut tree = BPlusTree::new(node_store);

for i in 0..100 {
    tree.insert(i, (i as f64, i as f64));
}

let cursor_0 = tree.cursor_first().unwrap();
let cursor_1 = tree.cursor_first().unwrap();

// remove the key 0
tree.remove(&0);

// cursor's value should be empty now
assert!(cursor_0.value(&tree).is_none());

// move to next
let cursor_next = cursor_0.next(&tree).unwrap();
assert_eq!(*cursor_next.key(), 1);
assert_eq!(cursor_next.value(&tree).unwrap().0, 1.);

// insert a new value to key 0
tree.insert(0, (100., 100.));

// now cursor_1 should retrieve the new value
assert_eq!(cursor_1.value(&tree).unwrap().0, 100.);
```

## Unsafe

This crate utilize unsafe code to improve performance. Mostly for memory initialize, copy and move operations. It is tested with fuzzy testing.

## Benchmark

Data collected on macbook pro m1. The Key type is `Point { x: f64, y: f64}`

```bash
# try it
cargo bench

# generate the table
critcmp > benchmark_data 
python3 render_table.py

```

### Advantages

* bptree ordered_get is way faster than random_get, also way faster(1.2ms vs 4.7ms) than btree's ordered_get.
* bptree iter's faster than btree(86us vs 220us).
* bptree bulk_insert is the most fast way to build a tree(938µs vs normal bptree insert 2ms vs btree insert 8ms).
* For unsorted data, sort then bulk_load is the fastest(9ms vs normal bptree 18.ms vs normal btree insert 13.9ms).

### Disadvantages

* bptree random_get is slower(13ms vs 9ms) than btree.
* random_remove(17ms vs 12ms).

### Point benchmark data

Point is a struct with 2 f64 fields, with very cheap clone and cmp cost.

| name | size | btree | bptree | speed factor |
| - | - | - | - | - |
| clone | 1000 | 12.4±0.08µs | 7.1±0.05µs | 1.75 |
| clone | 10000 | 135.4±1.22µs | 74.8±0.71µs | 1.81 |
| clone | 100000 | 2.5±0.02ms | 1216.6±79.89µs | 2.05 |
| cursor | 1000 | - | 5.0±0.03µs | - |
| cursor | 10000 | - | 51.1±0.13µs | - |
| cursor | 100000 | - | 518.1±2.61µs | - |
| drop | 1000 | 8.0±0.07µs | 1829.4±24.83ns | 4.37 |
| drop | 10000 | 84.9±0.47µs | 20.6±0.25µs | 4.12 |
| drop | 100000 | 1845.4±78.50µs | 350.0±34.88µs | 5.27 |
| into_iter | 1000 | 8.1±0.08µs | 1837.8±37.12ns | 4.41 |
| into_iter | 10000 | 85.6±0.66µs | 20.7±0.19µs | 4.14 |
| into_iter | 100000 | 1871.8±19.34µs | 321.8±21.43µs | 5.82 |
| iter | 1000 | 843.0±11.23ns | 370.8±9.62ns | 2.27 |
| iter | 10000 | 11.9±0.54µs | 6.7±0.08µs | 1.78 |
| iter | 100000 | 218.6±2.57µs | 85.9±0.53µs | 2.54 |
| ordered_get | 1000 | 23.8±1.62µs | 9.5±0.08µs | 2.51 |
| ordered_get | 10000 | 423.4±2.13µs | 109.9±0.86µs | 3.85 |
| ordered_get | 100000 | 4.7±0.02ms | 1175.1±17.09µs | 4.00 |
| ordered_remove | 1000 | 31.8±0.35µs | 40.6±0.79µs | 0.78 |
| ordered_remove | 10000 | 348.0±3.52µs | 443.5±3.00µs | 0.78 |
| ordered_remove | 100000 | 4.5±0.10ms | 5.3±0.04ms | 0.85 |
| random_get | 1000 | 22.7±3.05µs | 32.7±2.12µs | 0.69 |
| random_get | 10000 | 656.3±3.32µs | 986.8±8.60µs | 0.67 |
| random_get | 100000 | 9.4±0.19ms | 14.2±0.10ms | 0.66 |
| random_remove | 1000 | 58.8±2.28µs | 65.9±3.87µs | 0.89 |
| random_remove | 10000 | 940.2±2.31µs | 1202.3±2.60µs | 0.78 |
| random_remove | 100000 | 12.8±0.19ms | 17.4±0.48ms | 0.74 |

#### Point benchmark data with bulk_load

| name | size | type | time |
| - | - | - | - |
| ordered_insert | 1000 | bptree | 16.0±0.04µs
|  |  | bptree_bulk | 6.7±0.05µs
|  |  | btree | 52.3±0.80µs
| ordered_insert | 10000 | bptree | 173.1±1.53µs
|  |  | bptree_bulk | 72.7±0.93µs
|  |  | btree | 779.5±9.75µs
| ordered_insert | 100000 | bptree | 2.3±0.02ms
|  |  | bptree_bulk | 1025.5±34.59µs
|  |  | btree | 8.8±0.07ms
| random_insert | 1000 | bptree | 57.8±4.67µs
|  |  | bptree_sort_load | 43.6±0.31µs
|  |  | btree | 50.3±1.08µs
| random_insert | 10000 | bptree | 1288.2±13.88µs
|  |  | bptree_sort_load | 686.1±19.43µs
|  |  | btree | 939.9±7.26µs
| random_insert | 100000 | bptree | 18.4±4.51ms
|  |  | bptree_sort_load | 9.8±0.20ms
|  |  | btree | 13.7±0.17ms

### String benchmark data

String type is relative heavy for clone, cmp and drop.

For clone and drop, bptree actually needs to do more work, but still faster.
For random_get and random_remove, bptree still slower, but the margin is smaller.

| name | size | btree | bptree | speed factor |
| - | - | - | - | - |
| clone | 1000 | 34.9±0.34µs | 31.0±0.31µs | 1.13 |
| clone | 10000 | 435.9±7.29µs | 328.4±3.87µs | 1.33 |
| clone | 100000 | 7.2±0.11ms | 5.5±0.07ms | 1.31 |
| cursor | 1000 | - | 31.5±0.25µs | - |
| cursor | 10000 | - | 317.9±1.33µs | - |
| cursor | 100000 | - | 3.9±0.17ms | - |
| drop | 1000 | 22.1±0.88µs | 16.5±0.41µs | 1.34 |
| drop | 10000 | 237.0±3.58µs | 162.2±1.58µs | 1.46 |
| drop | 100000 | 4.5±0.08ms | 2.6±0.13ms | 1.73 |
| into_iter | 1000 | 21.2±0.41µs | 15.2±1.15µs | 1.39 |
| into_iter | 10000 | 255.7±41.04µs | 167.6±3.18µs | 1.53 |
| into_iter | 100000 | 4.6±0.27ms | 2.6±0.05ms | 1.77 |
| iter | 1000 | 844.3±11.93ns | 362.6±7.31ns | 2.33 |
| iter | 10000 | 17.0±0.57µs | 6.8±0.05µs | 2.50 |
| iter | 100000 | 236.9±7.38µs | 86.1±1.08µs | 2.75 |
| ordered_get | 1000 | 223.2±2.30µs | 208.7±2.06µs | 1.07 |
| ordered_get | 10000 | 2.4±0.01ms | 2.1±0.03ms | 1.14 |
| ordered_get | 100000 | 25.7±0.02ms | 22.4±0.94ms | 1.15 |
| ordered_remove | 1000 | 233.9±1.57µs | 282.3±3.43µs | 0.83 |
| ordered_remove | 10000 | 2.4±0.01ms | 2.9±0.00ms | 0.83 |
| ordered_remove | 100000 | 27.8±2.40ms | 30.9±0.06ms | 0.90 |
| random_get | 1000 | 64.5±0.94µs | 68.0±0.51µs | 0.95 |
| random_get | 10000 | 1204.6±28.03µs | 1505.9±29.45µs | 0.80 |
| random_get | 100000 | 23.3±0.20ms | 29.1±3.15ms | 0.80 |
| random_remove | 1000 | 128.3±2.33µs | 133.0±0.93µs | 0.96 |
| random_remove | 10000 | 1800.9±5.62µs | 2.1±0.05ms | 0.86 |
| random_remove | 100000 | 31.9±2.66ms | 36.7±1.32ms | 0.87 |

#### String benchmark data with bulk_load

| name | size | type | time |
| - | - | - | - |
| ordered_insert | 1000 | bptree | 211.3±1.57µs
|  |  | bptree_bulk | 177.6±1.22µs
|  |  | btree | 273.0±1.92µs
| ordered_insert | 10000 | bptree | 2.2±0.01ms
|  |  | bptree_bulk | 1782.6±17.59µs
|  |  | btree | 3.0±0.01ms
| ordered_insert | 100000 | bptree | 22.5±0.11ms
|  |  | bptree_bulk | 18.6±0.06ms
|  |  | btree | 33.1±0.21ms
| random_insert | 1000 | bptree | 140.9±1.41µs
|  |  | bptree_sort_load | 80.8±0.96µs
|  |  | btree | 122.8±1.46µs
| random_insert | 10000 | bptree | 2.3±0.03ms
|  |  | bptree_sort_load | 1455.0±19.45µs
|  |  | btree | 1824.0±22.60µs
| random_insert | 100000 | bptree | 37.2±0.21ms
|  |  | bptree_sort_load | 20.8±0.06ms
|  |  | btree | 30.5±0.24ms

## Contribution

Contributions are welcome! Please open an issue or a PR. Currently, documentation, feature parity with `std::collections::BTreeMap`, and performance improvements are the main areas of interest.

Things on my head:

* Inside inner/leaf node, the `binary` search part is hot(if not hottest) path, and it is not optimized yet.  related: <https://quickwit.io/blog/search-a-sorted-block>

* Mem move, e.g, when deleting, rotation and merging will do one memmove. I think it is possible to avoid this. E.g: use remove-empty instead of merge-at-half(now the impl is a quater).

# Sweep-bptree(under development)

In memory locality aware b+ tree, faster for ordered access.

## Motivation

While developing [poly2tri-rs](https://github.com/shuoli84/poly2tri-rs), I need a better datastructure to maintain "Sweeping Front/Advancing Front". It should:

1. performant to insert and remove.
2. performant for query, and the query pattern is more local than random. That means the query is more likely to be close to the last accessed node.
3. Provide floating cursor support, so I can keep a cursor around and modify the tree underlying.

### Why not splaytree

Splaytree is binary tree, so it has relative large number of nodes, which is bad for cache locality.

### Why not std btree

std::collections::BTreeMap's Cursor support is not stablized yet.

Also I couldn't come up a proper cache mechanism for BTree. BTree's value is stored in all nodes, that makes cache invalidate more frequently.

## Features

* Inspired by splaytree, maintains last accessed leaf node. Quite performant for ordered access. (Check out benchmark)
* Owned version of cursor, so you can keep a cursor around and modify the tree underlying.
* Plugable NodeStore, how to alloc or reuse Node is customizable.

## Example

### crud

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

### Create multiple owned cursors

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

## Benchmark

Data collected on macbook pro m1.
NOTE: The underlying code didn't tuned yet, there is a big space to improve.

### Highlight

* bptree ordered_get is way faster than random_get, also way faster than btree's ordered_get
* bptree iter's faster than btree iter by around 50%.
* bptree random_get and remove is slower than btree random_get by 100%. (Room to optimize)

```bash
group                          base                                   new
-----                          ----                                   ---
bptree clone 1000              1.00      3.5±0.03µs        ? ?/sec    1.00      3.5±0.03µs        ? ?/sec
bptree clone 10000             1.00     37.9±3.42µs        ? ?/sec    1.00     37.9±3.42µs        ? ?/sec
bptree cursor 1000             1.00      4.4±0.04µs        ? ?/sec    1.00      4.4±0.04µs        ? ?/sec
bptree cursor 10000            1.00     46.3±0.30µs        ? ?/sec    1.00     46.3±0.30µs        ? ?/sec
bptree insert 1000             1.00     20.9±0.13µs        ? ?/sec    1.00     20.9±0.13µs        ? ?/sec
bptree insert 10000            1.00    306.1±2.77µs        ? ?/sec    1.00    306.1±2.77µs        ? ?/sec
bptree iter 1000               1.00    337.9±1.19ns        ? ?/sec    1.00    337.9±1.19ns        ? ?/sec
bptree iter 10000              1.00      3.3±0.02µs        ? ?/sec    1.00      3.3±0.02µs        ? ?/sec
bptree ordered_get 1000        1.00     11.3±0.28µs        ? ?/sec    1.00     11.3±0.28µs        ? ?/sec
bptree ordered_get 10000       1.00    117.9±0.30µs        ? ?/sec    1.00    117.9±0.30µs        ? ?/sec
bptree ordered_remove 1000     1.00     58.4±0.37µs        ? ?/sec    1.00     58.4±0.37µs        ? ?/sec
bptree ordered_remove 10000    1.00   682.3±10.80µs        ? ?/sec    1.00   682.3±10.80µs        ? ?/sec
bptree random_get 1000         1.00     19.3±2.32µs        ? ?/sec    1.00     19.3±2.32µs        ? ?/sec
bptree random_get 10000        1.00    990.1±6.85µs        ? ?/sec    1.00    990.1±6.85µs        ? ?/sec
bptree random_insert 1000      1.00     70.2±0.60µs        ? ?/sec    1.00     70.2±0.60µs        ? ?/sec
bptree random_insert 10000     1.00  1331.9±12.50µs        ? ?/sec    1.00  1331.9±12.50µs        ? ?/sec
bptree random_remove 1000      1.00     59.0±1.33µs        ? ?/sec    1.00     59.0±1.33µs        ? ?/sec
bptree random_remove 10000     1.00   1221.1±7.52µs        ? ?/sec    1.00   1221.1±7.52µs        ? ?/sec
btree clone 1000               1.00     12.5±0.14µs        ? ?/sec    1.00     12.5±0.14µs        ? ?/sec
btree clone 10000              1.00    134.3±1.79µs        ? ?/sec    1.00    134.3±1.79µs        ? ?/sec
btree insert 1000              1.00     51.3±1.07µs        ? ?/sec    1.00     51.3±1.07µs        ? ?/sec
btree insert 10000             1.00   753.7±10.08µs        ? ?/sec    1.00   753.7±10.08µs        ? ?/sec
btree iter 1000                1.00    876.7±7.04ns        ? ?/sec    1.00    876.7±7.04ns        ? ?/sec
btree iter 10000               1.00     11.1±0.28µs        ? ?/sec    1.00     11.1±0.28µs        ? ?/sec
btree ordered_get 1000         1.00     18.7±1.12µs        ? ?/sec    1.00     18.7±1.12µs        ? ?/sec
btree ordered_get 10000        1.00    423.4±4.12µs        ? ?/sec    1.00    423.4±4.12µs        ? ?/sec
btree ordered_remove 1000      1.00     36.5±0.56µs        ? ?/sec    1.00     36.5±0.56µs        ? ?/sec
btree ordered_remove 10000     1.00   418.0±11.41µs        ? ?/sec    1.00   418.0±11.41µs        ? ?/sec
btree random_get 1000          1.00     23.2±1.38µs        ? ?/sec    1.00     23.2±1.38µs        ? ?/sec
btree random_get 10000         1.00    637.7±5.44µs        ? ?/sec    1.00    637.7±5.44µs        ? ?/sec
btree random_remove 1000       1.00     53.2±1.57µs        ? ?/sec    1.00     53.2±1.57µs        ? ?/sec
btree random_remove 10000      1.00   948.2±11.95µs        ? ?/sec    1.00   948.2±11.95µs        ? ?/sec
vec get 1000                   1.00     20.5±3.97µs        ? ?/sec    1.00     20.5±3.97µs        ? ?/sec
vec get 10000                  1.00    457.1±4.23µs        ? ?/sec    1.00    457.1±4.23µs        ? ?/sec
vec insert 1000                1.00     13.5±0.11µs        ? ?/sec    1.00     13.5±0.11µs        ? ?/sec
vec insert 10000               1.00    199.1±5.13µs        ? ?/sec    1.00    199.1±5.13µs        ? ?/sec
vec iter 1000                  1.00    319.7±3.02ns        ? ?/sec    1.00    319.7±3.02ns        ? ?/sec
vec iter 10000                 1.00      3.1±0.02µs        ? ?/sec    1.00      3.1±0.02µs        ? ?/sec
vec remove 1000                1.00    406.7±4.15µs        ? ?/sec    1.00    406.7±4.15µs        ? ?/sec
vec remove 10000               1.00     56.1±0.55ms        ? ?/sec    1.00     56.1±0.55ms        ? ?/sec
```

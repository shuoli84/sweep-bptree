# Sweep-bptree(under development)

In memory locality aware b+ tree, faster for ordered access.

# Motivation

While developing [poly2tri-rs](https://github.com/shuoli84/poly2tri-rs), I need a better datastructure to maintain "Sweeping Front/Advancing Front". It should:

1. performant to insert and remove.
2. performant for query, and the query pattern is more local than random. That means the query is more likely to be close to the last accessed node.
3. Provide floating cursor support, so I can keep a cursor around and modify the tree underlying.

**Why not splaytree**

Splaytree is binary tree, so it has relative large number of nodes, which is bad for cache locality.

**Why not std btree**

std::collections::BTreeMap's Cursor support is not stablized yet.

Also I couldn't come up a proper cache mechanism for BTree. BTree's value is stored in all nodes, that makes cache invalidate more frequently.

# Features

* Inspired by splaytree, maintains last accessed leaf node. Quite performant for ordered access. (Check out benchmark)
* Owned version of cursor, so you can keep a cursor around and modify the tree underlying.
* Plugable NodeStore, how to alloc or reuse Node is customizable.

# Example

## crud

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

## Create multiple owned cursors

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

# Benchmark

Data collected on macbook pro m1.
NOTE: The underlying code didn't tuned yet, there is a big space to improve.

## Highlight

* bptree ordered_get is way faster than random_get, also way faster than btree's ordered_get
* bptree iter's faster than btree iter by around 50%.
* bptree random_get and remove is slower than btree random_get by 100%. (Room to optimize)

```bash
group                          base                                   new
-----                          ----                                   ---
bptree cursor 1000             1.00      4.3±0.02µs        ? ?/sec    1.00      4.3±0.02µs        ? ?/sec
bptree cursor 10000            1.00     44.5±0.36µs        ? ?/sec    1.00     44.5±0.36µs        ? ?/sec
bptree insert 1000             1.00     20.8±0.20µs        ? ?/sec    1.00     20.8±0.20µs        ? ?/sec
bptree insert 10000            1.00    307.1±2.96µs        ? ?/sec    1.00    307.1±2.96µs        ? ?/sec
bptree iter 1000               1.00    339.2±2.52ns        ? ?/sec    1.00    339.2±2.52ns        ? ?/sec
bptree iter 10000              1.00      3.5±0.08µs        ? ?/sec    1.00      3.5±0.08µs        ? ?/sec
bptree ordered_get 1000        1.00     15.2±0.14µs        ? ?/sec    1.00     15.2±0.14µs        ? ?/sec
bptree ordered_get 10000       1.00    153.0±1.70µs        ? ?/sec    1.00    153.0±1.70µs        ? ?/sec
bptree ordered_remove 1000     1.00     66.0±0.53µs        ? ?/sec    1.00     66.0±0.53µs        ? ?/sec
bptree ordered_remove 10000    1.00   741.8±10.50µs        ? ?/sec    1.00   741.8±10.50µs        ? ?/sec
bptree random_get 1000         1.00    43.1±11.76µs        ? ?/sec    1.00    43.1±11.76µs        ? ?/sec
bptree random_get 10000        1.00  1072.8±14.05µs        ? ?/sec    1.00  1072.8±14.05µs        ? ?/sec
bptree random_remove 1000      1.00     69.5±4.26µs        ? ?/sec    1.00     69.5±4.26µs        ? ?/sec
bptree random_remove 10000     1.00  1280.1±13.84µs        ? ?/sec    1.00  1280.1±13.84µs        ? ?/sec
btree insert 1000              1.00     52.1±1.20µs        ? ?/sec    1.00     52.1±1.20µs        ? ?/sec
btree insert 10000             1.00    749.5±8.59µs        ? ?/sec    1.00    749.5±8.59µs        ? ?/sec
btree iter 1000                1.00    875.6±5.73ns        ? ?/sec    1.00    875.6±5.73ns        ? ?/sec
btree iter 10000               1.00     10.9±0.31µs        ? ?/sec    1.00     10.9±0.31µs        ? ?/sec
btree ordered_get 1000         1.00     41.4±2.39µs        ? ?/sec    1.00     41.4±2.39µs        ? ?/sec
btree ordered_get 10000        1.00   609.0±13.05µs        ? ?/sec    1.00   609.0±13.05µs        ? ?/sec
btree ordered_remove 1000      1.00     36.7±0.26µs        ? ?/sec    1.00     36.7±0.26µs        ? ?/sec
btree ordered_remove 10000     1.00   421.3±11.56µs        ? ?/sec    1.00   421.3±11.56µs        ? ?/sec
btree random_get 1000          1.00     26.1±5.54µs        ? ?/sec    1.00     26.1±5.54µs        ? ?/sec
btree random_get 10000         1.00    638.8±7.00µs        ? ?/sec    1.00    638.8±7.00µs        ? ?/sec
btree random_remove 1000       1.00     63.3±5.08µs        ? ?/sec    1.00     63.3±5.08µs        ? ?/sec
btree random_remove 10000      1.00   958.3±10.64µs        ? ?/sec    1.00   958.3±10.64µs        ? ?/sec
vec get 1000                   1.00     15.1±1.98µs        ? ?/sec    1.00     15.1±1.98µs        ? ?/sec
vec get 10000                  1.00    448.5±5.28µs        ? ?/sec    1.00    448.5±5.28µs        ? ?/sec
vec insert 1000                1.00     13.4±0.14µs        ? ?/sec    1.00     13.4±0.14µs        ? ?/sec
vec insert 10000               1.00    198.7±2.32µs        ? ?/sec    1.00    198.7±2.32µs        ? ?/sec
vec iter 1000                  1.00    318.8±1.57ns        ? ?/sec    1.00    318.8±1.57ns        ? ?/sec
vec iter 10000                 1.00      3.1±0.03µs        ? ?/sec    1.00      3.1±0.03µs        ? ?/sec
vec remove 1000                1.00    407.9±4.87µs        ? ?/sec    1.00    407.9±4.87µs        ? ?/sec
vec remove 10000               1.00     56.5±0.42ms        ? ?/sec    1.00     56.5±0.42ms        ? ?/sec
```

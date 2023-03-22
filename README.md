# Sweep-bptree(under development)

A b+ tree, locality aware, so it's faster for ordered access. 

# Motivation

While developing [poly2tri-rs](https://github.com/shuoli84/poly2tri-rs), I need a better datastructure to maintain "Sweeping Front/Advancing Front". It should:

1. performant to insert and remove. 
2. performant for query, and the query pattern is more local than random. That means the query is more likely to be close to the last accessed node. 
3. Provide floating cursor support, so I can keep a cursor around and modify the tree underlying.

**Why not splaytree**

Splaytree is binary tree, so it has relative large number of nodes, which is bad for cache locality. 

**Why not std btree**

std::collections::BTreeMap's Cursor support is not stablized yet. 

Also I couldn't come up a design to introduce the page cache. BTree's value is stored in all nodes, that makes cache invalidate more frequently.

# Features

* Inspired by splaytree, maintains last accessed leaf page. Quite performant for ordered access. (Check out benchmark)
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

## Highlight: 

* bptree ordered_get is way faster than random_get, also way faster than btree's ordered_get
* bptree iter's faster than btree iter by around 50%.
* bptree random_get and remove is slower than btree random_get by 100%. (Room to optimize)


```bash
group                       base
-----                       ----
bptree cursor 1000          1.00      6.1±1.18µs        ? ?/sec
bptree cursor 10000         1.00     59.3±7.64µs        ? ?/sec
bptree insert 1000          1.00     34.0±0.34µs        ? ?/sec
bptree insert 10000         1.00   547.4±32.76µs        ? ?/sec
bptree iter 1000            1.00    498.5±4.37ns        ? ?/sec
bptree iter 10000           1.00      8.7±0.07µs        ? ?/sec
bptree ordered_get 1000     1.00     17.9±5.75µs        ? ?/sec
bptree ordered_get 10000    1.00    168.7±3.42µs        ? ?/sec
bptree random_get 1000      1.00     55.3±5.13µs        ? ?/sec
bptree random_get 10000     1.00  1174.1±15.75µs        ? ?/sec
bptree remove 1000          1.00     82.9±0.64µs        ? ?/sec
bptree remove 10000         1.00    959.4±8.39µs        ? ?/sec
btree insert 1000           1.00     50.0±1.00µs        ? ?/sec
btree insert 10000          1.00   728.4±12.75µs        ? ?/sec
btree iter 1000             1.00   1187.7±9.63ns        ? ?/sec
btree iter 10000            1.00     12.6±0.15µs        ? ?/sec
btree ordered_get 1000      1.00     42.3±4.07µs        ? ?/sec
btree ordered_get 10000     1.00   587.1±15.16µs        ? ?/sec
btree random_get 1000       1.00     25.8±5.20µs        ? ?/sec
btree random_get 10000      1.00    630.2±6.60µs        ? ?/sec
btree remove 1000           1.00     35.4±0.31µs        ? ?/sec
btree remove 10000          1.00   413.6±10.69µs        ? ?/sec
vec get 1000                1.00     31.2±2.66µs        ? ?/sec
vec get 10000               1.00    444.7±5.95µs        ? ?/sec
vec insert 1000             1.00     13.2±0.11µs        ? ?/sec
vec insert 10000            1.00    202.0±3.64µs        ? ?/sec
vec iter 1000               1.00    319.4±2.79ns        ? ?/sec
vec iter 10000              1.00      3.1±0.03µs        ? ?/sec
vec remove 1000             1.00    405.3±3.57µs        ? ?/sec
vec remove 10000            1.00     56.0±0.47ms        ? ?/sec
```
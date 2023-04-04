# Sweep-bptree(under development)

In memory locality aware b+ tree, faster for ordered access.

## Motivation

While developing [poly2tri-rs](https://github.com/shuoli84/poly2tri-rs), I need a better datastructure to maintain "Sweeping Front/Advancing Front". It should:

1. performant to insert and remove.
2. performant for query, and the query pattern is more local than random. That means the query is more likely to be close to the last accessed node.
3. Provide floating cursor support, so I can keep a cursor around and modify the tree underlying.

Though it is designed for "Sweeping Front/Advancing Front", it is a general purpose tree, so can be used in other scenarios.

### Why not splaytree

Splaytree is binary tree, so it has relative large number of nodes, which is bad for cache locality.

### Why not std btree

std::collections::BTreeMap's Cursor support is not stablized yet.

Also I couldn't come up a proper cache mechanism for BTree. BTree's value is stored in all nodes, that makes cache invalidate more frequently.

## Features

* Inspired by splaytree, maintains last accessed leaf node. Quite performant for ordered(local) access. (Check out benchmark)
* Owned version of cursor, so you can keep a cursor around and modify the tree underlying.
* Bulk load, currently the most performant way to build a tree. (Check out benchmark)

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

Data collected on macbook pro m1. The Key type is `Point { x: f64, y: f64}`

### Highlight

(All number is for elment count 100000)

#### Advantages

* bptree ordered_get is way faster than random_get, also way faster(1.6ms vs 4.7ms) than btree's ordered_get.
* bptree iter's faster than btree(57us vs 200us).
* bptree bulk_insert is the most fast way to build a tree(938µs vs normal bptree insert 2ms vs btree insert 8ms).
* For unsorted data, sort then bulk_load is the fastest(9ms vs normal bptree 18.ms vs normal btree insert 13.9ms).

#### Disadvantages

* bptree random_get is slower(13ms vs 9ms) than btree.
* random_remove(17ms vs 12ms).

| name | bptree | btree |
| --- | --- | --- |
| ordered_get | 1.6ms | 4.7ms |
| random_get | 13ms | 9ms |
| iter | 57us | 200us |
| cursor(1) | 486us | - |
| ordered_insert | 2ms | 8ms |
| bulk_load | 938µs | - |
| sort then bulk_load | 9ms | - |
| random_insert | 18.8ms | 13.9ms |
| random_remove | 17ms | 12ms |
| clone | 1.1ms | 2.6ms |
| drop | 345us | 1800us |

1. cursor here is the `floating` cursor, you can keep it around and modify the tree underlying. It's slower than `owned` cursor, because it has to check if the node is still valid.

```bash
group                                    base
-----                                    ----
clone/bptree/1000                        1.00      5.7±0.07µs
clone/bptree/10000                       1.00     60.8±0.52µs
clone/bptree/100000                      1.00  1045.9±81.45µs
clone/btree/1000                         1.00     12.3±0.13µs
clone/btree/10000                        1.00    133.5±2.84µs
clone/btree/100000                       1.00      2.6±0.09ms
cursor/bptree/1000                       1.00      4.7±0.02µs
cursor/bptree/10000                      1.00     48.6±0.42µs
cursor/bptree/100000                     1.00    486.2±3.31µs
drop/bptree/1000                         1.00  1393.4±18.35ns
drop/bptree/10000                        1.00     15.7±0.16µs
drop/bptree/100000                       1.00   345.8±16.61µs
drop/btree/1000                          1.00      7.8±0.07µs
drop/btree/10000                         1.00     85.4±1.23µs
drop/btree/100000                        1.00  1824.9±52.91µs
into_iter/bptree/1000                    1.00  1398.9±24.90ns
into_iter/bptree/10000                   1.00     15.3±0.33µs
into_iter/bptree/100000                  1.00   326.3±19.66µs
into_iter/btree/1000                     1.00      7.9±0.07µs
into_iter/btree/10000                    1.00     85.2±1.14µs
into_iter/btree/100000                   1.00  1838.8±61.67µs
iter/bptree/1000                         1.00    397.8±4.35ns
iter/bptree/10000                        1.00      5.3±0.03µs
iter/bptree/100000                       1.00     57.3±0.28µs
iter/btree/1000                          1.00    843.5±6.98ns
iter/btree/10000                         1.00     11.2±0.10µs
iter/btree/100000                        1.00    216.6±1.98µs
ordered_get/bptree/1000                  1.00     10.3±0.06µs
ordered_get/bptree/10000                 1.00    111.8±4.24µs
ordered_get/bptree/100000                1.00   1164.3±1.80µs
ordered_get/btree/1000                   1.00     24.9±4.07µs
ordered_get/btree/10000                  1.00    423.8±1.59µs
ordered_get/btree/100000                 1.00      4.7±0.02ms
ordered_insert/bptree bulk/1000          1.00      6.1±0.04µs
ordered_insert/bptree bulk/10000         1.00     69.2±2.56µs
ordered_insert/bptree bulk/100000        1.00   938.2±30.39µs
ordered_insert/bptree/1000               1.00     15.2±0.11µs
ordered_insert/bptree/10000              1.00    163.2±1.36µs
ordered_insert/bptree/100000             1.00      2.0±0.03ms
ordered_insert/btree/1000                1.00     51.0±1.25µs
ordered_insert/btree/10000               1.00    753.7±7.59µs
ordered_insert/btree/100000              1.00      8.9±0.09ms
ordered_remove/bptree/1000               1.00     62.7±0.34µs
ordered_remove/bptree/10000              1.00    658.9±1.83µs
ordered_remove/bptree/100000             1.00      7.3±0.11ms
ordered_remove/btree/1000                1.00     31.9±0.26µs
ordered_remove/btree/10000               1.00    352.6±3.90µs
ordered_remove/btree/100000              1.00      4.6±0.12ms
random_get/bptree/1000                   1.00     22.6±0.56µs
random_get/bptree/10000                  1.00    990.6±8.44µs
random_get/bptree/100000                 1.00     13.7±0.01ms
random_get/btree/1000                    1.00     14.4±0.11µs
random_get/btree/10000                   1.00    651.1±3.97µs
random_get/btree/100000                  1.00      9.4±0.14ms
random_insert/bptree sort_load/1000      1.00     43.3±0.16µs
random_insert/bptree sort_load/10000     1.00    676.9±7.22µs
random_insert/bptree sort_load/100000    1.00      9.5±0.08ms
random_insert/bptree/1000                1.00     65.0±2.79µs
random_insert/bptree/10000               1.00  1391.2±14.28µs
random_insert/bptree/100000              1.00     18.8±0.17ms
random_insert/btree/1000                 1.00     54.4±4.52µs
random_insert/btree/10000                1.00    949.8±8.07µs
random_insert/btree/100000               1.00     13.9±0.11ms
random_remove/bptree/1000                1.00     67.4±2.21µs
random_remove/bptree/10000               1.00   1249.4±8.83µs
random_remove/bptree/100000              1.00     17.3±0.29ms
random_remove/btree/1000                 1.00     57.3±3.65µs
random_remove/btree/10000                1.00    920.1±8.75µs
random_remove/btree/100000               1.00     12.8±0.21ms
```

use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
mod models;
use models::*;

use std::collections::BTreeMap;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use sweep_bptree::{BPlusTree, NodeStoreVec};

const COUNTS: [usize; 3] = [1000, 10000, 10_0000];
const RAND_SEED: u64 = 123;

type NodeStoreBench = NodeStoreVec<Point, Value, 64, 65, 64>;

fn benchmark_bp_tree(c: &mut Criterion) {
    for count in COUNTS {
        c.bench_function(format!("bptree ordered_insert {count}").as_str(), |b| {
            b.iter(|| {
                let node_store = NodeStoreBench::new();
                let mut tree = BPlusTree::new(node_store);

                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.insert(k, Value::default());
                }
                tree
            });
        });

        c.bench_function(format!("bptree random_insert {count}").as_str(), |b| {
            let mut keys = vec![];
            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                keys.push(k);
            }

            let mut r = StdRng::seed_from_u64(RAND_SEED);
            keys.shuffle(&mut r);
            b.iter(|| {
                let node_store = NodeStoreBench::new();
                let mut tree = BPlusTree::new(node_store);

                for k in &keys {
                    tree.insert(*k, Value::default());
                }

                tree
            });
        });

        c.bench_function(format!("bptree clone {count}").as_str(), |b| {
            let tree = create_tree(count);
            b.iter(|| black_box(tree.clone()));
        });

        c.bench_function(format!("bptree drop {count}").as_str(), |b| {
            b.iter_batched(
                || create_tree(count),
                |tree| {
                    drop(tree);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        c.bench_function(format!("bptree ordered_remove {count}").as_str(), |b| {
            let node_store = NodeStoreBench::new();
            let mut tree = BPlusTree::new(node_store);

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let mut tree = tree.clone();
                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.remove(&k);
                }
                tree
            });
        });

        c.bench_function(format!("bptree random_remove {count}").as_str(), |b| {
            let tree = create_tree(count);

            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            let mut r = StdRng::seed_from_u64(RAND_SEED);
            keys.shuffle(&mut r);

            b.iter(|| {
                let mut tree = tree.clone();
                for k in keys.iter() {
                    tree.remove(&k);
                }
                tree
            });
        });

        c.bench_function(format!("bptree ordered_get {count}").as_str(), |b| {
            let tree = create_tree(count);

            b.iter(|| {
                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.get(&k);
                }
            });
        });

        c.bench_function(format!("bptree random_get {count}").as_str(), |b| {
            let tree = create_tree(count);

            let mut r = StdRng::seed_from_u64(RAND_SEED);
            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            keys.shuffle(&mut r);

            b.iter(|| {
                for k in keys.iter() {
                    tree.get(&k);
                }
            });
        });

        c.bench_function(format!("bptree iter {count}").as_str(), |b| {
            let node_store = NodeStoreBench::new();
            let mut tree = BPlusTree::new(node_store);

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let c = tree.iter().count();
                assert_eq!(c, tree.len());
            });
        });

        // note: this into_iter is slower than iter, mostly due to it has to drop items
        c.bench_function(format!("bptree into_iter {count}").as_str(), |b| {
            let tree = create_tree(count);

            b.iter_batched(
                || tree.clone(),
                |tree| {
                    let count = tree.len();
                    let c = tree.into_iter().count();
                    assert_eq!(c, count);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        c.bench_function(format!("bptree cursor {count}").as_str(), |b| {
            let node_store = NodeStoreBench::new();
            let mut tree = BPlusTree::new(node_store);

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let mut c = tree.cursor_first().unwrap();
                let mut count = 1;
                while let Some(next) = c.next_with_value(&tree) {
                    count += 1;
                    c = next.0;
                }
                assert_eq!(count, tree.len());
            });
        });
    }
}

fn benchmark_btree(c: &mut Criterion) {
    for count in COUNTS {
        c.bench_function(format!("btree ordered_insert {count}").as_str(), |b| {
            b.iter(|| {
                let mut tree = BTreeMap::<Point, Value>::new();

                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.insert(k, Value::default());
                }
            });
        });

        c.bench_function(format!("btree random_insert {count}").as_str(), |b| {
            let mut keys = vec![];
            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                keys.push(k);
            }

            let mut r = StdRng::seed_from_u64(RAND_SEED);
            keys.shuffle(&mut r);
            b.iter(|| {
                let mut tree = BTreeMap::new();

                for k in &keys {
                    tree.insert(*k, Value::default());
                }
                tree
            });
        });

        c.bench_function(format!("btree clone {count}").as_str(), |b| {
            let tree = create_btree(count);
            b.iter(|| {
                black_box(tree.clone());
            });
        });

        c.bench_function(format!("btree ordered_remove {count}").as_str(), |b| {
            let mut tree = BTreeMap::<Point, Value>::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let mut tree = tree.clone();
                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.remove(&k);
                }
                tree
            });
        });

        c.bench_function(format!("btree random_remove {count}").as_str(), |b| {
            let tree = create_btree(count);

            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            let mut r = StdRng::seed_from_u64(RAND_SEED);
            keys.shuffle(&mut r);

            b.iter(|| {
                let mut tree = tree.clone();
                for k in keys.iter() {
                    tree.remove(&k);
                }
            });
        });

        c.bench_function(format!("btree ordered_get {count}").as_str(), |b| {
            let mut tree = BTreeMap::<Point, Value>::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.get(&k);
                }
            });
        });

        c.bench_function(format!("btree random_get {count}").as_str(), |b| {
            let mut tree = BTreeMap::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            let mut r = StdRng::seed_from_u64(RAND_SEED);
            keys.shuffle(&mut r);

            b.iter(|| {
                for k in keys.iter() {
                    tree.get(&k);
                }
            });
        });

        c.bench_function(format!("btree iter {count}").as_str(), |b| {
            let mut tree = BTreeMap::<Point, Value>::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let c = tree.iter().count();
                assert_eq!(c, tree.len());
            });
        });

        c.bench_function(format!("btree drop {count}").as_str(), |b| {
            b.iter_batched(
                || create_btree(count),
                |tree| drop(tree),
                criterion::BatchSize::NumIterations(1),
            )
        });
    }
}

fn create_tree(count: usize) -> BPlusTree<NodeStoreBench> {
    let node_store = NodeStoreBench::new();
    let mut tree = BPlusTree::new(node_store);

    let mut keys = (0..count).collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for i in keys {
        let k = Point {
            x: i as f64,
            y: i as f64,
        };
        tree.insert(k, Value::default());
    }

    tree
}

fn create_btree(count: usize) -> BTreeMap<Point, Value> {
    let mut tree = BTreeMap::default();

    let mut keys = (0..count).collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for i in keys {
        let k = Point {
            x: i as f64,
            y: i as f64,
        };
        tree.insert(k, Value::default());
    }

    tree
}

criterion_group!(benches, benchmark_bp_tree, benchmark_btree,);
criterion_main!(benches);

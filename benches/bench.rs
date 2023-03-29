mod sorted_vec;
use rand::seq::SliceRandom;
use sorted_vec::SortedVec;
mod models;
use models::*;

use std::collections::BTreeMap;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use sweep_bptree::{BPlusTree, NodeStoreVec};

const COUNTS: [usize; 2] = [1000, 10000];

type NodeStoreBench = NodeStoreVec<Point, Value, 64, 65, 64>;

fn benchmark_sorted_vec(c: &mut Criterion) {
    for count in COUNTS {
        c.bench_function(format!("vec insert {count}").as_str(), |b| {
            b.iter(|| {
                let mut tree = SortedVec::new();

                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.insert(k, Value::default());
                }
            });
        });

        c.bench_function(format!("vec remove {count}").as_str(), |b| {
            let mut tree = SortedVec::new();

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
            });
        });

        c.bench_function(format!("vec get {count}").as_str(), |b| {
            let mut tree = SortedVec::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let tree = tree.clone();
                for i in 0..count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.get(&k);
                }
            });
        });

        c.bench_function(format!("vec iter {count}").as_str(), |b| {
            let mut tree = SortedVec::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            b.iter(|| {
                let c = tree.iter().fold(0, |a, _i| a + black_box(1));
                assert_eq!(c, tree.len());
            });
        });
    }
}

fn benchmark_bp_tree(c: &mut Criterion) {
    for count in COUNTS {
        c.bench_function(format!("bptree insert {count}").as_str(), |b| {
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
            });
        });
    }

    for count in COUNTS {
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
            });
        });

        c.bench_function(format!("bptree random_remove {count}").as_str(), |b| {
            let node_store = NodeStoreBench::new();
            let mut tree = BPlusTree::new(node_store);

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            keys.shuffle(&mut rand::thread_rng());

            b.iter(|| {
                let mut tree = tree.clone();
                for k in keys.iter() {
                    tree.remove(&k);
                }
            });
        });

        c.bench_function(format!("bptree ordered_get {count}").as_str(), |b| {
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
                let tree = tree.clone();
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
            let node_store = NodeStoreBench::new();
            let mut tree = BPlusTree::new(node_store);

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            keys.shuffle(&mut rand::thread_rng());

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
        c.bench_function(format!("btree insert {count}").as_str(), |b| {
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
            });
        });

        c.bench_function(format!("btree random_remove {count}").as_str(), |b| {
            let mut tree = BTreeMap::<Point, Value>::new();

            for i in 0..count {
                let k = Point {
                    x: i as f64,
                    y: i as f64,
                };
                tree.insert(k, Value::default());
            }

            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            keys.shuffle(&mut rand::thread_rng());

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
                let tree = tree.clone();
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
            keys.shuffle(&mut rand::thread_rng());

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
    }
}

criterion_group!(
    benches,
    benchmark_bp_tree,
    benchmark_btree,
    benchmark_sorted_vec
);
criterion_main!(benches);

use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
mod models;
use models::*;

use std::collections::BTreeMap;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use sweep_bptree::{BPlusTree, NodeStoreVec};

const COUNTS: [usize; 3] = [1000, 10000, 10_0000];
const RAND_SEED: u64 = 123;

type NodeStoreBench = NodeStoreVec<Point, Value, 64, 65, 64>;

fn bench_ordered_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("ordered_input");

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter(|| {
                let node_store = NodeStoreBench::new();
                let mut tree = BPlusTree::new(node_store);

                for i in 0..*count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.insert(k, Value::default());
                }
                tree
            });
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter(|| {
                let mut tree = BTreeMap::<Point, Value>::new();

                for i in 0..*count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    tree.insert(k, Value::default());
                }

                tree
            });
        });
    }
}

fn bench_random_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_insert");

    for count in COUNTS {
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

        group.bench_function(BenchmarkId::new("bptree", count), |b| {
            b.iter(|| {
                let node_store = NodeStoreBench::new();
                let mut tree = BPlusTree::new(node_store);

                for k in &keys {
                    tree.insert(*k, Value::default());
                }

                tree
            });
        });

        group.bench_function(BenchmarkId::new("btree", count), |b| {
            b.iter(|| {
                let mut tree = BTreeMap::new();

                for k in &keys {
                    tree.insert(*k, Value::default());
                }
                tree
            });
        });
    }
}

fn bench_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("clone");
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_tree(*count);
            b.iter(|| black_box(tree.clone()));
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree(*count);
            b.iter(|| black_box(tree.clone()));
        });
    }
}

fn bench_drop(c: &mut Criterion) {
    let mut group = c.benchmark_group("drop");
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || create_tree(*count),
                |tree| {
                    drop(tree);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter_batched(
                || create_btree(*count),
                |tree| {
                    drop(tree);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });
    }
}

fn bench_iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_tree(*count);
            b.iter(|| {
                let c = tree.iter().count();
                assert_eq!(c, tree.len());
            });
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree(*count);
            b.iter(|| {
                let c = tree.iter().count();
                assert_eq!(c, tree.len());
            });
        });
    }
}

fn bench_into_iter(c: &mut Criterion) {
    // note: into_iter is slower than iter, mostly due to heavy drop
    let mut group = c.benchmark_group("into_iter");
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || create_tree(*count),
                |tree| {
                    let count = tree.len();
                    let c = tree.into_iter().count();
                    assert_eq!(c, count);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter_batched(
                || create_btree(*count),
                |tree| {
                    let count = tree.len();
                    let c = tree.into_iter().count();
                    assert_eq!(c, count);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });
    }
}

fn bench_ordered_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("ordered_remove");

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || create_tree(*count),
                |mut tree| {
                    for i in 0..*count {
                        let k = Point {
                            x: i as f64,
                            y: i as f64,
                        };
                        assert!(tree.remove(&k).is_some());
                    }
                    tree
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter_batched(
                || create_btree(*count),
                |mut tree| {
                    for i in 0..*count {
                        let k = Point {
                            x: i as f64,
                            y: i as f64,
                        };
                        assert!(tree.remove(&k).is_some());
                    }
                    tree
                },
                criterion::BatchSize::NumIterations(1),
            );
        });
    }
}

fn bench_random_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_remove");

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || {
                    let tree = create_tree(*count);

                    let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
                    let mut r = StdRng::seed_from_u64(RAND_SEED);
                    keys.shuffle(&mut r);
                    (tree, keys)
                },
                |(mut tree, keys)| {
                    for k in keys.iter() {
                        tree.remove(&k);
                    }
                    tree
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter_batched(
                || {
                    let tree = create_btree(*count);

                    let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
                    let mut r = StdRng::seed_from_u64(RAND_SEED);
                    keys.shuffle(&mut r);
                    (tree, keys)
                },
                |(mut tree, keys)| {
                    for k in keys.iter() {
                        tree.remove(&k);
                    }
                    tree
                },
                criterion::BatchSize::NumIterations(1),
            );
        });
    }
}

fn bench_ordered_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("ordered_get");

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_tree(*count);
            b.iter(|| {
                for i in 0..*count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    assert!(tree.get(&k).is_some());
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree(*count);
            b.iter(|| {
                for i in 0..*count {
                    let k = Point {
                        x: i as f64,
                        y: i as f64,
                    };
                    assert!(tree.get(&k).is_some());
                }
            });
        });
    }
}

fn bench_random_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_get");

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_tree(*count);

            let mut r = StdRng::seed_from_u64(RAND_SEED);
            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            keys.shuffle(&mut r);

            b.iter(|| {
                for k in keys.iter() {
                    assert!(tree.get(&k).is_some());
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree(*count);

            let mut r = StdRng::seed_from_u64(RAND_SEED);
            let mut keys = tree.iter().map(|(k, _v)| k).cloned().collect::<Vec<_>>();
            keys.shuffle(&mut r);

            b.iter(|| {
                for k in keys.iter() {
                    assert!(tree.get(&k).is_some());
                }
            });
        });
    }
}

fn bench_cursor(c: &mut Criterion) {
    let mut group = c.benchmark_group("cursor");
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_tree(*count);

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

criterion_group!(
    benches,
    bench_clone,
    bench_drop,
    bench_iter,
    bench_into_iter,
    bench_ordered_insert,
    bench_random_insert,
    bench_ordered_remove,
    bench_random_remove,
    bench_ordered_get,
    bench_random_get,
    bench_cursor,
);
criterion_main!(benches);

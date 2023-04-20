use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
mod models;
use models::*;

use std::collections::BTreeMap;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use sweep_bptree::{BPlusTree, NodeStoreVec};

const COUNTS: [usize; 3] = [1000, 10000, 10_0000];
const RAND_SEED: u64 = 123;

type NodeStoreBench<K> = NodeStoreVec<K, Value>;

fn bench_ordered_insert<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("ordered_insert/{}", K::name()));

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter(|| {
                let mut tree = BPlusTree::<NodeStoreBench<K>>::new(NodeStoreBench::<K>::new());
                for i in 0..*count {
                    let k = K::from_i(i);
                    tree.insert(k, Value::default());
                }
                tree
            });
        });

        group.bench_with_input(
            BenchmarkId::new("bptree_bulk", count),
            &count,
            |b, count| {
                b.iter(|| {
                    let mut kvs = Vec::with_capacity(*count);

                    for i in 0..*count {
                        let k = K::from_i(i);
                        kvs.push((k, Value::default()));
                    }

                    BPlusTree::<NodeStoreBench<K>>::bulk_load(kvs)
                });
            },
        );

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter(|| {
                let mut tree = BTreeMap::<K, Value>::new();

                for i in 0..*count {
                    let k = K::from_i(i);
                    tree.insert(k, Value::default());
                }

                tree
            });
        });
    }
}

fn bench_random_insert<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("random_insert/{}", K::name()));

    for count in COUNTS {
        let mut keys = vec![];
        for i in 0..count {
            let k = K::from_i(i);
            keys.push(k);
        }

        let mut r = StdRng::seed_from_u64(RAND_SEED);
        keys.shuffle(&mut r);

        group.bench_function(BenchmarkId::new("bptree", count), |b| {
            b.iter(|| {
                let node_store = NodeStoreBench::<K>::new();
                let mut tree = BPlusTree::new(node_store);

                for k in &keys {
                    tree.insert(k.clone(), Value::default());
                }

                tree
            });
        });

        group.bench_function(BenchmarkId::new("bptree_sort_load", count), |b| {
            b.iter_batched(
                || keys.clone(),
                |mut keys| {
                    keys.sort();
                    BPlusTree::<NodeStoreBench<K>>::bulk_load(
                        keys.into_iter()
                            .map(|k| (k, Value::default()))
                            .collect::<Vec<_>>(),
                    )
                },
                BatchSize::NumIterations(1),
            )
        });

        group.bench_function(BenchmarkId::new("btree", count), |b| {
            b.iter(|| {
                let mut tree = BTreeMap::new();

                for k in &keys {
                    tree.insert(k.clone(), Value::default());
                }
                tree
            });
        });
    }
}

fn bench_clone<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("clone/{}", K::name()));
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_bptree::<K>(*count);
            b.iter(|| black_box(tree.clone()));
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree::<K>(*count);
            b.iter(|| black_box(tree.clone()));
        });
    }
}

fn bench_drop<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("drop/{}", K::name()));
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || create_bptree::<K>(*count),
                |tree| {
                    drop(tree);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter_batched(
                || create_btree::<K>(*count),
                |tree| {
                    drop(tree);
                },
                criterion::BatchSize::NumIterations(1),
            );
        });
    }
}

fn bench_iter<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("iter/{}", K::name()));
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_bptree::<K>(*count);
            b.iter(|| {
                let c = tree.iter().count();
                assert_eq!(c, tree.len());
            });
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree::<K>(*count);
            b.iter(|| {
                let c = tree.iter().count();
                assert_eq!(c, tree.len());
            });
        });
    }
}

fn bench_into_iter<K: TestKey>(c: &mut Criterion) {
    // note: into_iter is slower than iter, mostly due to heavy drop
    let mut group = c.benchmark_group(format!("into_iter/{}", K::name()));
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || create_bptree::<K>(*count),
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
                || create_btree::<K>(*count),
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

fn bench_ordered_remove<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("ordered_remove/{}", K::name()));

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || create_bptree::<K>(*count),
                |mut tree| {
                    for i in 0..*count {
                        let k = K::from_i(i);
                        assert!(tree.remove(&k).is_some());
                    }
                    tree
                },
                criterion::BatchSize::NumIterations(1),
            );
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            b.iter_batched(
                || create_btree::<K>(*count),
                |mut tree| {
                    for i in 0..*count {
                        let k = K::from_i(i);
                        assert!(tree.remove(&k).is_some());
                    }
                    tree
                },
                criterion::BatchSize::NumIterations(1),
            );
        });
    }
}

fn bench_random_remove<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("random_remove/{}", K::name()));

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            b.iter_batched(
                || {
                    let tree = create_bptree::<K>(*count);

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
                    let tree = create_btree::<K>(*count);

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

fn bench_ordered_get<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("ordered_get/{}", K::name()));

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_bptree::<K>(*count);
            b.iter(|| {
                for i in 0..*count {
                    let k = K::from_i(i);
                    assert!(tree.get(&k).is_some());
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("btree", count), &count, |b, count| {
            let tree = create_btree::<K>(*count);
            b.iter(|| {
                for i in 0..*count {
                    let k = K::from_i(i);
                    assert!(tree.get(&k).is_some());
                }
            });
        });
    }
}

fn bench_random_get<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("random_get/{}", K::name()));

    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_bptree::<K>(*count);

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
            let tree = create_btree::<K>(*count);

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

fn bench_cursor<K: TestKey>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("cursor/{}", K::name()));
    for count in COUNTS {
        group.bench_with_input(BenchmarkId::new("bptree", count), &count, |b, count| {
            let tree = create_bptree::<K>(*count);

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

fn create_bptree<K: TestKey>(count: usize) -> BPlusTree<NodeStoreBench<K>> {
    let node_store = NodeStoreBench::new();
    let mut tree = BPlusTree::new(node_store);

    let mut keys = (0..count).collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for i in keys {
        let k = K::from_i(i);
        tree.insert(k, Value::default());
    }

    tree
}

fn create_btree<K: TestKey>(count: usize) -> BTreeMap<K, Value> {
    let mut tree = BTreeMap::default();

    let mut keys = (0..count).collect::<Vec<_>>();
    let mut r = StdRng::seed_from_u64(RAND_SEED);
    keys.shuffle(&mut r);

    for i in keys {
        let k = K::from_i(i);
        tree.insert(k, Value::default());
    }

    tree
}

criterion_group!(
    benches,
    bench_clone<Point>,
    bench_clone<String>,
    bench_drop<Point>,
    bench_drop<String>,
    bench_iter<Point>,
    bench_iter<String>,
    bench_into_iter<Point>,
    bench_into_iter<String>,
    bench_ordered_insert<Point>,
    bench_ordered_insert<String>,
    bench_random_insert<Point>,
    bench_random_insert<String>,
    bench_ordered_remove<Point>,
    bench_ordered_remove<String>,
    bench_random_remove<Point>,
    bench_random_remove<String>,
    bench_ordered_get<Point>,
    bench_ordered_get<String>,
    bench_random_get<Point>,
    bench_random_get<String>,
    bench_random_get<std::rc::Rc<String>>,
    bench_cursor<Point>,
    bench_cursor<String>,
);
criterion_main!(benches);

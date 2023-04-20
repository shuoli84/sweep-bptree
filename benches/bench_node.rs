mod models;
use models::*;

use criterion::{criterion_group, criterion_main, Criterion};

use sweep_bptree::tree::{INode, InnerNode, InnerNodeId, LNode, LeafNode, NodeId};

fn bench_inner<K: TestKey, const N: usize, const C: usize>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("inner_node_{}_{N}", K::name()));

    let node = InnerNode::<K, (), N, C>::new_from_iter(
        (0..N).map(|i| K::from_i(i)),
        (0..C).map(|i| NodeId::Inner(InnerNodeId::from_usize(i))),
        (0..C).map(|_| ()),
    );

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            for i in 0..128 {
                let key = K::from_i(i);
                node.locate_child(&key);
            }
        })
    });

    group.finish();
}

fn bench_leaf<K: TestKey, V: Default>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("leaf_node_{}", K::name()));

    let keys = (0..128).map(|i| K::from_i(i)).collect::<Vec<_>>();

    let mut node = LeafNode::<K, V>::new();
    node.set_data((0..64).map(|i| (K::from_i(i), V::default())));

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            bench_leaf_inner(&keys, &node);
        })
    });

    group.finish();
}

#[inline(never)]
fn bench_leaf_inner<K: TestKey, V: Default>(keys: &[K], node: &LeafNode<K, V>) {
    let mut c = 0;
    for key in keys {
        match node.locate_slot(&key) {
            Ok(_) => c += 1,
            Err(_) => {}
        }
    }
    assert!(c > 0);
}

criterion_group!(benches,
    bench_inner<Point, 32, 33>,
    bench_leaf<Point, Value>,
    bench_inner<Point, 64, 65>,
);
criterion_main!(benches);

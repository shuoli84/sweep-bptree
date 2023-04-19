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

fn bench_leaf<K: TestKey, V: Default, const N: usize>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("leaf_node_{}_{N}", K::name()));

    let keys = (0..128).map(|i| K::from_i(i)).collect::<Vec<_>>();

    let mut node = LeafNode::<K, V, N>::new();
    node.set_data((0..N).map(|i| (K::from_i(i), V::default())));

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            bench_leaf_inner(&keys, &node);
        })
    });

    group.finish();
}

#[inline(never)]
fn bench_leaf_inner<K: TestKey, V: Default, const N: usize>(keys: &[K], node: &LeafNode<K, V, N>) {
    let mut c = 0;
    for key in keys {
        match node.locate_slot(&key) {
            Ok(_) => c += 1,
            Err(_) => {}
        }
    }
    assert!(c > 0);
}

#[inline(never)]
fn bench_leaf_0_32(c: &mut Criterion) {
    type K = Point3<0>;
    const N: usize = 32;
    type V = Value;

    let mut group = c.benchmark_group(format!("a_leaf_node_0_32"));

    let keys = (0..128).map(|i| K::from_i(i)).collect::<Vec<_>>();

    let mut node = LeafNode::<K, Value, N>::new();
    node.set_data((0..N).map(|i| (K::from_i(i), V::default())));

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            bench_leaf_inner_0_32(&keys, &node);
        })
    });

    group.finish();
}

#[inline(never)]
fn bench_leaf_1_32(c: &mut Criterion) {
    type K = Point3<1>;
    const N: usize = 32;
    type V = Value;

    let mut group = c.benchmark_group(format!("a_leaf_node_0_32"));

    let keys = (0..128).map(|i| K::from_i(i)).collect::<Vec<_>>();

    let mut node = LeafNode::<K, Value, N>::new();
    node.set_data((0..N).map(|i| (K::from_i(i), V::default())));

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            bench_leaf_inner_1_32(&keys, &node);
        })
    });

    group.finish();
}

#[inline(never)]
fn bench_leaf_8_32(c: &mut Criterion) {
    type K = Point3<8>;
    const N: usize = 32;
    type V = Value;

    let mut group = c.benchmark_group(format!("a_leaf_node_8_32"));

    let keys = (0..128).map(|i| K::from_i(i)).collect::<Vec<_>>();

    let mut node = LeafNode::<K, Value, N>::new();
    node.set_data((0..N).map(|i| (K::from_i(i), V::default())));

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            bench_leaf_inner_8_32(&keys, &node);
        })
    });

    group.finish();
}

#[inline(never)]
fn bench_leaf_9_32(c: &mut Criterion) {
    type K = Point3<9>;
    const N: usize = 32;
    type V = Value;

    let mut group = c.benchmark_group(format!("a_leaf_node_9_32"));

    let keys = (0..128).map(|i| K::from_i(i)).collect::<Vec<_>>();

    let mut node = LeafNode::<K, Value, N>::new();
    node.set_data((0..N).map(|i| (K::from_i(i), V::default())));

    group.bench_function("locate_child", |b| {
        b.iter(|| {
            bench_leaf_inner_9_32(&keys, &node);
        })
    });

    group.finish();
}

#[inline(never)]
fn bench_leaf_inner_0_32(keys: &[Point3<0>], node: &LeafNode<Point3<0>, Value, 32>) {
    let mut c = 0;
    for key in keys {
        match node.locate_slot(&key) {
            Ok(_) => c += 1,
            Err(_) => {}
        }
    }
    assert!(c > 0);
}

#[inline(never)]
fn bench_leaf_inner_1_32(keys: &[Point3<1>], node: &LeafNode<Point3<1>, Value, 32>) {
    let mut c = 0;
    for key in keys {
        match node.locate_slot(&key) {
            Ok(_) => c += 1,
            Err(_) => {}
        }
    }
    assert!(c > 0);
}

#[inline(never)]
fn bench_leaf_inner_8_32(keys: &[Point3<8>], node: &LeafNode<Point3<8>, Value, 32>) {
    let mut c = 0;
    for key in keys {
        match node.locate_slot(&key) {
            Ok(_) => c += 1,
            Err(_) => {}
        }
    }
    assert!(c > 0);
}

#[inline(never)]
fn bench_leaf_inner_9_32(keys: &[Point3<9>], node: &LeafNode<Point3<9>, Value, 32>) {
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
    bench_leaf<Point, Value, 32>,
    bench_inner<Point, 64, 65>,
    bench_leaf<Point, Value, 64>,

    // 24
    bench_inner<Point3<0>, 32, 33>,
    bench_leaf<Point3<0>, Value, 32>,
    bench_inner<Point3<0>, 64, 65>,
    bench_leaf<Point3<0>, Value, 64>,

    // 24 + 8 = 32
    bench_inner<Point3<8>, 32, 33>,
    bench_leaf<Point3<8>, Value, 32>,
    bench_inner<Point3<8>, 64, 65>,
    bench_leaf<Point3<8>, Value, 64>,

    // 24 + 33 = 57
    bench_inner<Point3<33>, 32, 33>,
    bench_leaf<Point3<33>, Value, 32>,
    bench_inner<Point3<33>, 64, 65>,
    bench_leaf<Point3<33>, Value, 64>,

    bench_leaf_0_32,
    bench_leaf_1_32,
    bench_leaf_8_32,
    bench_leaf_9_32,
);
criterion_main!(benches);

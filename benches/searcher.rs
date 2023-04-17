mod models;

use sweep_bptree::key_search::*;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[inline(never)]
fn bench_for_searcher<S: KeySearcher<Key = usize>>(keys: &[usize], n: usize) {
    for i in 0..n {
        let r = S::search(&keys, &black_box(i));
        if i < keys.len() {
            assert_eq!(r.unwrap(), i);
        } else {
            assert!(r.is_err());
        }
    }
}

fn bench_key_searcher(c: &mut Criterion) {
    let mut g = c.benchmark_group("key_searcher");
    const N: usize = 64;
    let mut keys = vec![];
    for i in 0..64 {
        keys.push(i);
    }

    g.bench_function("binary_search", |b| {
        b.iter(|| {
            bench_for_searcher::<BinarySearch<_>>(&keys, N);
        });
    });

    g.bench_function("unfold_binary_search", |b| {
        b.iter(|| {
            bench_for_searcher::<UnrolledBinarySearch<_, 64>>(&keys, N);
        });
    });
}

criterion_group!(benches, bench_key_searcher);

criterion_main!(benches);

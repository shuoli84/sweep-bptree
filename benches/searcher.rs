mod models;

use sweep_bptree::key_search::*;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_key_searcher(c: &mut Criterion) {
    let mut g = c.benchmark_group("key_searcher");
    const N: usize = 64;
    let mut keys = [0; N];
    for i in 0..N {
        keys[i] = i;
    }

    g.bench_function("simd", |b| {
        b.iter(|| {
            for i in 0..N {
                assert_eq!(
                    SimdLinearSearch::<_, 4>::search(&keys, &black_box(i)).unwrap(),
                    i
                );
            }
        });
    });

    g.bench_function("binary_search", |b| {
        b.iter(|| {
            for i in 0..N {
                assert_eq!(BinarySearch::search(&keys, &black_box(i)).unwrap(), i);
            }
        });
    });

    g.bench_function("branchless_binary_search", |b| {
        b.iter(|| {
            for i in 0..N {
                assert_eq!(
                    BranchlessBinarySearch::search(&keys, &black_box(i)).unwrap(),
                    i
                );
            }
        });
    });

    g.bench_function("branchless_2_binary_search", |b| {
        b.iter(|| {
            for i in 0..N {
                assert_eq!(Branchless2Search::search(&keys, &black_box(i)).unwrap(), i);
            }
        });
    });

    g.bench_function("linear", |b| {
        b.iter(|| {
            for i in 0..N {
                assert_eq!(LinearSearch::search(&keys, &black_box(i)).unwrap(), i);
            }
        });
    });
}

criterion_group!(benches, bench_key_searcher);

criterion_main!(benches);

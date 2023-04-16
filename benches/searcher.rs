mod models;

use std::cmp::Ordering;

use sweep_bptree::key_search::*;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[inline(never)]
fn test_tttttt<S: KeySearcher<Key = usize>>(keys: &[usize], n: usize) {
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
    for i in 0..32 {
        keys.push(i);
    }

    g.bench_function("simd", |b| {
        b.iter(|| {
            test_tttttt::<SimdLinearSearch<_, 4>>(&keys, N);
        });
    });

    g.bench_function("binary_search", |b| {
        b.iter(|| {
            test_tttttt::<BinarySearch<_>>(&keys, N);
        });
    });

    g.bench_function("branchless_binary_search", |b| {
        b.iter(|| {
            test_tttttt::<BranchlessBinarySearch<_>>(&keys, N);
        });
    });

    g.bench_function("branchless_2_binary_search", |b| {
        b.iter(|| {
            test_tttttt::<Branchless2Search<_>>(&keys, N);
        });
    });

    g.bench_function("linear", |b| {
        b.iter(|| {
            test_tttttt::<LinearSearch<_>>(&keys, N);
        });
    });

    {
        let mut keys = [None; 64];
        for i in 0..32 {
            keys[i] = Some(i);
        }
        g.bench_function("optional_arr", |b| {
            b.iter(|| {
                for i in 0..N {
                    let r = test_optional_array(&keys, &black_box(i));
                    if i < 32 {
                        assert_eq!(r.unwrap(), i);
                    } else {
                        assert!(r.is_err());
                    }
                }
            })
        });
    }
    g.bench_function("arr_with_const_n", |b| {
        b.iter(|| {
            for i in 0..N {
                let r = test_array_with_const_n(&keys, &black_box(i), black_box(32));
                if i < 32 {
                    assert_eq!(r.unwrap(), i);
                } else {
                    assert!(r.is_err());
                }
            }
        })
    });
}

criterion_group!(benches, bench_key_searcher);

criterion_main!(benches);

pub fn test_optional_array(keys: &[Option<usize>; 64], k: &usize) -> Result<usize, usize> {
    let mut start = 0;
    let mut len = keys.len();
    for _ in 0..6 {
        len /= 2;
        let pivot = unsafe { keys.get_unchecked(start + len - 1) };
        let cmp = cmp_optional(pivot, k);
        if matches!(cmp, Ordering::Less) {
            start += len;
        }
    }

    let pivot = unsafe { keys.get_unchecked(start) };
    match cmp_optional(pivot, k) {
        Ordering::Less => Err(start + 1),
        Ordering::Equal => Ok(start),
        Ordering::Greater => Err(start),
    }
}

fn cmp_optional(pivot: &Option<usize>, k: &usize) -> Ordering {
    match pivot {
        Some(t) => t.cmp(k),
        None => Ordering::Greater,
    }
}

pub fn test_array_with_const_n(keys: &[usize], k: &usize, data_len: usize) -> Result<usize, usize> {
    let mut start = 0;
    let mut len = 64;
    for _ in 0..6 {
        len /= 2;
        let cmp = if start + len > data_len {
            Ordering::Greater
        } else {
            let pivot = unsafe { keys.get_unchecked(start + len - 1) };
            pivot.cmp(k)
        };

        if matches!(cmp, Ordering::Less) {
            start += len;
        }
    }

    let pivot = unsafe { keys.get_unchecked(start) };
    match pivot.cmp(k) {
        Ordering::Less => Err(start + 1),
        Ordering::Equal => Ok(start),
        Ordering::Greater => Err(start),
    }
}

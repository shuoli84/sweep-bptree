//! In order to optimize binary search, there are several ways:
//! 1. branchless
//! 2. unroll loops to reduce branch mis-prediction
//! 3. utilize cpu pipeline to reduce overall time cost
//! 
//! I've tried 1. and 3. but the result is not optimal, it could be my impl is
//! not good enough. But I get better result for approach 2. That's `UnrolledBinarySearch`
use std::{borrow::Borrow, cmp::Ordering};

/// A trait to abstract the key search algorithm
pub trait KeySearcher {
    type Key: Ord;

    /// search the k in search, returns same result as binary search
    fn search<Q: Ord + ?Sized>(keys: &[Self::Key], k: &Q) -> Result<usize, usize>
    where
        Self::Key: Borrow<Q>;
}

/// Standard binary search
pub struct BinarySearch<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for BinarySearch<K> {
    type Key = K;

    fn search<Q: Ord + ?Sized>(keys: &[Self::Key], k: &Q) -> Result<usize, usize>
    where
        Self::Key: Borrow<Q>,
    {
        keys.binary_search_by_key(&k, |k| k.borrow())
    }
}

/// A binary search impl which unfold by the compiler, it gives about 20% performance
/// gain over BinarySearch for simple Keys(e.g Primitive Copy types), but not suitable 
/// for complex keys(e.g: String, Vec etc).
pub struct UnrolledBinarySearch<K, const N: usize>(std::marker::PhantomData<K>);

impl<K: Ord, const N: usize> KeySearcher for UnrolledBinarySearch<K, N> {
    type Key = K;

    fn search<Q: Ord + ?Sized>(keys: &[Self::Key], k: &Q) -> Result<usize, usize>
    where
        Self::Key: Borrow<Q>,
    {
        let mut start = 0;
        // Use the const N, so compiler knows each step's start and len.
        // for relative small N(64 as tested), the following loop is
        // unrolled
        let mut len = N;
        let data_len = keys.len();
        if keys.is_empty() {
            return Err(0);
        }

        while len > 1 {
            // ceil(len / 2)
            len = (len - 1) / 2 + 1;
            let cmp = if start + len >= data_len {
                Ordering::Greater
            } else {
                let pivot = unsafe { keys.get_unchecked(start + len - 1) };
                pivot.borrow().cmp(k)
            };

            if matches!(cmp, Ordering::Less) {
                start += len;
            }
        }

        let pivot = unsafe { keys.get_unchecked(start) };
        match pivot.borrow().cmp(k) {
            Ordering::Less => Err(start + 1),
            Ordering::Equal => Ok(start),
            Ordering::Greater => Err(start),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::any::type_name;

    use super::*;

    fn test_searcher<S: KeySearcher<Key = u32>, const N: usize>() {
        println!("testing {} {N}", type_name::<S>());
        let mut keys = vec![];
        for i in 0..N {
            keys.push((i as u32 + 1) * 2);
        }

        dbg!(&keys);

        assert_eq!(S::search(&keys, &0), Err(0));

        for i in 0..N {
            assert_eq!(S::search(&keys, dbg!(&((i as u32 + 1) * 2))), Ok(i));
            assert_eq!(S::search(&keys, dbg!(&((i as u32 + 1) * 2 - 1))), Err(i));
        }

        assert_eq!(S::search(&keys, dbg!(&((N as u32 + 1) * 2))), Err(N));
        assert_eq!(S::search(&keys, dbg!(&((N as u32 + 1) * 2 - 1))), Err(N));
    }

    #[test]
    fn test_searchers() {
        test_searcher::<BinarySearch<_>, 64>();
        test_searcher::<UnrolledBinarySearch<_, 64>, 64>();
        test_searcher::<BinarySearch<_>, 32>();
        test_searcher::<UnrolledBinarySearch<_, 64>, 32>();
        test_searcher::<UnrolledBinarySearch<_, 6>, 4>();
        test_searcher::<UnrolledBinarySearch<_, 5>, 4>();
        test_searcher::<UnrolledBinarySearch<_, 4>, 0>();
        test_searcher::<UnrolledBinarySearch<_, 4>, 1>();
        test_searcher::<UnrolledBinarySearch<_, 4>, 2>();
        test_searcher::<UnrolledBinarySearch<_, 4>, 3>();
        test_searcher::<UnrolledBinarySearch<_, 4>, 4>();
    }
}

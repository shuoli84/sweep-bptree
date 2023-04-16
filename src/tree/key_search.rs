use std::cmp::Ordering;

pub trait KeySearcher {
    type Key: Ord;

    /// search the k in search, returns same result as binary search
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize>;
}

pub struct BinarySearch<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for BinarySearch<K> {
    type Key = K;

    // #[inline(never)]
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        keys.binary_search(k)
    }
}

pub struct BranchlessBinarySearch<K>(std::marker::PhantomData<K>);

fn search<K: Ord, const N: usize>(keys: &[K], k: &K) -> Result<usize, usize> {
    let mut start = 0;
    let mut len = N;
    loop {
        len /= 2;
        let pivot = unsafe { keys.get_unchecked(start + len - 1) };
        let cmp = pivot.cmp(k);

        if matches!(cmp, Ordering::Less) {
            start += len;
        }

        if len == 1 {
            let pivot = unsafe { keys.get_unchecked(start) };
            let cmp = pivot.cmp(k);

            return match cmp {
                Ordering::Greater => Err(start),
                Ordering::Equal => Ok(start),
                Ordering::Less => {
                    start += len;
                    let pivot = unsafe { keys.get_unchecked(start) };
                    let cmp = pivot.cmp(k);
                    match cmp {
                        Ordering::Equal => Ok(start),
                        Ordering::Less => Err(start),
                        Ordering::Greater => Err(start),
                    }
                }
            };
        }
    }
}

impl<K: Ord + std::fmt::Debug> KeySearcher for BranchlessBinarySearch<K> {
    type Key = K;

    // #[inline(never)]
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        if keys.len() >= 48 {
            match search::<_, 48>(&keys[..48], &k) {
                Ok(idx) => Ok(idx),
                Err(idx) if idx < 47 => Err(idx),
                _ => match keys[48..].binary_search(k) {
                    Ok(idx) => Ok(48 + idx),
                    Err(idx) => Err(48 + idx),
                },
            }
        } else if keys.len() >= 32 {
            match search::<_, 32>(&keys[..32], &k) {
                Ok(idx) => Ok(idx),
                Err(idx) if idx < 31 => Err(idx),
                _ => match keys[32..].binary_search(k) {
                    Ok(idx) => Ok(32 + idx),
                    Err(idx) => Err(32 + idx),
                },
            }
        } else {
            keys.binary_search(k)
        }
    }
}

pub struct Branchless2Search<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for Branchless2Search<K> {
    type Key = K;

    // #[inline(never)]
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        let mut start = 0;
        let mut len = 64;
        let data_len = keys.len();

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
}

pub struct LinearSearch<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for LinearSearch<K> {
    type Key = K;

    #[inline(never)]
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        keys.iter()
            .enumerate()
            .find_map(|(idx, key)| match key.cmp(k) {
                std::cmp::Ordering::Less => None,
                std::cmp::Ordering::Equal => Some(Ok(idx)),
                std::cmp::Ordering::Greater => Some(Err(idx)),
            })
            .unwrap_or(Err(keys.len()))
    }
}

pub struct SimdLinearSearch<K, const N: usize>(std::marker::PhantomData<K>);

impl<K: Ord, const N: usize> KeySearcher for SimdLinearSearch<K, N> {
    type Key = K;

    #[inline(never)]
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        // we split this into chunks
        let chunk_size = N;

        let off = keys
            .chunks_exact(chunk_size)
            .take_while(|key_chunk| {
                let mut all_less: bool = true;
                key_chunk
                    .iter()
                    .for_each(|key| all_less = all_less & (key.cmp(k) == Ordering::Less));
                all_less
            })
            .count()
            * chunk_size;

        for (idx, key) in unsafe { keys.get_unchecked(off..) }.iter().enumerate() {
            match key.cmp(k) {
                std::cmp::Ordering::Less => continue,
                std::cmp::Ordering::Equal => return Ok(off + idx),
                std::cmp::Ordering::Greater => return Err(off + idx),
            }
        }
        Err(keys.len())
    }
}

#[cfg(test)]
mod tests {
    use std::any::type_name;

    use super::*;

    fn test_searcher<S: KeySearcher<Key = u32>>() {
        println!("testing {}", type_name::<S>());
        let mut keys = [0u32; 64];
        for i in 0..64 {
            keys[i] = (i as u32 + 1) * 2;
        }
        assert_eq!(S::search(&keys, &1), Err(0));
        assert_eq!(S::search(&keys, &2), Ok(0));
        assert_eq!(S::search(&keys, &3), Err(1));
        assert_eq!(S::search(&keys, &4), Ok(1));
        assert_eq!(S::search(&keys, &5), Err(2));
        assert_eq!(S::search(&keys, &6), Ok(2));
        assert_eq!(S::search(&keys, &7), Err(3));
        assert_eq!(S::search(&keys, &8), Ok(3));
        assert_eq!(S::search(&keys, &9), Err(4));
        assert_eq!(S::search(&keys, &10), Ok(4));
        assert_eq!(S::search(&keys, &128), Ok(63));
        assert_eq!(S::search(&keys, &129), Err(64));
        assert_eq!(S::search(&keys, &130), Err(64));
    }

    #[test]
    fn test_searchers() {
        test_searcher::<BinarySearch<_>>();
        test_searcher::<LinearSearch<_>>();
        test_searcher::<SimdLinearSearch<_, 4>>();
        test_searcher::<SimdLinearSearch<_, 8>>();
        test_searcher::<BranchlessBinarySearch<_>>();
        test_searcher::<Branchless2Search<_>>();
    }
}

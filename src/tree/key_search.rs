pub trait KeySearcher {
    type Key: Ord;

    /// search the k in search, returns same result as binary search
    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize>;
}

pub struct BinarySearch<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for BinarySearch<K> {
    type Key = K;

    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        keys.binary_search(k)
    }
}

pub struct LinearSearch<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for LinearSearch<K> {
    type Key = K;

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

pub struct SimdLinearSearch<K>(std::marker::PhantomData<K>);

impl<K: Ord> KeySearcher for SimdLinearSearch<K> {
    type Key = K;

    fn search(keys: &[Self::Key], k: &Self::Key) -> Result<usize, usize> {
        // we split this into chunks
        let chunk_size = 4;

        let off = keys
            .chunks_exact(chunk_size)
            .take_while(|key_chunk| key_chunk.iter().all(|key| key < k))
            .count()
            * chunk_size;

        keys[off..]
            .iter()
            .enumerate()
            .find_map(|(idx, key)| match key.cmp(k) {
                std::cmp::Ordering::Less => None,
                std::cmp::Ordering::Equal => Some(Ok(off + idx)),
                std::cmp::Ordering::Greater => Some(Err(off + idx)),
            })
            .unwrap_or(Err(keys.len()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_searcher<S: KeySearcher<Key = i8>>() {
        let keys = [2, 4, 6, 8];
        assert_eq!(S::search(&keys, &1), Err(0));
        assert_eq!(S::search(&keys, &2), Ok(0));
        assert_eq!(S::search(&keys, &3), Err(1));
        assert_eq!(S::search(&keys, &7), Err(3));
        assert_eq!(S::search(&keys, &8), Ok(3));
        assert_eq!(S::search(&keys, &9), Err(4));
    }

    #[test]
    fn test_searchers() {
        test_searcher::<BinarySearch<i8>>();
        test_searcher::<LinearSearch<i8>>();
        test_searcher::<SimdLinearSearch<i8>>();
    }
}

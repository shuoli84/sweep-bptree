use std::borrow::Borrow;

use crate::{BPlusTree, Key, NodeStoreVec};

pub struct BPlusTreeMap<K: Key, V> {
    inner: BPlusTree<NodeStoreVec<K, V, 64, 65, 64>>,
}

impl<K: Key, V> Default for BPlusTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key, V> BPlusTreeMap<K, V> {
    /// Create a new BPlusTreeMap
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let map = BPlusTreeMap::<i32, i32>::new();
    ///
    /// assert!(map.is_empty());
    /// ```
    #[inline]
    pub fn new() -> Self {
        let inner = BPlusTree::new(Default::default());

        Self { inner }
    }

    /// Returns item count in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the map contains no item
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let map = BPlusTreeMap::<i32, i32>::new();
    ///
    /// assert!(map.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Insert a key-value pair into the map
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let mut map = BPlusTreeMap::<i32, i32>::new();
    /// map.insert(1, 2);
    /// map.insert(2, 4);
    ///
    /// assert!(!map.is_empty());
    /// assert_eq!(map.len(), 2);
    /// ```
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.inner.insert(key, value)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let mut map = BPlusTreeMap::<i32, i32>::new();
    /// map.insert(1, 2);
    ///
    /// assert_eq!(map.get(&1).unwrap(), &2);
    /// assert!(map.get(&2).is_none());
    /// ```
    #[inline]
    pub fn get<Q: ?Sized + Ord>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        self.inner.get(key)
    }

    /// Returns a mut reference to the value corresponding to the key.
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let mut map = BPlusTreeMap::<i32, i32>::new();
    /// map.insert(1, 2);
    /// *map.get_mut(&1).unwrap() += 1;
    /// assert_eq!(map.get(&1).unwrap(), &3);
    /// ```
    #[inline]
    pub fn get_mut<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
    {
        self.inner.get_mut(key)
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let mut map = BPlusTreeMap::<i32, i32>::new();
    /// map.insert(1, 2);
    ///
    /// assert!(map.remove(&1).is_some());
    /// assert!(map.remove(&2).is_none());
    /// ```
    #[inline]
    pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        self.inner.remove(key)
    }

    /// Returns an iterator over the map.
    ///
    /// # Examples
    /// ```rust
    ///
    /// use sweep_bptree::BPlusTreeMap;
    ///
    /// let mut map = BPlusTreeMap::<i32, i32>::new();
    /// map.insert(1, 2);
    /// map.insert(2, 3);
    ///
    /// let kvs = map.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>();
    /// assert_eq!(kvs.len(), 2);
    /// assert_eq!(kvs, vec![(1, 2), (2, 3)]);
    /// ```
    #[inline]
    pub fn iter(&self) -> iter::Iter<K, V> {
        iter::Iter {
            inner: self.inner.iter(),
        }
    }
}

mod iter {
    use std::iter::FusedIterator;

    use super::*;

    pub struct Iter<'a, K: Key, V> {
        pub(super) inner: crate::tree::Iter<'a, NodeStoreVec<K, V, 64, 65, 64>>,
    }

    impl<'a, K: Key, V> Iterator for Iter<'a, K, V> {
        type Item = (&'a K, &'a V);

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.inner.size_hint()
        }

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next()
        }
    }

    impl<'a, K: Key, V> DoubleEndedIterator for Iter<'a, K, V> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.inner.next_back()
        }
    }

    impl<'a, K: Key, V> ExactSizeIterator for Iter<'a, K, V> {}
    impl<'a, K: Key, V> FusedIterator for Iter<'a, K, V> {}
}

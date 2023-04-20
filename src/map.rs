use std::borrow::Borrow;

use crate::{
    argument::RankArgumentation,
    tree::{Argumentation, SearchArgumentation},
    BPlusTree, Key, NodeStoreVec,
};

pub struct BPlusTreeMap<K: Key, V, A: Argumentation<K> = ()> {
    inner: BPlusTree<NodeStoreVec<K, V, A>>,
}

impl<K: Key, V> Default for BPlusTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key, V, A: Argumentation<K>> BPlusTreeMap<K, V, A> {
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
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        iter::Iter {
            inner: self.inner.iter(),
        }
    }

    /// Get value by argument's query
    ///
    /// # Example
    /// ```rust
    ///
    /// use sweep_bptree::BPlusTreeMap;
    /// use sweep_bptree::argument::ElementCount;
    ///
    ///
    /// let mut map = BPlusTreeMap::<i32, i32, ElementCount>::new();
    /// map.insert(1, 2);
    /// map.insert(2, 3);
    /// map.insert(3, 4);
    ///
    /// assert_eq!(map.get_by_argument(0), Some((&1, &2)));
    /// assert_eq!(map.get_by_argument(1), Some((&2, &3)));
    /// assert_eq!(map.get_by_argument(2), Some((&3, &4)));
    ///
    /// ```
    pub fn get_by_argument<Q>(&self, query: Q) -> Option<(&K, &V)>
    where
        A: SearchArgumentation<K, Query = Q>,
    {
        self.inner.get_by_argument(query)
    }

    /// Get the rank for key
    ///
    /// # Example
    ///
    /// ``` rust
    ///
    /// use sweep_bptree::BPlusTreeMap;
    /// use sweep_bptree::argument::ElementCount;
    ///
    /// let mut map = BPlusTreeMap::<i32, i32, ElementCount>::new();
    /// map.insert(1, 2);
    /// map.insert(2, 3);
    /// map.insert(3, 4);
    ///
    /// // 0 does not exists
    /// assert_eq!(map.rank_by_argument(&0), Err(0));
    ///
    /// // 1's rank is 0
    /// assert_eq!(map.rank_by_argument(&1), Ok(0));
    /// assert_eq!(map.rank_by_argument(&2), Ok(1));
    /// assert_eq!(map.rank_by_argument(&3), Ok(2));
    ///
    /// // 4 does not exists
    /// assert_eq!(map.rank_by_argument(&4), Err(3));
    ///
    /// ```
    pub fn rank_by_argument<R>(&self, k: &K) -> Result<R, R>
    where
        A: RankArgumentation<K, Rank = R>,
    {
        self.inner.rank_by_argument(k)
    }
}

mod iter {
    use std::iter::FusedIterator;

    use crate::NodeStore;

    pub struct Iter<'a, S: NodeStore> {
        pub(super) inner: crate::tree::Iter<'a, S>,
    }

    impl<'a, S: NodeStore> Iterator for Iter<'a, S> {
        type Item = (&'a S::K, &'a S::V);

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.inner.size_hint()
        }

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next()
        }
    }

    impl<'a, S: NodeStore> DoubleEndedIterator for Iter<'a, S> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.inner.next_back()
        }
    }

    impl<'a, S: NodeStore> ExactSizeIterator for Iter<'a, S> {}
    impl<'a, S: NodeStore> FusedIterator for Iter<'a, S> {}
}

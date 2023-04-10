use std::borrow::Borrow;

use crate::{BPlusTree, Key, NodeStoreVec};

pub struct BPlusTreeMap<K: Key, V> {
    inner: BPlusTree<NodeStoreVec<K, V, 64, 65, 64>>,
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
    pub fn new() -> Self {
        let inner = BPlusTree::new(Default::default());

        Self { inner }
    }

    /// Returns item count in the map
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
    pub fn get<Q: ?Sized + Ord>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        self.inner.get(key)
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
    pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        self.inner.remove(key)
    }
}

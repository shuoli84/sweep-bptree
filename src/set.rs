use crate::{BPlusTree, Key, NodeStoreVec};

pub struct BPlusTreeSet<K: crate::Key> {
    tree: BPlusTree<NodeStoreVec<K, (), 64, 65, 64>>,
}

impl<K: Key> BPlusTreeSet<K> {
    /// Create a new BPlusTreeSet
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// ```
    pub fn new() -> Self {
        let store = NodeStoreVec::new();

        Self {
            tree: BPlusTree::new(store),
        }
    }

    /// Returns key count in the set
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::new();
    /// assert_eq!(set.len(), 0);

    /// set.insert(1);
    /// assert_eq!(set.len(), 1);
    ///
    /// set.insert(1);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns true if the set contains no key
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert(1);
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// Insert a key into the set
    /// Returns true if the key was inserted, false if it already existed
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// assert!(set.insert(1));
    /// assert!(!set.insert(1));
    /// ```
    pub fn insert(&mut self, k: K) -> bool {
        self.tree.insert(k, ()).is_none()
    }

    /// Remove a key from the set
    /// Returns true if the key was removed, false if it didn't exist
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// set.insert(1);
    /// assert!(set.remove(&1));
    /// assert!(!set.remove(&2));
    /// ```
    pub fn remove(&mut self, k: &K) -> bool {
        self.tree.remove(k).is_some()
    }

    /// Clears the set
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree.clear();
    }
}

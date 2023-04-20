use std::borrow::Borrow;

use crate::{BPlusTree, Key, NodeStoreVec};

/// A B+ tree based set
pub struct BPlusTreeSet<K: crate::Key> {
    tree: BPlusTree<NodeStoreVec<K, (), 64, 65>>,
}

impl<K: Key> Default for BPlusTreeSet<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key> BPlusTreeSet<K> {
    /// Create a new BPlusTreeSet
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// BPlusTreeSet::<i32>::new();
    /// ```
    #[inline]
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
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// assert_eq!(set.len(), 0);

    /// set.insert(1);
    /// assert_eq!(set.len(), 1);
    ///
    /// set.insert(1);
    /// assert_eq!(set.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns true if the set contains no key
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert(1);
    /// assert!(!set.is_empty());
    /// ```
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> bool
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.tree.remove(k).is_some()
    }

    /// Returns true if the set contains the key
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    /// set.insert(1);
    /// assert!(set.contains(&1));
    /// set.remove(&1);
    /// assert!(!set.contains(&1));
    /// ```
    #[inline]
    pub fn contains<Q: ?Sized>(&self, k: &Q) -> bool
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.tree.get(k).is_some()
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
    #[inline]
    pub fn clear(&mut self) {
        self.tree.clear();
    }

    /// Returns a reference to the first key in the set, if any
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    ///
    /// assert!(set.first().is_none());
    ///
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// assert_eq!(*set.first().unwrap(), 1);
    /// ```
    #[inline]
    pub fn first(&self) -> Option<&K> {
        self.tree.first().map(|(k, _)| k)
    }

    /// Returns a reference to the last key in the set, if any
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    ///
    /// assert!(set.last().is_none());
    ///
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// assert_eq!(*set.last().unwrap(), 2);
    /// ```
    #[inline]
    pub fn last(&self) -> Option<&K> {
        self.tree.last().map(|(k, _)| k)
    }

    /// Returns a iterator over the keys in the set
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<i32>::new();
    ///
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// let keys = set.iter().collect::<Vec<_>>();
    /// assert_eq!(keys.len(), 2);
    ///
    /// ```
    #[inline]
    pub fn iter(&self) -> iter::Iter<K> {
        iter::Iter {
            inner: self.tree.iter(),
        }
    }

    /// Returns a iterator over the keys in the set
    ///
    /// # Examples
    /// ```rust
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut set = BPlusTreeSet::<String>::new();
    ///
    /// set.insert(1.to_string());
    /// set.insert(2.to_string());
    ///
    /// let keys = set.into_iter().collect::<Vec<_>>();
    /// assert_eq!(keys.len(), 2);
    ///
    /// ```
    #[inline]
    pub fn into_iter(self) -> iter::IntoIter<K> {
        iter::IntoIter {
            inner: self.tree.into_iter(),
        }
    }

    /// Visits the elements representing the union,
    /// i.e., all the elements in `self` or `other`, without duplicates,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use sweep_bptree::BPlusTreeSet;
    ///
    /// let mut a = BPlusTreeSet::new();
    /// a.insert(1);
    ///
    /// let mut b = BPlusTreeSet::new();
    /// b.insert(1);
    /// b.insert(2);
    ///
    /// let union: Vec<_> = a.union(&b).cloned().collect();
    /// assert_eq!(union, [1, 2]);
    /// ```
    #[inline]
    pub fn union<'a>(&'a self, other: &'a Self) -> iter::Union<'a, K> {
        use crate::merge_iter::MergeIterInner;
        iter::Union(MergeIterInner::new(self.iter(), other.iter()))
    }
}

mod iter {
    use std::{cmp::max, iter::FusedIterator};

    use crate::merge_iter::MergeIterInner;

    use super::*;

    /// An iterator over the references of keys in a `BPlusTreeSet`
    #[derive(Clone)]
    pub struct Iter<'a, K: crate::Key> {
        pub(super) inner: crate::tree::Iter<'a, NodeStoreVec<K, (), 64, 65>>,
    }

    impl<'a, K: crate::Key> Iterator for Iter<'a, K> {
        type Item = &'a K;

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.inner.size_hint()
        }

        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next().map(|(k, _)| k)
        }
    }

    impl<'a, K: crate::Key> DoubleEndedIterator for Iter<'a, K> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.inner.next_back().map(|(k, _)| k)
        }
    }

    impl<'a, K: crate::Key> FusedIterator for Iter<'a, K> {}
    impl<'a, K: crate::Key> ExactSizeIterator for Iter<'a, K> {}

    /// An iterator over the keys in a `BPlusTreeSet`
    pub struct IntoIter<K: crate::Key> {
        pub(super) inner: crate::tree::IntoIter<NodeStoreVec<K, (), 64, 65>>,
    }

    impl<K: crate::Key> Iterator for IntoIter<K> {
        type Item = K;

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.inner.size_hint()
        }

        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next().map(|(k, _)| k)
        }
    }

    impl<K: crate::Key> DoubleEndedIterator for IntoIter<K> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.inner.next_back().map(|(k, _)| k)
        }
    }

    impl<K: crate::Key> FusedIterator for IntoIter<K> {}
    impl<K: crate::Key> ExactSizeIterator for IntoIter<K> {}

    /// This Union impl is a dup from std lib
    /// /// A lazy iterator producing elements in the union of `BTreeSet`s.
    ///
    /// This `struct` is created by the [`union`] method on [`BTreeSet`].
    /// See its documentation for more.
    ///
    /// [`union`]: BPlusTreeSet::union
    pub struct Union<'a, K: crate::Key>(pub(crate) MergeIterInner<Iter<'a, K>>);

    impl<K: crate::Key + Clone> Clone for Union<'_, K> {
        fn clone(&self) -> Self {
            Union(self.0.clone())
        }
    }

    impl<'a, T: crate::Key> Iterator for Union<'a, T> {
        type Item = &'a T;

        fn next(&mut self) -> Option<&'a T> {
            let (a_next, b_next) = self.0.nexts(Self::Item::cmp);
            a_next.or(b_next)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let (a_len, b_len) = self.0.lens();
            // No checked_add - see SymmetricDifference::size_hint.
            (max(a_len, b_len), Some(a_len + b_len))
        }

        fn min(mut self) -> Option<&'a T> {
            self.next()
        }
    }
}

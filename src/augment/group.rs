use std::{borrow::Cow, cmp::Ordering};

use crate::Key;

use super::{Augmentation, RankAugmentation, SearchAugmentation};

/// Augmentation to count the number of groups in a set of keys
/// Note, the group must be ordered
/// This Augmentation basically provides two capabilities:
/// 1. Get the group count
/// 2. Query inside group by offset
#[derive(Clone, Debug)]
pub enum GroupCount<G> {
    Zero,
    One(G, usize),
    Multiple {
        min_group: (G, usize),
        max_group: (G, usize),
        /// how many groups for child
        group_count: usize,
    },
}

impl<G: Clone + Ord> Default for GroupCount<G> {
    fn default() -> Self {
        Self::Zero
    }
}

impl<G: Clone + Ord> GroupCount<G> {
    pub fn is_zero(&self) -> bool {
        matches!(self, GroupCount::Zero)
    }

    pub fn group_count(&self) -> usize {
        match self {
            GroupCount::Zero => 0,
            GroupCount::One(_, _) => 1,
            GroupCount::Multiple { group_count, .. } => *group_count,
        }
    }

    /// Returns max_group and it's item count
    pub fn max_group(&self) -> Option<(&G, usize)> {
        match self {
            GroupCount::Zero => None,
            GroupCount::One(g, c) => Some((g, *c)),
            GroupCount::Multiple {
                max_group,
                group_count: _,
                min_group: _,
            } => Some((&max_group.0, max_group.1)),
        }
    }

    /// merge self with right
    fn merge_with(&mut self, right: &Self) {
        let new_value = match (std::mem::take(self), right) {
            (GroupCount::Zero, r) => r.clone(),
            (l, GroupCount::Zero) => l,

            (GroupCount::One(g1, c1), GroupCount::One(g2, c2)) => {
                if g1.cmp(g2) == Ordering::Equal {
                    GroupCount::One(g1.clone(), c1 + *c2)
                } else {
                    GroupCount::Multiple {
                        min_group: (g1.clone(), c1),
                        max_group: (g2.clone(), *c2),
                        group_count: 2,
                    }
                }
            }
            (
                GroupCount::One(g1, c1),
                GroupCount::Multiple {
                    min_group,
                    max_group,
                    group_count,
                },
            ) => {
                if g1.cmp(&min_group.0) == Ordering::Equal {
                    GroupCount::Multiple {
                        min_group: (g1, c1 + min_group.1),
                        max_group: max_group.clone(),
                        group_count: *group_count,
                    }
                } else {
                    GroupCount::Multiple {
                        min_group: (g1, c1),
                        max_group: max_group.clone(),
                        group_count: *group_count + 1,
                    }
                }
            }
            (
                GroupCount::Multiple {
                    min_group,
                    mut max_group,
                    mut group_count,
                },
                GroupCount::One(ref g2, c2),
            ) => {
                if g2.cmp(&max_group.0) == Ordering::Equal {
                    max_group.1 += c2;
                } else {
                    max_group = (g2.clone(), *c2);
                    group_count += 1;
                }

                GroupCount::Multiple {
                    min_group,
                    max_group,
                    group_count,
                }
            }
            (
                GroupCount::Multiple {
                    min_group: left_min_group,
                    max_group: left_max_group,
                    group_count: left_group_count,
                },
                GroupCount::Multiple {
                    min_group: right_min_group,
                    max_group: rigth_max_group,
                    group_count: right_group_count,
                },
            ) => {
                let mut new_group_count = left_group_count + right_group_count;

                if left_max_group.0.cmp(&right_min_group.0) == Ordering::Equal {
                    new_group_count -= 1;
                }

                GroupCount::Multiple {
                    min_group: left_min_group,
                    max_group: rigth_max_group.clone(),
                    group_count: new_group_count,
                }
            }
        };

        *self = new_value;
    }
}

/// Group need to implement this trait for Key, it is used when construct G instance
pub trait FromRef<T> {
    fn from_ref(input: &T) -> Self;
}

impl<K, V, G> Augmentation<K, V> for GroupCount<G>
where
    K: Key,
    G: FromRef<K> + Clone + Ord + std::fmt::Debug,
{
    fn from_leaf(keys: &[K], _: &[V]) -> Self {
        let mut keys_iter = keys.iter();

        let first_group = G::from_ref(match keys_iter.next() {
            Some(k) => k,
            None => return Self::Zero,
        });

        let mut group_count = 1;
        let mut min_group_count = 1;
        let mut last_group_count = 1;

        let mut last_group = Cow::Borrowed(&first_group);
        let mut last_group_item_count = &mut min_group_count;

        for key in keys_iter {
            let group = G::from_ref(key);
            if last_group.as_ref().ne(&group) {
                group_count += 1;
                last_group_item_count = &mut last_group_count;
                last_group = Cow::Owned(group);
            } else {
                *last_group_item_count += 1;
            }
        }

        match group_count {
            1 => GroupCount::One(first_group, min_group_count),
            _ => {
                let last_group = last_group.into_owned();
                GroupCount::Multiple {
                    min_group: (first_group, min_group_count),
                    max_group: (last_group, last_group_count),
                    group_count,
                }
            }
        }
    }

    fn from_inner(_keys: &[K], group_counts: &[Self]) -> Self {
        if group_counts.is_empty() {
            return Self::Zero;
        }

        let mut accumulated = Self::Zero;
        group_counts.iter().for_each(|a| accumulated.merge_with(a));
        accumulated
    }
}

impl<K, V, G> SearchAugmentation<K, V> for GroupCount<G>
where
    K: Key,
    G: FromRef<K> + Clone + Ord + std::fmt::Debug,
{
    /// It can be searched by Group and offset
    type Query = (G, usize);

    fn locate_in_leaf((group, offset): (G, usize), keys: &[K], _: &[V]) -> Option<usize> {
        let mut in_group_offset = 0;
        for (idx, k) in keys.iter().enumerate() {
            let group_for_key = G::from_ref(k);

            match group_for_key.cmp(&group) {
                Ordering::Less => continue,
                Ordering::Equal => {
                    if in_group_offset == offset {
                        return Some(idx);
                    } else {
                        in_group_offset += 1;
                    }
                }
                Ordering::Greater => return None,
            }
        }

        None
    }

    fn locate_in_inner(
        (group, mut offset): Self::Query,
        _keys: &[K],
        group_counts: &[Self],
    ) -> Option<(usize, Self::Query)> {
        for (idx, a) in group_counts.iter().enumerate() {
            match a {
                GroupCount::Zero => {}
                GroupCount::One(g, c) => match g.cmp(&group) {
                    Ordering::Less => continue,
                    Ordering::Equal => {
                        if *c > offset {
                            return Some((idx, (group, offset)));
                        } else {
                            offset -= c;
                            continue;
                        }
                    }
                    Ordering::Greater => return None,
                },
                GroupCount::Multiple { max_group, .. } => match max_group.0.cmp(&group) {
                    Ordering::Less => continue,
                    Ordering::Equal => {
                        if max_group.1 > offset {
                            return Some((idx, (group, offset)));
                        } else {
                            offset -= max_group.1;
                            continue;
                        }
                    }
                    Ordering::Greater => {
                        return Some((idx, (group, offset)));
                    }
                },
            }
        }
        None
    }
}

impl<K, V, G> RankAugmentation<K, V> for GroupCount<G>
where
    K: Key,
    G: FromRef<K> + Clone + Ord + std::fmt::Debug,
{
    /// The group and it's offset, if there is no items, it should be None
    type Rank = Option<(G, usize)>;

    fn initial_value() -> Self::Rank {
        None
    }

    fn fold_inner(_k: &K, rank: Option<(G, usize)>, group_counts: &[Self]) -> Option<(G, usize)> {
        // How:
        // 1. locate the max group and count for augmentations
        // 2. then if rank's g is same as max_group's g, merge count
        //    otherwise, just use the max_group
        let mut rev_iter = group_counts.iter().rev();
        let last_augmentation = rev_iter.next()?;

        let (max_group, mut max_group_size) = last_augmentation.max_group()?;

        for a in rev_iter {
            match a.max_group() {
                Some((group, count)) if group.cmp(max_group) == Ordering::Equal => {
                    max_group_size += count;
                }
                _ => break,
            }
        }

        match rank {
            Some((group, count)) if group.cmp(max_group) == Ordering::Equal => {
                Some((group, count + max_group_size))
            }
            _ => Some((max_group.clone(), max_group_size)),
        }
    }

    fn fold_leaf(
        key: &K,
        rank: Self::Rank,
        slot: Result<usize, usize>,
        keys: &[K],
    ) -> Result<Self::Rank, Self::Rank> {
        if keys.is_empty() {
            return Err(Some((G::from_ref(key), 0)));
        }

        let (group, offset) = rank.unwrap_or((G::from_ref(&keys[0]), 0));

        let group_for_key = G::from_ref(key);

        // if group is same, return early by sum accumulated offset and slot
        if group.cmp(&group_for_key) == Ordering::Equal {
            return match slot {
                Ok(idx) => Ok(Some((group_for_key, idx + offset))),
                Err(idx) => Err(Some((group_for_key, idx + offset))),
            };
        }

        // otherwise, find the G and it's offset
        // todo: this can be improved by binary search
        let mut count = 0;
        let slot_idx = match slot {
            Ok(idx) => idx,
            Err(idx) => idx,
        };

        for k in &keys[0..slot_idx] {
            let group_candidate = G::from_ref(k);
            if group_candidate.cmp(&group_for_key) != Ordering::Equal {
                continue;
            } else {
                count += 1;
            }
        }

        match slot {
            Ok(_) => Ok(Some((group_for_key, count))),
            Err(_) => Err(Some((group_for_key, count))),
        }
    }
}

pub use visit::ExtractGroupSize;

mod visit {
    use super::*;
    use crate::tree::visit::{DescendVisit, DescendVisitResult};

    /// This visit returns element count for one group.
    pub struct ExtractGroupSize<G, K> {
        group: G,
        element_count: usize,
        _marker: std::marker::PhantomData<K>,
    }

    impl<G, K> ExtractGroupSize<G, K> {
        pub fn new(g: G) -> Self {
            Self {
                group: g,
                element_count: 0,
                _marker: std::marker::PhantomData,
            }
        }
    }

    impl<K: Key, V, G: FromRef<K> + Ord + Clone> DescendVisit<K, V, GroupCount<G>>
        for ExtractGroupSize<G, K>
    {
        /// The group's total count
        type Result = usize;

        fn visit_inner(
            &mut self,
            _keys: &[K],
            group_counts: &[GroupCount<G>],
        ) -> crate::tree::visit::DescendVisitResult<usize> {
            let mut child_idx = 0;
            let mut prev_group_count = 0;
            for (idx, a) in group_counts.iter().enumerate() {
                child_idx = idx;
                match a.max_group() {
                    Some((max_group, max_group_count)) => match max_group.cmp(&self.group) {
                        Ordering::Less => continue,
                        Ordering::Equal => {
                            self.element_count += prev_group_count;
                            prev_group_count = max_group_count;
                            continue;
                        }
                        Ordering::Greater => {
                            // break out and go down
                            self.element_count += prev_group_count;
                            break;
                        }
                    },
                    None => return DescendVisitResult::Cancel,
                }
            }

            crate::tree::visit::DescendVisitResult::GoDown(child_idx)
        }

        fn visit_leaf(&mut self, keys: &[K], _values: &[V]) -> Option<Self::Result> {
            for k in keys {
                match G::from_ref(k).cmp(&self.group) {
                    Ordering::Less => continue,
                    Ordering::Equal => self.element_count += 1,
                    Ordering::Greater => break,
                }
            }

            Some(self.element_count)
        }
    }
}

/// Extract two element tuple's first element as Group
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tuple2<T>(T);

impl<T1: Clone, T2> FromRef<(T1, T2)> for Tuple2<T1> {
    fn from_ref(input: &(T1, T2)) -> Self {
        Tuple2(input.0.clone())
    }
}

#[cfg(test)]
mod tests {
    use rand::seq::SliceRandom;

    use crate::BPlusTreeMap;

    use super::*;

    #[test]
    fn test_group_count() {
        // Tuple2 use pair's first element as group value
        let mut tree = BPlusTreeMap::<_, _, GroupCount<Tuple2<_>>>::new();

        // group count is 0 for empty tree
        assert_eq!(tree.root_augmentation().group_count(), 0);

        tree.insert((1, 1), 100);
        assert_eq!(tree.root_augmentation().group_count(), 1);
        tree.remove(&(1, 1));
        assert_eq!(tree.root_augmentation().group_count(), 0);

        tree.insert((1, 1), 100);
        tree.insert((1, 2), 101);
        assert_eq!(tree.root_augmentation().group_count(), 1);

        // get group size for Tuple2(1)
        assert_eq!(
            tree.descend_visit(ExtractGroupSize::new(Tuple2(1))),
            Some(2)
        );

        // get (k, v) by (group, offset)
        assert_eq!(tree.get_by_augmentation((Tuple2(1), 0)).unwrap().1, &100);

        // or get the (group, offset) tuple by key
        assert_eq!(
            tree.rank_by_augmentation(&(1, 0)),
            Err(Some((Tuple2(1), 0)))
        );

        tree.insert((1, 3), 100);
        tree.insert((2, 4), 100);
        assert_eq!(tree.root_augmentation().group_count(), 2);
        tree.insert((3, 5), 100);
        tree.insert((4, 6), 100);
        assert_eq!(tree.root_augmentation().group_count(), 4);
        tree.remove(&(4, 6));
        assert_eq!(tree.root_augmentation().group_count(), 3);

        // find in group First(1)
        // offset 0
        assert_eq!(tree.get_by_augmentation((Tuple2(1), 0)).unwrap().1, &100);
        // offset 1
        assert_eq!(tree.get_by_augmentation((Tuple2(1), 1)).unwrap().1, &101);
        // offset 3 (2 is also exists)
        assert!(tree.get_by_augmentation((Tuple2(1), 3)).is_none());

        assert_eq!(
            tree.rank_by_augmentation(&(1, 0)),
            Err(Some((Tuple2(1), 0)))
        );
        assert_eq!(tree.rank_by_augmentation(&(1, 1)), Ok(Some((Tuple2(1), 0))));
        assert_eq!(tree.rank_by_augmentation(&(1, 2)), Ok(Some((Tuple2(1), 1))));
        assert_eq!(tree.rank_by_augmentation(&(1, 3)), Ok(Some((Tuple2(1), 2))));
        assert_eq!(
            tree.rank_by_augmentation(&(1, 4)),
            Err(Some((Tuple2(1), 3)))
        );
        assert_eq!(
            tree.rank_by_augmentation(&(2, 3)),
            Err(Some((Tuple2(2), 0)))
        );
        assert_eq!(
            tree.rank_by_augmentation(&(5, 0)),
            Err(Some((Tuple2(5), 0)))
        );
    }

    #[test]
    fn test_group_large_group() {
        let mut tree = BPlusTreeMap::<(u64, u64), i64, GroupCount<Tuple2<_>>>::new();

        for i in 0..1000 {
            tree.insert((i / 500, i % 500), i as i64);
            let rank = tree.rank_by_augmentation(&(i / 500, i % 500));
            assert_eq!(rank, Ok(Some((Tuple2(i / 500), (i % 500) as usize))));
            assert_eq!(
                tree.rank_by_augmentation(&(i / 500, i % 500 + 1)),
                Err(Some((Tuple2(i / 500), (i % 500) as usize + 1)))
            );
        }

        assert_eq!(tree.root_augmentation().group_count(), 2);
    }

    #[test]
    fn test_group_visit_group_count() {
        let mut tree = BPlusTreeMap::<(u64, u64), i64, GroupCount<Tuple2<_>>>::new();

        for i in 0..1050 {
            tree.insert((i / 500, i % 500), i as i64);
        }

        assert_eq!(tree.root_augmentation().group_count(), 3);

        assert_eq!(
            tree.descend_visit(ExtractGroupSize::new(Tuple2(0))),
            Some(500)
        );
        assert_eq!(
            tree.descend_visit(ExtractGroupSize::new(Tuple2(1))),
            Some(500)
        );
        assert_eq!(
            tree.descend_visit(ExtractGroupSize::new(Tuple2(2))),
            Some(50)
        );

        let mut keys = tree.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>();
        keys.shuffle(&mut rand::thread_rng());

        // test remove
        for k in keys {
            let g = Tuple2::from_ref(&k);
            let prev_count = tree
                .descend_visit(ExtractGroupSize::new(g.clone()))
                .unwrap();
            assert!(tree.remove(&k).is_some());
            let new_count = tree.descend_visit(ExtractGroupSize::new(g)).unwrap();
            assert_eq!(new_count + 1, prev_count);
        }
    }
}

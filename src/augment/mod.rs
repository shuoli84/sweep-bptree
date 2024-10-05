use crate::Key;

pub mod count;
pub mod group;

/// Augmentation trait, it is used to store augmentation, like 'size'
/// NOTE: Since the lib has no control on how value changes, so augment only calculated from keys
/// e.g: Map<i64, Arc<Mutex<i64>>
pub trait Augmentation<K: Key, V>: Clone + Default {
    fn is_zst() -> bool {
        false
    }

    /// create a new Augmentation from inner node and its augment
    /// e.g: take size as example.
    /// the root node's augment is created from its children's augment and keys
    /// the inner node with height 1's is created from leaf's keys
    ///                             [k3][9, 5]
    ///                [k2][5, 4]                  [k4][3, 2]
    ///         leaf[0] 5       leaf[1] 4      leaf[2] 3   leaf[2] 2
    fn from_inner(keys: &[K], augmentations: &[Self]) -> Self;

    /// create a new Augmentation from leaf node's key
    fn from_leaf(keys: &[K]) -> Self;
}

/// Whether the augmentation able to locate element
/// `SearchAugmentation` acts like a secondary index, it is able to locate
/// the record.
pub trait SearchAugmentation<K: Key, V>: Augmentation<K, V> {
    type Query;

    /// locate the offset of the element in leaf node
    fn locate_in_leaf(query: Self::Query, keys: &[K]) -> Option<usize>;

    /// locate the child index of query in inner node, with new query
    fn locate_in_inner(
        query: Self::Query,
        keys: &[K],
        augmentations: &[Self],
    ) -> Option<(usize, Self::Query)>;
}

/// Whether the augmentation able to rank element(like the index of key)
pub trait RankAugmentation<K: Key, V>: Augmentation<K, V> {
    type Rank;

    /// Initial rank value, e.g: 0 for size
    /// it will be passed to the first call of `folder_inner` or `folder_leaf`
    fn initial_value() -> Self::Rank;

    /// combine rank with all ranks for prev sibling augmentations.
    /// The passed in augment slice doesn't contain the augmentation 'k' belongs
    /// The result will be passed to `fold_inner` for inner layer
    /// and finally to `fold_leaf`
    fn fold_inner(k: &K, rank: Self::Rank, augmentations: &[Self]) -> Self::Rank;

    /// Get rank of the key in leaf node
    /// Returns Ok(Rank) for existing key, Err(Rank) for non-existing key
    fn fold_leaf(
        k: &K,
        rank: Self::Rank,
        slot: Result<usize, usize>,
        keys: &[K],
    ) -> Result<Self::Rank, Self::Rank>;
}

/// () is a dummy augment that turns Augmented tree to a normal tree
impl<K: Key, V> Augmentation<K, V> for () {
    fn is_zst() -> bool {
        true
    }

    #[inline(always)]
    fn from_leaf(_: &[K]) -> Self {}

    #[inline(always)]
    fn from_inner(_: &[K], _: &[Self]) -> Self {}
}

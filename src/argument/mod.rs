use crate::Key;

pub mod count;
pub mod group;

/// Augument trait, it is used to store augumentation, like 'size'
pub trait Argument<K: Key>: Clone + Default + std::fmt::Debug {
    fn is_zst() -> bool {
        false
    }

    /// create a new Argumentation from leaf node's key
    fn from_leaf(keys: &[K]) -> Self;

    /// create a new Argumentation from inner node and its argument
    /// e.g: take size as example.
    /// the root node's argument is created from its children's argument and keys
    /// the inner node with height 1's is created from leaf's keys
    ///                             [k3][9, 5]
    ///                [k2][5, 4]                  [k4][3, 2]
    ///         leaf[0] 5       leaf[1] 4      leaf[2] 3   leaf[2] 2
    fn from_inner(keys: &[K], arguments: &[Self]) -> Self;
}

/// Whether the argumentation able to locate element
pub trait SearchArgument<K: Key>: Argument<K> {
    type Query;

    /// locate the offset of the element in leaf node
    fn locate_in_leaf(query: Self::Query, keys: &[K]) -> Option<usize>;

    /// locate the child index of query in inner node, with new query
    fn locate_in_inner(
        query: Self::Query,
        keys: &[K],
        arguments: &[Self],
    ) -> Option<(usize, Self::Query)>;
}

/// Whether the argumentation able to rank element(like the index of key)
pub trait RankArgument<K: Key>: Argument<K> {
    type Rank;

    /// Initial rank value, e.g: 0 for size
    /// it will be passed to the first call of `combine_rank`
    fn initial_value() -> Self::Rank;

    /// combine rank with all ranks for prev sibling arguments.
    /// The passed in argument slice doesn't contain the argument 'k' belongs
    /// The result will be passed to `fold_inner` for inner layer
    /// and finally to `fold_leaf`
    fn fold_inner(k: &K, rank: Self::Rank, arguments: &[Self]) -> Self::Rank;

    /// Get rank of the key in leaf node
    /// Returns Ok(Rank) for existing key, Err(Rank) for non-existing key
    fn fold_leaf(
        k: &K,
        rank: Self::Rank,
        slot: Result<usize, usize>,
        keys: &[K],
    ) -> Result<Self::Rank, Self::Rank>;
}

/// () is a dummy argumentation, it is used as the default
impl<K: Key> Argument<K> for () {
    fn is_zst() -> bool {
        true
    }

    #[inline(always)]
    fn from_leaf(_: &[K]) -> Self {
        ()
    }

    #[inline(always)]
    fn from_inner(_: &[K], _: &[Self]) -> Self {
        ()
    }
}

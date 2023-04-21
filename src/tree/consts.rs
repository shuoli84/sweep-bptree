/// Inner node Key capacity
pub(crate) const INNER_N: usize = 64;
/// Inner node Child capacity/branch factor
pub(crate) const INNER_C: usize = INNER_N + 1;
/// Leaf node capacity
pub(crate) const LEAF_N: usize = INNER_N;

/// Minimum branching factor of the tree. Now the tree's deleting operation is merge at 1/4
/// This value reduced tree's rotation fix count and also provide large enough leaf.
const MIN_N: usize = INNER_N / 4;

/// Visit Stack capacity, it is the maximum depth of the tree.
/// The formular is `ceil(log(u64::MAX, K))`, the K is the minimum branching factor of the tree.
pub(crate) const MAX_DEPTH: usize = usize::MAX.ilog(MIN_N) as usize;

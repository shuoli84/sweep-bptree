#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InnerNodeId(pub(crate) usize);

impl InnerNodeId {
    #[inline(always)]
    pub fn from_usize(id: usize) -> Self {
        Self(id)
    }

    #[inline(always)]
    pub fn as_usize(&self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LeafNodeId(pub(crate) usize);

impl LeafNodeId {
    #[inline(always)]
    pub fn from_usize(id: usize) -> Self {
        Self(id)
    }

    #[inline(always)]
    pub fn as_usize(&self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NodeId {
    Inner(InnerNodeId),
    Leaf(LeafNodeId),
}

impl NodeId {
    #[inline(always)]
    pub fn leaf_id(&self) -> Option<LeafNodeId> {
        match self {
            NodeId::Leaf(id) => Some(*id),
            _ => None,
        }
    }

    #[inline(always)]
    pub unsafe fn leaf_id_unchecked(&self) -> LeafNodeId {
        match self {
            NodeId::Leaf(id) => *id,
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    #[inline(always)]
    pub fn inner_id(&self) -> Option<InnerNodeId> {
        match self {
            NodeId::Inner(id) => Some(*id),
            _ => None,
        }
    }

    #[inline(always)]
    pub unsafe fn inner_id_unchecked(&self) -> InnerNodeId {
        match self {
            NodeId::Inner(id) => *id,
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

impl From<LeafNodeId> for NodeId {
    fn from(value: LeafNodeId) -> Self {
        Self::Leaf(value)
    }
}

impl From<InnerNodeId> for NodeId {
    fn from(value: InnerNodeId) -> Self {
        Self::Inner(value)
    }
}

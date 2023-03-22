#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InnerNodeId(pub(crate) u32);

impl InnerNodeId {
    pub fn from_u32(id: u32) -> Self {
        Self(id)
    }

    pub fn as_u32(&self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LeafNodeId(pub(crate) u32);

impl LeafNodeId {
    pub fn from_u32(id: u32) -> Self {
        Self(id)
    }

    pub fn as_u32(&self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NodeId {
    Inner(InnerNodeId),
    Leaf(LeafNodeId),
}

impl NodeId {
    pub fn leaf_id(&self) -> Option<LeafNodeId> {
        match self {
            NodeId::Leaf(id) => Some(*id),
            _ => None,
        }
    }

    pub fn inner_id(&self) -> Option<InnerNodeId> {
        match self {
            NodeId::Inner(id) => Some(*id),
            _ => None,
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

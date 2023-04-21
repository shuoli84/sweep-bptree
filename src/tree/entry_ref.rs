use super::{InnerNodeId, LeafNodeId, NodeId};

const N: usize = super::consts::MAX_DEPTH;

#[derive(Debug, Clone, Copy)]
struct StackEntry {
    /// inner node id
    id: InnerNodeId,
    /// child offset
    offset: usize,
    /// corresponding child id
    child_id: NodeId,
}

impl StackEntry {
    const fn invalid() -> Self {
        Self {
            id: InnerNodeId::INVALID,
            offset: 0,
            child_id: NodeId::Inner(InnerNodeId::INVALID),
        }
    }
}

/// Keeps breadcrumbs of the tree traversal
#[derive(Debug)]
pub struct VisitStack {
    /// current stack size
    len: u16,

    /// Inner nodes
    stack: [StackEntry; N],
}

impl VisitStack {
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl VisitStack {
    /// Create a new empty stack
    pub const fn new() -> Self {
        Self {
            len: 0,
            stack: [StackEntry::invalid(); N],
        }
    }

    pub fn push(&mut self, id: InnerNodeId, offset: usize, child_id: NodeId) {
        assert!(self.len < N as u16);

        let entry = StackEntry {
            id,
            offset,
            child_id,
        };

        self.stack[self.len as usize] = entry;
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<(InnerNodeId, usize, NodeId)> {
        if self.len == 0 {
            return None;
        }

        assert!(self.len <= N as u16);

        self.len -= 1;
        let StackEntry {
            id,
            offset,
            child_id,
        } = self.stack[self.len as usize];
        Some((id, offset as usize, child_id))
    }
}

pub struct EntryRef {
    pub(crate) inner_stack: VisitStack,
    pub(crate) leaf_id: LeafNodeId,
    pub(crate) offset: usize,
}

impl EntryRef {
    /// Create a new entry reference
    pub fn new(inner_visit: VisitStack, leaf_id: LeafNodeId, offset: usize) -> Self {
        Self {
            inner_stack: inner_visit,
            leaf_id,
            offset,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visit_stack() {
        let mut stack = VisitStack::new();
        assert!(stack.is_empty());

        stack.push(InnerNodeId(1), 1, InnerNodeId(10).into());
        stack.push(InnerNodeId(2), 2, InnerNodeId(20).into());
        stack.push(InnerNodeId(3), 3, InnerNodeId(30).into());

        assert_eq!(stack.len(), 3);

        assert_eq!(
            stack.pop().unwrap(),
            (InnerNodeId(3), 3, NodeId::Inner(InnerNodeId(30)))
        );
        assert_eq!(
            stack.pop().unwrap(),
            (InnerNodeId(2), 2, NodeId::Inner(InnerNodeId(20)))
        );
        assert_eq!(
            stack.pop().unwrap(),
            (InnerNodeId(1), 1, NodeId::Inner(InnerNodeId(10)))
        );

        assert!(stack.is_empty());
    }
}

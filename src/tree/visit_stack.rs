use super::{InnerNodeId, NodeId};

const N: usize = super::consts::MAX_DEPTH;

/// Keeps breadcrumbs of the tree traversal
#[derive(Debug)]
pub struct VisitStack {
    /// current stack size
    len: u16,

    /// Inner nodes
    inner_nodes: [InnerNodeId; N],

    /// Offsets
    offsets: [u16; N],

    /// child id
    child_id: [NodeId; N],
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
    pub fn new() -> Self {
        Self {
            len: 0,
            inner_nodes: [InnerNodeId::INVALID; N],
            offsets: [0; N],
            child_id: [NodeId::Inner(InnerNodeId::INVALID); N],
        }
    }

    pub fn push(&mut self, id: InnerNodeId, offset: usize, child_id: NodeId) {
        assert!(self.len < N as u16);

        self.inner_nodes[self.len as usize] = id;
        self.offsets[self.len as usize] = offset as u16;
        self.child_id[self.len as usize] = child_id;
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<(InnerNodeId, usize, NodeId)> {
        if self.len == 0 {
            return None;
        }

        assert!(self.len <= N as u16);

        self.len -= 1;
        let id = self.inner_nodes[self.len as usize];
        let offset = self.offsets[self.len as usize];
        let child_id = self.child_id[self.len as usize];
        Some((id, offset as usize, child_id))
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

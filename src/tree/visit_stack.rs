use super::InnerNodeId;

pub const STACK_SIZE_FOR_64: usize = 12;

/// Type alias for branch factor 64
pub(crate) type VisitStack64 = VisitStack<STACK_SIZE_FOR_64>;

/// When visit descend in the tree, it is temping to think of the stack as a
/// dynamic growing array. However, this is not the case. The stack's maximum
/// cap is fixed. Take 64 as an example, the stack's maximum cap is 11. 64 ** 11
/// is larger than u64::MAX. The formular is a simple log(u64::MAX, K), the K is
/// the branching factor of the tree.
#[derive(Debug)]
pub(crate) struct VisitStack<const N: usize = STACK_SIZE_FOR_64> {
    /// current stack size
    len: u16,

    /// Nodes
    stack: [InnerNodeId; N],

    /// Offsets
    offsets: [u16; N],
}

impl<const N: usize> VisitStack<N> {
    /// Create a new empty stack
    pub fn new() -> Self {
        Self {
            len: 0,
            stack: [InnerNodeId::INVALID; N],
            offsets: [0; N],
        }
    }

    pub fn len(&self) -> usize {
        self.len as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn push(&mut self, id: InnerNodeId, offset: usize) {
        debug_assert!(self.len < N as u16);

        self.stack[self.len as usize] = id;
        self.offsets[self.len as usize] = offset as u16;
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<(InnerNodeId, usize)> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let id = self.stack[self.len as usize];
        let offset = self.offsets[self.len as usize];
        Some((id, offset as usize))
    }

    pub fn pop_unchecked(&mut self) -> (InnerNodeId, usize) {
        self.len -= 1;
        let id = self.stack[self.len as usize];
        let offset = self.offsets[self.len as usize];
        (id, offset as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visit_stack() {
        assert_eq!(std::mem::size_of::<VisitStack64>(), 128);

        let mut stack = VisitStack64::new();
        assert!(stack.is_empty());

        stack.push(InnerNodeId(1), 1);
        stack.push(InnerNodeId(2), 2);
        stack.push(InnerNodeId(3), 3);

        assert_eq!(stack.len(), 3);

        assert_eq!(stack.pop().unwrap(), (InnerNodeId(3), 3));
        assert_eq!(stack.pop().unwrap(), (InnerNodeId(2), 2));
        assert_eq!(stack.pop().unwrap(), (InnerNodeId(1), 1));

        assert!(stack.is_empty());
    }
}

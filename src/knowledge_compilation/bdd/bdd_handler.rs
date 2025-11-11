/// Error raised by a [`BddHandler`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BddError {
    /// Error raised by [`NumberOfNodesBddHandler`].
    NodeLimitReached,
    /// Error raised if a timeout is reached.
    TimoutReached,
}

/// Handler for BDD operations.
pub trait BddHandler {
    /// This method is called every time a new reference in the BDD is added.
    fn new_ref_added(&mut self) -> Option<BddError> {
        None
    }
}

/// A BDD handler which does never cancel the BDD computation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NopBddHandler {}
impl BddHandler for NopBddHandler {}

/// A BDD handler which cancels the build process after a given number of added nodes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NumberOfNodesBddHandler {
    bound: usize,
    count: usize,
}

impl NumberOfNodesBddHandler {
    /// Constructs a new handler, which stops the execution if a certain number
    /// of nodes is exceeded.
    pub const fn new(bound: usize) -> Self {
        Self { bound, count: 0 }
    }
}

impl BddHandler for NumberOfNodesBddHandler {
    fn new_ref_added(&mut self) -> Option<BddError> {
        self.count += 1;
        if self.count >= self.bound { Some(BddError::NodeLimitReached) } else { None }
    }
}

use crate::handlers::{ComputationHandler, LngComputation, LngEvent};

/// A BDD handler which cancels the build process after a given number of added nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumberOfNodesBddHandler {
    bound: usize,
    count: usize,
    canceled: bool,
}

impl NumberOfNodesBddHandler {
    /// Constructs a new handler, which stops the execution if a certain number
    /// of nodes is exceeded.
    pub const fn new(bound: usize) -> Self {
        assert!(bound >= 0, "The bound for added nodes must be >= 0");
        Self { bound, count: 0, canceled: false }
    }
}

impl ComputationHandler for NumberOfNodesBddHandler {
    fn should_resume(&mut self, event: LngEvent) -> bool {
        match event {
            LngEvent::ComputationStarted(LngComputation::Bdd) => {
                self.count = 0;
            }
            LngEvent::BddNewRefAdded => {
                self.count += 1;
                self.canceled = self.count >= self.bound;
            }
            _ => {}
        }
        !self.canceled
    }
}

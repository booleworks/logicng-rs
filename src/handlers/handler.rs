use super::LngEvent;

/// Basic handler trait which can be used to control computations.
pub trait ComputationHandler {
    fn should_resume(&mut self, event: LngEvent) -> bool;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NopHandler;

impl NopHandler {
    pub const fn new() -> Self {
        Self {}
    }
}

impl ComputationHandler for NopHandler {
    fn should_resume(&mut self, _: LngEvent) -> bool {
        true
    }
}

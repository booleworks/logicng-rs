use super::LngEvent;

/// Basic handler trait which can be used to control computations.
pub trait ComputationHandler {
    /// Returns whether the computation should continue after the given event.
    ///
    /// Returning `false` cancels the computation. The event is then used as the cancellation cause
    /// in the returned [`CancelableResult`](crate::handlers::CancelableResult), if the computation
    /// exposes cancellation through that type.
    fn should_resume(&mut self, event: LngEvent) -> bool;
}

/// Handler which never cancels a computation.
#[derive(Clone, Copy, Debug, Default)]
pub struct NopHandler;

impl NopHandler {
    /// Constructs a new no-op handler.
    pub const fn new() -> Self {
        Self {}
    }
}

impl ComputationHandler for NopHandler {
    fn should_resume(&mut self, _: LngEvent) -> bool {
        true
    }
}

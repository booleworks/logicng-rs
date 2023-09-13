/// Basic handler trait which can be used to control computations.
pub trait ComputationHandler {
    /// Initial call to start this handler.
    fn started(&mut self) {}

    /// Returns `true` if this handler is aborted. Usually, this means that the
    /// calculation will also abort.
    fn aborted(&self) -> bool {
        false
    }
}

use super::LngEvent;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

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

/// Determines how a [`TimeoutHandler`] interprets its timeout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TimerType {
    /// Starts once on the first computation-started event.
    SingleTimeout,
    /// Restarts on every computation-started event.
    RestartingTimeout,
    /// Interprets the value as a Unix timestamp in milliseconds.
    FixedEnd,
}

/// A generic computation handler which cancels after a timeout in milliseconds.
#[derive(Clone, Debug)]
pub struct TimeoutHandler {
    timeout: Duration,
    timer_type: TimerType,
    deadline: Option<Instant>,
    fixed_end: Option<SystemTime>,
}

impl TimeoutHandler {
    /// Creates a single-use timeout which starts with the first computation.
    pub fn new(timeout_ms: u64) -> Self {
        Self::with_timer_type(timeout_ms, TimerType::SingleTimeout)
    }

    /// Creates a timeout with the given timer semantics.
    pub fn with_timer_type(timeout_ms: u64, timer_type: TimerType) -> Self {
        let fixed_end = (timer_type == TimerType::FixedEnd)
            .then(|| UNIX_EPOCH + Duration::from_millis(timeout_ms));
        Self {
            timeout: Duration::from_millis(timeout_ms),
            timer_type,
            deadline: None,
            fixed_end,
        }
    }

    fn exceeded(&self) -> bool {
        self.deadline.is_some_and(|end| Instant::now() >= end)
            || self.fixed_end.is_some_and(|end| SystemTime::now() >= end)
    }
}

impl ComputationHandler for TimeoutHandler {
    fn should_resume(&mut self, event: LngEvent) -> bool {
        if matches!(event, LngEvent::ComputationStarted(_))
            && self.timer_type != TimerType::FixedEnd
            && (self.timer_type == TimerType::RestartingTimeout || self.deadline.is_none())
        {
            self.deadline = Some(Instant::now() + self.timeout);
        }
        !self.exceeded()
    }
}

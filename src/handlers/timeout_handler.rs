use std::time::{Duration, Instant};

use super::ComputationHandler;

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum Timer {
    SingleTimeout(Duration),
    RestartingTimeout(Duration),
    FixedEnd(Instant),
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct TimeoutHandler {
    timer: Timer,
    checkpoint: Instant,
}

impl TimeoutHandler {
    pub fn new(timer: Timer) -> Self {
        Self { timer, checkpoint: Instant::now() }
    }
}

impl ComputationHandler for TimeoutHandler {
    fn should_resume(&mut self, event: super::LngEvent) -> bool {
        match self.timer {
            Timer::SingleTimeout(timeout) => self.checkpoint.elapsed() < timeout,
            Timer::RestartingTimeout(timeout) => {
                if matches!(event, super::LngEvent::ComputationStarted(_)) {
                    self.checkpoint = Instant::now();
                }
                self.checkpoint.elapsed() < timeout
            }
            Timer::FixedEnd(end) => Instant::now() < end,
        }
    }
}

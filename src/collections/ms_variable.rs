use crate::solver::minisat::sat::Tristate;

/// A MiniSAT Variable
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct MsVariable {
    pub assignment: Tristate,
    pub level: Option<usize>,
    pub polarity: bool,
    pub decision: bool,
}

impl MsVariable {
    pub const fn new(polarity: bool, decision: bool) -> Self {
        Self { assignment: Tristate::Undef, level: None, polarity, decision }
    }

    pub fn level_greater_zero(&self) -> bool {
        self.level.unwrap_or(0) > 0
    }
}

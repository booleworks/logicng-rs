use crate::propositions::Proposition;

/// An unsatisfiable core (can be a minimal unsatisfiable sub-formula).
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct UnsatCore {
    /// Propositions of this MUS.
    pub propositions: Vec<Proposition>,
    /// Is `true` if the core is a MUS and `false` if it is yet unknown whether
    /// it is a MUS.
    pub is_mus: bool,
}

impl UnsatCore {
    /// Constructs a new unsatisfiable core.
    pub fn new(proposition: Vec<Proposition>, is_mus: bool) -> Self {
        Self { propositions: proposition, is_mus }
    }
}

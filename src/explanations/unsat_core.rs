use crate::propositions::Proposition;

/// An unsatisfiable core (can be a minimal unsatisfiable sub-formula).
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct UnsatCore<Backpack> {
    /// Propositions of this MUS.
    pub propositions: Vec<Proposition<Backpack>>,
    /// Is `true` if the core is a MUS and `false` if it is yet unknown whether
    /// it is a MUS.
    pub is_mus: bool,
}

impl<B> UnsatCore<B> {
    /// Constructs a new unsatisfiable core.
    pub fn new(proposition: Vec<Proposition<B>>, is_mus: bool) -> Self {
        Self { propositions: proposition, is_mus }
    }
}

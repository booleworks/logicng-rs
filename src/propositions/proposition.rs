use crate::formulas::EncodedFormula;

/// A proposition in LogicNG. A proposition is a formula with an additional
/// textual description.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Proposition {
    /// Formula which holds this proposition.
    pub formula: EncodedFormula,
    /// Description for the formula.
    pub description: Option<String>,
    /// Id of this proposition.
    pub id: Option<usize>,
}

impl Proposition {
    /// Constructs a new proposition for a formulas.
    pub const fn new(formula: EncodedFormula) -> Self {
        Self { formula, description: None, id: None }
    }

    /// Returns the backpack of this proposition.
    #[must_use]
    pub fn description(mut self, description: &str) -> Self {
        self.description = Some(description.to_string());
        self
    }

    /// Returns the id of this proposition.
    #[must_use]
    pub const fn id(mut self, id: usize) -> Self {
        self.id = Some(id);
        self
    }
}

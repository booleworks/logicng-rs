use std::rc::Rc;

use crate::formulas::EncodedFormula;

/// A proposition in LogicNG. A proposition is a formula with an additional
/// textual description.
#[derive(Eq, PartialEq, Hash, Debug)]
pub struct Proposition<T> {
    /// Formula which holds this proposition.
    pub formula: EncodedFormula,
    /// Description for the formula.
    pub backpack: Option<Rc<T>>,
}

impl<T> Clone for Proposition<T> {
    fn clone(&self) -> Self {
        Self { formula: self.formula, backpack: self.backpack.as_ref().map(Rc::clone) }
    }
}

impl<T> Proposition<T> {
    /// Constructs a new proposition for a formulas.
    pub const fn new(formula: EncodedFormula) -> Self {
        Self { formula, backpack: None }
    }

    /// Constructs a new proposition for a formulas with an assositated value (backpack).
    pub fn with_backpack(formula: EncodedFormula, backpack: T) -> Self {
        Self { formula, backpack: Some(Rc::new(backpack)) }
    }

    /// Update the backpack of this proposition.
    #[must_use]
    pub fn backpack(mut self, backpack: T) -> Self {
        self.backpack = Some(Rc::new(backpack));
        self
    }
}

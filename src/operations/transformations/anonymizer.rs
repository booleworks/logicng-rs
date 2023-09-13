use crate::formulas::{EncodedFormula, FormulaFactory};

use super::Substitution;

/// Anonymizer allows to remove/obscure the semantics of variables of formulas.
///
/// Anonymization replaces all variables names with `{prefix}1`,
/// `{prefix}2`, ... By doing so, the original semantics of the variable
/// names gets lost/obscured.
pub struct Anonymizer<'a> {
    /// prefix for new variables.
    pub prefix: String,
    substitution: Substitution,
    counter: usize,
    /// factory of this Anonymizer.
    pub factory: &'a FormulaFactory,
}

impl<'a> Anonymizer<'a> {
    /// Create a new `Anonymizer` with `v` as prefix.
    pub fn new(f: &'a FormulaFactory) -> Self {
        Self::with_prefix("v", f)
    }

    /// Create a new `Anonymizer` with an custom prefix.
    pub fn with_prefix(prefix: &str, f: &'a FormulaFactory) -> Self {
        Self { prefix: prefix.to_owned(), substitution: Substitution::new(), counter: 0, factory: f }
    }

    /// Anonymizes a formula.
    pub fn anonymize(&mut self, formula: EncodedFormula) -> EncodedFormula {
        let variables = formula.variables(self.factory);
        for variable in &*variables {
            self.substitution.entry(*variable).or_insert_with(|| {
                let c = self.counter;
                self.counter += 1;
                self.factory.variable(&format!("{}{}", self.prefix, c))
            });
        }
        self.factory.substitute(formula, &self.substitution)
    }

    /// Returns the substitions used by this anonymizer.
    pub const fn substitution(&self) -> &Substitution {
        &self.substitution
    }
}

use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::handlers::{ComputationHandler, LngComputation, LngEvent};
use crate::operations::transformations::cnf::CnfAlgorithm;
use crate::operations::transformations::cnf::CnfAlgorithm::Tseitin;

use super::CnfEncoder;

/// Constructs the _CNF_ of a formula with factorization and the given
/// [`AdvancedFactorizationConfig`].
pub fn advanced_cnf_encoding(
    formula: EncodedFormula,
    f: &FormulaFactory,
    config: &AdvancedFactorizationConfig,
    state: &mut CnfEncoder,
) -> EncodedFormula {
    if formula.is_and() {
        let new_ops = formula.operands(f).into_iter().map(|op| single_advanced_encoding(op, f, config, state));
        f.and(new_ops)
    } else {
        single_advanced_encoding(formula, f, config, state)
    }
}

fn single_advanced_encoding(
    formula: EncodedFormula,
    f: &FormulaFactory,
    config: &AdvancedFactorizationConfig,
    state: &mut CnfEncoder,
) -> EncodedFormula {
    CnfAlgorithm::Factorization
        .transform_with_handler(formula, f, state, &mut config.handler())
        .result()
        .unwrap_or_else(|| (*config.fallback_algorithm).transform(formula, f, state))
}

/// Configuration for advanced _CNF_ algorithms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdvancedFactorizationConfig {
    distribution_boundary: u64,
    created_clause_boundary: u64,
    atom_boundary: u64,
    fallback_algorithm: Box<CnfAlgorithm>,
}

impl Default for AdvancedFactorizationConfig {
    fn default() -> Self {
        Self { distribution_boundary: u64::MAX, created_clause_boundary: 1000, atom_boundary: 12, fallback_algorithm: Box::new(Tseitin) }
    }
}

impl AdvancedFactorizationConfig {
    /// Sets the boundary how many distributions should be performed in the
    /// factorization before the method is switched.
    #[must_use]
    pub const fn distribution_boundary(mut self, distribution_boundary: u64) -> Self {
        self.distribution_boundary = distribution_boundary;
        self
    }

    /// Sets the boundary how many clauses should be created in the
    /// factorization before the method is switched.
    #[must_use]
    pub const fn created_clause_boundary(mut self, created_clause_boundary: u64) -> Self {
        self.created_clause_boundary = created_clause_boundary;
        self
    }

    /// Sets the boundary for how many atoms in a formula factorization is
    /// performed in Tseitin and Plaisted & Greenbaum.
    ///
    /// The default value is 12.
    #[must_use]
    pub const fn atom_boundary(mut self, atom_boundary: u64) -> Self {
        self.atom_boundary = atom_boundary;
        self
    }

    /// Sets the fallback algorithm for the advanced CNF encoding. When the
    /// boundaries for the factorization are met, the encoding switches to this
    /// algorithm.
    ///
    /// The default value is [`CnfAlgorithm::TSEITIN`](`CnfAlgorithm`).
    #[must_use]
    pub fn fallback_algorithm(mut self, fallback_algorithm: CnfAlgorithm) -> Self {
        assert!(fallback_algorithm != CnfAlgorithm::Factorization, "Factorization can not be used as fallback");
        self.fallback_algorithm = Box::new(fallback_algorithm);
        self
    }

    /// Creates an new handler based on this configuration.
    pub fn handler(&self) -> AdvancedFactorizationHandler {
        AdvancedFactorizationHandler::new(Some(self.distribution_boundary), Some(self.created_clause_boundary))
    }
}

#[derive(Debug, Clone)]
pub(crate) struct AdvancedFactorizationHandler {
    distribution_boundary: Option<u64>,
    created_clause_boundary: Option<u64>,
    canceled: bool,
    current_distribution: usize,
    current_clause: usize,
}

impl AdvancedFactorizationHandler {
    pub fn new(distribution_boundary: Option<u64>, created_clause_boundary: Option<u64>) -> Self {
        Self { distribution_boundary, created_clause_boundary, canceled: false, current_distribution: 0, current_clause: 0 }
    }

    #[cfg(test)]
    pub fn canceled(&self) -> bool {
        self.canceled
    }

    #[cfg(test)]
    pub fn current_distribution(&self) -> usize {
        self.current_distribution
    }

    #[cfg(test)]
    pub fn current_clause(&self) -> usize {
        self.current_clause
    }
}

impl ComputationHandler for AdvancedFactorizationHandler {
    fn should_resume(&mut self, event: LngEvent) -> bool {
        match event {
            LngEvent::ComputationStarted(LngComputation::Factorization) => {
                self.current_distribution = 0;
                self.current_clause = 0;
            }
            LngEvent::DistributionPerformed => {
                self.current_distribution += 1;
                self.canceled = self.distribution_boundary.is_some_and(|bound| self.current_distribution > bound as usize);
            }
            LngEvent::FactorizationCreatedClause(_) => {
                self.current_clause += 1;
                self.canceled = self.created_clause_boundary.is_some_and(|bound| self.current_clause > bound as usize);
            }
            _ => {}
        }
        !self.canceled
    }
}

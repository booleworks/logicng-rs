mod advanced;
mod factorization;
mod plaisted_greenbaum_on_formula;
pub(super) mod plaisted_greenbaum_on_solver;
mod tseitin;

use std::collections::HashMap;

use crate::formulas::{EncodedFormula, FormulaFactory, Literal};
use crate::handlers::{FactorizationError, FactorizationHandler};
use crate::knowledge_compilation::bdd::{Bdd, BddError, BddHandler, BddKernel};
//use advanced::{advanced_cnf_encoding, AdvancedFactorizationConfig};
use factorization::{factorization_cnf, factorization_cnf_with_handler};
use plaisted_greenbaum_on_formula::pg_on_formula;
use tseitin::tseitin_cnf_with_boundary;

pub use advanced::*;

const DEFAULT_BOUNDARY_FOR_FACTORIZATION: u64 = 12;

/// Types of _CNF_ algorithms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CnfAlgorithm {
    /// Transformation of a formula in _CNF_ by factorization.
    Factorization,
    /// Transformation of a formula into _CNF_ due to Tseitin.
    Tseitin,
    /// Transformation of a formula into _CNF_ due to Tseitin with custom boundary.
    TseitinWithBoundary(u64),
    /// Transformation of a formula into _CNF_ due to Plaisted & Greenbaum.
    PlaistedGreenbaum,
    /// Transformation of a formula into _CNF_ due to Plaisted & Greenbaum with custom boundary.
    PlaistedGreenbaumWithBoundary(u64),
    /// Transformation of a formula in _CNF_ by converting it to a BDD.
    Bdd,
    /// Transformation of a formula in _CNF_ by factorization with advanced configuration options.
    Advanced(AdvancedFactorizationConfig),
}

impl CnfAlgorithm {
    /// Transform the given formula into a _CNF_ formula.
    fn transform(&self, formula: EncodedFormula, f: &FormulaFactory, state: &mut CnfEncoder) -> EncodedFormula {
        if formula.is_cnf(f) {
            return formula;
        }
        match self {
            Self::Factorization => factorization_cnf(formula, f),
            Self::Tseitin => tseitin_cnf_with_boundary(
                formula,
                f,
                DEFAULT_BOUNDARY_FOR_FACTORIZATION,
                state.tseitin_state.as_mut().unwrap_or(&mut TseitinState::default()),
            ),
            Self::TseitinWithBoundary(boundary) => {
                tseitin_cnf_with_boundary(formula, f, *boundary, state.tseitin_state.as_mut().unwrap_or(&mut TseitinState::default()))
            }
            Self::PlaistedGreenbaum => {
                pg_on_formula(formula, f, DEFAULT_BOUNDARY_FOR_FACTORIZATION, state.pg_state.as_mut().unwrap_or(&mut PGState::default()))
            }
            Self::PlaistedGreenbaumWithBoundary(boundary) => {
                pg_on_formula(formula, f, *boundary, state.pg_state.as_mut().unwrap_or(&mut PGState::default()))
            }
            Self::Advanced(config) => advanced_cnf_encoding(formula, f, config, state),
            Self::Bdd => {
                let mut kernel = BddKernel::new_with_num_vars(formula.variables(f).len(), 10_000, 10_000);
                Bdd::from_formula(formula, f, &mut kernel).cnf(f, &mut kernel)
            }
        }
    }
}

/// An encoder for conjunctive normal form (CNF).
///
/// An encoder is capable of keeping a state over multiple calculation, which is
/// used by the algorithm to yield faster/better results.
pub struct CnfEncoder {
    /// Algorithm used by this encoder.
    pub algorithm: CnfAlgorithm,
    tseitin_state: Option<TseitinState>,
    pg_state: Option<PGState>,
}

impl CnfEncoder {
    /// Returns a new encoder.
    ///
    /// Note that, this encoder will keep track of variables introduced by
    /// _Tseitin_ and _Pleisted-Greenbaum_, and reuses them even over multiple
    /// [`transform`](`Self::transform`) calls. If this behavior is unwanted, you should use
    /// [`CnfEncoder::stateless`], which will not keep this kind of state.
    pub fn new(algorithm: CnfAlgorithm) -> Self {
        Self { algorithm, tseitin_state: Some(TseitinState::default()), pg_state: Some(PGState::default()) }
    }

    /// Returns a new stateless encoder.
    ///
    /// A stateless encoder will not keep its state (except the algorithm) over
    /// multiple calculations. This might be handy, if you want to encode a
    /// couple of independent formulas, which should not influence each other.
    pub const fn stateless(algorithm: CnfAlgorithm) -> Self {
        Self { algorithm, tseitin_state: None, pg_state: None }
    }

    /// Transform a formula with the algorithm of this encoder.
    pub fn transform(&mut self, formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
        self.algorithm.clone().transform(formula, f, self)
    }
}

/// Types of cancellable _CNF_ algorithms.
pub enum CancellableCnfAlgorithm {
    /// Transformation of a formula in _CNF_ by factorization.
    FactorizationWithHandler(Box<dyn FactorizationHandler>),
    /// Transformation of a formula in _CNF_ by converting it to a BDD.
    BddWithHandler(Box<dyn BddHandler>),
}

impl CancellableCnfAlgorithm {
    /// Transform the given formula into a _CNF_ formula.
    pub fn transform(self, formula: EncodedFormula, f: &FormulaFactory) -> Result<EncodedFormula, CancellationReason> {
        match self {
            Self::FactorizationWithHandler(mut handler) => {
                factorization_cnf_with_handler(formula, f, &mut *handler).map_err(CancellationReason::FactorizationFailed)
            }
            Self::BddWithHandler(mut handler) => {
                let mut kernel = BddKernel::new_with_num_vars(formula.variables(f).len(), 10_000, 10_000);
                Ok(Bdd::from_formula_with_handler(formula, f, &mut kernel, &mut *handler)
                    .map_err(CancellationReason::BddGenerationFailed)?
                    .cnf(f, &mut kernel))
            }
        }
    }
}

/// Errors emitted by [`CancellableCnfAlgorithm`]s if the calculation gets canceled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CancellationReason {
    /// Emitted by factorization algorithms.
    FactorizationFailed(FactorizationError),
    /// Emitted by BDD algorithms.
    BddGenerationFailed(BddError),
}

#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct TseitinState {
    pub formula: HashMap<EncodedFormula, EncodedFormula>,
    pub variable: HashMap<EncodedFormula, Literal>,
}

#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct PGState {
    pub formula: HashMap<EncodedFormula, EncodedFormula>,
    pub variable: HashMap<EncodedFormula, Literal>,
}

#[cfg(test)]
mod tests {
    use CancellableCnfAlgorithm::FactorizationWithHandler;
    use CnfAlgorithm::{Advanced, Bdd, Factorization, Tseitin};
    use std::collections::HashSet;

    use crate::datastructures::Assignment;
    use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula, Variable};
    use crate::handlers::ClauseLimitFactorizationHandler;
    use crate::handlers::FactorizationError::{ClauseLimitReached, DistributionLimitReached};
    use crate::knowledge_compilation::bdd::{BddError, NumberOfNodesBddHandler};
    use crate::operations::transformations::CnfEncoder;
    use crate::operations::transformations::cnf::CancellationReason::{BddGenerationFailed, FactorizationFailed};
    use crate::operations::transformations::cnf::CnfAlgorithm::TseitinWithBoundary;
    use crate::operations::transformations::cnf::advanced::AdvancedFactorizationConfig;
    use crate::operations::transformations::cnf::{CancellableCnfAlgorithm, CnfAlgorithm};
    use crate::solver::functions::{ModelEnumerationConfig, enumerate_models_for_formula_with_config};

    const P1: &str = "(x1 | x2) & x3 & x4 & ((x1 & x5 & ~(x6 | x7) | x8) | x9)";
    const P2: &str = "(y1 | y2) & y3 & y4 & ((y1 & y5 & ~(y6 | y7) | y8) | y9)";
    const P3: &str = "(z1 | z2) & z3 & z4 & ((z1 & z5 & ~(z6 | z7) | z8) | z9)";

    #[test]
    fn test_factorization() {
        let f = &mut FormulaFactory::new();
        let phi1 = P1.to_formula(f);
        assert_eq!(
            f.cnf_of(phi1),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f)
        );
        f.config.cnf_config = Factorization;
        assert_eq!(
            f.cnf_of(phi1),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f)
        );
        assert_eq!(
            CnfEncoder::new(Factorization).transform(phi1, f),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f)
        );
    }

    #[test]
    fn test_tseitin() {
        let f = &mut FormulaFactory::with_id("FF42");
        let phi1 = P1.to_formula(f);
        let phi2 = P2.to_formula(f);
        f.config.cnf_config = Tseitin;
        assert_eq!(
            f.cnf_of(phi1),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f)
        );
        f.config.cnf_config = TseitinWithBoundary(8);
        assert_eq!(f.cnf_of(phi1), "(@RESERVED_FF42_CNF_0 | ~x1) & (@RESERVED_FF42_CNF_0 | ~x2) & (~@RESERVED_FF42_CNF_0 | x1 | x2) & (~@RESERVED_FF42_CNF_1 | x1) & (~@RESERVED_FF42_CNF_1 | x5) & (~@RESERVED_FF42_CNF_1 | ~x6) & (~@RESERVED_FF42_CNF_1 | ~x7) & (@RESERVED_FF42_CNF_1 | ~x1 | ~x5 | x6 | x7) & (@RESERVED_FF42_CNF_2 | ~@RESERVED_FF42_CNF_1) & (@RESERVED_FF42_CNF_2 | ~x8) & (@RESERVED_FF42_CNF_2 | ~x9) & (~@RESERVED_FF42_CNF_2 | @RESERVED_FF42_CNF_1 | x8 | x9) & @RESERVED_FF42_CNF_0 & x3 & x4 & @RESERVED_FF42_CNF_2".to_formula(f));
        f.config.cnf_config = TseitinWithBoundary(11);
        assert_eq!(
            f.cnf_of(phi2),
            "(y1 | y2) & y3 & y4 & (y1 | y8 | y9) & (y5 | y8 | y9) & (~y6 | y8 | y9) & (~y7 | y8 | y9)".to_formula(f)
        );
    }

    #[test]
    fn test_pg() {
        let f = &mut FormulaFactory::with_id("FF42");
        let phi1 = P1.to_formula(f);
        let phi2 = P2.to_formula(f);
        let phi1_vars = phi1.variables(f).iter().copied().collect();
        f.config.cnf_config = CnfAlgorithm::PlaistedGreenbaum;
        assert_eq!(
            f.cnf_of(phi1),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f),
        );
        f.config.cnf_config = CnfAlgorithm::PlaistedGreenbaumWithBoundary(8);
        assert!(equivalent_models(
            f.cnf_of(phi1),
            "@RESERVED_FF42_CNF_1 & x3 & x4 & @RESERVED_FF42_CNF_2 & (~@RESERVED_FF42_CNF_1 | x1 | x2) & (~@RESERVED_FF42_CNF_2 | @RESERVED_FF42_CNF_3 | x8 | x9) & (~@RESERVED_FF42_CNF_3 | x1) & (~@RESERVED_FF42_CNF_3 | x5) & (~@RESERVED_FF42_CNF_3 | ~x6) & (~@RESERVED_FF42_CNF_3 | ~x7)".to_formula(f),
            phi1_vars,
            f
        ));
        f.config.cnf_config = CnfAlgorithm::PlaistedGreenbaumWithBoundary(11);
        assert_eq!(
            f.cnf_of(phi2),
            "(y1 | y2) & y3 & y4 & (y1 | y8 | y9) & (y5 | y8 | y9) & (~y6 | y8 | y9) & (~y7 | y8 | y9)".to_formula(f)
        );
    }

    #[test]
    fn test_advanced() {
        let f = &mut FormulaFactory::with_id("FF42");
        let phi1 = P1.to_formula(f);
        let phi2 = P2.to_formula(f);
        let phi3 = P3.to_formula(f);
        assert_eq!(
            f.cnf_of(phi1),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f)
        );
        f.config.cnf_config = Advanced(
            AdvancedFactorizationConfig::default().created_clause_boundary(5).atom_boundary(3).fallback_algorithm(TseitinWithBoundary(3)),
        );
        let formula = f.cnf_of(phi2);
        assert_eq!(formula, "(y1 | y2) & y3 & y4 & (~@RESERVED_FF42_CNF_0 | y1) & (~@RESERVED_FF42_CNF_0 | y5) & (~@RESERVED_FF42_CNF_0 | ~y6) & (~@RESERVED_FF42_CNF_0 | ~y7) & (@RESERVED_FF42_CNF_0 | ~y1 | ~y5 | y6 | y7) & (@RESERVED_FF42_CNF_0 | y8 | y9)".to_formula(f));
        f.config.cnf_config = Advanced(
            AdvancedFactorizationConfig::default()
                .created_clause_boundary(u64::MAX)
                .distribution_boundary(5)
                .atom_boundary(3)
                .fallback_algorithm(TseitinWithBoundary(3)),
        );
        assert_eq!(f.cnf_of(phi3), "(z1 | z2) & z3 & z4 & (~@RESERVED_FF42_CNF_2 | z1) & (~@RESERVED_FF42_CNF_2 | z5) & (~@RESERVED_FF42_CNF_2 | ~z6) & (~@RESERVED_FF42_CNF_2 | ~z7) & (@RESERVED_FF42_CNF_2 | ~z1 | ~z5 | z6 | z7) & (@RESERVED_FF42_CNF_2 | z8 | z9)".to_formula(f));
    }

    #[test]
    fn test_advanced_with_pg_fallback() {
        let f = &mut FormulaFactory::with_id("FF42");
        let phi1 = P1.to_formula(f);
        let phi2 = P2.to_formula(f);
        let phi3 = P3.to_formula(f);
        assert_eq!(
            f.cnf_of(phi1),
            "(x1 | x2) & x3 & x4 & (x1 | x8 | x9) & (x5 | x8 | x9) & (~x6 | x8 | x9) & (~x7 | x8 | x9)".to_formula(f)
        );
        f.config.cnf_config = Advanced(
            AdvancedFactorizationConfig::default().created_clause_boundary(5).atom_boundary(3).fallback_algorithm(TseitinWithBoundary(3)),
        );
        let formula = f.cnf_of(phi2);
        assert_eq!(formula, "(y1 | y2) & y3 & y4 & (~@RESERVED_FF42_CNF_0 | y1) & (~@RESERVED_FF42_CNF_0 | y5) & (~@RESERVED_FF42_CNF_0 | ~y6) & (~@RESERVED_FF42_CNF_0 | ~y7) & (@RESERVED_FF42_CNF_0 | ~y1 | ~y5 | y6 | y7) & (@RESERVED_FF42_CNF_0 | y8 | y9)".to_formula(f));
        f.config.cnf_config = Advanced(
            AdvancedFactorizationConfig::default()
                .created_clause_boundary(u64::MAX)
                .distribution_boundary(5)
                .atom_boundary(3)
                .fallback_algorithm(TseitinWithBoundary(3)),
        );
        assert_eq!(f.cnf_of(phi3), "(z1 | z2) & z3 & z4 & (~@RESERVED_FF42_CNF_2 | z1) & (~@RESERVED_FF42_CNF_2 | z5) & (~@RESERVED_FF42_CNF_2 | ~z6) & (~@RESERVED_FF42_CNF_2 | ~z7) & (@RESERVED_FF42_CNF_2 | ~z1 | ~z5 | z6 | z7) & (@RESERVED_FF42_CNF_2 | z8 | z9)".to_formula(f));
    }

    #[test]
    fn test_bdd() {
        let f = &mut FormulaFactory::with_id("FF42");
        let phi1 = P1.to_formula(f);
        let phi2 = P2.to_formula(f);
        let phi3 = P3.to_formula(f);
        let phi1_vars = phi1.variables(f).iter().copied().collect();
        let phi2_vars = phi2.variables(f).iter().copied().collect();
        let phi3_vars = phi3.variables(f).iter().copied().collect();
        f.config.cnf_config = Bdd;
        assert!(equivalent_models(phi1, f.cnf_of(phi1), phi1_vars, f));
        assert!(equivalent_models(phi2, f.cnf_of(phi2), phi2_vars, f));
        assert!(equivalent_models(phi3, f.cnf_of(phi3), phi3_vars, f));
    }

    #[test]
    fn test_cancellable_cnf() {
        let f = &FormulaFactory::with_id("FF42");
        let phi1 = P1.to_formula(f);
        let cnf1 = FactorizationWithHandler(Box::new(ClauseLimitFactorizationHandler::new(5, 10000))).transform(phi1, f);
        let cnf2 = FactorizationWithHandler(Box::new(ClauseLimitFactorizationHandler::new(10000, 5))).transform(phi1, f);
        let cnf3 = FactorizationWithHandler(Box::new(ClauseLimitFactorizationHandler::new(10000, 10000))).transform(phi1, f);
        assert_eq!(cnf1, Err(FactorizationFailed(DistributionLimitReached)));
        assert_eq!(cnf2, Err(FactorizationFailed(ClauseLimitReached)));
        assert!(cnf3.is_ok());

        let cnf1 = CancellableCnfAlgorithm::BddWithHandler(Box::new(NumberOfNodesBddHandler::new(10))).transform(phi1, f);
        let cnf2 = CancellableCnfAlgorithm::BddWithHandler(Box::new(NumberOfNodesBddHandler::new(1000))).transform(phi1, f);
        assert_eq!(cnf1, Err(BddGenerationFailed(BddError::NodeLimitReached)));
        assert!(cnf2.is_ok());
    }

    fn equivalent_models(f1: EncodedFormula, f2: EncodedFormula, vars: Box<[Variable]>, f: &FormulaFactory) -> bool {
        let config = ModelEnumerationConfig::default().variables(vars);
        let models1: HashSet<Assignment> = enumerate_models_for_formula_with_config(f1, f, &config).iter().map(Assignment::from).collect();
        let models2: HashSet<Assignment> = enumerate_models_for_formula_with_config(f2, f, &config).iter().map(Assignment::from).collect();
        models1 == models2
    }
}

use std::collections::BTreeSet;

use num_bigint::BigUint;

use crate::datastructures::Assignment;
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Variable};
use crate::handlers::{CancelableResult, ComputationHandler, NopHandler};
use crate::knowledge_compilation::bdd::orderings::force_ordering;
use crate::knowledge_compilation::bdd::{Bdd, BddKernel};
use crate::knowledge_compilation::dnnf::compile_dnnf_with_handler;
use crate::operations::OperationError;
use crate::operations::transformations::{
    AdvancedFactorizationConfig, CnfAlgorithm, CnfEncoder, pure_expansion,
};

/// Algorithms available for model counting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModelCountAlgorithm {
    /// Dnnf based model counting.
    Dnnf,
    /// Bdd based model counting. Uses force ordering and initializes Bdd kernel
    /// with `node_size` and `cache_size`.
    Bdd {
        /// Node size of the Bdd kernel.
        node_size: usize,
        /// Cache size of the Bdd kernel.
        cache_size: usize,
    },
}

/// Computes the model count for a given formula.
///
/// # Errors
///
/// Returns an error if the formula cannot be encoded for the chosen model
/// counting algorithm or if the algorithm itself fails.
pub fn count_models(
    formula: EncodedFormula,
    algorithm: ModelCountAlgorithm,
    f: &FormulaFactory,
) -> LngResult<BigUint> {
    count_models_with_vars(formula, algorithm, &formula.variables(f), f)
}

/// Computes the model count for a given formula using a cancelable computation handler.
///
/// # Errors
///
/// Returns an error if the formula cannot be encoded or if the selected algorithm fails.
pub fn count_models_with_handler(
    formula: EncodedFormula,
    algorithm: ModelCountAlgorithm,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<BigUint>> {
    count_models_with_vars_with_handler(formula, algorithm, &formula.variables(f), f, handler)
}

/// Computes the model count for a given formula and a set of relevant
/// variables. This set can only be a superset of the original formula's
/// variables.
///
/// # Errors
///
/// Returns an error if `relevant_vars` does not contain all variables of the
/// formula, if the formula cannot be encoded for the chosen model counting
/// algorithm, or if the algorithm itself fails.
pub fn count_models_with_vars(
    formula: EncodedFormula,
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> LngResult<BigUint> {
    Ok(count_models_with_vars_with_handler(
        formula,
        algorithm,
        relevant_vars,
        f,
        &mut NopHandler::new(),
    )?
    .result()
    .expect("nop handler can never abort"))
}

/// Computes the model count for a formula and relevant variables using a
/// cancelable computation handler.
///
/// # Errors
///
/// Returns an error if `relevant_vars` omits formula variables or encoding or
/// counting fails.
pub fn count_models_with_vars_with_handler(
    formula: EncodedFormula,
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<BigUint>> {
    let vars = formula.variables(f);
    if !vars.is_subset(relevant_vars) {
        return Err(OperationError::MCNotAllVars.into());
    }

    if vars.is_empty() {
        return Ok(CancelableResult::Ok(if formula.is_verum() {
            BigUint::from(1_usize)
        } else {
            BigUint::from(0_usize)
        }));
    }

    let mut cnf_encoder = CnfEncoder::new(CnfAlgorithm::Advanced(
        AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin),
    ));
    let expanded = pure_expansion(formula, f)?;
    let cnf = match cnf_encoder.transform_with_handler(expanded, f, handler)? {
        CancelableResult::Ok(cnf) => cnf,
        CancelableResult::Canceled(event) | CancelableResult::Partial(_, event) => {
            return Ok(CancelableResult::Canceled(event));
        }
    };
    let count = count_formula_with_handler(cnf, algorithm, f, handler)?;
    let dont_care_vars = relevant_vars.difference(&cnf.variables(f)).count();
    let dc_size = u32::try_from(dont_care_vars).map_err(|_| OperationError::MCTooManyDontCares)?;
    let factor = BigUint::from(2_usize).pow(dc_size);
    Ok(count.map(|count| count * factor))
}

/// Computes the model count for a given set of formulas (interpreted as conjunction).
///
/// # Errors
///
/// Returns an error if the formulas cannot be encoded for the chosen model
/// counting algorithm or if the algorithm itself fails.
pub fn count_models_conjunction(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    f: &FormulaFactory,
) -> LngResult<BigUint> {
    Ok(
        count_models_conjunction_with_handler(formulas, algorithm, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Computes the model count of a conjunction using a cancelable computation handler.
///
/// # Errors
///
/// Returns an error if encoding or counting fails.
pub fn count_models_conjunction_with_handler(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<BigUint>> {
    let vars = formulas
        .iter()
        .fold(BTreeSet::default(), |mut variables, formula| {
            variables.extend((*formula.variables(f)).clone());
            variables
        });
    count_models_internal_with_handler(formulas, algorithm, &vars, &vars, f, handler)
}

/// Computes the model count for a given set of formulas (interpreted as conjunction)
/// and a set of relevant variables.  This set can only be a superset of the original
/// formulas' variables.
///
/// # Errors
///
/// Returns an error if `relevant_vars` does not contain all variables of the
/// formulas, if the formulas cannot be encoded for the chosen model counting
/// algorithm, or if the algorithm itself fails.
pub fn count_models_conjunction_with_vars(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> LngResult<BigUint> {
    Ok(count_models_conjunction_with_vars_with_handler(
        formulas,
        algorithm,
        relevant_vars,
        f,
        &mut NopHandler::new(),
    )?
    .result()
    .expect("nop handler can never abort"))
}

/// Computes the model count of a conjunction and relevant variables using a
/// cancelable computation handler.
///
/// # Errors
///
/// Returns an error if `relevant_vars` omits formula variables or encoding or
/// counting fails.
pub fn count_models_conjunction_with_vars_with_handler(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<BigUint>> {
    let vars = formulas
        .iter()
        .fold(BTreeSet::default(), |mut variables, formula| {
            variables.extend((*formula.variables(f)).clone());
            variables
        });
    count_models_internal_with_handler(formulas, algorithm, relevant_vars, &vars, f, handler)
}

fn count_models_internal_with_handler(
    formulas: &[EncodedFormula],
    algorithm: ModelCountAlgorithm,
    relevant_vars: &BTreeSet<Variable>,
    all_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<BigUint>> {
    if !all_vars.is_subset(relevant_vars) {
        return Err(OperationError::MCNotAllVars.into());
    }

    if all_vars.is_empty() {
        let all_verum = formulas.iter().all(|formula| formula.is_verum());
        return Ok(CancelableResult::Ok(BigUint::from(usize::from(all_verum))));
    }

    let cnfs = match encode_as_cnf_with_handler(formulas, f, handler)? {
        CancelableResult::Ok(cnfs) => cnfs,
        CancelableResult::Canceled(event) | CancelableResult::Partial(_, event) => {
            return Ok(CancelableResult::Canceled(event));
        }
    };
    let (backbone_variables, simplified) = simplify(&cnfs, f);
    let count = count_formula_with_handler(f.and(&simplified), algorithm, f, handler)?;
    let factor = dont_care_factor(backbone_variables, &simplified, relevant_vars, f)?;
    Ok(count.map(|count| count * factor))
}

fn count_formula_with_handler(
    formula: EncodedFormula,
    algorithm: ModelCountAlgorithm,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<BigUint>> {
    match algorithm {
        ModelCountAlgorithm::Dnnf => Ok(compile_dnnf_with_handler(formula, f, handler)?
            .map(|dnnf| crate::knowledge_compilation::dnnf::count(&dnnf, f))),
        ModelCountAlgorithm::Bdd {
            node_size,
            cache_size,
        } => {
            let mut kernel = BddKernel::new_with_var_ordering(
                &force_ordering(formula, f)?,
                node_size,
                cache_size,
            )?;
            Ok(
                Bdd::from_formula_with_handler(formula, f, &mut kernel, handler)?
                    .map(|bdd| bdd.model_count(&mut kernel)),
            )
        }
    }
}

fn dont_care_factor(
    backbone_variables: BTreeSet<Variable>,
    simplified: &[EncodedFormula],
    relevant_vars: &BTreeSet<Variable>,
    f: &FormulaFactory,
) -> LngResult<BigUint> {
    let used_vars = simplified
        .iter()
        .fold(backbone_variables, |mut akk, formula| {
            akk.extend((*formula.variables(f)).clone());
            akk
        });
    let dont_care_vars = relevant_vars.difference(&used_vars).count();
    let dc_size = u32::try_from(dont_care_vars).map_err(|_| OperationError::MCTooManyDontCares)?;
    Ok(BigUint::from(2_usize).pow(dc_size))
}

fn encode_as_cnf_with_handler(
    formulas: &[EncodedFormula],
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<Vec<EncodedFormula>>> {
    let mut cnf_encoder = CnfEncoder::new(CnfAlgorithm::Advanced(
        AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin),
    ));
    let expanded = formulas
        .iter()
        .map(|&formula| pure_expansion(formula, f))
        .collect::<Result<Vec<_>, _>>()?;
    let mut transformed = Vec::with_capacity(expanded.len());
    for formula in expanded {
        match cnf_encoder.transform_with_handler(formula, f, handler)? {
            CancelableResult::Ok(cnf) => transformed.push(cnf),
            CancelableResult::Canceled(event) | CancelableResult::Partial(_, event) => {
                return Ok(CancelableResult::Canceled(event));
            }
        }
    }
    Ok(CancelableResult::Ok(transformed))
}

fn simplify(
    formulas: &[EncodedFormula],
    f: &FormulaFactory,
) -> (BTreeSet<Variable>, Vec<EncodedFormula>) {
    let mut simple_backbone = Assignment::from_literals(&[]);
    let mut backbone_variables = BTreeSet::new();
    for formula in formulas {
        if let Formula::Lit(lit) = formula.unpack(f) {
            simple_backbone.add_literal(lit);
            backbone_variables.insert(lit.variable());
        }
    }
    let mut simplified = Vec::new();
    for &formula in formulas {
        let restrict = f.restrict(formula, &simple_backbone);
        if !restrict.is_verum() {
            simplified.push(restrict);
        }
    }
    (backbone_variables, simplified)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use num_bigint::BigUint;

    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::handlers::{ComputationHandler, LngComputation, LngEvent, NopHandler};
    use crate::operations::functions::{
        ModelCountAlgorithm, count_models_conjunction_with_handler,
        count_models_conjunction_with_vars_with_handler, count_models_with_handler,
        count_models_with_vars_with_handler,
    };

    struct CancelComputation(LngComputation);

    impl ComputationHandler for CancelComputation {
        fn should_resume(&mut self, event: LngEvent) -> bool {
            !matches!(event, LngEvent::ComputationStarted(computation) if computation == self.0)
        }
    }

    #[test]
    fn test_handler_variants() {
        let f = FormulaFactory::new();
        let formula = "a | b".to_formula(&f);
        let formulas = ["a | b".to_formula(&f), "~a | b".to_formula(&f)];
        let relevant_vars = BTreeSet::from([f.var("a"), f.var("b"), f.var("c")]);

        assert_eq!(
            count_models_with_handler(formula, ModelCountAlgorithm::Dnnf, &f, &mut NopHandler)
                .unwrap()
                .result(),
            Some(BigUint::from(3_u8))
        );
        assert_eq!(
            count_models_with_vars_with_handler(
                formula,
                ModelCountAlgorithm::Dnnf,
                &relevant_vars,
                &f,
                &mut NopHandler,
            )
            .unwrap()
            .result(),
            Some(BigUint::from(6_u8))
        );
        assert_eq!(
            count_models_conjunction_with_handler(
                &formulas,
                ModelCountAlgorithm::Dnnf,
                &f,
                &mut NopHandler,
            )
            .unwrap()
            .result(),
            Some(BigUint::from(2_u8))
        );
        assert_eq!(
            count_models_conjunction_with_vars_with_handler(
                &formulas,
                ModelCountAlgorithm::Dnnf,
                &relevant_vars,
                &f,
                &mut NopHandler,
            )
            .unwrap()
            .result(),
            Some(BigUint::from(4_u8))
        );
    }

    #[test]
    fn test_handler_cancellation() {
        let f = FormulaFactory::new();
        let formula = "(a | b) & (~a | c) & (~b | ~c)".to_formula(&f);
        assert!(
            count_models_with_handler(
                formula,
                ModelCountAlgorithm::Dnnf,
                &f,
                &mut CancelComputation(LngComputation::Backbone),
            )
            .unwrap()
            .is_canceled()
        );

        let bdd_f = FormulaFactory::new();
        let bdd_formula = "a | b".to_formula(&bdd_f);
        assert!(
            count_models_with_handler(
                bdd_formula,
                ModelCountAlgorithm::Bdd {
                    node_size: 100,
                    cache_size: 100,
                },
                &bdd_f,
                &mut CancelComputation(LngComputation::Bdd),
            )
            .unwrap()
            .is_canceled()
        );
    }

    mod dnnf {
        use crate::formulas::FormulaFactory;
        use crate::operations::functions::{ModelCountAlgorithm, count_models};
        use crate::util::read_model_counting_examples::{read_cnf, read_normal};
        use num_bigint::BigUint;

        #[test]
        fn test_verum() {
            let f = FormulaFactory::new();
            let count = count_models(f.verum(), ModelCountAlgorithm::Dnnf, &f).unwrap();
            assert_eq!(count, BigUint::from(1_u64));
        }

        #[test]
        fn test_falsum() {
            let f = FormulaFactory::new();
            let count = count_models(f.falsum(), ModelCountAlgorithm::Dnnf, &f).unwrap();
            assert_eq!(count, BigUint::from(0_u64));
        }

        #[test]
        fn test_normal_formulas() {
            let f = FormulaFactory::new();
            let tests = read_normal(&f);
            for (formula, expected) in tests {
                let count = count_models(formula, ModelCountAlgorithm::Dnnf, &f).unwrap();
                assert_eq!(count, expected);
            }
        }

        #[test]
        fn test_cnf_formulas() {
            let f = FormulaFactory::new();
            let tests = read_cnf(&f);
            for (formula, expected) in tests {
                let count = count_models(formula, ModelCountAlgorithm::Dnnf, &f).unwrap();
                assert_eq!(count, expected);
            }
        }
    }

    mod bdd {
        use crate::formulas::FormulaFactory;
        use crate::operations::functions::{ModelCountAlgorithm, count_models};
        use crate::util::read_model_counting_examples::{read_cnf, read_normal};
        use num_bigint::BigUint;

        #[test]
        fn test_verum() {
            let f = FormulaFactory::new();
            let count = count_models(
                f.verum(),
                ModelCountAlgorithm::Bdd {
                    node_size: 1000,
                    cache_size: 1000,
                },
                &f,
            )
            .unwrap();
            assert_eq!(count, BigUint::from(1_u64));
        }

        #[test]
        fn test_falsum() {
            let f = FormulaFactory::new();
            let count = count_models(
                f.falsum(),
                ModelCountAlgorithm::Bdd {
                    node_size: 1000,
                    cache_size: 1000,
                },
                &f,
            )
            .unwrap();
            assert_eq!(count, BigUint::from(0_u64));
        }

        #[test]
        fn test_normal_formulas() {
            let f = FormulaFactory::new();
            let tests = read_normal(&f);
            for (formula, expected) in tests {
                let count = count_models(
                    formula,
                    ModelCountAlgorithm::Bdd {
                        node_size: 1000,
                        cache_size: 1000,
                    },
                    &f,
                )
                .unwrap();
                assert_eq!(count, expected);
            }
        }

        #[test]
        fn test_cnf_formulas() {
            let f = FormulaFactory::new();
            let tests = read_cnf(&f);
            for (formula, expected) in tests {
                let count = count_models(
                    formula,
                    ModelCountAlgorithm::Bdd {
                        node_size: 1000,
                        cache_size: 1000,
                    },
                    &f,
                )
                .unwrap();
                assert_eq!(count, expected);
            }
        }
    }
}

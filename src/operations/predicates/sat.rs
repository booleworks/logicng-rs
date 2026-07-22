use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::handlers::{CancelableResult, ComputationHandler, NopHandler};
use crate::solver::lng_core_solver::{CnfMethod, SatSolver, SatSolverConfig};

/// A predicate tests whether a formula is satisfiable. A formula is satisfiable
/// if there exists at least one assignment such that the formula evaluates to
/// `true` with this assignment. Such an assignment is called *satisfying
/// assignment* or *model*. For example `A & B | C` is satisfiable for the
/// assignment `{A, B, ~C}`. In order to check for satisfiability, the
/// predicate internally calls a SAT solver.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_sat;
/// let f = FormulaFactory::new();
///
/// let formula = "a & b | c".to_formula(&f);
///
/// assert!(is_sat(formula, &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the formula cannot be added to the SAT solver, for
/// example because CNF conversion fails.
pub fn is_sat(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<bool> {
    Ok(is_sat_with_handler(formula, f, &mut NopHandler::new())?
        .result()
        .expect("nop handler can never abort"))
}

/// Tests whether a formula is satisfiable using a cancelable computation handler.
pub fn is_sat_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<bool>> {
    match f.caches.sat.get(formula) {
        Some(c) => Ok(CancelableResult::Ok(c)),
        None => {
            let mut solver = SatSolver::<()>::from_config(
                SatSolverConfig::default().cnf_method(CnfMethod::FactoryCnf),
            );
            solver.add_formula(formula, f)?;
            let result = solver.sat_call().handler(handler).sat(f)?;
            if f.config.caches.sat && result.is_success() {
                f.caches.sat.insert(formula, *result.result_ref().unwrap());
            }
            Ok(result)
        }
    }
}

/// A predicate indicating whether a given formula is a tautology, that is,
/// always holds, regardless of the assignment. An example for a tautology is
/// `(A & B) | (~A & B) | (A & ~B) | (~A & ~B)`.
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_tautology;
/// let f = FormulaFactory::new();
///
/// let formula = "(a & b) | (~a & b) | (a & ~b) | (~a & ~b)".to_formula(&f);
///
/// assert!(is_tautology(formula, &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the negated formula cannot be added to the SAT solver,
/// for example because CNF conversion fails.
pub fn is_tautology(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<bool> {
    Ok(
        is_tautology_with_handler(formula, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Tests whether a formula is a tautology using a cancelable computation handler.
pub fn is_tautology_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<bool>> {
    let negated_formula = f.negate(formula);
    match f.caches.sat.get(negated_formula) {
        Some(c) => Ok(CancelableResult::Ok(!c)),
        None => {
            let mut solver = SatSolver::<()>::from_config(
                SatSolverConfig::default().cnf_method(CnfMethod::FactoryCnf),
            );
            solver.add_formula(negated_formula, f)?;
            let result = solver.sat_call().handler(handler).sat(f)?.map(|sat| !sat);
            if f.config.caches.sat && result.is_success() {
                f.caches
                    .sat
                    .insert(negated_formula, !*result.result_ref().unwrap());
            }
            Ok(result)
        }
    }
}

/// Tests whether a formula is a contradiction, i.e. it evaluates to `false`
/// for every assignment.
///
/// # Example
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_contradiction;
/// let f = FormulaFactory::new();
///
/// assert!(is_contradiction("a & b & (a => ~b)".to_formula(&f), &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the formula cannot be added to the SAT solver, for
/// example because CNF conversion fails.
pub fn is_contradiction(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<bool> {
    Ok(
        is_contradiction_with_handler(formula, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Tests whether a formula is a contradiction using a cancelable computation handler.
pub fn is_contradiction_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<bool>> {
    Ok(is_sat_with_handler(formula, f, handler)?.map(|sat| !sat))
}

/// Tests whether a formula is contingent, i.e. it is satisfiable but not a
/// tautology.
///
/// # Example
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_contingency;
/// let f = FormulaFactory::new();
///
/// assert!(is_contingency("a & b".to_formula(&f), &f).unwrap());
/// assert!(!is_contingency("a | ~a".to_formula(&f), &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the formula or its negation cannot be added to the SAT
/// solver, for example because CNF conversion fails.
pub fn is_contingency(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<bool> {
    Ok(
        is_contingency_with_handler(formula, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Tests whether a formula is contingent using a cancelable computation handler.
pub fn is_contingency_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<bool>> {
    match is_sat_with_handler(formula, f, handler)? {
        CancelableResult::Ok(false) => Ok(CancelableResult::Ok(false)),
        CancelableResult::Ok(true) => {
            Ok(is_tautology_with_handler(formula, f, handler)?.map(|tautology| !tautology))
        }
        CancelableResult::Canceled(event) => Ok(CancelableResult::Canceled(event)),
        CancelableResult::Partial(_, event) => Ok(CancelableResult::Canceled(event)),
    }
}

/// Tests whether two formulas are semantically equivalent, i.e. they have the
/// same truth value for every assignment.
///
/// # Example
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::are_equivalent;
/// let f = FormulaFactory::new();
///
/// let first = "a => b".to_formula(&f);
/// let second = "~a | b".to_formula(&f);
/// assert!(are_equivalent(first, second, &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the equivalence cannot be added to the SAT solver, for
/// example because CNF conversion fails.
pub fn are_equivalent(
    first: EncodedFormula,
    second: EncodedFormula,
    f: &FormulaFactory,
) -> LngResult<bool> {
    Ok(
        are_equivalent_with_handler(first, second, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Tests whether two formulas are semantically equivalent using a cancelable computation handler.
pub fn are_equivalent_with_handler(
    first: EncodedFormula,
    second: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<bool>> {
    is_tautology_with_handler(f.equivalence(first, second), f, handler)
}

/// Tests whether the first formula implies the second formula, i.e. every
/// satisfying assignment of the first formula also satisfies the second one.
///
/// # Example
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::implies;
/// let f = FormulaFactory::new();
///
/// let first = "a & b".to_formula(&f);
/// let second = "a".to_formula(&f);
/// assert!(implies(first, second, &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the implication cannot be added to the SAT solver, for
/// example because CNF conversion fails.
pub fn implies(
    first: EncodedFormula,
    second: EncodedFormula,
    f: &FormulaFactory,
) -> LngResult<bool> {
    Ok(
        implies_with_handler(first, second, f, &mut NopHandler::new())?
            .result()
            .expect("nop handler can never abort"),
    )
}

/// Tests whether the first formula implies the second formula using a cancelable computation handler.
pub fn implies_with_handler(
    first: EncodedFormula,
    second: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<bool>> {
    is_tautology_with_handler(f.implication(first, second), f, handler)
}

#[cfg(test)]
mod tests {
    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::handlers::{ComputationHandler, LngComputation, LngEvent, NopHandler};

    use super::*;

    struct CancelSatStart;

    impl ComputationHandler for CancelSatStart {
        fn should_resume(&mut self, event: LngEvent) -> bool {
            !matches!(event, LngEvent::ComputationStarted(LngComputation::Sat))
        }
    }

    struct CancelSecondSatStart(usize);

    impl ComputationHandler for CancelSecondSatStart {
        fn should_resume(&mut self, event: LngEvent) -> bool {
            if matches!(event, LngEvent::ComputationStarted(LngComputation::Sat)) {
                self.0 += 1;
            }
            self.0 < 2
        }
    }

    #[test]
    fn handler_predicates_complete_normally() {
        let f = FormulaFactory::new();
        let mut handler = NopHandler::new();
        assert_eq!(
            is_sat_with_handler("a & b".to_formula(&f), &f, &mut handler)
                .unwrap()
                .result(),
            Some(true)
        );
        assert_eq!(
            is_tautology_with_handler("a | ~a".to_formula(&f), &f, &mut handler)
                .unwrap()
                .result(),
            Some(true)
        );
    }

    #[test]
    fn handler_predicates_can_be_canceled() {
        let f = FormulaFactory::new();
        assert!(
            is_sat_with_handler("a & b".to_formula(&f), &f, &mut CancelSatStart)
                .unwrap()
                .is_canceled()
        );
        assert!(
            is_tautology_with_handler("a | b".to_formula(&f), &f, &mut CancelSatStart)
                .unwrap()
                .is_canceled()
        );
    }

    #[test]
    fn canceled_results_are_not_cached() {
        let f = FormulaFactory::new();
        let formula = "a & b".to_formula(&f);
        assert!(
            is_sat_with_handler(formula, &f, &mut CancelSatStart)
                .unwrap()
                .is_canceled()
        );
        assert_eq!(
            is_sat_with_handler(formula, &f, &mut NopHandler::new())
                .unwrap()
                .result(),
            Some(true)
        );
    }

    #[test]
    fn contradiction_predicate() {
        let f = FormulaFactory::new();
        let contradiction = "a & ~a".to_formula(&f);
        let contingent = "a & b".to_formula(&f);

        assert!(is_contradiction(contradiction, &f).unwrap());
        assert!(!is_contradiction(contingent, &f).unwrap());
        let mut handler = NopHandler::new();
        assert_eq!(
            is_contradiction_with_handler(contradiction, &f, &mut handler)
                .unwrap()
                .result(),
            Some(true)
        );
        let uncached_f = FormulaFactory::new();
        assert!(
            is_contradiction_with_handler(
                "x & y".to_formula(&uncached_f),
                &uncached_f,
                &mut CancelSatStart,
            )
            .unwrap()
            .is_canceled()
        );
    }

    #[test]
    fn contingency_predicate() {
        let f = FormulaFactory::new();
        let contradiction = "a & ~a".to_formula(&f);
        let tautology = "a | ~a".to_formula(&f);
        let contingent = "a & b".to_formula(&f);

        assert!(is_contingency(contingent, &f).unwrap());
        assert!(!is_contingency(contradiction, &f).unwrap());
        assert!(!is_contingency(tautology, &f).unwrap());

        let handler_f = FormulaFactory::new();
        assert_eq!(
            is_contingency_with_handler(
                "x & y".to_formula(&handler_f),
                &handler_f,
                &mut NopHandler::new(),
            )
            .unwrap()
            .result(),
            Some(true)
        );
        let canceled_f = FormulaFactory::new();
        assert!(
            is_contingency_with_handler(
                "x & y".to_formula(&canceled_f),
                &canceled_f,
                &mut CancelSatStart,
            )
            .unwrap()
            .is_canceled()
        );
        let second_call_f = FormulaFactory::new();
        assert!(
            is_contingency_with_handler(
                "x & y".to_formula(&second_call_f),
                &second_call_f,
                &mut CancelSecondSatStart(0),
            )
            .unwrap()
            .is_canceled()
        );
    }

    #[test]
    fn equivalence_predicate() {
        let f = FormulaFactory::new();
        assert!(are_equivalent("a => b".to_formula(&f), "~a | b".to_formula(&f), &f).unwrap());
        assert!(!are_equivalent("a".to_formula(&f), "b".to_formula(&f), &f).unwrap());

        let handler_f = FormulaFactory::new();
        assert_eq!(
            are_equivalent_with_handler(
                "x => y".to_formula(&handler_f),
                "~x | y".to_formula(&handler_f),
                &handler_f,
                &mut NopHandler::new(),
            )
            .unwrap()
            .result(),
            Some(true)
        );
        let canceled_f = FormulaFactory::new();
        assert!(
            are_equivalent_with_handler(
                "x".to_formula(&canceled_f),
                "y".to_formula(&canceled_f),
                &canceled_f,
                &mut CancelSatStart,
            )
            .unwrap()
            .is_canceled()
        );
    }

    #[test]
    fn implication_predicate() {
        let f = FormulaFactory::new();
        assert!(implies("a & b".to_formula(&f), "a".to_formula(&f), &f).unwrap());
        assert!(!implies("a".to_formula(&f), "b".to_formula(&f), &f).unwrap());

        let handler_f = FormulaFactory::new();
        assert_eq!(
            implies_with_handler(
                "x & y".to_formula(&handler_f),
                "x".to_formula(&handler_f),
                &handler_f,
                &mut NopHandler::new(),
            )
            .unwrap()
            .result(),
            Some(true)
        );
        let canceled_f = FormulaFactory::new();
        assert!(
            implies_with_handler(
                "x".to_formula(&canceled_f),
                "y".to_formula(&canceled_f),
                &canceled_f,
                &mut CancelSatStart,
            )
            .unwrap()
            .is_canceled()
        );
    }
}

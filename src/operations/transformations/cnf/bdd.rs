use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::handlers::{CancelableResult, ComputationHandler, NopHandler};
use crate::knowledge_compilation::bdd::{Bdd, BddKernel};

/// Transforms a formula into _CNF_ by compiling it to a BDD first.
///
/// This convenience function uses a no-op handler and therefore either returns
/// a complete _CNF_ formula or an error.
///
/// # Example
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::transformations::bdd_cnf;
///
/// let f = FormulaFactory::new();
/// let formula = "(a | b) & ~(c & d)".to_formula(&f);
/// let cnf = bdd_cnf(formula, &f)?;
///
/// assert!(cnf.is_cnf(&f));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Errors
///
/// Returns an error if BDD construction or the extraction of the _CNF_ formula
/// from the BDD fails.
pub fn bdd_cnf(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<EncodedFormula> {
    let cnf = bdd_cnf_with_handler(formula, f, &mut NopHandler::new())?;
    Ok(cnf.result().expect("nop handler can never abort"))
}

/// Transforms a formula into _CNF_ by compiling it to a BDD first, reporting
/// BDD construction events to the given handler.
///
/// If the handler cancels the computation, the result is
/// [`CancelableResult::Canceled`] with the event that caused the cancellation.
///
/// # Example
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::handlers::CancelableResult;
/// use logicng::knowledge_compilation::bdd::NumberOfNodesBddHandler;
/// use logicng::operations::transformations::bdd_cnf_with_handler;
///
/// let f = FormulaFactory::new();
/// let formula = "(a | b) & ~(c & d)".to_formula(&f);
/// let mut handler = NumberOfNodesBddHandler::new(1_000);
/// let cnf = bdd_cnf_with_handler(formula, &f, &mut handler)?;
///
/// assert!(matches!(cnf, CancelableResult::Ok(result) if result.is_cnf(&f)));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Errors
///
/// Returns an error if BDD construction or the extraction of the _CNF_ formula
/// from the BDD fails. Handler cancellation is returned as a
/// [`CancelableResult::Canceled`] value, not as an error.
pub fn bdd_cnf_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<EncodedFormula>> {
    let mut kernel = BddKernel::new_with_num_vars(formula.variables(f).len(), 10_000, 10_000)?;
    let bdd = Bdd::from_formula_with_handler(formula, f, &mut kernel, handler)?;
    match bdd {
        CancelableResult::Ok(b) => Ok(CancelableResult::Ok(b.cnf(f, &mut kernel)?)),
        CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
            Ok(CancelableResult::Canceled(e))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};
    use crate::operations::predicates;

    use super::bdd_cnf;

    #[test]
    fn test_bdd_cnf_for_atomic_formulas() {
        let f = &FormulaFactory::new();

        test_bdd_cnf("$true".to_formula(f), f);
        test_bdd_cnf("$false".to_formula(f), f);
        test_bdd_cnf("a".to_formula(f), f);
        test_bdd_cnf("~a".to_formula(f), f);
    }

    #[test]
    fn test_bdd_cnf_for_compound_formula() {
        let f = &FormulaFactory::new();
        let formula = "(a | b) & (c => d) & ~(x & y)".to_formula(f);

        test_bdd_cnf(formula, f);
    }

    fn test_bdd_cnf(formula: EncodedFormula, f: &FormulaFactory) {
        let cnf = bdd_cnf(formula, f).unwrap();
        assert!(cnf.is_cnf(f));
        assert!(predicates::is_tautology(f.equivalence(formula, cnf), f).unwrap());
    }
}

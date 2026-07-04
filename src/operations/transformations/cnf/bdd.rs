use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::handlers::{CancelableResult, ComputationHandler, NopHandler};
use crate::knowledge_compilation::bdd::{Bdd, BddKernel};

pub fn bdd_cnf(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<EncodedFormula> {
    let cnf = bdd_cnf_with_handler(formula, f, &mut NopHandler::new())?;
    Ok(cnf.result().expect("nop handler can never abort"))
}

pub fn bdd_cnf_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<CancelableResult<EncodedFormula>> {
    let mut kernel = BddKernel::new_with_num_vars(formula.variables(f).len(), 10_000, 10_000)?;
    let bdd = Bdd::from_formula_with_handler(formula, f, &mut kernel, handler)?;
    match bdd {
        CancelableResult::Ok(b) => Ok(CancelableResult::Ok(b.cnf(f, &mut kernel)?)),
        CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => Ok(CancelableResult::Canceled(e)),
    }
}

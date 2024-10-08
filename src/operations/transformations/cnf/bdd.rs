use crate::{
    formulas::{EncodedFormula, FormulaFactory},
    handlers::{ComputationHandler, LngResult, NopHandler},
    knowledge_compilation::bdd::{Bdd, BddKernel},
};

pub fn bdd_cnf(formula: EncodedFormula, f: &FormulaFactory) -> EncodedFormula {
    bdd_cnf_with_handler(formula, f, &mut NopHandler::new()).result().expect("Nop Handler does not abort")
}

pub fn bdd_cnf_with_handler(
    formula: EncodedFormula,
    f: &FormulaFactory,
    handler: &mut dyn ComputationHandler,
) -> LngResult<EncodedFormula> {
    let mut kernel = BddKernel::new_with_num_vars(formula.variables(f).len(), 10_000, 10_000);
    Bdd::from_formula_with_handler(formula, f, &mut kernel, handler).map(|bdd| bdd.cnf(f, &mut kernel))
}

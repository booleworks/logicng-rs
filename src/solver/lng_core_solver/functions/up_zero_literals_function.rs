use std::collections::BTreeSet;

use crate::{
    formulas::{FormulaFactory, Literal},
    solver::lng_core_solver::{sign, var, SatSolver},
};

pub fn up_zero_literals<B: Clone>(solver: &mut SatSolver<B>, f: &FormulaFactory) -> BTreeSet<Literal> {
    if solver.sat(f) {
        let literals = solver.underlying_solver().up_zero_literals();
        literals.into_iter().map(|lit| Literal::new(solver.underlying_solver().variable_for_idx(var(lit), f), !sign(lit))).collect()
    } else {
        BTreeSet::new()
    }
}

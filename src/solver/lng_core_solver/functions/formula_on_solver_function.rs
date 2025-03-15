use std::collections::BTreeSet;

use crate::{
    formulas::{CType, EncodedFormula, FormulaFactory, Literal, Variable},
    solver::lng_core_solver::{sign, var, LngVar, SatSolver, Tristate},
};

pub fn formula_on_solver<B>(solver: &mut SatSolver<B>, f: &FormulaFactory) -> BTreeSet<EncodedFormula> {
    let mut formulas = BTreeSet::new();
    for i in 0..solver.underlying_solver().clauses().len() {
        let c_ref = solver.underlying_solver().clauses[i];
        let lit_idxs = solver.underlying_solver().c(c_ref).data.clone();
        let lits = lit_idxs
            .into_iter()
            .map(|l| Literal::new(solver.underlying_solver().variable_for_idx(var(l), f), !sign(l)))
            .collect::<Vec<_>>();
        if solver.underlying_solver().c(c_ref).is_at_most {
            let rhs = solver.underlying_solver().c(c_ref).len() + 1 - solver.underlying_solver().c(c_ref).at_most_watchers.unwrap_or(0);
            let vars = lits.iter().map(|&l| l.variable()).collect::<Box<[Variable]>>();
            formulas.insert(f.cc(CType::LE, rhs.try_into().expect("rhs too large"), vars));
        } else {
            formulas.insert(f.clause(&lits));
        }
    }
    for i in 0..solver.underlying_solver().vars.len() {
        let var = &solver.underlying_solver().vars[i];

        if var.level.is_some_and(|lvl| lvl == 0) {
            let phase = var.assignment == Tristate::True;
            let lit = Literal::new(solver.underlying_solver().variable_for_idx(LngVar(i), f), phase);
            formulas.insert(lit.into());
        }
    }
    if !solver.underlying_solver().ok() {
        formulas.insert(f.falsum());
    }
    formulas
}

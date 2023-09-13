use std::ops::Deref;
use std::sync::Arc;

use crate::formulas::{EncodedFormula, FormulaFactory, Literal};
use crate::solver::minisat::sat::Tristate::True;
use crate::solver::minisat::sat::{sign, var, MsVar};
use crate::solver::minisat::MiniSat;

impl MiniSat {
    /// Returns the current formula on the solver.
    ///
    /// Note that this formula is usually syntactically different from the
    /// formulas which were actually added to the solver, since the formulas are
    /// added as CNF and may be simplified or even removed, depending on the
    /// state of the solver. Furthermore, the solver might add learnt clauses or
    /// propagate literals. This can be useful to debug or analyze a solver at a
    /// given time.
    pub fn formula_on_solver(&self, f: &FormulaFactory) -> Arc<[EncodedFormula]> {
        let mut formulas = Vec::new();
        for clause_ref in &self.underlying_solver.clauses {
            let lits: Vec<Literal> = clause_ref
                .borrow()
                .deref()
                .data
                .iter()
                .map(|&lit| Literal::new(self.underlying_solver.variable_for_idx(var(lit)).unwrap(), !sign(lit)))
                .collect();
            formulas.push(f.clause(&lits));
        }
        self.underlying_solver
            .vars
            .iter()
            .enumerate()
            .filter(|(_, var)| var.level == Some(0))
            .map(|(i, var)| Literal::new(self.underlying_solver.variable_for_idx(MsVar(i)).unwrap(), var.assignment == True))
            .for_each(|lit| formulas.push(lit.into()));
        if !self.underlying_solver.ok {
            formulas.push(f.falsum());
        }
        formulas.into()
    }
}

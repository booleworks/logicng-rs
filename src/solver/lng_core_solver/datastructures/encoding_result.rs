use crate::{
    datastructures::{EncodingResult, SolverExportLiteral},
    formulas::Literal,
    propositions::Proposition,
    solver::lng_core_solver::{self, SatSolver},
};

use super::LngLit;

pub struct EncodingResultSatSolver<'s, B> {
    pub solver: &'s mut SatSolver<B>,
    proposition: Option<Proposition<B>>,
}

impl<'s, B> EncodingResultSatSolver<'s, B> {
    pub fn new(solver: &'s mut SatSolver<B>, proposition: Option<Proposition<B>>) -> Self {
        Self { solver, proposition }
    }

    fn add_literal(&mut self, lit: Literal) -> LngLit {
        let index = self.solver.underlying_solver().idx_for_variable(lit.variable());
        let var = index.unwrap_or_else(|| {
            let initial_phase = self.solver.config().initial_phase;
            let v = self.solver.underlying_solver().new_var(!initial_phase, true);
            self.solver.underlying_solver().add_variable(lit.variable(), v);
            v
        });
        lng_core_solver::mk_lit(var, !lit.phase())
    }
}

impl<B: Clone> EncodingResult for EncodingResultSatSolver<'_, B> {
    fn new_auxiliary_variable(&mut self, _aux_type: &str) -> SolverExportLiteral {
        let initial_phase = self.solver.config().initial_phase;
        let var = self.solver.underlying_solver().new_var(!initial_phase, true);
        let lit = lng_core_solver::mk_lit(var, false);
        //let name = format!("@AUX_{aux_type}_SAT_SOLVER_{}", index.0);
        // todo!("register auxiliary variables in solver");
        SolverExportLiteral::Solver(lit)
    }

    fn add_clause_literals(&mut self, lits: &[Literal]) {
        let mut exported_lits = Vec::with_capacity(lits.len());
        for &lit in lits {
            exported_lits.push(self.add_literal(lit));
        }
        self.solver.underlying_solver().add_clause(exported_lits, self.proposition.clone());
    }

    fn add_clause(&mut self, lits: &[SolverExportLiteral]) {
        let exported_lits = lits
            .iter()
            .map(|&lit| match lit {
                SolverExportLiteral::FF(literal) => self.add_literal(literal),
                SolverExportLiteral::Solver(lng_lit) => lng_lit,
            })
            .collect();
        self.solver.underlying_solver().add_clause(exported_lits, self.proposition.clone());
    }
}

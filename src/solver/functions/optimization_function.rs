use crate::datastructures::Model;
use crate::formulas::CType::GE;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::solver::minisat::sat::MsVar;
use crate::solver::minisat::sat::Tristate::{False, True};
use crate::solver::minisat::MiniSat;
use std::collections::{BTreeMap, BTreeSet};
use std::slice::Iter;

const SEL_PREFIX: &str = "@SEL_OPT";

/// This function can be used to compute a minimal or maximal model in the
/// number of positive assigned literals. I.e. when minimizing over a set of
/// variables you can compute a model with a globally minimal number of positive
/// assigned literals.
pub struct OptimizationFunction {
    literals: Vec<Literal>,
    result_model_variables: BTreeSet<Variable>,
    maximize: bool,
}

impl OptimizationFunction {
    /// Returns an optimization function which maximizes the given set of literals.
    pub fn maximize(literals: Vec<Literal>) -> Self {
        let result_model_variables = literals.iter().map(Literal::variable).collect();
        Self { literals, result_model_variables, maximize: true }
    }

    /// Returns an optimization function which minimizes the given set of literals.
    pub fn minimize(literals: Vec<Literal>) -> Self {
        let result_model_variables = literals.iter().map(Literal::variable).collect();
        Self { literals, result_model_variables, maximize: false }
    }

    /// Extends the function with additional variables.
    #[must_use]
    pub fn additional_variables(mut self, additional_variables: Iter<Variable>) -> Self {
        self.result_model_variables.extend(additional_variables);
        self
    }

    pub(crate) fn optimize(&self, solver: &mut MiniSat, f: &FormulaFactory) -> Option<Model> {
        let solver_state = if solver.config.incremental { Some(solver.save_state()) } else { None };
        let model = self.compute(solver, f);
        if let Some(state) = solver_state {
            solver.load_state(&state);
        };
        model
    }

    fn compute(&self, solver: &mut MiniSat, f: &FormulaFactory) -> Option<Model> {
        let selector_map: BTreeMap<Variable, Literal> =
            self.literals.iter().enumerate().map(|(i, &l)| (f.var(&format!("{SEL_PREFIX}{i}")), l)).collect();
        if self.maximize {
            selector_map
                .iter()
                .for_each(|(sel_var, lit)| solver.add(f.or(&[EncodedFormula::from(sel_var.negate()), EncodedFormula::from(*lit)]), f));
            selector_map
                .iter()
                .for_each(|(sel_var, lit)| solver.add(f.or(&[EncodedFormula::from(lit.negate()), EncodedFormula::from(*sel_var)]), f));
        } else {
            for (sel_var, lit) in &selector_map {
                solver.add(f.or(&[EncodedFormula::from(sel_var.negate()), EncodedFormula::from(lit.negate())]), f);
            }
            selector_map
                .iter()
                .for_each(|(sel_var, lit)| solver.add(f.or(&[EncodedFormula::from(*lit), EncodedFormula::from(*sel_var)]), f));
        }
        if solver.sat() != True {
            return None;
        }
        let selectors: Box<[Variable]> = selector_map.keys().copied().collect();
        let mut internal_model = solver.underlying_solver.model.clone();
        let mut current_model = solver.model(Some(&selectors)).unwrap();
        let mut current_bound = current_model.pos().len();
        if current_bound == 0 {
            solver.add(f.cc(GE, 1, selectors.clone()), f);
            if solver.sat() == False {
                return Some(self.mk_result_model(&internal_model, solver));
            }
            internal_model = solver.underlying_solver.model.clone();
            current_model = solver.model(Some(&selectors)).unwrap();
            current_bound = current_model.pos().len();
        } else if current_bound == selectors.len() {
            return Some(self.mk_result_model(&internal_model, solver));
        }
        let cc = f.cc(GE, current_bound as u64 + 1, selectors.clone()).as_cc(f).unwrap();
        let mut incremental_data = solver.add_incremental_cc(&cc, f);
        while solver.sat() == True {
            internal_model = solver.underlying_solver.model.clone();
            current_model = solver.model(Some(&selectors)).unwrap();
            current_bound = current_model.pos().len();
            if current_bound == selectors.len() {
                return Some(self.mk_result_model(&internal_model, solver));
            }
            incremental_data.as_mut().unwrap().new_lower_bound_for_solver(solver, f, current_bound as u64 + 1);
        }
        Some(self.mk_result_model(&internal_model, solver))
    }

    fn mk_result_model(&self, internal_model: &Vec<bool>, solver: &MiniSat) -> Model {
        let relevant_indices: Vec<MsVar> =
            self.result_model_variables.iter().filter_map(|&v| solver.underlying_solver.idx_for_variable(v)).collect();
        solver.create_assignment(internal_model, &Some(relevant_indices))
    }
}

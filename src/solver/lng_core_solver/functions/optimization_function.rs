use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use itertools::Itertools;

use crate::solver::lng_core_solver::{EncodingResultSatSolver, SatSolver};
use crate::{
    datastructures::Model,
    formulas::{CType, EncodedFormula, FormulaFactory, Literal, Variable},
    handlers::{ComputationHandler, LngComputation, LngEvent, LngResult},
};

const SEL_PREFIX: &str = "@SEL_OPT";

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
    pub fn additional_variables(mut self, additional_variables: impl IntoIterator<Item = Variable>) -> Self {
        self.result_model_variables.extend(additional_variables);
        self
    }

    pub fn optimize<B: Clone>(
        &self,
        solver: &mut SatSolver<B>,
        handler: &mut dyn ComputationHandler,
        f: &FormulaFactory,
    ) -> LngResult<Rc<Model>> {
        let initial_state = solver.save_state();
        let model = self.compute(solver, handler, f);
        solver.load_state(&initial_state);
        model
    }

    fn compute<B: Clone>(
        &self,
        solver: &mut SatSolver<B>,
        handler: &mut dyn ComputationHandler,
        f: &FormulaFactory,
    ) -> LngResult<Rc<Model>> {
        if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Optimization)) {
            return LngResult::Canceled(LngEvent::ComputationStarted(LngComputation::Optimization));
        }
        let result_model_variables_vec = self.result_model_variables.iter().copied().collect_vec();
        let selector_map: BTreeMap<Variable, Literal> =
            self.literals.iter().enumerate().map(|(i, &l)| (f.var(format!("{SEL_PREFIX}{i}")), l)).collect();
        let selectors = selector_map.keys().copied().collect_vec();
        if self.maximize {
            for (sel_var, lit) in &selector_map {
                solver.add_formula(f.or([EncodedFormula::from(sel_var.negate()), EncodedFormula::from(*lit)]), f);
            }
            for (sel_var, lit) in &selector_map {
                solver.add_formula(f.or([EncodedFormula::from(lit.negate()), EncodedFormula::from(*sel_var)]), f);
            }
        } else {
            for (sel_var, lit) in &selector_map {
                solver.add_formula(f.or([EncodedFormula::from(sel_var.negate()), EncodedFormula::from(lit.negate())]), f);
            }
            selector_map
                .iter()
                .for_each(|(sel_var, lit)| solver.add_formula(f.or([EncodedFormula::from(*lit), EncodedFormula::from(*sel_var)]), f));
        }

        let mut sat_call = solver.sat_call().handler(handler).solve(f);
        match sat_call.get_sat_result() {
            LngResult::Canceled(lng_event) | LngResult::Partial(_, lng_event) => return LngResult::Canceled(lng_event),
            LngResult::Ok(res) => {
                assert!(res, "The given formula must be satisfiable");
            }
        }
        let mut last_result_model = Rc::new(sat_call.model(&result_model_variables_vec, f).expect("formula is sat"));
        let mut current_selector_model = sat_call.model(&selectors, f).expect("formula is sat");
        if current_selector_model.pos().len() == selector_map.len() {
            // all optimization literals satisfied -- no need for further
            // optimization
            return LngResult::Ok(Rc::new(sat_call.model(&result_model_variables_vec, f).expect("formula is sat")));
        }
        drop(sat_call);

        let mut current_bound = current_selector_model.pos().len();
        if current_bound == 0 {
            solver.add_formula(f.cc(CType::GE, 1, selectors.clone()), f);
            let mut sat_call = solver.sat_call().handler(handler).solve(f);
            let sat_result = sat_call.get_sat_result();
            match sat_result {
                LngResult::Canceled(lng_event) | LngResult::Partial(_, lng_event) => {
                    return LngResult::Partial(last_result_model, lng_event)
                }
                LngResult::Ok(res) => {
                    if !res {
                        return LngResult::Ok(last_result_model);
                    }
                    last_result_model = Rc::new(sat_call.model(&result_model_variables_vec, f).expect("formula is sat"));
                    current_selector_model = sat_call.model(&selectors, f).expect("formula is sat");
                    current_bound = current_selector_model.pos().len();
                }
            }
        }
        let cc = f.cc(CType::GE, u32::try_from(current_bound).expect("rhs of cc too large") + 1, selectors.clone()).as_cc(f).unwrap();
        let mut incremental_data = solver.add_incremental_cc(cc);
        loop {
            let (mut sat_call, handler) = solver.sat_call().handler(handler).solve_and_get_handler(f);
            let handler = handler.unwrap();
            let sat_result = sat_call.get_sat_result();
            match sat_result {
                LngResult::Canceled(lng_event) | LngResult::Partial(_, lng_event) => {
                    return LngResult::Partial(last_result_model, lng_event)
                }
                LngResult::Ok(res) => {
                    if !res {
                        return LngResult::Ok(last_result_model);
                    }
                    last_result_model = Rc::new(sat_call.model(&result_model_variables_vec, f).expect("formula is sat"));
                    let better_bound_event = LngEvent::OptimizationFoundBetterBound(Rc::clone(&last_result_model));
                    if !handler.should_resume(better_bound_event.clone()) {
                        return LngResult::Partial(last_result_model, better_bound_event);
                    }
                    current_selector_model = sat_call.model(&selectors, f).expect("formula is sat");
                    current_bound = current_selector_model.pos().len();
                    if current_bound == selectors.len() {
                        return LngResult::Ok(last_result_model);
                    }
                }
            }
            drop(sat_call);
            let mut result = EncodingResultSatSolver::new(solver, None);
            incremental_data.as_mut().unwrap().new_lower_bound(&mut result, u32::try_from(current_bound).expect("rhs of cc too large") + 1);
        }
    }
}

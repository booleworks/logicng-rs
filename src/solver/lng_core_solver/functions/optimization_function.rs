use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use itertools::Itertools;

use crate::solver::lng_core_solver::SatSolver;
use crate::{
    datastructures::Model,
    errors::LngResult,
    formulas::{CType, EncodedFormula, FormulaFactory, Literal, Variable},
    handlers::{CancelableResult, ComputationHandler, LngComputation, LngEvent},
};

const SEL_PREFIX: &str = "@SEL_OPT";

/// Configures whether a model optimization minimizes or maximizes its target literals.
pub struct OptimizationFunction {
    literals: Vec<Literal>,
    result_model_variables: BTreeSet<Variable>,
    maximize: bool,
}

impl OptimizationFunction {
    /// Returns an optimization function which maximizes the given set of literals.
    pub fn maximize(literals: Vec<Literal>) -> Self {
        let result_model_variables = literals.iter().map(Literal::variable).collect();
        Self {
            literals,
            result_model_variables,
            maximize: true,
        }
    }

    /// Returns an optimization function which minimizes the given set of literals.
    pub fn minimize(literals: Vec<Literal>) -> Self {
        let result_model_variables = literals.iter().map(Literal::variable).collect();
        Self {
            literals,
            result_model_variables,
            maximize: false,
        }
    }

    /// Extends the function with additional variables.
    #[must_use]
    pub fn additional_variables(
        mut self,
        additional_variables: impl IntoIterator<Item = Variable>,
    ) -> Self {
        self.result_model_variables.extend(additional_variables);
        self
    }

    /// Runs this optimization on `solver` and returns the best model found.
    pub fn optimize<B>(
        &self,
        solver: &mut SatSolver<B>,
        handler: &mut dyn ComputationHandler,
        f: &FormulaFactory,
    ) -> LngResult<CancelableResult<Rc<Model>>> {
        let initial_state = solver.save_state()?;
        let model = self.compute(solver, handler, f);
        solver.load_state(&initial_state)?;
        model
    }

    fn compute<B>(
        &self,
        solver: &mut SatSolver<B>,
        handler: &mut dyn ComputationHandler,
        f: &FormulaFactory,
    ) -> LngResult<CancelableResult<Rc<Model>>> {
        if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Optimization)) {
            return Ok(CancelableResult::Canceled(LngEvent::ComputationStarted(
                LngComputation::Optimization,
            )));
        }
        let result_model_variables_vec = self.result_model_variables.iter().copied().collect_vec();
        let selector_map: BTreeMap<Variable, Literal> = self
            .literals
            .iter()
            .enumerate()
            .map(|(i, &l)| (f.var(format!("{SEL_PREFIX}{i}")), l))
            .collect();
        let selectors = selector_map.keys().copied().collect_vec();
        if self.maximize {
            for (sel_var, lit) in &selector_map {
                solver.add_formula(
                    f.or([
                        EncodedFormula::from(sel_var.negate()),
                        EncodedFormula::from(*lit),
                    ]),
                    f,
                )?;
            }
            for (sel_var, lit) in &selector_map {
                solver.add_formula(
                    f.or([
                        EncodedFormula::from(lit.negate()),
                        EncodedFormula::from(*sel_var),
                    ]),
                    f,
                )?;
            }
        } else {
            for (sel_var, lit) in &selector_map {
                solver.add_formula(
                    f.or([
                        EncodedFormula::from(sel_var.negate()),
                        EncodedFormula::from(lit.negate()),
                    ]),
                    f,
                )?;
            }
            for (sel_var, lit) in &selector_map {
                solver.add_formula(
                    f.or([EncodedFormula::from(*lit), EncodedFormula::from(*sel_var)]),
                    f,
                )?;
            }
        }

        let mut sat_call = solver.sat_call().handler(handler).solve(f)?;
        match sat_call.get_sat_result()? {
            CancelableResult::Canceled(lng_event) | CancelableResult::Partial(_, lng_event) => {
                return Ok(CancelableResult::Canceled(lng_event));
            }
            CancelableResult::Ok(res) => {
                if !res {
                    return Err(crate::solver::SolverError::OptimizationOnUnsat.into());
                }
            }
        }
        let mut last_result_model = Rc::new(
            sat_call
                .model(&result_model_variables_vec, f)?
                .ok_or(crate::solver::SolverError::MissingModel)?,
        );
        let mut current_selector_model = sat_call
            .model(&selectors, f)?
            .ok_or(crate::solver::SolverError::MissingModel)?;
        if current_selector_model.pos().len() == selector_map.len() {
            // all optimization literals satisfied -- no need for further
            // optimization
            return Ok(CancelableResult::Ok(Rc::new(
                sat_call
                    .model(&result_model_variables_vec, f)?
                    .ok_or(crate::solver::SolverError::MissingModel)?,
            )));
        }
        drop(sat_call);

        let mut current_bound = current_selector_model.pos().len();
        if current_bound == 0 {
            solver.add_formula(f.cc(CType::GE, 1, selectors.clone())?, f)?;
            let mut sat_call = solver.sat_call().handler(handler).solve(f)?;
            let sat_result = sat_call.get_sat_result()?;
            match sat_result {
                CancelableResult::Canceled(lng_event) | CancelableResult::Partial(_, lng_event) => {
                    return Ok(CancelableResult::Partial(last_result_model, lng_event));
                }
                CancelableResult::Ok(res) => {
                    if !res {
                        return Ok(CancelableResult::Ok(last_result_model));
                    }
                    last_result_model = Rc::new(
                        sat_call
                            .model(&result_model_variables_vec, f)?
                            .ok_or(crate::solver::SolverError::MissingModel)?,
                    );
                    current_selector_model = sat_call
                        .model(&selectors, f)?
                        .ok_or(crate::solver::SolverError::MissingModel)?;
                    current_bound = current_selector_model.pos().len();
                }
            }
        }
        let bound = u32::try_from(current_bound).map_err(|_| {
            crate::solver::SolverError::OptimizationBoundTooLarge {
                bound: current_bound,
            }
        })?;
        let cc_formula = f.cc(
            CType::GE,
            bound
                .checked_add(1)
                .ok_or(crate::solver::SolverError::OptimizationBoundTooLarge {
                    bound: current_bound,
                })?,
            selectors.clone(),
        )?;
        let cc = cc_formula
            .as_cc(f)
            .ok_or(crate::solver::SolverError::InvalidExternalResponse)?;
        let Some(mut incremental_data) = solver.add_incremental_cc(&cc, f)? else {
            let mut sat_call = solver.sat_call().handler(handler).solve(f)?;
            return match sat_call.get_sat_result()? {
                CancelableResult::Canceled(event) | CancelableResult::Partial(_, event) => {
                    Ok(CancelableResult::Partial(last_result_model, event))
                }
                CancelableResult::Ok(false) => Ok(CancelableResult::Ok(last_result_model)),
                CancelableResult::Ok(true) => Ok(CancelableResult::Ok(Rc::new(
                    sat_call
                        .model(&result_model_variables_vec, f)?
                        .ok_or(crate::solver::SolverError::MissingModel)?,
                ))),
            };
        };
        loop {
            let (mut sat_call, returned_handler) = solver
                .sat_call()
                .handler(handler)
                .solve_and_get_handler(f)?;
            let handler =
                returned_handler.ok_or(crate::solver::SolverError::InvalidExternalResponse)?;
            let sat_result = sat_call.get_sat_result()?;
            match sat_result {
                CancelableResult::Canceled(lng_event) | CancelableResult::Partial(_, lng_event) => {
                    return Ok(CancelableResult::Partial(last_result_model, lng_event));
                }
                CancelableResult::Ok(res) => {
                    if !res {
                        return Ok(CancelableResult::Ok(last_result_model));
                    }
                    last_result_model = Rc::new(
                        sat_call
                            .model(&result_model_variables_vec, f)?
                            .ok_or(crate::solver::SolverError::MissingModel)?,
                    );
                    let better_bound_event =
                        LngEvent::OptimizationFoundBetterBound((*last_result_model).clone());
                    if !handler.should_resume(better_bound_event.clone()) {
                        return Ok(CancelableResult::Partial(
                            last_result_model,
                            better_bound_event,
                        ));
                    }
                    current_selector_model = sat_call
                        .model(&selectors, f)?
                        .ok_or(crate::solver::SolverError::MissingModel)?;
                    current_bound = current_selector_model.pos().len();
                    if current_bound == selectors.len() {
                        return Ok(CancelableResult::Ok(last_result_model));
                    }
                }
            }
            drop(sat_call);
            let bound = u32::try_from(current_bound).map_err(|_| {
                crate::solver::SolverError::OptimizationBoundTooLarge {
                    bound: current_bound,
                }
            })?;
            incremental_data.new_lower_bound_for_solver(
                solver,
                f,
                bound.checked_add(1).ok_or(
                    crate::solver::SolverError::OptimizationBoundTooLarge {
                        bound: current_bound,
                    },
                )?,
            )?;
        }
    }
}

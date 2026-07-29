use super::super::encoding::Encoder;
use super::solver::{ProblemType, Solver};
use crate::backends::MaxSatResult;
use crate::errors::LngResult;
use crate::handlers::{CancelableResult, ComputationHandler, LngEvent};
use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not};
use crate::solver::maxsat::MaxSatError;
use crate::solver::maxsat::openwbo_rs::config::{
    CardinalEncoding, IncrementalStrategy, OpenWboConfig,
};
use std::collections::BTreeMap;

pub(crate) struct Msu3 {
    solver: Option<LngCoreSolver>,
    encoder: Encoder,
    incremental_strategy: IncrementalStrategy,
}

impl Msu3 {
    pub(crate) fn new(config: &OpenWboConfig) -> Self {
        Self {
            solver: None,
            encoder: Encoder::from_config(config),
            incremental_strategy: config.incremental_strategy,
        }
    }

    pub(crate) fn search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        if maxsat.problem_type == ProblemType::Weighted {
            return Err(MaxSatError::IllegalConfig.into());
        }
        self.encoder = Encoder::from_config(&maxsat.config);
        match self.incremental_strategy {
            IncrementalStrategy::None => self.none(maxsat, handler),
            IncrementalStrategy::Iterative => {
                if maxsat.config.cardinal_encoding != CardinalEncoding::Totalizer {
                    return Err(MaxSatError::IllegalConfig.into());
                }
                self.iterative(maxsat, handler)
            }
            IncrementalStrategy::Blocking | IncrementalStrategy::Weakening => {
                Err(MaxSatError::IllegalConfig.into())
            }
        }
    }

    fn none(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        maxsat.nb_initial_variables = maxsat.nb_vars;
        let obj_function = Self::init_relaxation(maxsat);
        self.solver = Some(Self::rebuild_solver(maxsat));
        self.encoder.set_incremental(IncrementalStrategy::None);

        let core_mapping = Self::core_mapping(maxsat);
        let mut active_soft = vec![false; maxsat.soft_clauses.len()];
        let mut assumptions = Vec::new();

        loop {
            let sat = match self.solve_sat(maxsat, handler, &assumptions) {
                Ok(sat) => sat,
                Err(canceled) => return Ok(canceled),
            };
            if sat {
                maxsat.nb_satisfiable += 1;
                let model = self.solver_ref().model().to_vec();
                let new_cost = maxsat.compute_cost_model(&model, None);
                maxsat.save_model(&model);
                maxsat.ub_cost = new_cost;

                if maxsat.nb_satisfiable == 1 {
                    assumptions = obj_function.iter().copied().map(not).collect();
                } else {
                    return Ok(maxsat.optimum_result());
                }
                continue;
            }

            maxsat.lb_cost += 1;
            maxsat.nb_cores += 1;
            if maxsat.nb_satisfiable == 0 {
                return Ok(Solver::unsatisfiable());
            }
            if maxsat.lb_cost == maxsat.ub_cost {
                return Ok(maxsat.optimum_result());
            }

            let conflict = self.solver_ref().assumptions_conflict().to_vec();
            maxsat.sum_size_cores += conflict.len() as u64;
            for literal in conflict {
                let index = core_mapping[&literal];
                active_soft[index] = true;
            }

            let (current_obj_function, next_assumptions) =
                Self::current_objective(maxsat, &active_soft);
            assumptions = next_assumptions;
            self.solver = Some(Self::rebuild_solver(maxsat));
            let bound = usize::try_from(maxsat.lb_cost).map_err(|_| MaxSatError::IllegalConfig)?;
            let (encoder, solver) = (
                &mut self.encoder,
                self.solver.as_mut().expect("MSU3 solver is initialized"),
            );
            encoder.encode_cardinality(solver, &current_obj_function, bound);
        }
    }

    fn iterative(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        maxsat.nb_initial_variables = maxsat.nb_vars;
        let obj_function = Self::init_relaxation(maxsat);
        self.solver = Some(Self::rebuild_solver(maxsat));
        self.encoder.set_incremental(IncrementalStrategy::Iterative);

        let core_mapping = Self::core_mapping(maxsat);
        let mut active_soft = vec![false; maxsat.soft_clauses.len()];
        let mut assumptions = Vec::new();
        let mut encoding_assumptions = Vec::new();

        loop {
            let sat = match self.solve_sat(maxsat, handler, &assumptions) {
                Ok(sat) => sat,
                Err(canceled) => return Ok(canceled),
            };
            if sat {
                maxsat.nb_satisfiable += 1;
                let model = self.solver_ref().model().to_vec();
                let new_cost = maxsat.compute_cost_model(&model, None);
                maxsat.save_model(&model);
                maxsat.ub_cost = new_cost;

                if maxsat.nb_satisfiable == 1 {
                    assumptions = obj_function.iter().copied().map(not).collect();
                } else {
                    return Ok(maxsat.optimum_result());
                }
                continue;
            }

            maxsat.lb_cost += 1;
            maxsat.nb_cores += 1;
            if maxsat.nb_satisfiable == 0 {
                return Ok(Solver::unsatisfiable());
            }
            if maxsat.lb_cost == maxsat.ub_cost {
                return Ok(maxsat.optimum_result());
            }

            let conflict = self.solver_ref().assumptions_conflict().to_vec();
            maxsat.sum_size_cores += conflict.len() as u64;
            if conflict.is_empty() {
                return Ok(Solver::unsatisfiable());
            }

            let mut join_obj_function = Vec::new();
            for literal in conflict {
                if let Some(&index) = core_mapping.get(&literal) {
                    active_soft[index] = true;
                    join_obj_function.push(maxsat.soft_clauses[index].relaxation_vars[0]);
                }
            }

            let (current_obj_function, mut next_assumptions) =
                Self::current_objective(maxsat, &active_soft);
            let bound = usize::try_from(maxsat.lb_cost).map_err(|_| MaxSatError::IllegalConfig)?;

            if self.encoder.has_card_encoding() {
                let (encoder, solver) = (
                    &mut self.encoder,
                    self.solver.as_mut().expect("MSU3 solver is initialized"),
                );
                encoder.inc_update_cardinality(
                    solver,
                    &join_obj_function,
                    &current_obj_function,
                    bound,
                    &mut encoding_assumptions,
                )?;
            } else if bound != current_obj_function.len() {
                let (encoder, solver) = (
                    &mut self.encoder,
                    self.solver.as_mut().expect("MSU3 solver is initialized"),
                );
                encoder.build_cardinality(solver, &current_obj_function, bound)?;
                join_obj_function.clear();
                encoder.inc_update_cardinality(
                    solver,
                    &join_obj_function,
                    &current_obj_function,
                    bound,
                    &mut encoding_assumptions,
                )?;
            }
            next_assumptions.extend_from_slice(&encoding_assumptions);
            assumptions = next_assumptions;
        }
    }

    fn init_relaxation(maxsat: &mut Solver) -> Vec<LngLit> {
        let mut objective = Vec::with_capacity(maxsat.soft_clauses.len());
        for index in 0..maxsat.soft_clauses.len() {
            let literal = maxsat.new_lit(false);
            maxsat.soft_clauses[index].relaxation_vars.push(literal);
            maxsat.soft_clauses[index].assumption_var = Some(literal);
            objective.push(literal);
        }
        objective
    }

    fn core_mapping(maxsat: &Solver) -> BTreeMap<LngLit, usize> {
        maxsat
            .soft_clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| (clause.assumption_var.unwrap(), index))
            .collect()
    }

    fn current_objective(maxsat: &Solver, active_soft: &[bool]) -> (Vec<LngLit>, Vec<LngLit>) {
        let mut objective = Vec::new();
        let mut assumptions = Vec::new();
        for (index, clause) in maxsat.soft_clauses.iter().enumerate() {
            if active_soft[index] {
                objective.push(clause.relaxation_vars[0]);
            } else {
                assumptions.push(not(clause.assumption_var.unwrap()));
            }
        }
        (objective, assumptions)
    }

    fn rebuild_solver(maxsat: &Solver) -> LngCoreSolver {
        let mut solver = maxsat.new_sat_solver();
        maxsat.reserve_sat_variables(&mut solver);
        for hard_clause in &maxsat.hard_clauses {
            solver.add_clause(hard_clause.clause.clone(), None);
        }
        for soft_clause in &maxsat.soft_clauses {
            let mut clause = soft_clause.clause.clone();
            clause.extend_from_slice(&soft_clause.relaxation_vars);
            solver.add_clause(clause, None);
        }
        solver
    }

    fn solve_sat(
        &mut self,
        maxsat: &Solver,
        handler: &mut dyn ComputationHandler,
        assumptions: &[LngLit],
    ) -> Result<bool, CancelableResult<MaxSatResult>> {
        let event = LngEvent::MaxSatSolverCall;
        if !handler.should_resume(event.clone()) {
            return Err(Self::canceled(maxsat, event));
        }
        match self
            .solver_mut()
            .internal_solve_with_assumptions(handler, assumptions.to_vec())
        {
            CancelableResult::Ok(result) => Ok(result),
            CancelableResult::Canceled(event) | CancelableResult::Partial(_, event) => {
                Err(Self::canceled(maxsat, event))
            }
        }
    }

    fn canceled(maxsat: &Solver, event: LngEvent) -> CancelableResult<MaxSatResult> {
        if maxsat.nb_satisfiable > 0 {
            CancelableResult::Partial(maxsat.optimum(), event)
        } else {
            CancelableResult::Canceled(event)
        }
    }

    fn solver_ref(&self) -> &LngCoreSolver {
        self.solver.as_ref().expect("MSU3 solver is initialized")
    }

    fn solver_mut(&mut self) -> &mut LngCoreSolver {
        self.solver.as_mut().expect("MSU3 solver is initialized")
    }
}

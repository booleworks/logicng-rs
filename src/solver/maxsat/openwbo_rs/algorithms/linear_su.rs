use crate::backends::MaxSatResult;
use crate::handlers::{CancelableResult, ComputationHandler, LngEvent};
use crate::solver::lng_core_solver::{LngCoreSolver, LngLit};
use crate::solver::maxsat::openwbo_rs::config::{OpenWboConfig, PbEncoding};

use super::super::encoding::Encoder;
use super::solver::{ProblemType, Solver};

pub(crate) struct LinearSu {
    solver: Option<LngCoreSolver>,
    encoder: Encoder,
    pb_encoding: PbEncoding,
    bmo_mode: bool,
    all_false: bool,
    obj_function: Vec<LngLit>,
    coeffs: Vec<usize>,
    is_bmo: bool,
}

impl LinearSu {
    pub(crate) fn new(config: &OpenWboConfig) -> Self {
        Self {
            solver: None,
            encoder: Encoder::from_config(config),
            pb_encoding: config.pb_encoding.clone(),
            bmo_mode: config.bmo,
            all_false: false,
            obj_function: Vec::new(),
            coeffs: Vec::new(),
            is_bmo: false,
        }
    }

    pub(crate) fn search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> CancelableResult<MaxSatResult> {
        self.encoder = Encoder::from_config(&maxsat.config);
        self.encoder.set_pb_encoding(self.pb_encoding.clone());
        self.obj_function.clear();
        self.coeffs.clear();
        maxsat.nb_initial_variables = maxsat.nb_vars;

        if maxsat.problem_type == ProblemType::Weighted {
            self.is_bmo = maxsat.config.bmo && maxsat.is_bmo(true);
            if self.bmo_mode && self.is_bmo {
                self.bmo_search(maxsat, handler)
            } else {
                self.normal_search(maxsat, handler)
            }
        } else {
            self.normal_search(maxsat, handler)
        }
    }

    fn bmo_search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> CancelableResult<MaxSatResult> {
        self.init_relaxation(maxsat);
        let mut current_weight = maxsat.order_weights[0];
        let min_weight = *maxsat.order_weights.last().unwrap();
        let mut pos_weight = 0usize;
        let mut functions = Vec::<Vec<LngLit>>::new();
        let mut weights = Vec::<usize>::new();
        self.solver = Some(self.rebuild_bmo(maxsat, &functions, &weights, current_weight));
        let mut local_cost = 0u64;
        maxsat.ub_cost = 0;
        let mut has_incumbent = false;

        loop {
            let maxsat_call = LngEvent::MaxSatSolverCall;
            if !handler.should_resume(maxsat_call.clone()) {
                return Self::canceled_result(maxsat, maxsat_call, has_incumbent);
            }
            let res = self.solver_mut().internal_solve(handler);
            match res {
                CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                    return Self::canceled_result(maxsat, e, has_incumbent);
                }
                CancelableResult::Ok(true) => {
                    maxsat.nb_satisfiable += 1;
                    let model = &self.solver_ref().model;
                    let new_cost = maxsat.compute_cost_model(model, Some(current_weight));
                    if current_weight == min_weight {
                        let model = self.solver_ref().model.clone();
                        maxsat.save_model(&model);
                        maxsat.ub_cost = new_cost.saturating_add(maxsat.lb_cost);
                        has_incumbent = true;
                    }

                    if new_cost == 0 && current_weight == min_weight {
                        return maxsat.optimum_result();
                    }

                    if new_cost == 0 {
                        functions.push(self.obj_function.clone());
                        local_cost = new_cost;
                        weights.push(0);
                        pos_weight += 1;
                        current_weight = maxsat.order_weights[pos_weight];
                        self.solver =
                            Some(self.rebuild_bmo(maxsat, &functions, &weights, current_weight));
                    } else {
                        let rhs = (new_cost / current_weight - 1) as usize;
                        if local_cost == 0 {
                            let solver = self.solver.as_mut().expect("solver is initialized");
                            self.encoder
                                .encode_cardinality(solver, &self.obj_function, rhs);
                        } else {
                            let solver = self.solver.as_mut().expect("solver is initialized");
                            self.encoder.update_cardinality(solver, rhs);
                        }
                        local_cost = new_cost;
                    }
                }
                CancelableResult::Ok(false) => {
                    maxsat.nb_cores += 1;
                    if current_weight == min_weight {
                        return if maxsat.nb_satisfiable == 0 {
                            Solver::unsatisfiable()
                        } else {
                            maxsat.optimum_result()
                        };
                    }

                    functions.push(self.obj_function.clone());
                    weights.push((local_cost / current_weight) as usize);
                    maxsat.lb_cost = maxsat.lb_cost.saturating_add(local_cost);
                    pos_weight += 1;
                    current_weight = maxsat.order_weights[pos_weight];
                    local_cost = 0;
                    self.solver =
                        Some(self.rebuild_bmo(maxsat, &functions, &weights, current_weight));
                }
            }
        }
    }

    fn normal_search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> CancelableResult<MaxSatResult> {
        self.init_relaxation(maxsat);
        self.solver = Some(self.rebuild_solver(maxsat, 1));
        let mut has_incumbent = false;

        loop {
            let maxsat_call = LngEvent::MaxSatSolverCall;
            if !handler.should_resume(maxsat_call.clone()) {
                return Self::canceled_result(maxsat, maxsat_call, has_incumbent);
            }
            let res = self.solver_mut().internal_solve(handler);
            match res {
                CancelableResult::Canceled(e) | CancelableResult::Partial(_, e) => {
                    return Self::canceled_result(maxsat, e, has_incumbent);
                }
                CancelableResult::Ok(true) => {
                    maxsat.nb_satisfiable += 1;
                    let model = self.solver_ref().model.clone();
                    let new_cost = maxsat.compute_cost_model(&model, None);
                    maxsat.save_model(&model);
                    has_incumbent = true;

                    if new_cost == 0 {
                        maxsat.ub_cost = new_cost;
                        return maxsat.optimum_result();
                    }

                    let rhs = (new_cost - 1) as usize;
                    if maxsat.problem_type == ProblemType::Weighted {
                        if !self.encoder.has_pb_encoding() {
                            let solver = self.solver.as_mut().expect("solver is initialized");
                            self.encoder.encode_pb(
                                solver,
                                &mut self.obj_function,
                                &mut self.coeffs,
                                rhs,
                            );
                        } else {
                            let solver = self.solver.as_mut().expect("solver is initialized");
                            self.encoder.update_pb(solver, rhs);
                        }
                    } else if !self.encoder.has_card_encoding() {
                        let solver = self.solver.as_mut().expect("solver is initialized");
                        self.encoder
                            .encode_cardinality(solver, &self.obj_function, rhs);
                    } else {
                        let solver = self.solver.as_mut().expect("solver is initialized");
                        self.encoder.update_cardinality(solver, rhs);
                    }
                    maxsat.ub_cost = new_cost;
                }
                CancelableResult::Ok(false) => {
                    maxsat.nb_cores += 1;
                    return if maxsat.nb_satisfiable == 0 {
                        Solver::unsatisfiable()
                    } else {
                        maxsat.optimum_result()
                    };
                }
            }
        }
    }

    fn canceled_result(
        maxsat: &Solver,
        event: LngEvent,
        has_incumbent: bool,
    ) -> CancelableResult<MaxSatResult> {
        if has_incumbent {
            CancelableResult::Partial(maxsat.optimum(), event)
        } else {
            CancelableResult::Canceled(event)
        }
    }

    fn rebuild_solver(&self, maxsat: &Solver, min_weight: u64) -> LngCoreSolver {
        let mut solver = maxsat.new_sat_solver();
        maxsat.reserve_sat_variables(&mut solver);
        for hard_clause in &maxsat.hard_clauses {
            solver.add_clause(hard_clause.clause.clone(), None);
        }
        for soft_clause in &maxsat.soft_clauses {
            if soft_clause.weight < min_weight {
                continue;
            }
            let mut clause = soft_clause.clause.clone();
            clause.extend_from_slice(&soft_clause.relaxation_vars);
            solver.add_clause(clause, None);
        }
        solver
    }

    fn rebuild_bmo(
        &mut self,
        maxsat: &Solver,
        functions: &[Vec<LngLit>],
        rhs: &[usize],
        current_weight: u64,
    ) -> LngCoreSolver {
        let mut solver = self.rebuild_solver(maxsat, current_weight);
        self.obj_function.clear();
        self.coeffs.clear();
        for soft_clause in &maxsat.soft_clauses {
            if soft_clause.weight == current_weight {
                self.obj_function.push(soft_clause.relaxation_vars[0]);
                self.coeffs.push(soft_clause.weight as usize);
            }
        }
        for (function, rhs) in functions.iter().zip(rhs) {
            self.encoder.encode_cardinality(&mut solver, function, *rhs);
        }
        solver
    }

    fn init_relaxation(&mut self, maxsat: &mut Solver) {
        self.obj_function.clear();
        self.coeffs.clear();
        for i in 0..maxsat.soft_clauses.len() {
            let lit = maxsat.new_lit(false);
            let weight = maxsat.soft_clauses[i].weight;
            maxsat.soft_clauses[i].relaxation_vars.push(lit);
            self.obj_function.push(lit);
            self.coeffs.push(weight as usize);
        }
    }

    fn solver_ref(&self) -> &LngCoreSolver {
        self.solver
            .as_ref()
            .expect("LinearSU solver is initialized")
    }

    fn solver_mut(&mut self) -> &mut LngCoreSolver {
        self.solver
            .as_mut()
            .expect("LinearSU solver is initialized")
    }
}

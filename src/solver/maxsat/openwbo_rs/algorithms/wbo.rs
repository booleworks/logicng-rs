use crate::backends::MaxSatResult;
use crate::errors::LngResult;
use crate::handlers::{CancelableResult, ComputationHandler, LngEvent};
use crate::solver::lng_core_solver::{LngCoreSolver, LngLit, not, var};
use crate::solver::maxsat::openwbo_rs::config::{OpenWboConfig, Symmetry, WeightStrategy};
use std::collections::{BTreeMap, BTreeSet};

use super::solver::{ProblemType, SoftClause, Solver};

pub(crate) struct Wbo {
    solver: Option<LngCoreSolver>,
    nb_current_soft: usize,
    weight_strategy: WeightStrategy,
    core_mapping: BTreeMap<LngLit, usize>,
    assumptions: Vec<LngLit>,
    symmetry_strategy: bool,
    index_soft_core: Vec<usize>,
    soft_mapping: Vec<Vec<usize>>,
    relaxation_mapping: Vec<Vec<LngLit>>,
    duplicated_symmetry_clauses: BTreeSet<(usize, usize)>,
    symmetry_breaking_limit: i32,
}

impl Wbo {
    pub(crate) fn new(config: &OpenWboConfig) -> Self {
        Self {
            solver: None,
            nb_current_soft: 0,
            weight_strategy: config.weight_strategy.clone(),
            core_mapping: BTreeMap::new(),
            assumptions: Vec::new(),
            symmetry_strategy: matches!(config.symmetry, Symmetry::Sym(limit) if limit > 0),
            index_soft_core: Vec::new(),
            soft_mapping: Vec::new(),
            relaxation_mapping: Vec::new(),
            duplicated_symmetry_clauses: BTreeSet::new(),
            symmetry_breaking_limit: match config.symmetry {
                Symmetry::None => 0,
                Symmetry::Sym(limit) => limit,
            },
        }
    }

    pub(crate) fn search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        maxsat.nb_initial_variables = maxsat.nb_vars;
        self.core_mapping.clear();
        self.assumptions.clear();
        self.index_soft_core.clear();
        self.soft_mapping.clear();
        self.relaxation_mapping.clear();
        self.duplicated_symmetry_clauses.clear();

        if maxsat.current_weight == 1 {
            self.weight_strategy = WeightStrategy::None;
        }
        if self.symmetry_strategy {
            self.init_symmetry(maxsat);
        }

        let result = if maxsat.problem_type == ProblemType::Unweighted
            || self.weight_strategy == WeightStrategy::None
        {
            self.normal_search(maxsat, handler)
        } else {
            self.weight_search(maxsat, handler)
        };
        Ok(result)
    }

    fn normal_search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> CancelableResult<MaxSatResult> {
        match self.unsat_search(maxsat, handler) {
            Ok(false) => return Solver::unsatisfiable(),
            Ok(true) => {}
            Err(canceled) => return canceled,
        }

        self.init_assumptions(maxsat);
        self.solver = Some(self.rebuild_solver(maxsat));
        loop {
            let assumptions = self.assumptions.clone();
            let sat = match self.solve_sat(maxsat, handler, &assumptions) {
                Ok(sat) => sat,
                Err(canceled) => return canceled,
            };
            if sat {
                maxsat.nb_satisfiable += 1;
                let model = self.solver_ref().model().to_vec();
                maxsat.ub_cost = maxsat.compute_cost_model(&model, None);
                maxsat.save_model(&model);
                return maxsat.optimum_result();
            }

            maxsat.nb_cores += 1;
            let conflict = self.solver_ref().assumptions_conflict().to_vec();
            let core_cost = self.compute_cost_core(maxsat, &conflict);
            maxsat.lb_cost += core_cost;
            if maxsat.lb_cost == maxsat.ub_cost {
                return maxsat.optimum_result();
            }
            self.relax_core(maxsat, &conflict, core_cost);
            self.solver = Some(self.rebuild_solver(maxsat));
        }
    }

    fn weight_search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> CancelableResult<MaxSatResult> {
        match self.unsat_search(maxsat, handler) {
            Ok(false) => return Solver::unsatisfiable(),
            Ok(true) => {}
            Err(canceled) => return canceled,
        }

        self.init_assumptions(maxsat);
        self.update_current_weight(maxsat);
        self.solver = Some(self.rebuild_weight_solver(maxsat));
        loop {
            let assumptions = self.assumptions.clone();
            let sat = match self.solve_sat(maxsat, handler, &assumptions) {
                Ok(sat) => sat,
                Err(canceled) => return canceled,
            };
            if !sat {
                maxsat.nb_cores += 1;
                let conflict = self.solver_ref().assumptions_conflict().to_vec();
                let core_cost = self.compute_cost_core(maxsat, &conflict);
                maxsat.lb_cost += core_cost;
                self.relax_core(maxsat, &conflict, core_cost);
                self.solver = Some(self.rebuild_weight_solver(maxsat));
                continue;
            }

            maxsat.nb_satisfiable += 1;
            let model = self.solver_ref().model().to_vec();
            if self.nb_current_soft == maxsat.soft_clauses.len() {
                if maxsat.lb_cost < maxsat.ub_cost {
                    maxsat.ub_cost = maxsat.lb_cost;
                    maxsat.save_model(&model);
                }
                return maxsat.optimum_result();
            }

            self.update_current_weight(maxsat);
            let cost = maxsat.compute_cost_model(&model, None);
            if cost < maxsat.ub_cost {
                maxsat.ub_cost = cost;
                maxsat.save_model(&model);
            }
            if maxsat.lb_cost == maxsat.ub_cost {
                return maxsat.optimum_result();
            }
            self.solver = Some(self.rebuild_weight_solver(maxsat));
        }
    }

    fn unsat_search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> Result<bool, CancelableResult<MaxSatResult>> {
        self.solver = Some(Self::rebuild_hard_solver(maxsat));
        let result = self.solve_sat(maxsat, handler, &[]);
        match result {
            Ok(false) => maxsat.nb_cores += 1,
            Ok(true) => {
                maxsat.nb_satisfiable += 1;
                let model = self.solver_ref().model().to_vec();
                let cost = maxsat.compute_cost_model(&model, None);
                maxsat.ub_cost = cost;
                maxsat.save_model(&model);
            }
            Err(_) => {}
        }
        self.solver = None;
        result
    }

    fn rebuild_hard_solver(maxsat: &Solver) -> LngCoreSolver {
        let mut solver = maxsat.new_sat_solver();
        maxsat.reserve_sat_variables(&mut solver);
        for clause in &maxsat.hard_clauses {
            solver.add_clause(clause.clause.clone(), None);
        }
        solver
    }

    fn rebuild_solver(&mut self, maxsat: &mut Solver) -> LngCoreSolver {
        let mut solver = Self::rebuild_hard_solver(maxsat);
        if self.symmetry_strategy {
            self.symmetry_breaking(maxsat);
        }
        for soft in &maxsat.soft_clauses {
            let mut clause = soft.clause.clone();
            clause.extend_from_slice(&soft.relaxation_vars);
            clause.push(soft.assumption_var.expect("WBO assumption is initialized"));
            solver.add_clause(clause, None);
        }
        solver
    }

    fn rebuild_weight_solver(&mut self, maxsat: &mut Solver) -> LngCoreSolver {
        let mut solver = Self::rebuild_hard_solver(maxsat);
        if self.symmetry_strategy {
            self.symmetry_breaking(maxsat);
        }
        self.nb_current_soft = 0;
        for soft in &maxsat.soft_clauses {
            if soft.weight >= maxsat.current_weight {
                self.nb_current_soft += 1;
                let mut clause = soft.clause.clone();
                clause.extend_from_slice(&soft.relaxation_vars);
                clause.push(soft.assumption_var.expect("WBO assumption is initialized"));
                solver.add_clause(clause, None);
            }
        }
        solver
    }

    fn init_assumptions(&mut self, maxsat: &mut Solver) {
        for index in 0..maxsat.soft_clauses.len() {
            let assumption = maxsat.new_lit(false);
            maxsat.soft_clauses[index].assumption_var = Some(assumption);
            self.core_mapping.insert(assumption, index);
            self.assumptions.push(not(assumption));
        }
    }

    fn update_current_weight(&self, maxsat: &mut Solver) {
        maxsat.current_weight = match self.weight_strategy {
            WeightStrategy::Normal => Self::find_next_weight(maxsat, maxsat.current_weight),
            WeightStrategy::Diversify => self.find_next_weight_diversity(maxsat),
            WeightStrategy::None => unreachable!("weighted WBO requires a weight strategy"),
        };
    }

    fn find_next_weight(maxsat: &Solver, weight: u64) -> u64 {
        maxsat
            .soft_clauses
            .iter()
            .map(|clause| clause.weight)
            .filter(|candidate| *candidate < weight)
            .max()
            .unwrap_or(1)
    }

    fn find_next_weight_diversity(&self, maxsat: &Solver) -> u64 {
        let mut next_weight = maxsat.current_weight;
        let mut find_next = false;
        loop {
            if maxsat.nb_satisfiable > 1 || find_next {
                next_weight = Self::find_next_weight(maxsat, next_weight);
            }
            let weights = maxsat
                .soft_clauses
                .iter()
                .filter(|clause| clause.weight >= next_weight)
                .map(|clause| clause.weight)
                .collect::<BTreeSet<_>>();
            let clauses = maxsat
                .soft_clauses
                .iter()
                .filter(|clause| clause.weight >= next_weight)
                .count();
            if clauses as f64 / weights.len() as f64 > 1.25 || clauses == maxsat.soft_clauses.len()
            {
                return next_weight;
            }
            if maxsat.nb_satisfiable == 1 && !find_next {
                find_next = true;
            }
        }
    }

    fn compute_cost_core(&self, maxsat: &Solver, conflict: &[LngLit]) -> u64 {
        if maxsat.problem_type == ProblemType::Unweighted {
            return 1;
        }
        conflict
            .iter()
            .map(|literal| maxsat.soft_clauses[self.core_mapping[literal]].weight)
            .min()
            .expect("WBO core is not empty")
    }

    fn relax_core(&mut self, maxsat: &mut Solver, conflict: &[LngLit], core_weight: u64) {
        let mut relaxations = Vec::with_capacity(conflict.len());
        for &literal in conflict {
            let index = self.core_mapping[&literal];
            let relaxation = maxsat.new_lit(false);
            relaxations.push(relaxation);

            if maxsat.soft_clauses[index].weight == core_weight {
                maxsat.soft_clauses[index].relaxation_vars.push(relaxation);
                if self.symmetry_strategy {
                    self.symmetry_log(maxsat, index);
                }
            } else {
                maxsat.soft_clauses[index].weight -= core_weight;
                let clause = maxsat.soft_clauses[index].clause.clone();
                let mut vars = maxsat.soft_clauses[index].relaxation_vars.clone();
                vars.push(relaxation);
                let new_index = maxsat.soft_clauses.len();
                maxsat.soft_clauses.push(SoftClause {
                    clause,
                    weight: core_weight,
                    assumption_var: None,
                    relaxation_vars: vars,
                });
                let assumption = maxsat.new_lit(false);
                maxsat.soft_clauses[new_index].assumption_var = Some(assumption);
                self.core_mapping.insert(assumption, new_index);
                self.assumptions.push(not(assumption));
                if self.symmetry_strategy {
                    self.symmetry_log(maxsat, new_index);
                }
            }
        }
        Self::encode_eo(maxsat, &relaxations);
        maxsat.sum_size_cores += conflict.len() as u64;
    }

    fn encode_eo(maxsat: &mut Solver, literals: &[LngLit]) {
        if literals.len() == 1 {
            maxsat.add_hard_clause(vec![literals[0]]);
            return;
        }

        let auxiliaries = (0..literals.len() - 1)
            .map(|_| maxsat.new_lit(false))
            .collect::<Vec<_>>();
        for (i, &literal) in literals.iter().enumerate() {
            if i == 0 {
                maxsat.add_hard_clause(vec![literal, not(auxiliaries[i])]);
                maxsat.add_hard_clause(vec![not(literal), auxiliaries[i]]);
            } else if i == literals.len() - 1 {
                maxsat.add_hard_clause(vec![literal, auxiliaries[i - 1]]);
                maxsat.add_hard_clause(vec![not(literal), not(auxiliaries[i - 1])]);
            } else {
                maxsat.add_hard_clause(vec![not(auxiliaries[i - 1]), auxiliaries[i]]);
                maxsat.add_hard_clause(vec![literal, not(auxiliaries[i]), auxiliaries[i - 1]]);
                maxsat.add_hard_clause(vec![not(literal), auxiliaries[i]]);
                maxsat.add_hard_clause(vec![not(literal), not(auxiliaries[i - 1])]);
            }
        }
    }

    fn init_symmetry(&mut self, maxsat: &Solver) {
        self.soft_mapping
            .resize_with(maxsat.soft_clauses.len(), Vec::new);
        self.relaxation_mapping
            .resize_with(maxsat.soft_clauses.len(), Vec::new);
    }

    fn symmetry_log(&mut self, maxsat: &Solver, index: usize) {
        if maxsat.nb_symmetry_clauses >= self.symmetry_breaking_limit as u64 {
            return;
        }
        while self.soft_mapping.len() <= index {
            self.soft_mapping.push(Vec::new());
            self.relaxation_mapping.push(Vec::new());
        }
        self.soft_mapping[index].push(maxsat.nb_cores as usize);
        self.relaxation_mapping[index].push(
            *maxsat.soft_clauses[index]
                .relaxation_vars
                .last()
                .expect("symmetry is logged after relaxation"),
        );
        if self.soft_mapping[index].len() > 1 {
            self.index_soft_core.push(index);
        }
    }

    fn symmetry_breaking(&mut self, maxsat: &mut Solver) {
        if !self.index_soft_core.is_empty()
            && maxsat.nb_symmetry_clauses < self.symmetry_breaking_limit as u64
        {
            let mut previous = vec![Vec::<LngLit>::new(); maxsat.nb_cores as usize];
            let mut current = vec![Vec::<LngLit>::new(); maxsat.nb_cores as usize];
            let mut core_list = Vec::new();

            'soft: for &soft in &self.index_soft_core {
                let mut added_cores = Vec::new();
                for j in 0..self.soft_mapping[soft].len() - 1 {
                    let core = self.soft_mapping[soft][j];
                    added_cores.push(core);
                    if previous[core].is_empty() {
                        core_list.push(core);
                    }
                    let relaxation = self.relaxation_mapping[soft][j];
                    previous[core].push(relaxation);
                }
                for core in added_cores {
                    let last = self.soft_mapping[soft].len() - 1;
                    let relaxation = self.relaxation_mapping[soft][last];
                    current[core].push(relaxation);
                }

                for &core in &core_list {
                    for m in 0..previous[core].len() {
                        for j in m + 1..current[core].len() {
                            let first = previous[core][m];
                            let second = current[core][j];
                            let pair = if var(first).0 < var(second).0 {
                                (var(first).0, var(second).0)
                            } else {
                                (var(second).0, var(first).0)
                            };
                            if self.duplicated_symmetry_clauses.insert(pair) {
                                maxsat.add_hard_clause(vec![not(first), not(second)]);
                                maxsat.nb_symmetry_clauses += 1;
                                if maxsat.nb_symmetry_clauses == self.symmetry_breaking_limit as u64
                                {
                                    break 'soft;
                                }
                            }
                        }
                    }
                }
            }
        }
        self.index_soft_core.clear();
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
        self.solver.as_ref().expect("WBO solver is initialized")
    }

    fn solver_mut(&mut self) -> &mut LngCoreSolver {
        self.solver.as_mut().expect("WBO solver is initialized")
    }
}

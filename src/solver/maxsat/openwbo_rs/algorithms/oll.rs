use super::super::encoding::Encoder;
use super::solver::{ProblemType, SoftClause, Solver};
use crate::backends::MaxSatResult;
use crate::errors::LngResult;
use crate::handlers::{CancelableResult, ComputationHandler, LngEvent};
use crate::solver::lng_core_solver::{not, LngCoreSolver, LngLit};
use crate::solver::maxsat::openwbo_rs::config::{CardinalEncoding, IncrementalStrategy};
use crate::solver::maxsat::PbEncoding;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BoundInfo {
    id: usize,
    bound: usize,
    weight: u64,
}

pub(crate) struct Oll {
    solver: Option<LngCoreSolver>,
    encoder: Encoder,
}

impl Oll {
    pub(crate) fn new() -> Self {
        Self {
            solver: None,
            encoder: Self::iterative_totalizer(),
        }
    }

    pub(crate) fn search(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        self.encoder = Self::iterative_totalizer();
        if maxsat.problem_type == ProblemType::Weighted {
            self.weighted(maxsat, handler)
        } else {
            self.unweighted(maxsat, handler)
        }
    }

    fn unweighted(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        maxsat.nb_initial_variables = maxsat.nb_vars;
        Self::init_relaxation(maxsat);
        self.solver = Some(Self::rebuild_solver(maxsat));

        let mut assumptions = Vec::new();
        let mut active_soft = vec![false; maxsat.soft_clauses.len()];
        let core_mapping = maxsat
            .soft_clauses
            .iter()
            .enumerate()
            .map(|(i, clause)| (clause.assumption_var.unwrap(), i))
            .collect::<BTreeMap<_, _>>();
        let mut bound_mapping = BTreeMap::<LngLit, BoundInfo>::new();
        let mut cardinality_assumptions = BTreeSet::<LngLit>::new();
        let mut soft_cardinality = Vec::<Encoder>::new();

        loop {
            let result = self.solve_sat(maxsat, handler, &assumptions);
            let sat = match result {
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
                    if new_cost == 0 {
                        return Ok(maxsat.optimum_result());
                    }
                    assumptions.extend(
                        maxsat
                            .soft_clauses
                            .iter()
                            .map(|clause| not(clause.assumption_var.unwrap())),
                    );
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
            let mut soft_relax = Vec::new();
            let mut cardinality_relax = Vec::new();

            for p in conflict {
                if let Some(&index) = core_mapping.get(&p) {
                    active_soft[index] = true;
                    soft_relax.push(p);
                }
                if let Some(&info) = bound_mapping.get(&p) {
                    cardinality_assumptions.remove(&p);
                    cardinality_relax.push(p);
                    Self::increase_bound(
                        self.solver_mut(),
                        &mut soft_cardinality,
                        &mut bound_mapping,
                        &mut cardinality_assumptions,
                        info,
                        1,
                    )?;
                }
            }

            Self::relax_core(
                self.solver_mut(),
                &mut soft_cardinality,
                &mut bound_mapping,
                &mut cardinality_assumptions,
                soft_relax,
                cardinality_relax,
                1,
            )?;
            assumptions =
                Self::unweighted_assumptions(maxsat, &active_soft, &cardinality_assumptions);
        }
    }

    #[allow(clippy::too_many_lines)]
    fn weighted(
        &mut self,
        maxsat: &mut Solver,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        maxsat.nb_initial_variables = maxsat.nb_vars;
        Self::init_relaxation(maxsat);
        self.solver = Some(Self::rebuild_solver(maxsat));

        let mut assumptions = Vec::new();
        let mut active_soft = vec![false; maxsat.soft_clauses.len()];
        let mut core_mapping = maxsat
            .soft_clauses
            .iter()
            .enumerate()
            .map(|(i, clause)| (clause.assumption_var.unwrap(), i))
            .collect::<BTreeMap<_, _>>();
        let mut bound_mapping = BTreeMap::<LngLit, BoundInfo>::new();
        let mut cardinality_assumptions = BTreeSet::<LngLit>::new();
        let mut soft_cardinality = Vec::<Encoder>::new();
        let mut min_weight = maxsat.current_weight;

        loop {
            let result = self.solve_sat(maxsat, handler, &assumptions);
            let sat = match result {
                Ok(sat) => sat,
                Err(canceled) => return Ok(canceled),
            };
            if sat {
                maxsat.nb_satisfiable += 1;
                let model = self.solver_ref().model().to_vec();
                let new_cost = maxsat.compute_cost_model(&model, None);
                if new_cost < maxsat.ub_cost || maxsat.nb_satisfiable == 1 {
                    maxsat.save_model(&model);
                    maxsat.ub_cost = new_cost;
                }

                if maxsat.nb_satisfiable == 1 {
                    min_weight = Self::find_next_weight_diversity(
                        maxsat,
                        min_weight,
                        &cardinality_assumptions,
                        &bound_mapping,
                    );
                    assumptions = maxsat
                        .soft_clauses
                        .iter()
                        .filter(|clause| clause.weight >= min_weight)
                        .map(|clause| not(clause.assumption_var.unwrap()))
                        .collect();
                } else {
                    let not_considered_soft = maxsat
                        .soft_clauses
                        .iter()
                        .filter(|clause| clause.weight < min_weight)
                        .count();
                    let not_considered_cardinality = cardinality_assumptions
                        .iter()
                        .filter(|lit| bound_mapping[lit].weight < min_weight)
                        .count();
                    if not_considered_soft + not_considered_cardinality == 0 {
                        return Ok(maxsat.optimum_result());
                    }
                    min_weight = Self::find_next_weight_diversity(
                        maxsat,
                        min_weight,
                        &cardinality_assumptions,
                        &bound_mapping,
                    );
                    assumptions = Self::weighted_assumptions(
                        maxsat,
                        &active_soft,
                        &cardinality_assumptions,
                        &bound_mapping,
                        min_weight,
                    );
                }
                continue;
            }

            let conflict = self.solver_ref().assumptions_conflict().to_vec();
            maxsat.nb_cores += 1;
            if maxsat.nb_satisfiable == 0 {
                return Ok(Solver::unsatisfiable());
            }
            let min_core = conflict
                .iter()
                .filter_map(|p| {
                    core_mapping
                        .get(p)
                        .map(|&i| maxsat.soft_clauses[i].weight)
                        .or_else(|| bound_mapping.get(p).map(|info| info.weight))
                })
                .min()
                .expect("an OLL core contains a relaxation literal");

            maxsat.lb_cost += min_core;
            if maxsat.lb_cost == maxsat.ub_cost {
                return Ok(maxsat.optimum_result());
            }
            maxsat.sum_size_cores += conflict.len() as u64;

            let mut soft_relax = Vec::new();
            let mut cardinality_relax = Vec::new();
            for p in conflict {
                if let Some(&index) = core_mapping.get(&p) {
                    if maxsat.soft_clauses[index].weight > min_core {
                        maxsat.soft_clauses[index].weight -= min_core;
                        let mut clause = maxsat.soft_clauses[index].clause.clone();

                        while maxsat.nb_vars < self.solver_ref().n_vars() {
                            maxsat.new_lit(false);
                        }
                        let relaxation = maxsat.new_lit(false);
                        maxsat.soft_clauses.push(SoftClause {
                            clause: clause.clone(),
                            weight: min_core,
                            assumption_var: Some(relaxation),
                            relaxation_vars: vec![relaxation],
                        });
                        active_soft.push(true);

                        self.solver_mut().new_var(true, true);
                        clause.push(relaxation);
                        self.solver_mut().add_clause(clause, None);
                        let new_index = maxsat.soft_clauses.len() - 1;
                        core_mapping.insert(relaxation, new_index);
                        soft_relax.push(relaxation);
                    } else {
                        active_soft[index] = true;
                        soft_relax.push(p);
                    }
                }

                if let Some(&info) = bound_mapping.get(&p) {
                    if info.weight == min_core {
                        cardinality_assumptions.remove(&p);
                        cardinality_relax.push(p);
                        Self::increase_bound(
                            self.solver_mut(),
                            &mut soft_cardinality,
                            &mut bound_mapping,
                            &mut cardinality_assumptions,
                            info,
                            min_core,
                        )?;
                    } else {
                        let lits = soft_cardinality[info.id].lits()?.to_vec();
                        let mut duplicate = Self::iterative_totalizer();
                        duplicate.build_cardinality(self.solver_mut(), &lits, info.bound)?;
                        let out = duplicate.outputs()?[info.bound];
                        soft_cardinality.push(duplicate);
                        let duplicate_id = soft_cardinality.len() - 1;
                        bound_mapping.insert(
                            out,
                            BoundInfo {
                                id: duplicate_id,
                                bound: info.bound,
                                weight: min_core,
                            },
                        );
                        cardinality_relax.push(out);
                        bound_mapping.insert(
                            p,
                            BoundInfo {
                                weight: info.weight - min_core,
                                ..info
                            },
                        );
                        let duplicate_info = bound_mapping[&out];
                        Self::increase_bound(
                            self.solver_mut(),
                            &mut soft_cardinality,
                            &mut bound_mapping,
                            &mut cardinality_assumptions,
                            duplicate_info,
                            min_core,
                        )?;
                    }
                }
            }

            Self::relax_core(
                self.solver_mut(),
                &mut soft_cardinality,
                &mut bound_mapping,
                &mut cardinality_assumptions,
                soft_relax,
                cardinality_relax,
                min_core,
            )?;
            assumptions = Self::weighted_assumptions(
                maxsat,
                &active_soft,
                &cardinality_assumptions,
                &bound_mapping,
                min_weight,
            );
        }
    }

    fn init_relaxation(maxsat: &mut Solver) {
        for i in 0..maxsat.soft_clauses.len() {
            let lit = maxsat.new_lit(false);
            maxsat.soft_clauses[i].relaxation_vars.push(lit);
            maxsat.soft_clauses[i].assumption_var = Some(lit);
        }
    }

    fn rebuild_solver(maxsat: &Solver) -> LngCoreSolver {
        let mut solver = maxsat.new_sat_solver();
        maxsat.reserve_sat_variables(&mut solver);
        for hard in &maxsat.hard_clauses {
            solver.add_clause(hard.clause.clone(), None);
        }
        for soft in &maxsat.soft_clauses {
            let mut clause = soft.clause.clone();
            clause.extend_from_slice(&soft.relaxation_vars);
            solver.add_clause(clause, None);
        }
        solver
    }

    fn iterative_totalizer() -> Encoder {
        Encoder::new(
            CardinalEncoding::Totalizer,
            PbEncoding::Swc,
            IncrementalStrategy::Iterative,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn relax_core(
        solver: &mut LngCoreSolver,
        soft_cardinality: &mut Vec<Encoder>,
        bound_mapping: &mut BTreeMap<LngLit, BoundInfo>,
        cardinality_assumptions: &mut BTreeSet<LngLit>,
        mut soft_relax: Vec<LngLit>,
        cardinality_relax: Vec<LngLit>,
        weight: u64,
    ) -> LngResult<()> {
        if soft_relax.len() == 1 && cardinality_relax.is_empty() {
            solver.add_clause(vec![soft_relax[0]], None);
        }
        soft_relax.extend(cardinality_relax);
        if soft_relax.len() > 1 {
            let mut encoder = Self::iterative_totalizer();
            encoder.build_cardinality(solver, &soft_relax, 1)?;
            let out = encoder.outputs()?[1];
            soft_cardinality.push(encoder);
            bound_mapping.insert(
                out,
                BoundInfo {
                    id: soft_cardinality.len() - 1,
                    bound: 1,
                    weight,
                },
            );
            cardinality_assumptions.insert(out);
        }
        Ok(())
    }

    fn increase_bound(
        solver: &mut LngCoreSolver,
        soft_cardinality: &mut [Encoder],
        bound_mapping: &mut BTreeMap<LngLit, BoundInfo>,
        cardinality_assumptions: &mut BTreeSet<LngLit>,
        info: BoundInfo,
        weight: u64,
    ) -> LngResult<()> {
        let lits = soft_cardinality[info.id].lits()?.to_vec();
        let next_bound = info.bound + 1;
        soft_cardinality[info.id].inc_update_cardinality(
            solver,
            &[],
            &lits,
            next_bound,
            &mut Vec::new(),
        )?;
        let outputs = soft_cardinality[info.id].outputs()?;
        if next_bound < outputs.len() {
            let out = outputs[next_bound];
            bound_mapping.insert(
                out,
                BoundInfo {
                    id: info.id,
                    bound: next_bound,
                    weight,
                },
            );
            cardinality_assumptions.insert(out);
        }
        Ok(())
    }

    fn unweighted_assumptions(
        maxsat: &Solver,
        active_soft: &[bool],
        cardinality_assumptions: &BTreeSet<LngLit>,
    ) -> Vec<LngLit> {
        maxsat
            .soft_clauses
            .iter()
            .zip(active_soft)
            .filter(|(_, active)| !**active)
            .map(|(clause, _)| not(clause.assumption_var.unwrap()))
            .chain(cardinality_assumptions.iter().copied().map(not))
            .collect()
    }

    fn weighted_assumptions(
        maxsat: &Solver,
        active_soft: &[bool],
        cardinality_assumptions: &BTreeSet<LngLit>,
        bound_mapping: &BTreeMap<LngLit, BoundInfo>,
        min_weight: u64,
    ) -> Vec<LngLit> {
        maxsat
            .soft_clauses
            .iter()
            .zip(active_soft)
            .filter(|(clause, active)| !**active && clause.weight >= min_weight)
            .map(|(clause, _)| not(clause.assumption_var.unwrap()))
            .chain(
                cardinality_assumptions
                    .iter()
                    .filter(|lit| bound_mapping[*lit].weight >= min_weight)
                    .copied()
                    .map(not),
            )
            .collect()
    }

    fn find_next_weight_diversity(
        maxsat: &Solver,
        weight: u64,
        cardinality_assumptions: &BTreeSet<LngLit>,
        bound_mapping: &BTreeMap<LngLit, BoundInfo>,
    ) -> u64 {
        let mut next_weight = weight;
        let mut find_next = false;
        loop {
            if maxsat.nb_satisfiable > 1 || find_next {
                next_weight = Self::find_next_weight(
                    maxsat,
                    next_weight,
                    cardinality_assumptions,
                    bound_mapping,
                );
            }
            let mut count = 0usize;
            let mut weights = BTreeSet::new();
            for clause in &maxsat.soft_clauses {
                if clause.weight >= next_weight {
                    count += 1;
                    weights.insert(clause.weight);
                }
            }
            for lit in cardinality_assumptions {
                let info = bound_mapping[lit];
                if info.weight >= next_weight {
                    count += 1;
                    weights.insert(info.weight);
                }
            }
            if count == maxsat.soft_clauses.len() + cardinality_assumptions.len()
                || count.saturating_mul(4) > weights.len().saturating_mul(5)
            {
                return next_weight;
            }
            if maxsat.nb_satisfiable == 1 && !find_next {
                find_next = true;
            }
        }
    }

    fn find_next_weight(
        maxsat: &Solver,
        weight: u64,
        cardinality_assumptions: &BTreeSet<LngLit>,
        bound_mapping: &BTreeMap<LngLit, BoundInfo>,
    ) -> u64 {
        maxsat
            .soft_clauses
            .iter()
            .map(|clause| clause.weight)
            .chain(
                cardinality_assumptions
                    .iter()
                    .map(|lit| bound_mapping[lit].weight),
            )
            .filter(|candidate| *candidate < weight)
            .max()
            .unwrap_or(1)
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
        self.solver.as_ref().expect("OLL solver is initialized")
    }

    fn solver_mut(&mut self) -> &mut LngCoreSolver {
        self.solver.as_mut().expect("OLL solver is initialized")
    }
}

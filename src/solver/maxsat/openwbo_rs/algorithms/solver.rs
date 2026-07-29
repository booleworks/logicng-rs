use super::super::encoding::Encoder;
use crate::backends::MaxSatResult;
use crate::datastructures::Model;
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::handlers::CancelableResult;
use crate::solver::lng_core_solver::{mk_lit, sign, var, LngCoreSolver, LngLit, LngVar};
use crate::solver::maxsat::openwbo_rs::config::OpenWboConfig;
use crate::solver::maxsat::{IncrementalStrategy, MaxSatError};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProblemType {
    Unweighted,
    Weighted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct HardClause {
    pub(crate) clause: Vec<LngLit>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SoftClause {
    pub(crate) clause: Vec<LngLit>,
    pub(crate) weight: u64,
    pub(crate) assumption_var: Option<LngLit>,
    pub(crate) relaxation_vars: Vec<LngLit>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MaxSatState {
    pub(crate) state_id: usize,
    pub(crate) nb_vars: usize,
    pub(crate) nb_hard: usize,
    pub(crate) nb_soft: usize,
    pub(crate) ub_cost: u64,
    pub(crate) current_weight: u64,
    pub(crate) soft_weights: Vec<u64>,
}

pub(crate) struct Solver {
    pub(crate) encoder: Encoder,
    pub(crate) config: OpenWboConfig,
    pub(crate) incremental_strategy: IncrementalStrategy,
    pub(crate) status: MaxSatResult,
    pub(crate) model: Vec<bool>,
    pub(crate) var2index: BTreeMap<Variable, usize>,
    pub(crate) index2var: BTreeMap<usize, Variable>,
    pub(crate) soft_clauses: Vec<SoftClause>,
    pub(crate) hard_clauses: Vec<HardClause>,
    pub(crate) order_weights: Vec<u64>,
    pub(crate) problem_type: ProblemType,
    pub(crate) nb_vars: usize,
    pub(crate) nb_initial_variables: usize,
    pub(crate) nb_cores: u64,
    pub(crate) nb_symmetry_clauses: u64,
    pub(crate) sum_size_cores: u64,
    pub(crate) nb_satisfiable: u64,
    pub(crate) ub_cost: u64,
    pub(crate) lb_cost: u64,
    pub(crate) current_weight: u64,
    valid_states: Vec<usize>,
    next_state_id: usize,
}

impl Solver {
    pub(crate) fn new(config: &OpenWboConfig) -> Self {
        Self {
            encoder: Encoder::from_config(config),
            config: config.clone(),
            incremental_strategy: config.incremental_strategy,
            status: MaxSatResult::Undef,
            model: Vec::new(),
            var2index: BTreeMap::new(),
            index2var: BTreeMap::new(),
            soft_clauses: Vec::new(),
            hard_clauses: Vec::new(),
            order_weights: Vec::new(),
            problem_type: ProblemType::Unweighted,
            nb_vars: 0,
            nb_initial_variables: 0,
            nb_cores: 0,
            nb_symmetry_clauses: 0,
            sum_size_cores: 0,
            nb_satisfiable: 0,
            ub_cost: 0,
            lb_cost: 0,
            current_weight: 1,
            valid_states: Vec::new(),
            next_state_id: 0,
        }
    }

    pub(crate) fn save_state(&mut self) -> MaxSatState {
        let state_id = self.next_state_id;
        self.next_state_id += 1;
        self.valid_states.push(state_id);
        MaxSatState {
            state_id,
            nb_vars: self.nb_vars,
            nb_hard: self.hard_clauses.len(),
            nb_soft: self.soft_clauses.len(),
            ub_cost: self.ub_cost,
            current_weight: self.current_weight,
            soft_weights: self
                .soft_clauses
                .iter()
                .map(|clause| clause.weight)
                .collect(),
        }
    }

    pub(crate) fn load_state(&mut self, state: &MaxSatState) -> LngResult<()> {
        let Some(position) = self
            .valid_states
            .iter()
            .rposition(|id| *id == state.state_id)
        else {
            return Err(MaxSatError::InvalidSolverState.into());
        };
        self.valid_states.truncate(position + 1);
        self.hard_clauses.truncate(state.nb_hard);
        self.soft_clauses.truncate(state.nb_soft);
        self.order_weights.clear();
        for i in state.nb_vars..self.nb_vars {
            if let Some(var) = self.index2var.remove(&i) {
                self.var2index.remove(&var);
            }
        }
        self.nb_vars = state.nb_vars;
        self.nb_cores = 0;
        self.nb_symmetry_clauses = 0;
        self.sum_size_cores = 0;
        self.nb_satisfiable = 0;
        self.ub_cost = state.ub_cost;
        self.lb_cost = 0;
        self.current_weight = state.current_weight;
        for (clause, weight) in self.soft_clauses.iter_mut().zip(&state.soft_weights) {
            clause.relaxation_vars.clear();
            clause.weight = *weight;
            clause.assumption_var = None;
        }
        self.model.clear();
        Ok(())
    }

    pub(crate) fn new_var(&mut self) -> LngVar {
        let var = LngVar(self.nb_vars);
        self.nb_vars += 1;
        var
    }

    pub(crate) fn new_lit(&mut self, sign: bool) -> LngLit {
        mk_lit(self.new_var(), sign)
    }

    pub(crate) fn new_sat_solver(&self) -> LngCoreSolver {
        LngCoreSolver::new()
    }

    pub(crate) fn reserve_sat_variables(&self, solver: &mut LngCoreSolver) {
        for _ in 0..self.nb_vars {
            solver.new_var(true, true);
        }
    }

    pub(crate) fn add_hard_clause(&mut self, clause: Vec<LngLit>) {
        self.hard_clauses.push(HardClause { clause });
    }

    pub(crate) fn add_soft_clause(&mut self, weight: u64, clause: Vec<LngLit>) {
        self.set_current_weight(weight);
        self.update_sum_weights(weight);
        if weight != 1 {
            self.problem_type = ProblemType::Weighted;
        }
        self.soft_clauses.push(SoftClause {
            clause,
            weight,
            assumption_var: None,
            relaxation_vars: Vec::new(),
        });
    }

    pub(crate) fn add_formula_clause(
        &mut self,
        weight: Option<u64>,
        formula: EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        let clause = formula
            .literals_for_clause_or_term(f)?
            .into_iter()
            .map(|lit| self.literal(lit))
            .collect();
        match weight {
            Some(weight) => self.add_soft_clause(weight, clause),
            None => self.add_hard_clause(clause),
        }
        Ok(())
    }

    pub(crate) fn literal(&mut self, lit: Literal) -> LngLit {
        let variable = lit.variable();
        let index = if let Some(index) = self.var2index.get(&variable) {
            *index
        } else {
            let index = self.new_var().0;
            self.var2index.insert(variable, index);
            self.index2var.insert(index, variable);
            index
        };
        mk_lit(LngVar(index), !lit.phase())
    }

    pub(crate) fn is_bmo(&mut self, cache: bool) -> bool {
        let mut bmo = true;
        let mut nb_partition_weights = BTreeMap::<u64, u64>::new();
        for clause in &self.soft_clauses {
            *nb_partition_weights.entry(clause.weight).or_default() += 1;
        }
        self.order_weights = nb_partition_weights.keys().rev().copied().collect();

        let mut total_weights = nb_partition_weights
            .iter()
            .map(|(weight, count)| weight.saturating_mul(*count))
            .sum::<u64>();
        for weight in &self.order_weights {
            total_weights =
                total_weights.saturating_sub(weight.saturating_mul(nb_partition_weights[weight]));
            if *weight < total_weights {
                bmo = false;
                break;
            }
        }
        if !cache {
            self.order_weights.clear();
        }
        bmo
    }

    pub(crate) fn save_model(&mut self, current_model: &[bool]) {
        self.model.clear();
        self.model.extend(
            current_model
                .iter()
                .take(self.nb_initial_variables)
                .copied(),
        );
    }

    pub(crate) fn compute_cost_model(&self, current_model: &[bool], weight: Option<u64>) -> u64 {
        let mut current_cost = 0u64;
        for soft_clause in &self.soft_clauses {
            if weight.is_some_and(|weight| soft_clause.weight != weight) {
                continue;
            }
            let unsatisfied = !soft_clause.clause.iter().any(|&lit| {
                let var = var(lit).0;
                sign(lit) != current_model[var]
            });
            if unsatisfied {
                current_cost = current_cost.saturating_add(soft_clause.weight);
            }
        }
        current_cost
    }

    pub(crate) fn current_model(&self) -> Model {
        self.model_from_values(&self.model, None)
    }

    pub(crate) fn optimum(&self) -> MaxSatResult {
        MaxSatResult::Optimum {
            bound: self.ub_cost,
            model: self.current_model(),
        }
    }

    pub(crate) fn optimum_result(&self) -> CancelableResult<MaxSatResult> {
        CancelableResult::Ok(self.optimum())
    }

    pub(crate) const fn unsatisfiable() -> CancelableResult<MaxSatResult> {
        CancelableResult::Ok(MaxSatResult::Unsatisfiable)
    }

    fn update_sum_weights(&mut self, weight: u64) {
        self.ub_cost = self.ub_cost.saturating_add(weight);
    }

    fn set_current_weight(&mut self, weight: u64) {
        if weight > self.current_weight {
            self.current_weight = weight;
        }
    }

    fn model_from_values(
        &self,
        values: &[bool],
        selector_variables: Option<&BTreeSet<Variable>>,
    ) -> Model {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for (index, value) in values.iter().enumerate() {
            let Some(variable) = self.index2var.get(&index).copied() else {
                continue;
            };
            if selector_variables.is_some_and(|selectors| selectors.contains(&variable)) {
                continue;
            }
            if *value {
                pos.push(variable);
            } else {
                neg.push(variable);
            }
        }
        Model::new(pos, neg)
    }

    fn filter_model(model: &Model, selector_variables: &BTreeSet<Variable>) -> Model {
        let pos = model
            .pos()
            .iter()
            .filter(|variable| !selector_variables.contains(variable))
            .copied()
            .collect::<Vec<_>>();
        let neg = model
            .neg()
            .iter()
            .filter(|variable| !selector_variables.contains(variable))
            .copied()
            .collect::<Vec<_>>();
        Model::new(pos, neg)
    }
}

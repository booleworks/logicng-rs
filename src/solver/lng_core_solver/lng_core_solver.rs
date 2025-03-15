use itertools::Itertools;

use crate::backbones::Backbone;
use crate::handlers::{ComputationHandler, LngComputation, LngEvent, LngResult};
use crate::solver::lng_core_solver::not;
use std::cmp::Ordering::{Greater, Less};
use std::cmp::{min, Ordering};
use std::collections::{BTreeSet, HashMap};
use std::error::Error;

use crate::collections::LNG_VEC_INIT_SIZE;
use crate::formulas::{FormulaFactory, Literal, Variable};
use crate::propositions::Proposition;

use super::functions::backbone_function::BackboneType;
use super::{
    mk_lit, sign, var, BoundedQueue, ClauseMinimization, ClauseRef, LngClause, LngHeap, LngLit, LngState, LngVar, LngVariable, LngWatcher,
    ProofInformation, SatSolverConfig, SolverState, Tristate,
};

pub const RATIO_REMOVE_CLAUSES: usize = 2;
pub const LB_BLOCKING_RESTART: usize = 10_000;

pub const AUX_LNG_CORE_SOLVER: &str = "LNG_CORE_SOLVER";

#[allow(clippy::struct_excessive_bools)]
pub struct LngCoreSolver<B> {
    pub(crate) config: SatSolverConfig,

    // mapping of variable names to variable indices
    pub(crate) var2idx: HashMap<Variable, LngVar>,
    pub(crate) idx2var: HashMap<LngVar, Variable>,
    pub(crate) aux2idx: HashMap<Variable, LngVar>,
    pub(crate) idx2aux: HashMap<LngVar, Variable>,

    pub(crate) valid_states: Vec<LngState>,
    pub(crate) next_state_id: usize,

    // internal solver state
    pub(crate) ok: bool,
    pub(crate) qhead: usize,
    pub(crate) unit_clauses: Vec<LngLit>,
    pub(crate) all_clauses: Vec<LngClause>,
    pub(crate) clauses: Vec<ClauseRef>,
    pub(crate) learnts: Vec<ClauseRef>,
    pub(crate) watches: Vec<Vec<LngWatcher>>,
    pub(crate) vars: Vec<LngVariable>,
    pub(crate) order_heap: LngHeap,
    pub(crate) trail: Vec<LngLit>,
    pub(crate) trail_lim: Vec<usize>,
    pub(crate) model: Vec<bool>,
    pub(crate) assumptions_conflict: Vec<LngLit>,
    pub(crate) assumptions: Vec<LngLit>,
    pub(crate) assumption_propositions: Vec<Proposition<B>>,
    pub(crate) seen: Vec<bool>,
    pub(crate) analyze_bt_level: usize,
    pub(crate) cla_inc: f64,
    pub(crate) var_inc: f64,
    pub(crate) var_decay: f64,
    pub(crate) clauses_literals: usize,
    pub(crate) learnts_literals: usize,

    // Proof generating information
    pub(crate) pg_original_clauses: Vec<ProofInformation<B>>,
    pub(crate) pg_proof: Vec<Vec<isize>>,

    // backbone computation
    pub(crate) computing_backbone: bool,
    pub(crate) backbone_candidates: Vec<LngLit>,
    pub(crate) backbone_assumptions: Vec<LngLit>,
    pub(crate) backbone_map: HashMap<LngVar, Tristate>,

    // Selection order
    pub(crate) selection_order: Vec<LngLit>,
    pub(crate) selection_order_idx: usize,

    // internal glucose-related state
    pub(crate) watches_bin: Vec<Vec<LngWatcher>>,
    pub(crate) perm_diff: Vec<isize>,
    pub(crate) last_decision_level: Vec<LngLit>,
    pub(crate) lbd_queue: BoundedQueue<usize>,
    pub(crate) trail_queue: BoundedQueue<usize>,
    pub(crate) my_flag: isize,
    pub(crate) analyze_lbd: usize,
    pub(crate) nb_clauses_before_reduce: usize,
    pub(crate) conflicts: usize,
    pub(crate) conflicts_restarts: usize,
    pub(crate) sum_lbd: usize,
    pub(crate) cur_restart: usize,
}

impl<B> Default for LngCoreSolver<B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<B> LngCoreSolver<B> {
    /// Constructs a new solver with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self::new_with_config(SatSolverConfig::default())
    }

    /// Constructs a new solver with custom configuration.
    pub fn new_with_config(mut config: SatSolverConfig) -> Self {
        config.use_at_most_clauses = !config.proof_generation && config.use_at_most_clauses;
        let mut lbd_queue = BoundedQueue::new();
        lbd_queue.init_size(config.low_level_config().size_lbd_queue());
        let mut trail_queue = BoundedQueue::new();
        trail_queue.init_size(config.low_level_config().size_trail_queue());
        Self {
            var2idx: HashMap::new(),
            idx2var: HashMap::new(),
            aux2idx: HashMap::new(),
            idx2aux: HashMap::new(),
            valid_states: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            next_state_id: 0,
            ok: true,
            qhead: 0,
            unit_clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            all_clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            learnts: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            watches: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            vars: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            order_heap: LngHeap::new(),
            trail: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            trail_lim: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            model: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            assumptions_conflict: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            assumptions: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            assumption_propositions: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            seen: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            analyze_bt_level: 0,
            cla_inc: 1.0,
            var_inc: config.low_level_config().var_inc(),
            var_decay: config.low_level_config().var_decay(),
            clauses_literals: 0,
            learnts_literals: 0,
            pg_original_clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            pg_proof: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            computing_backbone: false,
            backbone_candidates: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            backbone_assumptions: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            backbone_map: HashMap::new(),
            selection_order: Vec::new(),
            selection_order_idx: 0,
            watches_bin: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            perm_diff: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            last_decision_level: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            lbd_queue,
            trail_queue,
            my_flag: 0,
            analyze_lbd: 0,
            nb_clauses_before_reduce: config.low_level_config().first_reduce_db(),
            conflicts: 0,
            conflicts_restarts: 0,
            sum_lbd: 0,
            cur_restart: 1,
            config,
        }
    }

    pub(crate) fn c(&self, cls: ClauseRef) -> &LngClause {
        &self.all_clauses[cls.0]
    }

    pub(crate) fn c_mut(&mut self, cls: ClauseRef) -> &mut LngClause {
        &mut self.all_clauses[cls.0]
    }

    pub(crate) fn v(&self, lit: LngLit) -> &LngVariable {
        &self.vars[var(lit).0]
    }

    pub(crate) fn v_mut(&mut self, lit: LngLit) -> &mut LngVariable {
        &mut self.vars[var(lit).0]
    }

    pub(crate) fn value(&self, lit: LngLit) -> Tristate {
        let val = self.v(lit).assignment;
        if sign(lit) {
            val.negate()
        } else {
            val
        }
    }

    /// Returns the internal representation of a variable, if there is one.
    pub fn idx_for_variable(&self, variable: Variable) -> Option<LngVar> {
        self.var2idx.get(&variable).or_else(|| self.aux2idx.get(&variable)).map(ToOwned::to_owned)
    }

    /// Returns the original variable of an internal representation.
    ///
    /// It creates a new auxiliary variable if no external variable is registered for the index.
    pub fn variable_for_idx(&mut self, var: LngVar, f: &FormulaFactory) -> Variable {
        if self.idx2var.contains_key(&var) {
            self.idx2var[&var]
        } else if self.idx2aux.contains_key(&var) {
            self.idx2aux[&var]
        } else {
            let aux_var = f.new_auxiliary_variable(AUX_LNG_CORE_SOLVER);
            self.add_aux_variable(aux_var, var);
            aux_var
        }
    }

    /// Registers a new variable to this solver.
    pub fn add_variable(&mut self, variable: Variable, id: LngVar) {
        self.var2idx.insert(variable, id);
        self.idx2var.insert(id, variable);
    }

    pub(crate) fn add_aux_variable(&mut self, variable: Variable, id: LngVar) {
        self.aux2idx.insert(variable, id);
        self.idx2aux.insert(id, variable);
    }

    /// Creates a new internal variable.
    pub fn new_var(&mut self, sign: bool, dvar: bool) -> LngVar {
        let v = LngVar(self.vars.len());
        self.vars.push(LngVariable::new(sign, dvar));
        self.watches.push(Vec::with_capacity(LNG_VEC_INIT_SIZE));
        self.watches.push(Vec::with_capacity(LNG_VEC_INIT_SIZE));
        self.seen.push(false);
        self.watches_bin.push(Vec::with_capacity(LNG_VEC_INIT_SIZE));
        self.watches_bin.push(Vec::with_capacity(LNG_VEC_INIT_SIZE));
        self.perm_diff.push(0);
        self.insert_var_order(v);
        v
    }

    pub(crate) fn add_new_clause(&mut self, clause: LngClause) -> ClauseRef {
        let index = self.all_clauses.len();
        self.all_clauses.push(clause);
        ClauseRef(index)
    }

    pub fn add_unit_clause(&mut self, lit: LngLit, proposition: Option<Proposition<B>>) {
        let unit = vec![lit];
        self.add_clause(unit, proposition);
    }

    /// Adds a clause to this solver.
    pub fn add_clause(&mut self, mut ps: Vec<LngLit>, proposition: Option<Proposition<B>>) -> bool {
        assert!(self.decision_level() == 0);

        if self.config.proof_generation {
            let pg_clause = ps.iter().map(|&p| (var(p).0 as isize + 1) * (-2 * isize::from(sign(p)) + 1)).collect();
            self.pg_original_clauses.push(ProofInformation::new(pg_clause, proposition));
        }
        if !self.ok {
            return false;
        }
        ps.sort_unstable();

        let flag = self.config.proof_generation && ps.iter().any(|&l| self.value(l) != Tristate::Undef);
        let oc = if flag { Some(ps.clone()) } else { None };

        let mut j = 0usize;
        let mut p = LngLit::UNDEF;
        for i in 0..ps.len() {
            let elem = ps[i];
            let elem_value = self.value(elem);
            if elem_value == Tristate::True || elem == not(p) {
                return true;
            } else if elem_value != Tristate::False && elem != p {
                p = elem;
                ps[j] = p;
                j += 1;
            }
        }
        ps.truncate(j);

        if flag {
            let mut vec = Vec::<isize>::with_capacity(ps.len() + 1);
            vec.push(1);
            for &elem in &ps {
                vec.push((var(elem).0 as isize + 1) * (-2 * isize::from(sign(elem)) + 1));
            }
            self.pg_proof.push(vec);

            let mut vec = Vec::<isize>::with_capacity(oc.as_ref().unwrap().len() + 1);
            vec.push(-1);
            for elem in oc.unwrap() {
                vec.push((var(elem).0 as isize + 1) * (-2 * isize::from(sign(elem)) + 1));
            }
            self.pg_proof.push(vec);
        }

        if ps.is_empty() {
            self.ok = false;
            if self.config.proof_generation {
                self.pg_proof.push(vec![0]);
            }
            return false;
        } else if ps.len() == 1 {
            let lit = ps[0];
            self.unchecked_enqueue(lit, None);
            self.ok = self.propagate().is_none();
            self.unit_clauses.push(lit);
            if !self.ok && self.config.proof_generation {
                self.pg_proof.push(vec![0]);
            }
            return self.ok;
        }
        let clause = LngClause::new(ps, None, false);
        let c = self.add_new_clause(clause);
        self.clauses.push(c);
        self.attach_clause(c);
        true
    }

    /// Solves the formula on this solver.
    pub fn internal_solve(&mut self, handler: &mut dyn ComputationHandler) -> LngResult<bool> {
        if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Sat)) {
            return LngResult::Canceled(LngEvent::ComputationStarted(LngComputation::Sat));
        }

        self.model.clear();
        self.assumptions_conflict.clear();
        if !self.ok {
            return LngResult::Ok(false);
        }
        let mut status = LngResult::Ok(Tristate::Undef);
        while status == LngResult::Ok(Tristate::Undef) {
            status = self.search(handler);
        }

        let result = match status {
            LngResult::Ok(s) => s == Tristate::True,
            LngResult::Canceled(lng_event) | LngResult::Partial(_, lng_event) => {
                self.cancel_until(0);
                return LngResult::Canceled(lng_event);
            }
        };

        if self.config.proof_generation && self.assumptions.is_empty() && !result {
            self.pg_proof.push(vec![0]);
        }

        if result {
            self.model = Vec::with_capacity(self.vars.len());
            for v in &self.vars {
                self.model.push(v.assignment == Tristate::True);
            }
        } else if self.assumptions_conflict.is_empty() {
            self.ok = false;
        }
        self.cancel_until(0);

        if !handler.should_resume(LngEvent::ComputationFinished(LngComputation::Sat)) {
            return LngResult::Canceled(LngEvent::ComputationFinished(LngComputation::Sat));
        }
        LngResult::Ok(result)
    }

    /// Solves the formula on this solver with a list of assumptions.
    pub fn internal_solve_with_assumptions(&mut self, handler: &mut dyn ComputationHandler, assumptions: Vec<LngLit>) -> LngResult<bool> {
        self.assumptions = assumptions;
        let result = self.internal_solve(handler);
        self.assumptions.clear();
        result
    }

    pub fn model(&self) -> &[bool] {
        &self.model
    }

    pub const fn ok(&self) -> bool {
        self.ok
    }

    pub fn assumptions_conflict(&self) -> &[LngLit] {
        &self.assumptions_conflict
    }

    pub fn save_state(&mut self) -> SolverState {
        let id = LngState(self.next_state_id);
        self.next_state_id += 1;
        self.valid_states.push(id);
        SolverState {
            id,
            ok: self.ok,
            vars_size: self.vars.len(),
            all_clause_size: self.all_clauses.len(),
            clause_size: self.clauses.len(),
            unit_clause_size: self.unit_clauses.len(),
            pg_original_size: if self.config.proof_generation { self.pg_original_clauses.len() } else { 0 },
            pg_proof_size: if self.config.proof_generation { self.pg_proof.len() } else { 0 },
        }
    }

    pub fn load_state(&mut self, solver_state: &SolverState) -> Result<(), Box<dyn Error>> {
        let mut index = None;
        for (i, &valid_state) in self.valid_states.iter().enumerate().rev() {
            if valid_state == solver_state.id {
                index = Some(i);
                break;
            }
        }
        let Some(index) = index else { return Err("The given solver state is not valid anymore".into()) };
        self.valid_states.truncate(index + 1);
        self.complete_backtrack();
        self.ok = solver_state.ok;
        let new_vars_size = min(solver_state.vars_size, self.vars.len());
        for i in (new_vars_size..self.vars.len()).rev() {
            self.order_heap.remove(LngVar(i), &self.vars);
            let name = self.idx2var.remove(&LngVar(i));
            let name2 = self.idx2aux.remove(&LngVar(i));
            if let Some(n) = name {
                self.var2idx.remove(&n);
            }
            if let Some(n) = name2 {
                self.aux2idx.remove(&n);
            }
        }
        self.vars.truncate(new_vars_size);
        self.perm_diff.truncate(new_vars_size);
        let new_clauses_size = min(solver_state.clause_size, self.clauses.len());
        for i in (new_clauses_size..self.clauses.len()).rev() {
            self.detach_clause(self.clauses[i]);
        }
        self.clauses.truncate(new_clauses_size);
        let mut new_learnts_length = 0;
        for i in 0..self.learnts.len() {
            let l = self.learnts[i];
            let learnt = self.c(l);
            if learnt.learnt_on_state.is_none_or(|s| s <= solver_state.id) {
                self.learnts[new_learnts_length] = l;
                new_learnts_length += 1;
            } else {
                self.detach_clause(l);
            }
        }
        self.learnts.truncate(new_learnts_length);
        self.watches.truncate(new_vars_size * 2);
        self.watches_bin.truncate(new_vars_size * 2);
        self.unit_clauses.truncate(solver_state.unit_clause_size);
        for i in 0..self.unit_clauses.len() {
            if self.ok {
                self.unchecked_enqueue(self.unit_clauses[i], None);
                self.ok = self.propagate().is_none();
            }
        }
        let new_all_clauses_size = min(solver_state.all_clause_size, self.all_clauses.len());
        self.all_clauses.truncate(new_all_clauses_size);
        if self.config.proof_generation {
            let new_pg_original_size = min(solver_state.pg_original_size, self.pg_original_clauses.len());
            self.pg_original_clauses.truncate(new_pg_original_size);
            let new_pg_proof_size = min(solver_state.pg_proof_size, self.pg_proof.len());
            self.pg_proof.truncate(new_pg_proof_size);
        }
        Ok(())
    }

    pub fn n_vars(&self) -> usize {
        self.vars.len()
    }

    pub fn known_variables(&self) -> BTreeSet<Variable> {
        self.var2idx.keys().copied().collect()
    }

    pub fn materialized_auxiliary_variables(&self) -> BTreeSet<Variable> {
        self.aux2idx.keys().copied().collect()
    }

    pub fn materialize_all_variables(&mut self, f: &FormulaFactory) {
        for i in 0..self.vars.len() {
            if !self.idx2var.contains_key(&LngVar(i)) && !self.idx2aux.contains_key(&LngVar(i)) {
                let var = f.new_auxiliary_variable(AUX_LNG_CORE_SOLVER);
                self.add_aux_variable(var, LngVar(i));
            }
        }
    }

    pub(crate) fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub(crate) fn abstract_level(&self, x: LngVar) -> usize {
        1 << (self.vars[x.0].level.unwrap() & 31)
    }

    pub(crate) fn insert_var_order(&mut self, x: LngVar) {
        if !self.order_heap.in_heap(x) && self.vars[x.0].decision {
            self.order_heap.insert(x, &self.vars);
        }
    }

    pub(crate) fn pick_branch_lit(&mut self) -> LngLit {
        if !self.selection_order.is_empty() && self.selection_order_idx < self.selection_order.len() {
            while self.selection_order_idx < self.selection_order.len() {
                let lit = self.selection_order[self.selection_order_idx];
                self.selection_order_idx += 1;
                if self.v(lit).assignment == Tristate::Undef {
                    return lit;
                }
            }
        }
        let mut next: Option<LngVar> = None;
        while next.is_none() || self.vars[next.unwrap().0].assignment != Tristate::Undef || !self.vars[next.unwrap().0].decision {
            if self.order_heap.empty() {
                return LngLit::UNDEF;
            }
            next = Some(self.order_heap.remove_min(&self.vars));
        }
        mk_lit(next.unwrap(), self.vars[next.unwrap().0].polarity)
    }

    pub(crate) fn var_decay_activities(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    pub(crate) fn var_bump_activity(&mut self, v: LngVar, inc: f64) {
        let var = &mut self.vars[v.0];
        var.increment_activity(inc);
        if var.activity > 1e100 {
            for variable in &mut self.vars {
                variable.rescale_activity();
            }
            self.var_inc *= 1e-100;
        }
        if self.order_heap.in_heap(v) {
            self.order_heap.decrease(v, &self.vars);
        }
    }

    pub(crate) fn locked(&self, cls: ClauseRef) -> bool {
        let c = self.c(cls);
        self.value(c.get(0)) == Tristate::True && self.v(c.get(0)).reason.is_some_and(|r| r == cls)
    }

    pub(crate) fn cla_decay_activities(&mut self) {
        self.cla_inc *= 1.0 / self.config.low_level_config().clause_decay();
    }

    pub(crate) fn cla_bump_activity(&mut self, c: ClauseRef) {
        let cls = &mut self.all_clauses[c.0];
        cls.increment_activity(self.cla_inc);
        if cls.activity > 1e20 {
            for clause in &mut self.learnts {
                self.all_clauses[clause.0].rescale_activity();
            }
            self.cla_inc *= 1e-20;
        }
    }

    pub(crate) fn unchecked_enqueue(&mut self, lit: LngLit, reason: Option<ClauseRef>) {
        assert!(self.value(lit) == Tristate::Undef);
        let level = self.decision_level();
        let var = self.v_mut(lit);
        var.assignment = Tristate::from_bool(!sign(lit));
        var.reason = reason;
        var.level = Some(level);
        self.trail.push(lit);
    }

    pub(crate) fn attach_clause(&mut self, clause_ref: ClauseRef) {
        let clause = &self.all_clauses[clause_ref.0];

        if clause.is_at_most {
            if let Some(at_most_watchers) = clause.at_most_watchers {
                for l in &clause.data[..at_most_watchers] {
                    self.watches[l.0].push(LngWatcher { clause_ref, blocking_literal: LngLit::UNDEF });
                }
            }
            self.clauses_literals += clause.len();
        } else {
            assert!(clause.len() > 1);
            let lit0 = clause.get(0);
            let lit1 = clause.get(1);

            if clause.len() == 2 {
                self.watches_bin[not(lit0).0].push(LngWatcher { clause_ref, blocking_literal: lit1 });
                self.watches_bin[not(lit1).0].push(LngWatcher { clause_ref, blocking_literal: lit0 });
            } else {
                self.watches[not(lit0).0].push(LngWatcher { clause_ref, blocking_literal: lit1 });
                self.watches[not(lit1).0].push(LngWatcher { clause_ref, blocking_literal: lit0 });
            }
            if clause.learnt_on_state.is_some() {
                self.learnts_literals += clause.len();
            } else {
                self.clauses_literals += clause.len();
            };
        }
    }

    pub(crate) fn detach_clause(&mut self, c_ref: ClauseRef) {
        self.simple_remove_clause(c_ref);
        let c = &self.all_clauses[c_ref.0];
        if c.learnt_on_state.is_some() {
            self.learnts_literals -= c.len();
        } else {
            self.clauses_literals -= c.len();
        }
    }

    pub(crate) fn remove_clause(&mut self, cls: ClauseRef) {
        let c = &self.c(cls);
        debug_assert!(!c.is_at_most);
        if self.config.proof_generation {
            let mut vec = Vec::<isize>::with_capacity(c.len());
            vec.push(-1);
            for &elem in &c.data {
                vec.push((var(elem).0 as isize + 1) * (-2 * isize::from(sign(elem)) + 1));
            }
            self.pg_proof.push(vec);
        }
        self.detach_clause(cls);
        if self.locked(cls) {
            let c = &self.all_clauses[cls.0];
            self.v_mut(c.get(0)).reason = None;
        }
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn propagate(&mut self) -> Option<ClauseRef> {
        let mut confl: Option<ClauseRef> = None;
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let mut i_ind = 0;
            let mut j_ind = 0;
            for k in 0..self.watches_bin[p.0].len() {
                let watcher_bin = &self.watches_bin[p.0][k];
                let imp = watcher_bin.blocking_literal;
                if self.value(imp) == Tristate::False {
                    return Some(watcher_bin.clause_ref);
                }
                if self.value(imp) == Tristate::Undef {
                    self.unchecked_enqueue(imp, Some(watcher_bin.clause_ref));
                }
            }
            while i_ind < self.watches[p.0].len() {
                let i = &self.watches[p.0][i_ind];
                let blocker = i.blocking_literal;
                if blocker != LngLit::UNDEF && self.value(blocker) == Tristate::True {
                    self.watches[p.0][j_ind] = i.clone();
                    j_ind += 1;
                    i_ind += 1;
                    continue;
                }
                let c_ref = i.clause_ref;
                if self.c(c_ref).is_at_most {
                    let new_watch = self.find_new_watch_for_at_most_clause(c_ref, p);
                    if new_watch == LngLit::UNDEF {
                        if let Some(at_most_watchers) = self.c(c_ref).at_most_watchers {
                            for k in 0..at_most_watchers {
                                let w = self.c(c_ref).get(k);
                                if w != p && self.value(w) != Tristate::False {
                                    assert!(self.value(w) == Tristate::Undef || self.value(w) == Tristate::False);
                                    self.unchecked_enqueue(not(w), Some(c_ref));
                                }
                            }
                        }
                        self.watches[p.0][j_ind] = self.watches[p.0][i_ind].clone();
                        j_ind += 1;
                        i_ind += 1;
                    } else if new_watch == LngLit::ERROR {
                        confl = Some(c_ref);
                        self.qhead = self.trail.len();
                        while i_ind < self.watches[p.0].len() {
                            self.watches[p.0][j_ind] = self.watches[p.0][i_ind].clone();
                            j_ind += 1;
                            i_ind += 1;
                        }
                    } else if new_watch == p {
                        self.watches[p.0][j_ind] = self.watches[p.0][i_ind].clone();
                        j_ind += 1;
                        i_ind += 1;
                    } else {
                        i_ind += 1;
                        let w = LngWatcher { clause_ref: c_ref, blocking_literal: LngLit::UNDEF };
                        self.watches[new_watch.0].push(w);
                    }
                } else {
                    let c = self.c(c_ref);
                    let false_lit = not(p);
                    if c.get(0) == false_lit {
                        let l1 = c.get(1);
                        self.c_mut(c_ref).set(0, l1);
                        self.c_mut(c_ref).set(1, false_lit);
                    }
                    let c = self.c(c_ref);
                    assert!(c.get(1) == false_lit);
                    i_ind += 1;
                    let first = c.get(0);
                    if first != blocker && self.value(first) == Tristate::True {
                        self.watches[p.0][j_ind] = LngWatcher { clause_ref: c_ref, blocking_literal: first };
                        j_ind += 1;
                        continue;
                    }
                    let mut found_watch = false;
                    for k in 2..c.len() {
                        let k_lit = c.get(k);
                        if self.value(k_lit) != Tristate::False {
                            self.all_clauses[c_ref.0].set(1, k_lit);
                            self.all_clauses[c_ref.0].set(k, false_lit);
                            let c = &self.all_clauses[c_ref.0];
                            self.watches[not(c.get(1)).0].push(LngWatcher { clause_ref: c_ref, blocking_literal: first });
                            found_watch = true;
                            break;
                        }
                    }
                    if !found_watch {
                        self.watches[p.0][j_ind] = LngWatcher { clause_ref: c_ref, blocking_literal: first };
                        j_ind += 1;
                        if self.value(first) == Tristate::False {
                            confl = Some(c_ref);
                            self.qhead = self.trail.len();
                            while i_ind < self.watches[p.0].len() {
                                self.watches[p.0].swap(j_ind, i_ind);
                                j_ind += 1;
                                i_ind += 1;
                            }
                        } else {
                            self.unchecked_enqueue(first, Some(c_ref));
                        }
                    }
                }
            }
            self.watches[p.0].truncate(j_ind);
        }
        confl
    }

    pub(crate) fn lit_redundant(&mut self, p: LngLit, abstract_levels: usize, analyze_to_clear: &mut Vec<LngLit>) -> bool {
        let mut analyze_stack = Vec::<LngLit>::with_capacity(analyze_to_clear.len());
        analyze_stack.push(p);
        let top = analyze_to_clear.len();

        while let Some(last) = analyze_stack.pop() {
            let c_ref = self.v(last).reason.expect("expected reason");
            let c = &self.all_clauses[c_ref.0];
            if c.is_at_most {
                for &l in &c.data {
                    if self.value(l) != Tristate::True {
                        continue;
                    }
                    let q = not(l);
                    if !self.seen[var(q).0] && self.v(q).level_greater_zero() {
                        if self.v(q).reason.is_some() && (self.abstract_level(var(q)) & abstract_levels) != 0 {
                            self.seen[var(q).0] = true;
                            analyze_stack.push(q);
                            analyze_to_clear.push(q);
                        } else {
                            for &j in &analyze_to_clear[top..] {
                                self.seen[var(j).0] = false;
                            }
                            analyze_to_clear.truncate(top);
                            return false;
                        }
                    }
                }
            } else {
                if c.len() == 2 && self.value(c.get(0)) == Tristate::False {
                    assert!(self.value(c.get(1)) == Tristate::True);
                    let l0 = c.get(0);
                    let l1 = c.get(1);
                    self.all_clauses[c_ref.0].set(0, l1);
                    self.all_clauses[c_ref.0].set(1, l0);
                }
                for &q in &self.all_clauses[c_ref.0].data[1..] {
                    if !self.seen[var(q).0] && self.v(q).level_greater_zero() {
                        if self.v(q).reason.is_some() && (self.abstract_level(var(q)) & abstract_levels) != 0 {
                            self.seen[var(q).0] = true;
                            analyze_stack.push(q);
                            analyze_to_clear.push(q);
                        } else {
                            for &j in &analyze_to_clear[top..] {
                                self.seen[var(j).0] = false;
                            }
                            analyze_to_clear.truncate(top);
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    pub(crate) fn analyze_assumption_conflict(&mut self, p: LngLit) {
        self.assumptions_conflict.clear();
        self.assumptions_conflict.push(p);
        if self.decision_level() == 0 {
            return;
        }
        let var_p = var(p);
        self.seen[var_p.0] = true;
        for i in (self.trail_lim[0]..self.trail.len()).rev() {
            let x_lit = self.trail[i];
            let x_var = var(x_lit);
            if self.seen[x_var.0] {
                let v = &self.vars[x_var.0];
                if let Some(c_ref) = v.reason {
                    let c = &self.all_clauses[c_ref.0];
                    if c.is_at_most {
                        for &l in &c.data {
                            if self.value(l) == Tristate::True && self.v(l).level_greater_zero() {
                                self.seen[var(l).0] = true;
                            }
                        }
                    } else {
                        let start = if c.len() == 2 { 0 } else { 1 };
                        for &l in &c.data[start..] {
                            if self.v(l).level_greater_zero() {
                                self.seen[var(l).0] = true;
                            }
                        }
                    }
                } else {
                    debug_assert!(v.level_greater_zero());
                    self.assumptions_conflict.push(not(x_lit));
                }
                self.seen[x_var.0] = false;
            }
        }
        self.seen[var_p.0] = false;
    }

    pub(crate) fn cancel_until(&mut self, level: usize) {
        if self.decision_level() > level {
            for c in (self.trail_lim[level]..self.trail.len()).rev() {
                let lit = self.trail[c];
                let x = var(lit);
                let v = &mut self.vars[x.0];
                v.assignment = Tristate::Undef;
                v.polarity = !self.computing_backbone && sign(lit);
                self.insert_var_order(x);
            }
            self.qhead = self.trail_lim[level];
            self.trail.truncate(self.qhead);
            self.trail_lim.truncate(level);
        }
    }

    pub(crate) fn reduce_db(&mut self) {
        self.manual_sort_learnts();
        if self.c(self.learnts[self.learnts.len() / RATIO_REMOVE_CLAUSES]).lbd <= 3 {
            self.nb_clauses_before_reduce += self.config.low_level_config().special_inc_reduce_db();
        }
        if self.c(*self.learnts.last().expect("expected learnt clause")).lbd <= 5 {
            self.nb_clauses_before_reduce += self.config.low_level_config().special_inc_reduce_db();
        }
        let mut limit = self.learnts.len() / 2;
        let mut j = 0;
        for i in 0..self.learnts.len() {
            let c_ref = self.learnts[i];
            let c = self.c(c_ref);
            if c.lbd > 2 && c.len() > 2 && c.can_be_del && !self.locked(c_ref) && i < limit {
                self.remove_clause(c_ref);
            } else {
                if !c.can_be_del {
                    limit += 1;
                }
                self.c_mut(c_ref).can_be_del = true;
                self.learnts.swap(i, j);
                j += 1;
            }
        }
        self.learnts.truncate(j);
    }

    pub const fn pg_original_clauses(&self) -> &Vec<ProofInformation<B>> {
        &self.pg_original_clauses
    }

    pub(crate) fn pg_original_clauses_mut(&mut self) -> &mut Vec<ProofInformation<B>> {
        &mut self.pg_original_clauses
    }

    pub const fn pg_proof(&self) -> &Vec<Vec<isize>> {
        &self.pg_proof
    }

    /// The main search procedure of the CDCL algorithm.
    #[allow(clippy::too_many_lines)]
    pub fn search(&mut self, handler: &mut dyn ComputationHandler) -> LngResult<Tristate> {
        if !self.ok {
            return LngResult::Ok(Tristate::False);
        }
        self.selection_order_idx = 0;
        loop {
            if let Some(confl) = self.propagate() {
                if !handler.should_resume(LngEvent::SatConflictDetected) {
                    return LngResult::Canceled(LngEvent::SatConflictDetected);
                }
                self.conflicts += 1;
                self.conflicts_restarts += 1;
                if self.conflicts % 5000 == 0 && self.var_decay < self.config.low_level_config().max_var_decay() {
                    self.var_decay += 0.01;
                }
                if self.decision_level() == 0 {
                    return LngResult::Ok(Tristate::False);
                }
                self.trail_queue.push(self.trail.len());
                if self.conflicts_restarts > LB_BLOCKING_RESTART
                    && self.lbd_queue.valid()
                    && self.trail.len() as f64 > self.config.low_level_config().factor_k() * self.trail_queue.avg() as f64
                {
                    self.lbd_queue.fast_clear();
                }
                let learnt_clause = self.analyze(confl);
                self.lbd_queue.push(self.analyze_lbd);
                self.sum_lbd += self.analyze_lbd;
                self.cancel_until(self.analyze_bt_level);
                if self.analyze_bt_level < self.selection_order.len() {
                    self.selection_order_idx = self.analyze_bt_level;
                }

                if self.config.proof_generation {
                    let mut vec = Vec::<isize>::with_capacity(learnt_clause.len() + 1);
                    vec.push(1);
                    for &elem in &learnt_clause {
                        vec.push((var(elem).0 as isize + 1) * (-2 * isize::from(sign(elem)) + 1));
                    }
                    self.pg_proof.push(vec);
                }

                if learnt_clause.len() == 1 {
                    let learnt_lit = learnt_clause[0];
                    self.unchecked_enqueue(learnt_lit, None);
                    self.unit_clauses.push(learnt_lit);
                } else {
                    let mut cr = LngClause::new(learnt_clause, Some(LngState(self.next_state_id)), false);
                    cr.lbd = self.analyze_lbd;
                    cr.one_watched = false;
                    let queue_lit = cr.get(0);
                    let cr_ref = self.add_new_clause(cr);
                    self.learnts.push(cr_ref);
                    self.attach_clause(cr_ref);
                    self.cla_bump_activity(cr_ref);
                    self.unchecked_enqueue(queue_lit, Some(cr_ref));
                }
                self.var_decay_activities();
                self.cla_decay_activities();
            } else {
                if self.lbd_queue.valid()
                    && (self.lbd_queue.avg() as f64 * self.config.low_level_config().factor_k())
                        > (self.sum_lbd as f64 / self.conflicts_restarts as f64)
                {
                    self.lbd_queue.fast_clear();
                    self.cancel_until(0);
                    return LngResult::Ok(Tristate::Undef);
                }
                if self.conflicts >= (self.cur_restart * self.nb_clauses_before_reduce) && !self.learnts.is_empty() {
                    self.cur_restart = (self.conflicts / self.nb_clauses_before_reduce) + 1;
                    self.reduce_db();
                    self.nb_clauses_before_reduce += self.config.low_level_config().inc_reduce_db();
                }
                let mut next = LngLit::UNDEF;
                while self.decision_level() < self.assumptions.len() {
                    let p = self.assumptions[self.decision_level()];
                    match self.value(p) {
                        Tristate::True => self.trail_lim.push(self.trail.len()),
                        Tristate::False => {
                            if self.config.proof_generation {
                                let drup_lit = (var(p).0 as isize + 1) * (-2 * isize::from(sign(p)) + 1);
                                self.pg_original_clauses.push(ProofInformation::new(
                                    Vec::from([drup_lit]),
                                    self.assumption_propositions.get(self.decision_level()).cloned(),
                                ));
                            }
                            self.analyze_assumption_conflict(not(p));
                            return LngResult::Ok(Tristate::False);
                        }
                        Tristate::Undef => {
                            if self.config.proof_generation {
                                let drup_lit = (var(p).0 as isize + 1) * (-2 * isize::from(sign(p)) + 1);
                                self.pg_original_clauses.push(ProofInformation::new(
                                    Vec::from([drup_lit]),
                                    self.assumption_propositions.get(self.decision_level()).cloned(),
                                ));
                            }
                            next = p;
                            break;
                        }
                    }
                }
                if next == LngLit::UNDEF {
                    next = self.pick_branch_lit();
                    if next == LngLit::UNDEF {
                        return LngResult::Ok(Tristate::True);
                    }
                }
                self.trail_lim.push(self.trail.len());
                self.unchecked_enqueue(next, None);
            }
        }
    }

    pub(crate) fn analyze(&mut self, clause_ref: ClauseRef) -> Vec<LngLit> {
        let mut out_learnt = Vec::<LngLit>::with_capacity(LNG_VEC_INIT_SIZE);
        let mut c_ref_option: Option<ClauseRef> = Some(clause_ref);
        let mut path_c = 0;
        let mut p = LngLit::UNDEF;
        out_learnt.push(LngLit::UNDEF);
        let mut first_run = true;
        let mut index = self.trail.len() - 1;

        while first_run || path_c > 0 {
            first_run = false;
            let c_ref = c_ref_option.expect("exptected clause");
            if self.c(c_ref).is_at_most {
                let end = self.c(c_ref).data.len();
                for j in 0..end {
                    let data_lit = self.c(c_ref).data[j];
                    if self.value(data_lit) != Tristate::True {
                        continue;
                    }
                    let q = not(data_lit);
                    if !self.seen[var(q).0] && self.v(q).level_greater_zero() {
                        self.var_bump_activity(var(q), self.var_inc);
                        self.seen[var(q).0] = true;
                        if self.v(q).level.is_some_and(|l| l >= self.decision_level()) {
                            path_c += 1;
                        } else {
                            out_learnt.push(q);
                        }
                    }
                }
            } else {
                let c = self.c(c_ref);
                if p != LngLit::UNDEF && c.len() == 2 && self.value(c.get(0)) == Tristate::False {
                    assert!(self.value(c.get(1)) == Tristate::True);
                    let l0 = c.get(0);
                    let l1 = c.get(1);
                    self.c_mut(c_ref).set(0, l1);
                    self.c_mut(c_ref).set(1, l0);
                }
                let c = self.c(c_ref);
                if c.learnt_on_state.is_some() {
                    self.cla_bump_activity(c_ref);
                } else if !c.seen {
                    self.c_mut(c_ref).seen = true;
                }
                let c = self.c(c_ref);
                if c.learnt_on_state.is_some() && c.lbd > 2 {
                    let nb_levels = self.compute_lbd_with_clause(c_ref);
                    let c = self.c(c_ref);
                    if nb_levels + 1 < c.lbd {
                        if c.lbd <= self.config.low_level_config().lb_lbd_frozen_clause() {
                            self.c_mut(c_ref).can_be_del = false;
                        }
                        self.c_mut(c_ref).lbd = nb_levels;
                    }
                }
                let start = if p == LngLit::UNDEF { 0 } else { 1 };
                let end = self.c(c_ref).data.len();
                for q in start..end {
                    let data_lit = self.c(c_ref).data[q];
                    if !self.seen[var(data_lit).0] && self.v(data_lit).level_greater_zero() {
                        self.var_bump_activity(var(data_lit), self.var_inc);
                        self.seen[var(data_lit).0] = true;
                        if self.v(data_lit).level.is_some_and(|l| l >= self.decision_level()) {
                            path_c += 1;
                            if self.v(data_lit).reason.is_some_and(|r| self.c(r).learnt_on_state.is_some()) {
                                self.last_decision_level.push(data_lit);
                            }
                        } else {
                            out_learnt.push(data_lit);
                        }
                    }
                }
            }
            while !self.seen[var(self.trail[index]).0] {
                index -= 1;
            }
            p = self.trail[index];
            c_ref_option = self.v(p).reason;
            self.seen[var(p).0] = false;
            path_c -= 1;
        }
        out_learnt[0] = not(p);
        self.simplify_clause(&mut out_learnt);
        out_learnt
    }

    fn simplify_clause(&mut self, out_learnt: &mut Vec<LngLit>) {
        let mut j: usize;
        let mut analyze_to_clear = out_learnt.clone();
        match self.config.clause_minimization() {
            ClauseMinimization::Deep => {
                let mut abstract_level = 0;
                for &i in &out_learnt[1..] {
                    abstract_level |= self.abstract_level(var(i));
                }
                j = 1;
                for i in 1..out_learnt.len() {
                    let i_lit = out_learnt[i];
                    if self.v(i_lit).reason.is_none() || !self.lit_redundant(i_lit, abstract_level, &mut analyze_to_clear) {
                        out_learnt[j] = i_lit;
                        j += 1;
                    }
                }
            }
            ClauseMinimization::Basic => {
                j = 1;
                for i in 1..out_learnt.len() {
                    let i_lit = out_learnt[i];
                    let reason = self.v(i_lit).reason;
                    if let Some(clause_ref) = reason {
                        let c = &self.all_clauses[clause_ref.0];
                        let start = if c.len() == 2 { 0 } else { 1 };
                        for &k in &c.data[start..] {
                            if !self.seen[var(k).0] && self.v(k).level_greater_zero() {
                                out_learnt[j] = i_lit;
                                j += 1;
                                break;
                            }
                        }
                    } else {
                        out_learnt[j] = i_lit;
                        j += 1;
                    }
                }
            }
            ClauseMinimization::None => {
                j = out_learnt.len();
            }
        }
        out_learnt.truncate(j);
        if out_learnt.len() <= self.config.low_level_config().lb_size_minimizing_clause() {
            self.minimisation_with_binary_resolution(out_learnt);
        }
        self.analyze_bt_level = 0;
        if out_learnt.len() > 1 {
            let mut max = 1;
            for k in 2..out_learnt.len() {
                if self.v(out_learnt[k]).level > self.v(out_learnt[max]).level {
                    max = k;
                }
            }
            let p = out_learnt[max];
            out_learnt.swap(max, 1);
            self.analyze_bt_level = self.v(p).level.unwrap();
        }
        self.analyze_lbd = self.compute_lbd(out_learnt);
        for k in 0..self.last_decision_level.len() {
            let reason = self.v(self.last_decision_level[k]).reason.expect("expected reason");
            let reason_clause = &self.all_clauses[reason.0];
            if reason_clause.lbd < self.analyze_lbd {
                self.var_bump_activity(var(self.last_decision_level[k]), self.var_inc);
            }
        }
        self.last_decision_level.clear();
        for i in analyze_to_clear {
            self.seen[var(i).0] = false;
        }
    }

    pub(crate) fn compute_lbd_with_clause(&mut self, c: ClauseRef) -> usize {
        let lits = &self.all_clauses[c.0].data;
        let mut nb_levels = 0;
        self.my_flag += 1;
        for &lit in lits {
            let l = self.v(lit).level.expect("expected level for variable");
            if self.perm_diff[l] != self.my_flag {
                self.perm_diff[l] = self.my_flag;
                nb_levels += 1;
            }
        }
        if !self.config.low_level_config().reduce_on_size() {
            return nb_levels;
        }
        if lits.len() < self.config.low_level_config().reduce_on_size_size() {
            return lits.len();
        }
        lits.len() + nb_levels
    }

    pub(crate) fn compute_lbd(&mut self, lits: &[LngLit]) -> usize {
        let mut nb_levels = 0;
        self.my_flag += 1;
        for &lit in lits {
            let l = self.v(lit).level.expect("expected level for variable");
            if self.perm_diff[l] != self.my_flag {
                self.perm_diff[l] = self.my_flag;
                nb_levels += 1;
            }
        }
        if !self.config.low_level_config().reduce_on_size() {
            return nb_levels;
        }
        if lits.len() < self.config.low_level_config().reduce_on_size_size() {
            return lits.len();
        }
        lits.len() + nb_levels
    }

    pub(crate) fn minimisation_with_binary_resolution(&mut self, out_learnt: &mut Vec<LngLit>) {
        let lbd = self.compute_lbd(out_learnt);
        let p = not(out_learnt[0]);
        if lbd <= self.config.low_level_config().lb_lbd_minimizing_clause() {
            self.my_flag += 1;
            for &i in &out_learnt[1..] {
                self.perm_diff[var(i).0] = self.my_flag;
            }
            let mut nb = 0;
            for wbin in &self.watches_bin[p.0] {
                let imp = wbin.blocking_literal;
                if self.perm_diff[var(imp).0] == self.my_flag && self.value(imp) == Tristate::True {
                    nb += 1;
                    self.perm_diff[var(imp).0] = self.my_flag - 1;
                }
            }
            let mut l = out_learnt.len() - 1;
            if nb > 0 {
                let mut i = 1;
                while i < out_learnt.len() - nb {
                    if self.perm_diff[var(out_learnt[i]).0] != self.my_flag {
                        out_learnt.swap(l, i);
                        l -= 1;
                        i -= 1;
                    }
                    i += 1;
                }
                out_learnt.truncate(out_learnt.len() - nb);
            }
        }
    }

    pub(crate) fn complete_backtrack(&mut self) {
        for v in 0..self.vars.len() {
            let var = &mut self.vars[v];
            var.assignment = Tristate::Undef;
            var.reason = None;
            if !self.order_heap.in_heap(LngVar(v)) && var.decision {
                self.order_heap.insert(LngVar(v), &self.vars);
            }
        }
        self.trail.clear();
        self.trail_lim.clear();
        self.qhead = 0;
    }

    pub(crate) fn simple_remove_clause(&mut self, clause: ClauseRef) {
        let c = &self.all_clauses[clause.0];
        if c.is_at_most {
            for i in 0..c.at_most_watchers.expect("expected at-most watchers") {
                let compare = LngWatcher { clause_ref: clause, blocking_literal: c.get(i) };
                let index = self.watches[i].iter().find_position(|e| e.clause_ref == compare.clause_ref);
                if let Some((index, _)) = index {
                    self.watches[i].remove(index);
                }
            }
        } else if c.len() == 2 {
            let lit = not(c.get(0));
            let compare = LngWatcher { clause_ref: clause, blocking_literal: c.get(1) };
            let index = self.watches_bin[lit.0].iter().find_position(|e| e.clause_ref == compare.clause_ref);
            if let Some((index, _)) = index {
                self.watches_bin[lit.0].remove(index);
            }

            let lit = not(c.get(1));
            let compare = LngWatcher { clause_ref: clause, blocking_literal: c.get(0) };
            let index = self.watches_bin[lit.0].iter().find_position(|e| e.clause_ref == compare.clause_ref);
            if let Some((index, _)) = index {
                self.watches_bin[lit.0].remove(index);
            }
        } else {
            let lit = not(c.get(0));
            let compare = LngWatcher { clause_ref: clause, blocking_literal: c.get(1) };
            let index = self.watches[lit.0].iter().find_position(|e| e.clause_ref == compare.clause_ref);
            if let Some((index, _)) = index {
                self.watches[lit.0].remove(index);
            }

            let lit = not(c.get(1));
            let compare = LngWatcher { clause_ref: clause, blocking_literal: c.get(0) };
            let index = self.watches[lit.0].iter().find_position(|e| e.clause_ref == compare.clause_ref);
            if let Some((index, _)) = index {
                self.watches[lit.0].remove(index);
            }
        }
    }

    pub fn add_at_most(&mut self, mut ps: Vec<LngLit>, rhs: usize) {
        let mut k = rhs;
        assert!(self.decision_level() == 0);
        if !self.ok {
            return;
        }
        let mut p = LngLit::UNDEF;
        let mut j = 0;
        for i in 0..ps.len() {
            if self.value(ps[i]) == Tristate::True {
                k -= 1;
            } else if ps[i] == not(p) {
                p = ps[i];
                j -= 1;
                k -= 1;
            } else if self.value(ps[i]) != Tristate::False {
                p = ps[i];
                ps[j] = p;
                j += 1;
            }
        }
        ps.truncate(j);
        if k >= ps.len() {
            return;
        }
        if k == 0 {
            for &i in &ps {
                self.unchecked_enqueue(not(i), None);
                self.unit_clauses.push(not(i));
            }
            self.ok = self.propagate().is_none();
            return;
        }
        let at_most_watchers = ps.len() - k as usize + 1;
        let mut cr = LngClause::new(ps, None, true);
        cr.at_most_watchers = Some(at_most_watchers);
        let c_ref = self.add_new_clause(cr);
        self.clauses.push(c_ref);
        self.attach_clause(c_ref);
    }

    pub(crate) fn find_new_watch_for_at_most_clause(&mut self, clause: ClauseRef, p: LngLit) -> LngLit {
        let c = &self.c(clause);
        assert!(c.is_at_most);
        let mut num_false = 0;
        let mut num_true = 0;
        let at_most_watchers = c.at_most_watchers.expect("exptected at-most watchers");
        let max_true = c.len() - at_most_watchers + 1;
        for q in 0..at_most_watchers {
            match self.value(c.get(q)) {
                Tristate::Undef => {}
                Tristate::False => {
                    num_false += 1;
                    if num_false >= at_most_watchers - 1 {
                        return p;
                    }
                }
                Tristate::True => {
                    num_true += 1;
                    if num_true > max_true {
                        return LngLit::ERROR;
                    }
                    if c.get(q) == p {
                        for next in at_most_watchers..c.len() {
                            if self.value(c.get(next)) != Tristate::True {
                                let new_watch = c.get(next);
                                let tmp = c.get(q);
                                self.c_mut(clause).set(next, tmp);
                                self.c_mut(clause).set(q, new_watch);
                                return new_watch;
                            }
                        }
                    }
                }
            }
        }
        if num_true > 1 {
            LngLit::ERROR
        } else {
            LngLit::UNDEF
        }
    }

    pub fn convert_internal_model(&mut self, internal_model: &[bool], relevant_indices: &[LngVar], f: &FormulaFactory) -> Vec<Literal> {
        let mut literals = Vec::with_capacity(internal_model.len());
        for &index in relevant_indices {
            if index != LngVar::UNDEF {
                if internal_model[index.0] {
                    literals.push(self.variable_for_idx(index, f).pos_lit());
                } else {
                    literals.push(self.variable_for_idx(index, f).neg_lit());
                }
            }
        }
        literals
    }

    pub fn convert_internal_model_on_solver(&mut self, relevant_indices: &[LngVar], f: &FormulaFactory) -> Vec<Literal> {
        let mut literals = Vec::with_capacity(self.model.len());
        for &index in relevant_indices {
            if index != LngVar::UNDEF {
                if self.model[index.0] {
                    literals.push(self.variable_for_idx(index, f).pos_lit());
                } else {
                    literals.push(self.variable_for_idx(index, f).neg_lit());
                }
            }
        }
        literals
    }

    /// Returns the unit propagated literals on level zero.
    pub fn up_zero_literals(&self) -> Vec<LngLit> {
        self.trail.iter().take_while(|&&lit| !self.v(lit).level_greater_zero()).copied().collect()
    }

    /// Computes the backbone on this solver.
    pub fn compute_backbone<V, I>(
        &mut self,
        variables: I,
        backbone_type: BackboneType,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<Backbone>
    where
        I: IntoIterator<Item = V> + Copy,
        V: Into<Variable>,
    {
        if !handler.should_resume(LngEvent::ComputationStarted(LngComputation::Backbone)) {
            return LngResult::Canceled(LngEvent::ComputationStarted(LngComputation::Backbone));
        }
        let state_before_backbone = self.save_state();
        let solve_result = self.internal_solve(handler);
        let result = if !solve_result.is_success() {
            LngResult::Canceled(solve_result.cancel_cause().unwrap())
        } else if solve_result.result().unwrap() {
            self.computing_backbone = true;
            let relevant_var_indices = self.get_relevant_var_indices(variables);
            self.init_backbone_ds(&relevant_var_indices);
            let backbone_event = self.compute_backbone_intern(&relevant_var_indices, backbone_type, handler);
            let r = backbone_event.map_or_else(|| LngResult::Ok(self.build_backbone(variables, backbone_type)), LngResult::Canceled);
            self.computing_backbone = false;
            r
        } else {
            LngResult::Ok(Backbone::new_unsat())
        };
        self.load_state(&state_before_backbone).expect("Controlled creation of state");
        result
    }

    pub fn get_relevant_var_indices<V, I>(&self, variables: I) -> Vec<LngVar>
    where
        I: IntoIterator<Item = V>,
        V: Into<Variable>,
    {
        variables.into_iter().filter_map(|v| self.idx_for_variable(v.into())).collect()
    }

    pub(crate) fn init_backbone_ds(&mut self, variables: &[LngVar]) {
        self.backbone_candidates = Vec::new();
        self.backbone_assumptions = Vec::with_capacity(variables.len());
        self.backbone_map = HashMap::new();
        for &var in variables {
            self.backbone_map.insert(var, Tristate::Undef);
        }
    }

    pub(crate) fn compute_backbone_intern(
        &mut self,
        variables: &[LngVar],
        backbone_type: BackboneType,
        handler: &mut dyn ComputationHandler,
    ) -> Option<LngEvent> {
        self.create_initial_candidates(variables, backbone_type);
        while let Some(lit) = self.backbone_candidates.pop() {
            let sat_result = self.solve_with_lit(lit, handler);
            if !sat_result.is_success() {
                return sat_result.cancel_cause();
            } else if sat_result.result().unwrap() {
                self.refine_upper_bound();
            } else {
                self.add_backbone_literal(lit);
            }
        }
        None
    }

    pub(crate) fn create_initial_candidates(&mut self, variables: &[LngVar], backbone_type: BackboneType) {
        for &var in variables {
            if self.is_up_zero_lit(var) {
                let backbone_lit = mk_lit(var, !self.model[var.0]);
                self.add_backbone_literal(backbone_lit);
            } else {
                let model_phase = self.model[var.0];
                if is_both_or_negative_type(backbone_type) && !model_phase || is_both_or_positive_type(backbone_type) && model_phase {
                    let lit = mk_lit(var, !model_phase);
                    if !self.is_rotatable(lit) {
                        self.backbone_candidates.push(lit);
                    }
                }
            }
        }
    }

    pub(crate) fn refine_upper_bound(&mut self) {
        let mut index = 0;
        for lit in self.backbone_candidates.clone() {
            let var = var(lit);
            if self.is_up_zero_lit(var) {
                self.backbone_candidates.remove(index);
                self.add_backbone_literal(lit);
            } else if self.model[var.0] == sign(lit) || self.is_rotatable(lit) {
                self.backbone_candidates.remove(index);
            } else {
                index += 1;
            }
        }
    }

    pub(crate) fn solve_with_lit(&mut self, lit: LngLit, handler: &mut dyn ComputationHandler) -> LngResult<bool> {
        self.backbone_assumptions.push(not(lit));
        let result = self.internal_solve_with_assumptions(handler, self.backbone_assumptions.clone());
        self.backbone_assumptions.pop();
        result
    }

    pub(crate) fn build_backbone<V, I>(&self, variables: I, backbone_type: BackboneType) -> Backbone
    where
        V: Into<Variable>,
        I: IntoIterator<Item = V>,
    {
        let mut pos = if backbone_type == BackboneType::OnlyNegative { None } else { Some(BTreeSet::new()) };
        let mut neg = if backbone_type == BackboneType::OnlyPositive { None } else { Some(BTreeSet::new()) };
        let mut opt = if backbone_type == BackboneType::PositiveAndNegative { Some(BTreeSet::new()) } else { None };
        for v in variables {
            let var = v.into();
            if let Some(lng_var) = self.idx_for_variable(var) {
                match self.backbone_map[&lng_var] {
                    Tristate::True => {
                        if let Some(pos) = pos.as_mut() {
                            pos.insert(var);
                        }
                    }
                    Tristate::False => {
                        if let Some(neg) = neg.as_mut() {
                            neg.insert(var);
                        }
                    }
                    Tristate::Undef => {
                        if let Some(opt) = opt.as_mut() {
                            opt.insert(var);
                        }
                    }
                }
            } else if let Some(opt) = opt.as_mut() {
                opt.insert(var);
            }
        }
        Backbone::new_sat(pos, neg, opt)
    }

    pub(crate) fn is_up_zero_lit(&self, var: LngVar) -> bool {
        !self.vars[var.0].level_greater_zero()
    }

    pub(crate) fn is_unit(&self, lit: LngLit, clause: ClauseRef) -> bool {
        let c = &self.c(clause);
        if c.is_at_most {
            let mut count_pos = 0;
            let cardinality = c.cardinality();
            for &i in &c.data {
                let v = var(i);
                if var(lit) != v && self.model[v.0] {
                    count_pos += 1;
                    if count_pos == cardinality {
                        return true;
                    }
                }
            }
            false
        } else {
            for &clause_lit in &c.data {
                if lit != clause_lit && self.model[var(clause_lit).0] != sign(clause_lit) {
                    return false;
                }
            }
            true
        }
    }

    pub(crate) fn is_rotatable(&self, lit: LngLit) -> bool {
        if self.v(lit).reason.is_none() {
            return false;
        }
        for watcher in &self.watches_bin[not(lit).0] {
            if self.is_unit(lit, watcher.clause_ref) {
                return false;
            }
        }
        for watcher in &self.watches[not(lit).0] {
            if self.is_unit(lit, watcher.clause_ref) {
                return false;
            }
        }
        true
    }

    pub(crate) fn add_backbone_literal(&mut self, lit: LngLit) {
        self.backbone_map.insert(var(lit), if sign(lit) { Tristate::False } else { Tristate::True });
        self.backbone_assumptions.push(lit);
    }

    pub const fn clauses(&self) -> &Vec<ClauseRef> {
        &self.clauses
    }

    pub const fn variables(&self) -> &Vec<LngVariable> {
        &self.vars
    }

    pub fn set_selection_order(&mut self, selection_order: &[Literal]) {
        self.selection_order.clear();
        for &literal in selection_order {
            if let Some(var) = self.idx_for_variable(literal.variable()) {
                self.selection_order.push(mk_lit(var, !literal.phase()));
            }
        }
    }

    pub const fn config(&self) -> &SatSolverConfig {
        &self.config
    }

    fn manual_sort_learnts(&mut self) {
        self.manual_sort_learnts_rec(0, self.learnts.len());
    }

    fn manual_sort_learnts_rec(&mut self, start: usize, end: usize) {
        if start == end {
            return;
        }
        if end - start <= 15 {
            self.selection_sort(start, end);
        } else {
            let (pivot_len, pivot_activity) = {
                let pivot_ref = self.learnts[start + (end - start) / 2];
                let pivot = self.c(pivot_ref);
                (pivot.len(), pivot.activity)
            };
            let mut i = start as isize - 1;
            let mut j = end as isize;
            loop {
                i += 1;
                let li = self.learnts[i as usize];
                let ci = &self.c(li);
                while Self::compare_learnt_clauses_2(ci.len(), ci.activity, pivot_len, pivot_activity) == Less {
                    i += 1;
                }
                j -= 1;
                let lj = self.learnts[j as usize];
                let cj = &self.c(lj);
                while Self::compare_learnt_clauses_2(pivot_len, pivot_activity, cj.len(), cj.activity) == Less {
                    j -= 1;
                }
                if i >= j {
                    break;
                }
                self.learnts.swap(i as usize, j as usize);
            }
            self.manual_sort_learnts_rec(start, i as usize);
            self.manual_sort_learnts_rec(i as usize, end);
        }
    }

    fn selection_sort(&mut self, start: usize, end: usize) {
        let mut best_i: usize;
        for i in start..end {
            best_i = i;
            for j in (i + 1)..end {
                let ci = &self.c(self.learnts[j]);
                let cj = &self.c(self.learnts[best_i]);
                if Self::compare_learnt_clauses(cj, ci) == Less {
                    best_i = j;
                }
            }
            if i != best_i {
                self.learnts.swap(i, best_i);
            }
        }
    }

    fn compare_learnt_clauses(x: &LngClause, y: &LngClause) -> Ordering {
        Self::compare_learnt_clauses_2(x.len(), x.activity, y.len(), y.activity)
    }

    fn compare_learnt_clauses_2(x_len: usize, x_activity: f64, y_len: usize, y_activity: f64) -> Ordering {
        if x_len > 2 && (y_len == 2 || x_activity < y_activity) {
            Less
        } else {
            Greater
        }
    }
}

impl<B> std::fmt::Debug for LngCoreSolver<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ok: {} \nqhead: {}\n#clauses: {}\n#learnts: {}\n#watches: {}\n#vars: {}\n#orderheap: {}\n#trail: {}\n#trail_lim: {}\nmodel: {}\nconflict: {}\nassumptions: {}\n#seen: {}\ncla_inc: {}\n#clause lits: {}\n#learnts lits: {}",
            self.ok,
            self.qhead,
            self.clauses.len(),
            self.learnts.len(),
            self.watches.len(),
            self.vars.len(),
            self.order_heap.len(),
            self.trail.len(),
            self.trail_lim.len(),
            self.model.len(),
            self.assumptions_conflict.len(),
            self.assumptions.len(),
            self.seen.len(),
            self.cla_inc,
            self.clauses_literals,
            self.learnts_literals)
    }
}

pub fn generate_clause_vector<B>(
    literals: &[Literal],
    solver: &mut LngCoreSolver<B>,
    initial_phase: bool,
    decision_var: bool,
) -> Vec<LngLit> {
    let mut clause_vec = Vec::with_capacity(literals.len());
    for &lit in literals {
        clause_vec.push(solver_literal(lit, solver, initial_phase, decision_var));
    }
    clause_vec
}

pub fn generate_clause_vector_wo_config<B>(literals: &[Literal], solver: &mut LngCoreSolver<B>) -> Vec<LngLit> {
    generate_clause_vector(literals, solver, solver.config.initial_phase, true)
}

pub fn solver_literal<B>(lit: Literal, solver: &mut LngCoreSolver<B>, initial_phase: bool, decision_var: bool) -> LngLit {
    match solver.idx_for_variable(lit.variable()) {
        None => {
            let new_idx = solver.new_var(!initial_phase, decision_var);
            solver.add_variable(lit.variable(), new_idx);
            mk_lit(new_idx, !lit.phase())
        }
        Some(idx) => mk_lit(idx, !lit.phase()),
    }
}

pub fn solver_literal_default<B>(lit: Literal, solver: &mut LngCoreSolver<B>) -> LngLit {
    solver_literal(lit, solver, solver.config.initial_phase, true)
}

pub const fn is_both_or_positive_type(backbone_type: BackboneType) -> bool {
    matches!(backbone_type, BackboneType::PositiveAndNegative | BackboneType::OnlyPositive)
}

pub const fn is_both_or_negative_type(backbone_type: BackboneType) -> bool {
    matches!(backbone_type, BackboneType::PositiveAndNegative | BackboneType::OnlyNegative)
}

pub const fn is_both_type(backbone_type: BackboneType) -> bool {
    matches!(backbone_type, BackboneType::PositiveAndNegative)
}

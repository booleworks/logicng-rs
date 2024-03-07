// Minisat Copyrights
//
// Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
// Copyright (c) 2007-2010, Niklas Sorensson
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
// associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
// NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
// OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#![allow(
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::redundant_else
)]

use crate::backbones::Backbone;
use crate::collections::remove_elem;
use std::cell::RefCell;
use std::cmp::Ordering::{Greater, Less};
use std::cmp::{min, Ordering};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::collections::{LngHeap, MsClause, MsVariable, LNG_VEC_INIT_SIZE};
use crate::formulas::{Literal, Variable};
use crate::propositions::Proposition;
use crate::solver::functions::BackboneType;
use crate::solver::functions::BackboneType::{OnlyNegative, OnlyPositive, PositiveAndNegative};
use crate::solver::minisat_config::MiniSatConfig;
use crate::solver::sat::minisat2::Tristate::{False, True, Undef};
use crate::solver::sat::minisat2_datastructures::{ClauseMinimization, ClauseRef, MsLit, MsVar, MsWatcher, ProofInformation, Tristate};

fn watch_equality(w1: &MsWatcher, w2: &MsWatcher) -> bool {
    w1.clause_ref == w2.clause_ref
}

/// A MiniSAT 2 implementation.
///
/// This is an actual implementation of a SAT-Solver. It exposes a lot of
/// internal details, which might be handy to manipulate/tweak the solver in a
/// certain way. Usually, this is not necessary and you want to use the wrapper
/// [`MiniSat`](`crate::solver::minisat::MiniSat`).
#[allow(clippy::struct_excessive_bools)]
pub struct MiniSat2Solver<Backpack> {
    pub(crate) config: MiniSatConfig,

    // internal solver state
    pub(crate) ok: bool,
    qhead: usize,
    pub(crate) unit_clauses: Vec<MsLit>,
    pub(crate) clauses: Vec<ClauseRef>,
    pub(crate) learnts: Vec<ClauseRef>,
    watches: Vec<Vec<MsWatcher>>,
    pub(crate) vars: Vec<MsVariable>,
    order_heap: LngHeap,
    pub(crate) trail: Vec<MsLit>,
    pub(crate) trail_lim: Vec<usize>,
    var_activities: Vec<f64>,
    var_reasons: Vec<Option<ClauseRef>>,
    /// Current model on this solver.
    pub model: Vec<bool>,
    conflict: Vec<MsLit>,
    assumptions: Vec<MsLit>,
    seen: Vec<bool>,
    pub(crate) analyze_bt_level: usize,
    pub(crate) cla_inc: f64,
    simp_db_assigns: isize,
    simp_db_props: isize,
    clauses_literals: usize,
    learnts_literals: usize,

    // mapping of variable names to variable indices
    pub(crate) name2idx: BTreeMap<Variable, MsVar>,
    pub(crate) idx2name: BTreeMap<MsVar, Variable>,

    // Proof generating information
    proof_generation: bool,
    pub(crate) pg_original_clauses: Vec<ProofInformation<Backpack>>,
    pub(crate) pg_proof: Vec<Vec<isize>>,

    // Selection order
    selection_order: Vec<MsLit>,
    selection_order_idx: usize,

    learntsize_adjust_confl: f64,
    learntsize_adjust_cnt: isize,
    learntsize_adjust_start_confl: isize,
    learntsize_adjust_inc: f64,
    max_learnts: f64,

    // Backbone
    computing_backbone: bool,

    pub(crate) dnnf_assignment: Option<Vec<Tristate>>,
}

impl<B> Default for MiniSat2Solver<B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<B> MiniSat2Solver<B> {
    /// Constructs a new solver with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self::new_with_config(&MiniSatConfig::default())
    }

    /// Constructs a new solver with custom configuration.
    pub fn new_with_config(config: &MiniSatConfig) -> Self {
        Self {
            config: config.clone(),
            ok: true,
            qhead: 0,
            unit_clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            learnts: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            watches: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            vars: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            order_heap: LngHeap::new(),
            trail: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            trail_lim: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            var_activities: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            var_reasons: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            model: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            conflict: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            assumptions: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            seen: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            analyze_bt_level: 0,
            cla_inc: 1.0,
            simp_db_assigns: -1,
            simp_db_props: 0,
            clauses_literals: 0,
            learnts_literals: 0,
            name2idx: BTreeMap::new(),
            idx2name: BTreeMap::new(),
            proof_generation: config.proof_generation,
            pg_original_clauses: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            pg_proof: Vec::with_capacity(LNG_VEC_INIT_SIZE),
            selection_order: Vec::new(),
            selection_order_idx: 0,
            learntsize_adjust_confl: 0.0,
            learntsize_adjust_cnt: 0,
            learntsize_adjust_start_confl: 100,
            learntsize_adjust_inc: 1.5,
            max_learnts: 0.0,
            computing_backbone: false,
            dnnf_assignment: None,
        }
    }

    fn luby(y: f64, x: isize) -> f64 {
        let mut int_x = x;
        let mut size = 1;
        let mut seq = 0;
        while size < int_x + 1 {
            seq += 1;
            size = 2 * size + 1;
        }
        while size - 1 != int_x {
            size = (size - 1) >> 1;
            seq -= 1;
            int_x %= size;
        }
        y.powi(seq)
    }

    fn v(&self, lit: MsLit) -> &MsVariable {
        &self.vars[var(lit).0]
    }

    fn v_mut(&mut self, lit: MsLit) -> &mut MsVariable {
        &mut self.vars[var(lit).0]
    }

    fn reason(&self, lit: MsLit) -> Option<ClauseRef> {
        return self.var_reasons[var(lit).0].as_ref().cloned();
    }

    fn set_reason(&mut self, lit: MsLit, reason: Option<ClauseRef>) {
        self.var_reasons[var(lit).0] = reason;
    }

    fn value(&self, lit: MsLit) -> Tristate {
        let val = self.v(lit).assignment;
        if sign(lit) {
            val.negate()
        } else {
            val
        }
    }

    /// Returns the internal representation of a variable, if there is one.
    pub fn idx_for_variable(&self, variable: Variable) -> Option<MsVar> {
        self.name2idx.get(&variable).map(ToOwned::to_owned)
    }

    /// Returns the original variable of an internal representation.
    pub fn variable_for_idx(&self, var: MsVar) -> Option<Variable> {
        self.idx2name.get(&var).map(ToOwned::to_owned)
    }

    /// Registers a new variable to this solver.
    pub fn add_variable(&mut self, variable: Variable, id: MsVar) {
        self.name2idx.insert(variable, id);
        self.idx2name.insert(id, variable);
    }

    fn insert_var_order(&mut self, x: MsVar) {
        if !self.order_heap.in_heap(x) && self.vars[x.0].decision {
            self.order_heap.insert(x, &self.var_activities);
        }
    }

    /// Creates a new internal variable.
    pub fn new_var(&mut self, sign: bool, dvar: bool) -> MsVar {
        let v = MsVar(self.vars.len());
        let new_var = MsVariable::new(sign, dvar);
        self.vars.push(new_var);
        self.watches.push(Vec::with_capacity(LNG_VEC_INIT_SIZE));
        self.watches.push(Vec::with_capacity(LNG_VEC_INIT_SIZE));
        self.seen.push(false);
        self.var_activities.push(0.0);
        self.var_reasons.push(None);
        self.insert_var_order(v);
        v
    }

    /// Adds a clause to this solver.
    pub fn add_clause(&mut self, mut ps: Vec<MsLit>, proposition: Option<Proposition<B>>) -> bool {
        if self.proof_generation {
            let pg_clause = ps.iter().map(|&p| (var(p).0 as isize + 1) * (-2 * isize::from(sign(p)) + 1)).collect();
            self.pg_original_clauses.push(ProofInformation::new(pg_clause, proposition));
        }
        if !self.ok {
            return false;
        }
        ps.sort_unstable();

        let flag = self.proof_generation && ps.iter().any(|&l| self.value(l) != Undef);
        let oc = if flag { Some(ps.clone()) } else { None };

        let mut j = 0usize;
        let mut p = MsLit::MAX;
        for i in 0..ps.len() {
            let elem = ps[i];
            let elem_value = self.value(elem);
            if elem_value == True || elem == not(p) {
                return true;
            } else if elem_value != False && elem != p {
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
            if self.proof_generation {
                self.pg_proof.push(vec![0]);
            }
            return false;
        } else if ps.len() == 1 {
            let lit = ps[0];
            self.unchecked_enqueue(lit, None);
            self.ok = self.propagate().is_none();
            if self.config.incremental {
                self.unit_clauses.push(lit);
            }
            if !self.ok && self.proof_generation {
                self.pg_proof.push(vec![0]);
            }
            return self.ok;
        } else {
            let clause = Rc::new(RefCell::new(MsClause::new(ps, false)));
            self.attach_clause(&clause);
            self.clauses.push(clause);
        }
        true
    }

    pub(crate) fn unchecked_enqueue(&mut self, lit: MsLit, reason: Option<ClauseRef>) {
        debug_assert!(self.value(lit) == Undef);
        let level = self.decision_level();
        if let Some(assignment) = &mut self.dnnf_assignment {
            assignment[lit.0] = True;
            assignment[lit.0 ^ 1] = False;
        }
        let var = self.v_mut(lit);
        var.assignment = Tristate::from_bool(!sign(lit));
        var.level = Some(level);
        self.set_reason(lit, reason);
        self.trail.push(lit);
    }

    pub(crate) fn attach_clause(&mut self, clause_ref: &ClauseRef) {
        let clause = (**clause_ref).borrow();
        let lit0 = clause.get(0);
        let lit1 = clause.get(1);
        self.watches[not(lit0).0].push(MsWatcher { clause_ref: Rc::clone(clause_ref), blocking_literal: Some(lit1) });
        self.watches[not(lit1).0].push(MsWatcher { clause_ref: Rc::clone(clause_ref), blocking_literal: Some(lit0) });
        if clause.learnt {
            self.learnts_literals += clause.len();
        } else {
            self.clauses_literals += clause.len();
        };
    }

    pub(crate) fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub(crate) fn propagate(&mut self) -> Option<ClauseRef> {
        let mut confl: Option<ClauseRef> = None;
        let mut num_props = 0;
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            let false_lit = not(p);
            self.qhead += 1;
            let mut i_ind = 0;
            let mut j_ind = 0;
            num_props += 1;
            while i_ind < self.watches[p.0].len() {
                let (clause_ref, blocker, blocker_value) = {
                    let blocker = self.watches[p.0][i_ind].blocking_literal.unwrap();
                    let blocker_val = self.value(blocker);
                    let ws = &mut self.watches[p.0];
                    (&mut ws[i_ind].clause_ref.clone(), blocker, blocker_val)
                };
                if blocker_value == True {
                    self.watches[p.0][j_ind] = MsWatcher { clause_ref: clause_ref.clone(), blocking_literal: Some(blocker) };
                    j_ind += 1;
                    i_ind += 1;
                    continue;
                }
                {
                    let mut c = (*clause_ref).borrow_mut();
                    if c.get(0) == false_lit {
                        let c1 = c.get(1);
                        c.set(0, c1);
                        c.set(1, false_lit);
                    }
                }
                let first = {
                    let c = (*clause_ref).borrow();
                    debug_assert!(c.get(1) == false_lit);
                    c.get(0)
                };
                i_ind += 1;
                let first_val = self.value(first);
                let w = MsWatcher { clause_ref: clause_ref.clone(), blocking_literal: Some(first) };
                if first != blocker && first_val == True {
                    self.watches[p.0][j_ind] = w;
                    j_ind += 1;
                    continue;
                }
                let found_watch = {
                    let c = (*clause_ref).borrow();
                    let mut found_watch = (0, 0);
                    for k in 2..c.len() {
                        if self.value(c.get(k)) != False {
                            found_watch = (k, c.get(k).0);
                            break;
                        }
                    }
                    found_watch
                };
                if found_watch.0 > 0 {
                    let mut c = (*clause_ref).borrow_mut();
                    c.set(1, MsLit(found_watch.1));
                    c.set(found_watch.0, false_lit);
                    let not_c1 = not(c.get(1));
                    self.watches[not_c1.0].push(w);
                } else {
                    let ws = &mut self.watches[p.0];
                    ws[j_ind] = w;
                    j_ind += 1;
                    if first_val == False {
                        confl = Some(clause_ref.clone());
                        self.qhead = self.trail.len();
                        while i_ind < ws.len() {
                            ws.swap(j_ind, i_ind);
                            j_ind += 1;
                            i_ind += 1;
                        }
                    } else {
                        self.unchecked_enqueue(first, Some(clause_ref.clone()));
                    };
                }
            }
            self.watches[p.0].truncate(j_ind);
        }
        self.simp_db_props -= num_props;
        confl
    }

    /// Solves the formula on this solver with a list of assumptions.
    pub fn solve_with_assumptions(&mut self, assumptions: Vec<MsLit>) -> Tristate {
        self.assumptions = assumptions;
        let result = self.solve();
        self.assumptions.clear();
        result
    }

    /// Solves the formula on this solver.
    pub fn solve(&mut self) -> Tristate {
        self.model.clear();
        self.conflict.clear();
        if !self.ok {
            return False;
        }
        self.learntsize_adjust_confl = self.learntsize_adjust_start_confl as f64;
        self.learntsize_adjust_cnt = self.learntsize_adjust_start_confl;
        self.max_learnts = self.clauses.len() as f64 * self.config.learntsize_factor;
        let mut status = Undef;
        let mut curr_restarts = 0;

        while status == Undef {
            let rest_base = Self::luby(self.config.restart_inc, curr_restarts);
            status = self.search((rest_base * self.config.restart_first as f64) as usize);
            curr_restarts += 1;
        }

        if self.proof_generation && self.assumptions.is_empty() && status == False {
            self.pg_proof.push(vec![0]);
        }

        if status == True {
            self.model = Vec::with_capacity(self.vars.len());
            for v in &self.vars {
                self.model.push(v.assignment == True);
            }
        } else if status == False && self.conflict.is_empty() {
            self.ok = false;
        }
        self.cancel_until(0);
        status
    }

    /// The main search procedure of the CDCL algorithm.
    pub fn search(&mut self, nof_conflicts: usize) -> Tristate {
        if !self.ok {
            return False;
        }
        let mut conflict_c = 0;
        self.selection_order_idx = 0;
        loop {
            if let Some(confl) = self.propagate() {
                conflict_c += 1;
                if self.decision_level() == 0 {
                    return False;
                }
                let learnt_clause = self.analyze(confl.clone());
                self.cancel_until(self.analyze_bt_level);
                if self.analyze_bt_level < self.selection_order.len() {
                    self.selection_order_idx = self.analyze_bt_level;
                }

                if self.proof_generation {
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
                    let cr = Rc::new(RefCell::new(MsClause::new(learnt_clause, true)));
                    self.attach_clause(&cr);
                    if !self.config.incremental {
                        (*cr).borrow_mut().activity += self.cla_inc;
                    }
                    self.unchecked_enqueue((*cr).borrow().get(0), Some(cr.clone()));
                    self.learnts.push(cr);
                }
                self.decay_activities();
            } else {
                if conflict_c >= nof_conflicts {
                    self.cancel_until(0);
                    return Undef;
                }
                if !self.config.incremental {
                    if self.decision_level() == 0 && !self.simplify() {
                        return False;
                    }
                    if (self.learnts.len() as isize - self.n_assigns() as isize) as f64 >= self.max_learnts {
                        self.reduce_db();
                    };
                }
                let mut next: Option<MsLit> = None;
                while self.decision_level() < self.assumptions.len() {
                    let p = self.assumptions[self.decision_level()];
                    match self.value(p) {
                        True => self.trail_lim.push(self.trail.len()),
                        False => {
                            self.analyze_final(not(p));
                            return False;
                        }
                        Undef => {
                            next = Some(p);
                            break;
                        }
                    }
                }
                if next.is_none() {
                    next = self.pick_branch_lit();
                    if next.is_none() {
                        return True;
                    }
                }
                self.trail_lim.push(self.trail.len());
                self.unchecked_enqueue(next.unwrap(), None);
            }
        }
    }

    pub(crate) fn cancel_until(&mut self, level: usize) {
        if self.decision_level() > level {
            for c in (self.trail_lim[level]..self.trail.len()).rev() {
                let lit = self.trail[c];
                if let Some(assignment) = &mut self.dnnf_assignment {
                    assignment[lit.0] = Undef;
                    assignment[lit.0 ^ 1] = Undef;
                }
                let x = var(lit);
                let v = &mut self.vars[x.0];
                v.assignment = Undef;
                v.polarity = !self.computing_backbone && sign(lit);
                self.insert_var_order(x);
            }
            self.qhead = self.trail_lim[level];
            self.trail.truncate(self.qhead);
            self.trail_lim.truncate(level);
        }
    }

    pub(crate) fn analyze(&mut self, clause_ref: ClauseRef) -> Vec<MsLit> {
        let incremental = self.config.incremental;
        let mut out_learnt = Vec::<MsLit>::with_capacity(LNG_VEC_INIT_SIZE);
        let mut c_ref_option: Option<ClauseRef> = Some(clause_ref);
        let mut path_c = 0;
        let mut first_run = true;
        let mut p = None;
        out_learnt.push(MsLit::MAX);
        let mut index = self.trail.len() - 1;

        while first_run || path_c > 0 {
            let c_ref = c_ref_option.unwrap();
            let current_cla_inc = self.cla_inc;
            {
                let mut c = (*c_ref).borrow_mut();
                let c_learnt = c.learnt;
                if !incremental && c_learnt {
                    c.activity += current_cla_inc;
                    if c.activity > 1e20 {
                        drop(c);
                        self.rescale_learnt_activities();
                    }
                }
            }
            {
                let c = (*c_ref).borrow();
                let j_start = usize::from(!first_run);
                for j in j_start..c.len() {
                    let q = c.get(j);
                    let q_var = var(q);
                    if !self.seen[q_var.0] && self.v(q).level_greater_zero() {
                        self.var_bump_activity(q_var);
                        self.seen[q_var.0] = true;
                        // the proposed change is just wrong (`self.v(q).level.map_or_else(|| out_learnt.push(q), |c| path_c += 1)`)
                        #[allow(clippy::option_if_let_else)]
                        match self.v(q).level {
                            Some(c) if c >= self.decision_level() => path_c += 1,
                            _ => out_learnt.push(q),
                        }
                    }
                }
            }
            while !self.seen[var(self.trail[index]).0] {
                index -= 1;
            }
            p = Some(self.trail[index]);
            c_ref_option = self.reason(p.unwrap());
            debug_assert!(path_c == 1 || c_ref_option.is_some());
            self.seen[var(p.unwrap()).0] = false;
            path_c -= 1;
            first_run = false;
        }
        out_learnt[0] = not(p.unwrap());
        self.simplify_clause(&mut out_learnt);
        out_learnt
    }

    fn rescale_learnt_activities(&mut self) {
        for clause in &mut self.learnts {
            (**clause).borrow_mut().rescale_activity();
        }
        self.cla_inc *= 1e-20;
    }

    fn var_bump_activity(&mut self, v: MsVar) {
        let activity = &mut self.var_activities[v.0];
        *activity += self.config.var_inc;
        if *activity > 1e100 {
            for a in &mut self.var_activities {
                *a *= 1e-100;
            }
            self.config.var_inc *= 1e-100;
        }
        if self.order_heap.in_heap(v) {
            self.order_heap.decrease(v, &self.var_activities);
        }
    }

    pub(crate) fn decay_activities(&mut self) {
        self.var_decay_activities();
        if !self.config.incremental {
            self.cla_decay_activities();
        }
        self.learntsize_adjust_cnt -= 1;
        if self.learntsize_adjust_cnt == 0 {
            self.learntsize_adjust_confl *= self.learntsize_adjust_inc;
            self.learntsize_adjust_cnt = self.learntsize_adjust_confl as isize;
            self.max_learnts *= self.config.learntsize_inc;
        }
    }

    fn analyze_final(&mut self, p: MsLit) {
        self.conflict.clear();
        self.conflict.push(p);
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
                if self.reason(x_lit).is_none() {
                    debug_assert!(v.level_greater_zero());
                    self.conflict.push(not(x_lit));
                } else {
                    let c = (*self.reason(x_lit).unwrap()).borrow().range_copy_from(1);
                    for j_lit in c {
                        if self.v(j_lit).level_greater_zero() {
                            self.seen[var(j_lit).0] = true;
                        }
                    }
                }
                self.seen[x_var.0] = false;
            }
        }
        self.seen[var_p.0] = false;
    }

    fn pick_branch_lit(&mut self) -> Option<MsLit> {
        if !self.selection_order.is_empty() && self.selection_order_idx < self.selection_order.len() {
            while self.selection_order_idx < self.selection_order.len() {
                let lit = self.selection_order[self.selection_order_idx];
                self.selection_order_idx += 1;
                if self.v(lit).assignment == Undef {
                    return Some(lit);
                }
            }
        }
        let mut next: Option<MsVar> = None;
        while next.is_none() || self.vars[next.unwrap().0].assignment != Undef || !self.vars[next.unwrap().0].decision {
            if self.order_heap.empty() {
                return None;
            } else {
                next = Some(self.order_heap.remove_min(&self.var_activities));
            }
        }
        Some(mk_lit(next.unwrap(), self.vars[next.unwrap().0].polarity))
    }

    fn simplify_clause(&mut self, out_learnt: &mut Vec<MsLit>) {
        let mut j: usize;
        let mut analyze_to_clear = out_learnt.clone();
        match self.config.clause_min {
            ClauseMinimization::Deep => {
                let mut abstract_level = 0;
                for i in out_learnt.iter().skip(1) {
                    abstract_level |= self.abstract_level(var(*i));
                }
                j = 1;
                for i in 1..out_learnt.len() {
                    let i_lit = out_learnt[i];
                    if self.reason(i_lit).is_none() || !self.lit_redundant(i_lit, abstract_level, &mut analyze_to_clear) {
                        out_learnt[j] = i_lit;
                        j += 1;
                    }
                }
            }
            ClauseMinimization::Basic => {
                j = 1;
                for i in 1..out_learnt.len() {
                    let i_lit = out_learnt[i];
                    let reason = self.reason(i_lit);
                    if let Some(clause_ref) = reason {
                        let c = clause_ref.borrow();
                        for k in 1..c.len() {
                            let k_lit = c.get(k);
                            if !self.seen[var(k_lit).0] && self.v(k_lit).level_greater_zero() {
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
                j = 1;
            }
        }
        out_learnt.truncate(j);
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
        for i in analyze_to_clear {
            self.seen[var(i).0] = false;
        }
    }

    fn lit_redundant(&mut self, p: MsLit, abstract_levels: usize, analyze_to_clear: &mut Vec<MsLit>) -> bool {
        let mut analyze_stack = Vec::<MsLit>::with_capacity(analyze_to_clear.len());
        analyze_stack.push(p);
        let top = analyze_to_clear.len();

        while let Some(last) = analyze_stack.pop() {
            let c_ref = self.reason(last).unwrap();

            for q in (*c_ref).borrow().range_copy_from(1) {
                let q_var = var(q);
                let q_variable = self.v(q);
                if !self.seen[q_var.0] && q_variable.level_greater_zero() {
                    if self.reason(q).is_some() && (self.abstract_level(q_var) & abstract_levels) != 0 {
                        self.seen[q_var.0] = true;
                        analyze_stack.push(q);
                        analyze_to_clear.push(q);
                    } else {
                        for j in analyze_to_clear.iter().skip(top) {
                            self.seen[var(*j).0] = false;
                        }
                        analyze_to_clear.truncate(top);
                        return false;
                    }
                }
            }
        }
        true
    }

    fn simplify(&mut self) -> bool {
        debug_assert!(self.decision_level() == 0);
        if !self.ok || self.propagate().is_some() {
            self.ok = false;
            return false;
        }
        if self.n_assigns() as isize == self.simp_db_assigns || self.simp_db_props > 0 {
            return true;
        }
        self.remove_satisfied();
        self.rebuild_order_heap();
        self.simp_db_assigns = self.n_assigns() as isize;
        self.simp_db_props = (self.clauses_literals + self.learnts_literals) as isize;
        true
    }

    fn rebuild_order_heap(&mut self) {
        let mut vs = Vec::<MsVar>::new();
        for v in 0..self.vars.len() {
            let var = &self.vars[v];
            if var.decision && var.assignment == Undef {
                vs.push(MsVar(v));
            }
        }
        self.order_heap.build(&vs, &self.var_activities);
    }

    fn reduce_db(&mut self) {
        self.verify_watches();
        let mut j = 0;
        let extra_lim = self.cla_inc / self.learnts.len() as f64;
        self.sort_learnts();
        self.verify_watches();

        for i in 0..self.learnts.len() {
            let remove = {
                let c_ref = &self.learnts[i];
                let c = (**c_ref).borrow();
                c.len() > 2 && !self.locked(c_ref) && (i < self.learnts.len() / 2 || c.activity < extra_lim)
            };
            if remove {
                self.remove_clause(true, i);
            } else {
                self.learnts.swap(i, j);
                j += 1;
            };
        }
        self.learnts.truncate(j);
    }

    fn sort_learnts(&mut self) {
        self.manual_sort_learnts();
    }

    fn remove_satisfied(&mut self) {
        self.remove_satisfied_gen(true, |s| &s.learnts, |s| &mut s.learnts);
        if self.config.remove_satisfied {
            self.remove_satisfied_gen(false, |s| &s.clauses, |s| &mut s.clauses);
        }
    }

    /// Generic method for `remove_satisfied`, `remove_vec(_mut)` refers to
    /// either `self.clauses` or `self.learnts`, `clause_ref` creates a
    /// `ClauseRef` for either `clauses` or `learnts`
    fn remove_satisfied_gen<R, RMUT>(&mut self, learnt: bool, remove_vec: R, remove_vec_mut: RMUT)
    where
        R: Fn(&Self) -> &Vec<ClauseRef>,
        RMUT: Fn(&mut Self) -> &mut Vec<ClauseRef>, {
        let mut j = 0;
        for i in 0..remove_vec(self).len() {
            let satisfied = {
                let c_ref = &remove_vec(self)[i];
                let c = &(**c_ref).borrow();
                self.satisfied(c)
            };
            if satisfied {
                self.remove_clause(learnt, i);
            } else {
                let mut c_lits: Vec<MsLit>;
                {
                    let c_ref = &remove_vec(self)[i];
                    let c = &(**c_ref).borrow();
                    debug_assert!(self.value(c.get(0)) == Undef && self.value(c.get(1)) == Undef);
                    c_lits = c.range_copy_from(0);
                    if !self.proof_generation {
                        let mut k = 2;
                        while k < c_lits.len() {
                            if self.value(c_lits[k]) == False {
                                c_lits[k] = c_lits[c_lits.len() - 1];
                                k -= 1;
                                c_lits.pop();
                            }
                            k += 1;
                        }
                    }
                }
                (*remove_vec_mut(self)[i]).borrow_mut().data = c_lits;
                remove_vec_mut(self).swap(i, j);
                j += 1;
            }
        }
        remove_vec_mut(self).truncate(j);
    }

    fn satisfied(&self, c: &MsClause) -> bool {
        for i in 0..c.len() {
            if self.value(c.get(i)) == True {
                return true;
            }
        }
        false
    }

    fn remove_clause(&mut self, learnt: bool, index: usize) {
        let clause_ref = if learnt { &self.learnts[index] } else { &self.clauses[index] };
        if self.proof_generation {
            let c = (**clause_ref).borrow();
            let mut vec = Vec::<isize>::with_capacity(c.len());
            vec.push(-1);
            for &elem in &c.data {
                vec.push((var(elem).0 as isize + 1) * (-2 * isize::from(sign(elem)) + 1));
            }
            self.pg_proof.push(vec);
        }
        let locked = self.locked(clause_ref);
        if locked {
            let c_0 = (**clause_ref).borrow().get(0);
            self.set_reason(c_0, None);
        }
        self.detach_clause(learnt, index);
    }

    fn detach_clause(&mut self, learnt: bool, index: usize) {
        let clause_ref = if learnt { &self.learnts[index] } else { &self.clauses[index] };
        let c = (**clause_ref).borrow();
        let c_0 = c.get(0);
        let c_1 = c.get(1);
        remove_elem(&mut self.watches[not(c_0).0], &MsWatcher { clause_ref: clause_ref.clone(), blocking_literal: None }, watch_equality);
        remove_elem(&mut self.watches[not(c_1).0], &MsWatcher { clause_ref: clause_ref.clone(), blocking_literal: None }, watch_equality);
        debug_assert!(learnt == c.learnt);
        if learnt {
            self.learnts_literals -= c.len();
        } else {
            self.clauses_literals -= c.len();
        }
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
                let pivot = (*self.learnts[start + (end - start) / 2]).borrow();
                (pivot.len(), pivot.activity)
            };
            let mut i = start as isize - 1;
            let mut j = end as isize;
            loop {
                i += 1;
                while Self::compare_learnt_clauses_2(
                    (*self.learnts[i as usize]).borrow().len(),
                    (*self.learnts[i as usize]).borrow().activity,
                    pivot_len,
                    pivot_activity,
                ) == Less
                {
                    i += 1;
                }
                j -= 1;
                while Self::compare_learnt_clauses_2(
                    pivot_len,
                    pivot_activity,
                    (*self.learnts[j as usize]).borrow().len(),
                    (*self.learnts[j as usize]).borrow().activity,
                ) == Less
                {
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
                if Self::compare_learnt_clauses(&(*self.learnts[j]).borrow(), &(*self.learnts[best_i]).borrow()) == Less {
                    best_i = j;
                }
            }
            if i != best_i {
                self.learnts.swap(i, best_i);
            }
        }
    }

    fn compare_learnt_clauses(x: &MsClause, y: &MsClause) -> Ordering {
        Self::compare_learnt_clauses_2(x.len(), x.activity, y.len(), y.activity)
    }

    fn compare_learnt_clauses_2(x_len: usize, x_activity: f64, y_len: usize, y_activity: f64) -> Ordering {
        if x_len > 2 && (y_len == 2 || x_activity < y_activity) {
            Less
        } else {
            Greater
        }
    }

    fn locked(&self, clause_ref: &ClauseRef) -> bool {
        let c_0 = (**clause_ref).borrow().get(0);
        self.value(c_0) == True && self.reason(c_0) == Some(clause_ref.clone())
    }

    fn abstract_level(&self, x: MsVar) -> usize {
        1 << (self.vars[x.0].level.unwrap() & 31)
    }

    fn var_decay_activities(&mut self) {
        self.config.var_inc *= 1.0 / self.config.var_decay;
    }
    fn cla_decay_activities(&mut self) {
        self.cla_inc *= 1.0 / self.config.clause_decay;
    }
    fn n_assigns(&self) -> usize {
        self.trail.len()
    }

    fn verify_watches(&self) {
        for i in 0..self.watches.len() {
            let watch = not(MsLit(i));
            let ws = self.watches.get(i).unwrap();
            for (j, w) in ws.iter().enumerate() {
                let watched_clause = (w.clause_ref).borrow();
                assert!(watched_clause.get(0) == watch || watched_clause.get(1) == watch, "Watch {i}, {j} does not watch {watch:?}");
            }
        }
    }

    #[allow(dead_code)]
    fn print_watch_info(&self) {
        for i in 0..self.watches.len() {
            let ws = self.watches.get(i).unwrap();
            println!("Watches for {i}:{}", if ws.is_empty() { " empty" } else { "" });
            for j in 0..ws.len() {
                let watch = ws.get(j).unwrap();
                let clause = (*watch.clause_ref).borrow();
                println!(
                    "  Learnt: {}, Blocker: {}, ClauseRef: {:?}, Clause: {:?}",
                    clause.learnt,
                    watch.blocking_literal.map_or(String::new(), |b| b.0.to_string()),
                    watch.clause_ref,
                    clause.data
                );
            }
        }
    }

    /// Resets the solver state.
    pub fn reset(&mut self) {
        self.ok = true;
        self.qhead = 0;
        self.unit_clauses = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.clauses = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.learnts = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.watches = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.vars = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.order_heap = LngHeap { heap: Vec::with_capacity(LNG_VEC_INIT_SIZE), indices: Vec::with_capacity(LNG_VEC_INIT_SIZE) };
        self.trail = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.trail_lim = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.var_activities = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.var_reasons = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.model = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.conflict = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.assumptions = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.seen = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.analyze_bt_level = 0;
        self.cla_inc = 1.0;
        self.simp_db_assigns = -1;
        self.simp_db_props = 0;
        self.clauses_literals = 0;
        self.learnts_literals = 0;
        self.name2idx = BTreeMap::new();
        self.idx2name = BTreeMap::new();
        self.pg_original_clauses = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.pg_proof = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        self.selection_order = Vec::new();
        self.selection_order_idx = 0;
        self.learntsize_adjust_confl = 0.0;
        self.learntsize_adjust_cnt = 0;
        self.learntsize_adjust_start_confl = 100;
        self.learntsize_adjust_inc = 1.5;
        self.max_learnts = 0.0;
        self.computing_backbone = false;
        self.dnnf_assignment = None;
    }

    pub(crate) fn save_state(&self) -> [usize; 7] {
        assert!(self.config.incremental, "Cannot save a state when the incremental mode is deactivated");
        let (pg_clauses, pg_proof) = if self.proof_generation { (self.pg_original_clauses.len(), self.pg_proof.len()) } else { (0, 0) };
        [usize::from(self.ok), self.vars.len(), self.clauses.len(), self.learnts.len(), self.unit_clauses.len(), pg_clauses, pg_proof]
    }

    pub(crate) fn load_state(&mut self, state: [usize; 7]) {
        assert!(self.config.incremental, "Cannot load a state when the incremental mode is deactivated");
        self.complete_backtrack();
        self.ok = state[0] > 0;
        let new_vars_size = min(state[1], self.vars.len());
        for i in (new_vars_size..self.vars.len()).rev() {
            self.order_heap.remove(self.name2idx.remove(&self.idx2name.remove(&MsVar(i)).unwrap()).unwrap(), &self.var_activities);
        }
        self.vars.truncate(new_vars_size);
        self.var_activities.truncate(new_vars_size);
        self.var_reasons.truncate(new_vars_size);

        let new_clauses_size = min(state[2], self.clauses.len());
        for i in (new_clauses_size..self.clauses.len()).rev() {
            self.simple_remove_clause(false, i);
        }
        self.clauses.truncate(new_clauses_size);

        let new_learnts_size = min(state[3], self.learnts.len());
        for i in (new_learnts_size..self.learnts.len()).rev() {
            self.simple_remove_clause(true, i);
        }
        self.learnts.truncate(new_learnts_size);

        self.watches.truncate(new_vars_size * 2);

        self.unit_clauses.truncate(state[4]);
        for i in 0..self.unit_clauses.len() {
            if self.ok {
                self.unchecked_enqueue(self.unit_clauses[i], None);
                self.ok = self.propagate().is_none();
            }
        }

        if self.proof_generation {
            self.pg_original_clauses.truncate(min(state[5], self.pg_original_clauses.len()));
            self.pg_proof.truncate(min(state[6], self.pg_proof.len()));
        }
    }

    fn complete_backtrack(&mut self) {
        for v in 0..self.vars.len() {
            let var = &mut self.vars[v];
            var.assignment = Undef;
            self.var_reasons[v] = None;
            if !self.order_heap.in_heap(MsVar(v)) && var.decision {
                self.order_heap.insert(MsVar(v), &self.var_activities);
            }
        }
        self.trail.clear();
        self.trail_lim.clear();
        self.qhead = 0;
    }

    fn simple_remove_clause(&mut self, learnt: bool, i: usize) {
        self.detach_clause(learnt, i);
    }

    /// Returns the unit propagated literals on level zero.
    pub fn up_zero_literals(&self) -> Vec<MsLit> {
        self.trail.iter().take_while(|&&lit| !self.v(lit).level_greater_zero()).copied().collect()
    }

    /// Computes the backbone on this solver.
    pub fn compute_backbone(&mut self, variables: Vec<Variable>, backbone_type: BackboneType) -> Backbone {
        if self.solve() == True {
            self.computing_backbone = true;
            let relevant_var_indices = variables.iter().filter_map(|v| self.name2idx.get(v)).copied().collect::<Vec<MsVar>>();
            let mut state = self.init_backbone_ds();
            self.backbone_impl(&mut state, &relevant_var_indices, backbone_type);
            let backbone = self.build_backbone(&state, variables, backbone_type);
            self.computing_backbone = false;
            backbone
        } else {
            Backbone::new_unsat()
        }
    }

    fn init_backbone_ds(&mut self) -> BackboneComputationState {
        BackboneComputationState { candidates: vec![], assumptions: vec![], map: vec![Undef; self.vars.len()] }
    }

    fn backbone_impl(&mut self, state: &mut BackboneComputationState, variables: &Vec<MsVar>, backbone_type: BackboneType) {
        self.create_initial_candidates(state, variables, backbone_type);
        while let Some(lit) = state.candidates.pop() {
            state.assumptions.push(not(lit));
            let sat = self.solve_with_assumptions(state.assumptions.clone()) == True;
            state.assumptions.pop();
            if sat {
                self.refine_upper_bound(state);
            } else {
                state.add_backbone_literal(lit);
            }
        }
    }

    fn create_initial_candidates(&mut self, state: &mut BackboneComputationState, variables: &Vec<MsVar>, backbone_type: BackboneType) {
        for &var in variables {
            let model_phase = self.model[var.0];
            let lit = mk_lit(var, !model_phase);
            if self.vars[var.0].level == Some(0) {
                state.add_backbone_literal(lit);
            } else if backbone_type.matches_phase(model_phase)
                && (!self.config.bb_initial_ubcheck_for_rotatable_literals || !self.is_rotatable(lit))
            {
                state.candidates.push(lit);
            }
        }
    }

    fn refine_upper_bound(&mut self, state: &mut BackboneComputationState) {
        let mut new_candidates = vec![];
        let mut new_backbone_lits = vec![];
        for &lit in &state.candidates {
            let var = var(lit);
            if self.vars[var.0].level == Some(0) {
                new_backbone_lits.push(lit);
            } else if !(self.config.bb_check_for_complement_model_literals && self.model[var.0] == sign(lit)
                || self.config.bb_check_for_rotatable_literals && self.is_rotatable(lit))
            {
                new_candidates.push(lit);
            }
        }
        new_backbone_lits.iter().for_each(|&lit| state.add_backbone_literal(lit));
        state.candidates = new_candidates;
    }

    fn build_backbone(&self, state: &BackboneComputationState, variables: Vec<Variable>, backbone_type: BackboneType) -> Backbone {
        let mut pos = if backbone_type == OnlyNegative { None } else { Some(BTreeSet::new()) };
        let mut neg = if backbone_type == OnlyPositive { None } else { Some(BTreeSet::new()) };
        let mut opt = if backbone_type == PositiveAndNegative { Some(BTreeSet::new()) } else { None };
        for var in variables {
            if let Some(&ms_var) = self.name2idx.get(&var) {
                match state.map.get(ms_var.0).unwrap() {
                    True => {
                        if let Some(pos) = pos.as_mut() {
                            pos.insert(var);
                        }
                    }
                    False => {
                        if let Some(neg) = neg.as_mut() {
                            neg.insert(var);
                        }
                    }
                    Undef => {
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

    fn is_rotatable(&self, lit: MsLit) -> bool {
        // A rotatable literal MUST NOT be a unit propagated literal
        if self.reason(lit).is_some() {
            return false;
        }
        // A rotatable literal MUST NOT be unit
        !self.watches[not(lit).0].iter().any(|watcher| self.is_unit(lit, &(*watcher.clause_ref).borrow()))
    }

    fn is_unit(&self, lit: MsLit, clause: &MsClause) -> bool {
        !clause.data.iter().any(|&clause_lit| lit != clause_lit && self.model[var(clause_lit).0] != sign(clause_lit))
    }

    pub(crate) fn set_selection_order(&mut self, selection_order: &[Literal]) {
        self.selection_order = selection_order
            .iter()
            .filter_map(|lit| self.name2idx.get(&lit.variable()).map(|ms_var| mk_lit(*ms_var, !lit.phase())))
            .collect();
    }

    pub(crate) fn reset_selection_order(&mut self) {
        self.selection_order.clear();
    }
}

/// Constructs an MiniSAT literal from a MiniSAT variable.
pub fn mk_lit(var: MsVar, sign: bool) -> MsLit {
    MsLit(var.0 + var.0 + usize::from(sign))
}

/// Constructs the negation of a MiniSAT literal.
pub const fn not(lit: MsLit) -> MsLit {
    MsLit(lit.0 ^ 1)
}

/// Returns the sign of the literal.
pub const fn sign(lit: MsLit) -> bool {
    lit.0 & 1 == 1
}

/// Returns the MiniSAT variable of MiniSAT variable.
pub const fn var(lit: MsLit) -> MsVar {
    MsVar(lit.0 >> 1)
}

struct BackboneComputationState {
    candidates: Vec<MsLit>,
    assumptions: Vec<MsLit>,
    map: Vec<Tristate>,
}

impl BackboneComputationState {
    pub fn add_backbone_literal(&mut self, lit: MsLit) {
        self.map[var(lit).0] = Tristate::from_bool(!sign(lit));
        self.assumptions.push(lit);
    }
}

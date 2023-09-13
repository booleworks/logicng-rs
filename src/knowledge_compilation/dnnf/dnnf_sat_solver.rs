#![allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::iter::repeat;
use std::rc::Rc;

use bitvec::vec::BitVec;

use crate::collections::MsClause;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, Variable};
use crate::solver::minisat::sat::Tristate::Undef;
use crate::solver::minisat::sat::{mk_lit, ClauseRef, MiniSat2Solver, MsLit, MsVar, Tristate};
use crate::util::exceptions::panic_unexpected_formula_type;

pub struct DnnfSatSolver {
    internal_solver: MiniSat2Solver,
    newly_implied_dirty: bool,
    assertion_level: isize,
    last_learnt: Option<Vec<MsLit>>,
}

impl DnnfSatSolver {
    pub fn new(mut internal_solver: MiniSat2Solver, number_of_variables: usize) -> Self {
        internal_solver.dnnf_assignment = Some(repeat(Undef).take(2 * number_of_variables).collect());
        Self { internal_solver, newly_implied_dirty: false, assertion_level: -1, last_learnt: None }
    }

    pub fn start(&mut self) -> bool {
        self.newly_implied_dirty = true;
        self.internal_solver.propagate().is_none()
    }

    pub fn add(&mut self, formula: EncodedFormula, f: &FormulaFactory) {
        match formula.unpack(f) {
            Formula::True => {}
            Formula::False | Formula::Or(_) | Formula::Lit(_) => {
                let clause_vec = self.generate_clause_vec(&formula.literals(f));
                self.internal_solver.add_clause(clause_vec, &None);
            }
            Formula::And(ops) => ops.for_each(|op| {
                let clause_vec = self.generate_clause_vec(&op.literals(f));
                self.internal_solver.add_clause(clause_vec, &None);
            }),
            _ => panic_unexpected_formula_type(formula, Some(f)),
        }
    }

    pub fn decide(&mut self, var: MsVar, phase: bool) -> bool {
        self.newly_implied_dirty = true;
        let lit = mk_lit(var, !phase);
        self.internal_solver.trail_lim.push(self.internal_solver.trail.len());
        self.internal_solver.unchecked_enqueue(lit, None);
        self.propagate_after_decide()
    }

    pub fn undo_decide(&mut self, var: MsVar) {
        self.newly_implied_dirty = false;
        self.internal_solver.cancel_until(self.internal_solver.vars[var.0].level.unwrap() - 1);
    }

    pub fn at_assertion_level(&mut self) -> bool {
        self.internal_solver.decision_level() as isize == self.assertion_level
    }

    pub fn assert_cd_literal(&mut self) -> bool {
        self.newly_implied_dirty = true;
        assert!(self.at_assertion_level());
        if self.last_learnt.as_ref().unwrap().len() == 1 {
            let lit = self.last_learnt.as_ref().unwrap()[0];
            self.internal_solver.unchecked_enqueue(lit, None);
            self.internal_solver.unit_clauses.push(lit);
        } else {
            let cr = Rc::new(RefCell::new(MsClause::new(self.last_learnt.as_ref().unwrap().clone(), true)));
            self.internal_solver.attach_clause(&cr);
            if !self.internal_solver.config.incremental {
                (*cr).borrow_mut().activity += self.internal_solver.cla_inc;
            }
            self.internal_solver.unchecked_enqueue((*cr).borrow().get(0), Some(cr.clone()));
            self.internal_solver.learnts.push(cr);
        }
        self.internal_solver.decay_activities();
        self.propagate_after_decide()
    }

    pub fn newly_implied(&mut self, known_variables: &BitVec, f: &FormulaFactory) -> EncodedFormula {
        let mut implied_operands = Vec::new();
        if self.newly_implied_dirty {
            if let Some(&limit) = self.internal_solver.trail_lim.last() {
                for i in (limit..self.internal_solver.trail.len()).rev() {
                    let lit = self.internal_solver.trail[i];
                    if *known_variables.get(Self::var(lit).0).unwrap() {
                        implied_operands.push(self.int_to_literal(lit));
                    }
                }
            }
        }
        self.newly_implied_dirty = false;
        f.and(&implied_operands)
    }

    pub fn value_of(&self, lit: MsLit) -> Tristate {
        self.internal_solver.dnnf_assignment.as_ref().unwrap()[lit.0]
    }

    pub fn variable_index(&self, lit: Literal) -> MsVar {
        self.internal_solver.idx_for_variable(lit.variable()).unwrap()
    }

    pub fn var_for_idx(&self, var: MsVar) -> Variable {
        self.internal_solver.variable_for_idx(var).unwrap()
    }

    pub const fn var(lit: MsLit) -> MsVar {
        MsVar(lit.0 >> 1)
    }

    pub const fn phase(lit: MsLit) -> bool {
        lit.0 & 1 == 0
    }

    fn propagate_after_decide(&mut self) -> bool {
        self.internal_solver.propagate().map_or(true, |conflict| {
            self.handle_conflict(conflict);
            false
        })
    }

    fn handle_conflict(&mut self, conflict: ClauseRef) {
        if self.internal_solver.decision_level() > 0 {
            self.last_learnt = Some(self.internal_solver.analyze(conflict));
            self.assertion_level = self.internal_solver.analyze_bt_level as isize;
        } else {
            self.internal_solver.cancel_until(0);
            self.last_learnt = None;
            self.assertion_level = -1;
        }
    }

    fn generate_clause_vec(&mut self, literals: &BTreeSet<Literal>) -> Vec<MsLit> {
        literals.iter().map(|lit| self.generate_literal(*lit)).collect()
    }

    fn generate_literal(&mut self, literal: Literal) -> MsLit {
        let variable = literal.variable();
        let index = self.internal_solver.idx_for_variable(variable).unwrap_or_else(|| {
            let new_index = self.internal_solver.new_var(false, true);
            self.internal_solver.add_variable(variable, new_index);
            new_index
        });
        mk_lit(index, !literal.phase())
    }

    fn int_to_literal(&self, lit: MsLit) -> EncodedFormula {
        let variable = self.internal_solver.variable_for_idx(Self::var(lit)).unwrap();
        EncodedFormula::from(Literal::new(variable, Self::phase(lit)))
    }
}

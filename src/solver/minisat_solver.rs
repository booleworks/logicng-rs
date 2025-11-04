#![allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]

use std::collections::{BTreeSet, HashMap};
use std::ops::Deref;
use std::sync::Arc;

use crate::cardinality_constraints::{CcEncoder, CcIncrementalData};
use crate::collections::LNG_VEC_INIT_SIZE;
use crate::datastructures::Model;
use crate::explanations::UnsatCore;
use crate::formulas::{CardinalityConstraint, EncodedFormula, Formula, FormulaFactory, FormulaType, Literal, Variable};
use crate::operations::transformations::{CnfAlgorithm, CnfEncoder, PgOnSolverConfig, VarCacheEntry, add_cnf_to_solver};
use crate::propositions::Proposition;
use crate::solver::functions::compute_unsat_core;
use crate::solver::minisat::sat::Tristate::{False, True, Undef};
use crate::solver::minisat::sat::{MiniSat2Solver, MsLit, Tristate, mk_lit, sign, var};
use crate::solver::minisat::{MiniSatConfig, SolverCnfMethod, SolverState};
use crate::util::exceptions::panic_unexpected_formula_type;

use super::functions::OptimizationFunction;
use super::minisat::sat::MsVar;

/// Wrapper for the MiniSAT-style SAT solvers.
pub struct MiniSat<Backpack = ()> {
    /// actual MiniSAT solver
    pub underlying_solver: MiniSat2Solver<Backpack>,
    pub(crate) result: Tristate,
    pub(crate) config: MiniSatConfig,
    valid_states: Vec<usize>,
    next_state_id: usize,
    pub(crate) last_computation_with_assumptions: bool,
    pg_variable_cache: HashMap<EncodedFormula, VarCacheEntry>,
    full_pg_variable_cache: HashMap<EncodedFormula, VarCacheEntry>,
}

impl<B: Clone> Default for MiniSat<B> {
    fn default() -> Self {
        Self::new_with_backpack()
    }
}

impl MiniSat {
    /// Constructs a new SAT solver instance.
    #[must_use]
    pub fn new() -> Self {
        Self::new_with_backpack()
    }

    /// Constructs a new SAT solver instance bases on a configuration.
    #[must_use]
    pub fn from_config(config: MiniSatConfig) -> Self {
        Self::from_config_with_backpack(config)
    }
}

impl<B> MiniSat<B> {
    /// Constructs a new SAT solver instance.
    pub fn new_with_backpack() -> Self {
        Self {
            underlying_solver: MiniSat2Solver::new(),
            result: Undef,
            config: MiniSatConfig::default(),
            valid_states: Vec::new(),
            next_state_id: 0,
            last_computation_with_assumptions: false,
            pg_variable_cache: HashMap::default(),
            full_pg_variable_cache: HashMap::default(),
        }
    }

    /// Constructs a new SAT solver instance bases on a configuration.
    pub fn from_config_with_backpack(config: MiniSatConfig) -> Self {
        Self {
            underlying_solver: MiniSat2Solver::new_with_config(&config),
            result: Undef,
            config,
            valid_states: Vec::<usize>::with_capacity(LNG_VEC_INIT_SIZE),
            next_state_id: 0,
            last_computation_with_assumptions: false,
            pg_variable_cache: HashMap::default(),
            full_pg_variable_cache: HashMap::default(),
        }
    }

    /// Adds the given formulas to the solver.
    pub fn add_all(&mut self, formulas: &[EncodedFormula], f: &FormulaFactory) {
        for &formula in formulas {
            self.add(formula, f);
        }
    }

    /// Adds the given formula to the solver.
    pub fn add(&mut self, formula: EncodedFormula, f: &FormulaFactory) {
        self.result = Undef;
        if formula.formula_type() == FormulaType::Cc {
            CcEncoder::new(f.config.cc_config.clone()).encode_on(self, &formula.as_cc(f).unwrap(), f);
        } else {
            match self.config.cnf_method {
                SolverCnfMethod::FactoryCnf => {
                    let cnf = f.cnf_of(formula);
                    self.add_clause_set(cnf, None, f);
                }
                SolverCnfMethod::PgOnSolver => {
                    add_cnf_to_solver(
                        &mut self.underlying_solver,
                        formula,
                        None,
                        f,
                        &mut self.pg_variable_cache,
                        PgOnSolverConfig::default().perform_nnf(true).initial_phase(self.config.initial_phase),
                    );
                }
                SolverCnfMethod::FullPgOnSolver => {
                    add_cnf_to_solver(
                        &mut self.underlying_solver,
                        formula,
                        None,
                        f,
                        &mut self.full_pg_variable_cache,
                        PgOnSolverConfig::default().perform_nnf(false).initial_phase(self.config.initial_phase),
                    );
                }
            }
        }
        self.add_all_original_variables(formula, f);
    }

    /// Adds the given propositions to the solver.
    pub fn add_propositions<Props: IntoIterator<Item = Proposition<B>>>(&mut self, propositions: Props, f: &FormulaFactory) {
        propositions.into_iter().for_each(|proposition| self.add_proposition(proposition, f));
    }

    /// Adds the given proposition to the solver.
    pub fn add_proposition(&mut self, proposition: Proposition<B>, f: &FormulaFactory) {
        self.result = Undef;
        match self.config.cnf_method {
            SolverCnfMethod::FactoryCnf => {
                let cnf = CnfEncoder::new(CnfAlgorithm::Factorization).transform(proposition.formula, f);
                self.add_clause_set(cnf, Some(proposition), f);
            }
            SolverCnfMethod::PgOnSolver => {
                add_cnf_to_solver(
                    &mut self.underlying_solver,
                    proposition.formula,
                    Some(proposition),
                    f,
                    &mut self.pg_variable_cache,
                    PgOnSolverConfig::default().perform_nnf(true).initial_phase(self.config.initial_phase),
                );
            }
            SolverCnfMethod::FullPgOnSolver => {
                add_cnf_to_solver(
                    &mut self.underlying_solver,
                    proposition.formula,
                    Some(proposition),
                    f,
                    &mut self.full_pg_variable_cache,
                    PgOnSolverConfig::default().perform_nnf(false).initial_phase(self.config.initial_phase),
                );
            }
        }
    }

    /// Solves the current problem on the solver.
    pub fn sat(&mut self) -> Tristate {
        self.result = self.underlying_solver.solve();
        self.last_computation_with_assumptions = false;
        self.result
    }

    /// Solves the current problem on the solver with the given [`SatBuilder`].
    pub fn sat_with(&mut self, sat_builder: &SatBuilder) -> Tristate {
        self.set_solver_to_undef();
        if let Some(selection_order) = sat_builder.selection_order {
            self.underlying_solver.set_selection_order(selection_order);
        }
        let assumptions: Option<Vec<MsLit>> = if let Some(assumption) = sat_builder.single_assumption {
            Some(self.generate_clause_vec(&[assumption]))
        } else {
            sat_builder.assumptions.map(|ass| self.generate_clause_vec(ass))
        };
        self.result = if let Some(assumptions) = assumptions {
            let result = self.underlying_solver.solve_with_assumptions(assumptions);
            self.last_computation_with_assumptions = true;
            result
        } else {
            self.underlying_solver.solve()
        };
        if sat_builder.selection_order.is_some() {
            self.underlying_solver.reset_selection_order();
        }
        self.result
    }

    pub(crate) fn set_solver_to_undef(&mut self) {
        self.result = Undef;
    }

    /// Resets the solver.
    pub fn reset(&mut self) {
        self.underlying_solver.reset();
        self.result = Undef;
        self.last_computation_with_assumptions = false;
        self.pg_variable_cache.clear();
        self.full_pg_variable_cache.clear();
    }

    /// Returns the model the solver found, if the search was successful. If the
    /// result is `false`, it returns `None`. And panics if the result is
    /// undefined.
    ///
    /// # Panic
    ///
    /// Panics, if the result of the solver is `Undef`.
    pub fn model(&self, variables: Option<&[Variable]>) -> Option<Model> {
        match self.result {
            Undef => panic!("Cannot get a model as long as the formula is not solved.  Call 'sat' first."),
            False => None,
            True => {
                let relevant_indices = variables.map(|vars| {
                    let mut result = Vec::<MsVar>::with_capacity(vars.len());
                    for v in vars {
                        if let Some(index) = self.underlying_solver.idx_for_variable(*v) {
                            result.push(index);
                        }
                    }
                    result
                });
                Some(self.create_assignment(&self.underlying_solver.model, &relevant_indices))
            }
        }
    }

    /// Saves the state of the solver.
    pub fn save_state(&mut self) -> SolverState {
        let id = self.next_state_id;
        self.next_state_id += 1;
        self.valid_states.push(id);
        SolverState::new(id, self.underlying_solver.save_state())
    }

    /// Loads the state of the solver.
    pub fn load_state(&mut self, state: &SolverState) {
        let index = self
            .valid_states
            .iter()
            .enumerate()
            .rev()
            .find(|(_index, id)| **id == state.id)
            .expect("The given solver state is not valid anymore.")
            .0;
        self.valid_states.truncate(index + 1);
        self.underlying_solver.load_state(state.state);
        self.result = Undef;
        self.pg_variable_cache.clear();
        self.full_pg_variable_cache.clear();
    }

    /// Returns all known variables on the solver.
    pub fn known_variables(&self) -> Vec<Variable> {
        let n_vars = self.underlying_solver.vars.len();
        self.underlying_solver.name2idx.iter().filter(|&(_, &idx)| idx.0 < n_vars).map(|(&var, _)| var).collect()
    }

    /// Adds a cardinality constraint and returns its incremental data in order
    /// to refine the constraint on the solver.
    ///
    /// Usage constraints:
    /// - "&lt;": Cannot be used with right-hand side 2, returns null for
    ///   right-hand side 1, but constraint is added to solver.
    /// - "&lt;=": Cannot be used with right-hand side 1, returns null for
    ///   right-hand side 0, but constraint is added to solver.
    /// - "&gt;": Returns null for right-hand side 0 or number of variables -1,
    ///   but constraint is added to solver. Adds false to solver for right-hand
    ///   side &gt;= number of variables.
    /// - "&gt;=": Returns null for right-hand side 1 or number of variables,
    ///   but constraint is added to solver. Adds false to solver for right-hand
    ///   side &gt; number of variables.
    pub fn add_incremental_cc(&mut self, cc: &CardinalityConstraint, f: &FormulaFactory) -> Option<CcIncrementalData> {
        CcEncoder::new(f.config.cc_config.clone()).encode_incremental_on(self, cc, f)
    }

    /// A solver function which returns all unit propagated literals on level 0
    /// of the current formula on the solver. If the formula is UNSAT, `None`
    /// will be returned.
    pub fn up_zero_literals(&self) -> Option<BTreeSet<Literal>> {
        match self.result {
            Undef => panic!("Cannot get unit propagated literals on level 0 as long as the formula is not solved.  Call 'sat' first."),
            False => None,
            True => Some(
                self.underlying_solver
                    .up_zero_literals()
                    .iter()
                    .map(|&lit| Literal::new(*self.underlying_solver.idx2name.get(&var(lit)).unwrap(), !sign(lit)))
                    .collect(),
            ),
        }
    }

    /// Computes a model for the formula on the solver which has a global
    /// minimum or maximum of satisfied literals. If the formula is UNSAT or the
    /// optimization handler aborted the computation, `None` will be returned.
    pub fn optimize(&mut self, f: &FormulaFactory, optimization_function: &OptimizationFunction) -> Option<Model> {
        optimization_function.optimize(self, f)
    }

    /// Returns the current formula on the solver.
    ///
    /// Note that this formula is usually syntactically different from the
    /// formulas which were actually added to the solver, since the formulas are
    /// added as CNF and may be simplified or even removed, depending on the
    /// state of the solver. Furthermore, the solver might add learnt clauses or
    /// propagate literals. This can be useful to debug or analyze a solver at a
    /// given time.
    pub fn formula_on_solver(&self, f: &FormulaFactory) -> Arc<[EncodedFormula]> {
        let mut formulas = Vec::new();
        for clause_ref in &self.underlying_solver.clauses {
            let lits: Vec<Literal> = clause_ref
                .borrow()
                .deref()
                .data
                .iter()
                .map(|&lit| Literal::new(self.underlying_solver.variable_for_idx(var(lit)).unwrap(), !sign(lit)))
                .collect();
            formulas.push(f.clause(&lits));
        }
        self.underlying_solver
            .vars
            .iter()
            .enumerate()
            .filter(|(_, var)| var.level == Some(0))
            .map(|(i, var)| Literal::new(self.underlying_solver.variable_for_idx(MsVar(i)).unwrap(), var.assignment == True))
            .for_each(|lit| formulas.push(lit.into()));
        if !self.underlying_solver.ok {
            formulas.push(f.falsum());
        }
        formulas.into()
    }

    fn add_all_original_variables(&mut self, formula: EncodedFormula, f: &FormulaFactory) {
        formula.variables(f).iter().for_each(|v| {
            self.generate_literal(v.pos_lit());
        });
    }

    fn add_clause_set(&mut self, cnf: EncodedFormula, proposition: Option<Proposition<B>>, f: &FormulaFactory) {
        match cnf.unpack(f) {
            Formula::True => {}
            Formula::False | Formula::Or(_) | Formula::Lit(_) => self.add_clause(cnf, proposition, f),
            Formula::And(ops) => ops.for_each(|op| self.add_clause(op, proposition.clone(), f)),
            _ => panic_unexpected_formula_type(cnf, Some(f)),
        }
    }

    fn add_clause(&mut self, clause: EncodedFormula, proposition: Option<Proposition<B>>, f: &FormulaFactory) {
        self.result = Undef;
        let clause_vec = self.generate_clause_vec(&clause.literals_for_clause_or_term(f));
        self.underlying_solver.add_clause(clause_vec, proposition);
    }

    fn generate_clause_vec(&mut self, literals: &[Literal]) -> Vec<MsLit> {
        literals.iter().map(|lit| self.generate_literal(*lit)).collect()
    }

    fn generate_literal(&mut self, literal: Literal) -> MsLit {
        let variable = literal.variable();
        let index = self.underlying_solver.idx_for_variable(variable).unwrap_or_else(|| {
            let new_index = self.underlying_solver.new_var(!self.config.initial_phase, true);
            self.underlying_solver.add_variable(variable, new_index);
            new_index
        });
        mk_lit(index, !literal.phase())
    }

    #[allow(clippy::ref_option)]
    pub(crate) fn create_assignment(&self, model: &[bool], relevant_indices: &Option<Vec<MsVar>>) -> Model {
        let capacity = relevant_indices.as_ref().map_or(model.len(), Vec::len);
        let mut pos = Vec::with_capacity(capacity);
        let mut neg = Vec::with_capacity(capacity);
        match relevant_indices {
            None => {
                for (i, value) in model.iter().enumerate() {
                    let variable = self.underlying_solver.variable_for_idx(MsVar(i)).unwrap();
                    if self.is_relevant_variable(variable) {
                        if *value {
                            pos.push(variable);
                        } else {
                            neg.push(variable);
                        }
                    }
                }
            }
            Some(relevant) => {
                for &index in relevant {
                    let variable = self.underlying_solver.variable_for_idx(index).unwrap();
                    if self.is_relevant_variable(variable) {
                        if model[index.0] {
                            pos.push(variable);
                        } else {
                            neg.push(variable);
                        }
                    }
                }
            }
        }
        Model::new(pos, neg)
    }

    pub(crate) const fn is_relevant_variable(&self, var: Variable) -> bool {
        match var {
            Variable::FF(_) => true,
            Variable::Aux(_, _) => self.config.auxiliary_variables_in_models,
        }
    }

    pub(crate) fn add_literal(&mut self, lit: &Literal) -> MsLit {
        let index = self.underlying_solver.idx_for_variable(lit.variable()).unwrap_or_else(|| {
            let new_index = self.underlying_solver.new_var(!self.config.initial_phase, true);
            self.underlying_solver.add_variable(lit.variable(), new_index);
            new_index
        });
        mk_lit(index, !lit.phase())
    }
}

impl<B: PartialEq> MiniSat<B> {
    /// Computes the unsatisfiable core on this solver.
    pub fn unsat_core(&mut self, f: &FormulaFactory) -> UnsatCore<B> {
        compute_unsat_core(self, f)
    }
}

/// A builder which can be used in addition to [`MiniSat`] with
/// [`MiniSat::sat_with()`]. It allows you to feed the solver with assumptions
/// and a selection order.
pub struct SatBuilder<'a, 'o> {
    single_assumption: Option<Literal>,
    assumptions: Option<&'a [Literal]>,
    selection_order: Option<&'o [Literal]>,
}

impl<'a, 'o> SatBuilder<'a, 'o> {
    /// Creates an empty instance.
    pub const fn new() -> Self {
        Self { single_assumption: None, assumptions: None, selection_order: None }
    }

    /// Stores a single assumption.
    ///
    /// You can only have one _single assumption_. If you need multiple
    /// assumptions you need to use [`SatBuilder::assumptions()`].
    #[must_use]
    pub fn assumption(mut self, lit: Literal) -> Self {
        assert_eq!(None, self.assumptions, "You cannot set both `assumption` and `assumptions`.");
        self.single_assumption = Some(lit);
        self
    }

    /// Stores a list of assumptions.
    #[must_use]
    pub fn assumptions(mut self, assumptions: &'a [Literal]) -> Self {
        assert_eq!(None, self.single_assumption, "You cannot set both `assumption` and `assumptions`.");
        self.assumptions = Some(assumptions);
        self
    }

    /// Stores a selection order.
    #[must_use]
    pub const fn selection_order(mut self, selection_order: &'o [Literal]) -> Self {
        self.selection_order = Some(selection_order);
        self
    }
}

impl Default for SatBuilder<'_, '_> {
    fn default() -> Self {
        Self::new()
    }
}

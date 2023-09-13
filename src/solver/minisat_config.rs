use crate::solver::minisat::sat::ClauseMinimization;

/// Configuration for [`MiniSat`](crate::solver::minisat::MiniSat) solver.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, PartialEq, Debug)]
pub struct MiniSatConfig {
    /// Variable activity decay factor.
    pub var_decay: f64,
    /// Initial value to bump a variable with each time it is used in conflict
    /// resolution.
    pub var_inc: f64,
    /// Clause minimization method
    pub clause_min: ClauseMinimization,
    /// Base restart interval.
    pub restart_first: usize,
    /// Restart interval increase factor.
    pub restart_inc: f64,
    /// Clause activity decay factor.
    pub clause_decay: f64,
    /// Satisfied original clauses will be removed when simplifying on level 0.
    pub remove_satisfied: bool,
    /// Initial limit for learnt clauses as a factor of the original clauses.
    pub learntsize_factor: f64,
    /// Factor by which the limit for learnt clauses is multiplied every
    /// restart.
    pub learntsize_inc: f64,
    /// Incremental mode of the solver.
    pub incremental: bool,
    /// Initial phase of the solver.
    pub initial_phase: bool,
    /// Recording of information for generating a proof with DRUP.
    pub proof_generation: bool,
    /// CNF method for converting formula which are not in CNF.
    pub cnf_method: SolverCnfMethod,
    /// Include auxiliary variables (CNF, cardinality constraints,
    /// pseudo-Boolean constraints) in produced models.
    pub auxiliary_variables_in_models: bool,
    /// Backbone algorithm should check for rotatable literals during initial
    /// unit propagation.
    pub bb_initial_ubcheck_for_rotatable_literals: bool,
    /// Backbone algorithm should check for complement model literals.
    pub bb_check_for_complement_model_literals: bool,
    /// Backbone algorithm should check for rotatable literals.
    pub bb_check_for_rotatable_literals: bool,
}

/// The different methods for generating a CNF for a formula to put on the
/// solver.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SolverCnfMethod {
    /// Calls the
    /// [`FormulaFactory::cnf_of()`](`crate::formulas::FormulaFactory`) method
    /// to convert formulas to CNF. Therefore the CNF including all auxiliary
    /// variables will be added to the formula factory.
    FactoryCnf,
    /// A solver-internal implementation of Plaisted-Greenbaum. Auxiliary
    /// variables are only added on the solver, not on the factory. This usually
    /// leads to a reduced heap usage and often faster performance. Before
    /// applying Plaisted-Greenbaum, this method performs an NNF transformation
    /// on the input formula first.
    PgOnSolver,
    /// A solver-internal implementation of Plaisted-Greenbaum. Auxiliary
    /// variables are only added on the solver, not on the factory. This usually
    /// leads to a reduced heap usage and often faster performance. In contrast
    /// to `PgOnSolver`, this method does not transform the input formula to NNF
    /// first. The Plaisted-Greenbaum transformation is applied directly to all
    /// operators of the formula, hence prefix `FULL`. Without the NNF
    /// transformation the formula factory and the heap will not be polluted
    /// with intermediate formulas.
    FullPgOnSolver,
}

impl Default for MiniSatConfig {
    fn default() -> Self {
        Self {
            var_decay: 0.95,
            var_inc: 1.0,
            clause_min: ClauseMinimization::Deep,
            restart_first: 100,
            restart_inc: 2.0,
            clause_decay: 0.999,
            remove_satisfied: true,
            learntsize_factor: 1.0 / 3.0,
            learntsize_inc: 1.1,
            incremental: true,
            initial_phase: false,
            proof_generation: false,
            cnf_method: SolverCnfMethod::PgOnSolver,
            auxiliary_variables_in_models: false,
            bb_initial_ubcheck_for_rotatable_literals: true,
            bb_check_for_complement_model_literals: true,
            bb_check_for_rotatable_literals: true,
        }
    }
}

impl MiniSatConfig {
    /// Sets the variable activity decay factor to a given value. The default
    /// value is 0.95. `var_decay` should be in \[0,1\].
    #[must_use]
    pub const fn var_decay(mut self, var_decay: f64) -> Self {
        self.var_decay = var_decay;
        self
    }

    /// Sets the initial value to bump a variable with each time it is used in
    /// conflict resolution to a given value. The default value is 1.0.
    #[must_use]
    pub const fn var_inc(mut self, var_inc: f64) -> Self {
        self.var_inc = var_inc;
        self
    }

    /// Sets the clause minimization method. The default value is
    /// [`ClauseMinimization#DEEP`].
    #[must_use]
    pub const fn clause_min(mut self, clause_min: ClauseMinimization) -> Self {
        self.clause_min = clause_min;
        self
    }

    /// Sets the base restart interval to the given value. The default value is
    /// 100. `restart_first` should be at least 1.
    #[must_use]
    pub const fn restart_first(mut self, restart_first: usize) -> Self {
        self.restart_first = restart_first;
        self
    }

    /// Sets the restart interval increase factor to the given value. The
    /// default value is 2.0. `restart_inc` should be at least 1.
    #[must_use]
    pub const fn restart_inc(mut self, restart_inc: f64) -> Self {
        self.restart_inc = restart_inc;
        self
    }

    /// Sets the clause activity decay factor to a given value. The default
    /// value is 0.999. `clauseDecay` should be in \[0,1\].
    #[must_use]
    pub const fn clause_decay(mut self, clause_decay: f64) -> Self {
        self.clause_decay = clause_decay;
        self
    }

    /// If turned on, the satisfied original clauses will be removed when
    /// simplifying on level 0, when turned off, only the satisfied learnt
    /// clauses will be removed. The default value is `true`.
    #[must_use]
    pub const fn remove_satisfied(mut self, remove_satisfied: bool) -> Self {
        self.remove_satisfied = remove_satisfied;
        self
    }

    /// Sets the initial limit for learnt clauses as a factor of the original
    /// clauses to the given value. The default value is 1/3.
    #[must_use]
    pub const fn learntsize_factor(mut self, learntsize_factor: f64) -> Self {
        self.learntsize_factor = learntsize_factor;
        self
    }

    /// Sets the factor by which the limit for learnt clauses is multiplied
    /// every restart to a given value. The default value is 1.1.
    #[must_use]
    pub const fn learntsize_inc(mut self, learntsize_inc: f64) -> Self {
        self.learntsize_inc = learntsize_inc;
        self
    }

    /// Turns the incremental mode of the solver off and on. The default value
    /// is `true`.
    #[must_use]
    pub const fn incremental(mut self, incremental: bool) -> Self {
        self.incremental = incremental;
        self
    }

    /// Sets the initial phase of the solver. The default value is `true`.
    #[must_use]
    pub const fn initial_phase(mut self, initial_phase: bool) -> Self {
        self.initial_phase = initial_phase;
        self
    }

    /// Sets whether the information for generating a proof with DRUP should be
    /// recorded or not. The default value is `false`.
    #[must_use]
    pub const fn proof_generation(mut self, proof_generation: bool) -> Self {
        self.proof_generation = proof_generation;
        self
    }

    /// Sets the CNF method for converting formula which are not in CNF for the
    /// solver. The default value is [`SolverCnfMethod::PgOnSolver`].
    #[must_use]
    pub const fn cnf_method(mut self, cnf_method: SolverCnfMethod) -> Self {
        self.cnf_method = cnf_method;
        self
    }

    /// Sets whether auxiliary variables (CNF, cardinality constraints,
    /// pseudo-Boolean constraints) should be included in methods like
    /// [`MiniSat::model()`](`crate::solver::minisat::MiniSat::model()`). If set
    /// to `true`, all variables will be included in these methods,  if set to
    /// `false`, variables starting with ``@RESERVED_CC_``, ``@RESERVED_PB_``,
    /// and ``@RESERVED_CNF_`` will be excluded from the models. The default
    /// value is `false`.
    #[must_use]
    pub const fn auxiliary_variables_in_models(mut self, auxiliary_variables_in_models: bool) -> Self {
        self.auxiliary_variables_in_models = auxiliary_variables_in_models;
        self
    }

    /// Sets whether the backbone algorithm should check for rotatable literals
    /// during initial unit propagation. The default value is `true`.
    #[must_use]
    pub const fn bb_initial_ubcheck_for_rotatable_literals(mut self, bb_initial_ubcheck_for_rotatable_literals: bool) -> Self {
        self.bb_initial_ubcheck_for_rotatable_literals = bb_initial_ubcheck_for_rotatable_literals;
        self
    }

    /// Sets whether the backbone algorithm should check for complement model
    /// literals. The default value is `true`.
    #[must_use]
    pub const fn bb_check_for_complement_model_literals(mut self, bb_check_for_complement_model_literals: bool) -> Self {
        self.bb_check_for_complement_model_literals = bb_check_for_complement_model_literals;
        self
    }

    /// Sets whether the backbone algorithm should check for rotatable literals.
    /// The default value is `true`.
    #[must_use]
    pub const fn bb_check_for_rotatable_literals(mut self, bb_check_for_rotatable_literals: bool) -> Self {
        self.bb_check_for_rotatable_literals = bb_check_for_rotatable_literals;
        self
    }
}

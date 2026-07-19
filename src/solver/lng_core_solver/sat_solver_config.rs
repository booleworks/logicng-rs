/// Configuration for the high-level SAT solver and its CNF integration.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct SatSolverConfig {
    /// Whether incremental save/load operations are enabled.
    pub incremental: bool,
    /// Whether auxiliary variables are included in returned models.
    pub auxiliary_variables_in_models: bool,
    /// Whether the solver records a proof for unsatisfiable-core extraction.
    pub proof_generation: bool,
    /// Whether cardinality constraints may use native at-most clauses.
    pub use_at_most_clauses: bool,
    /// Method used to convert formulas to clauses.
    pub cnf_method: CnfMethod,
    /// Learnt-clause minimization strategy.
    pub clause_minimization: ClauseMinimization,
    /// Initial phase selected for newly created variables.
    pub initial_phase: bool,
    /// Low-level CDCL and Glucose tuning parameters.
    pub low_level_config: SatSolverLowLevelConfig,
}

impl Default for SatSolverConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl SatSolverConfig {
    /// Creates a solver configuration with the standard defaults.
    pub fn new() -> Self {
        Self {
            incremental: true,
            auxiliary_variables_in_models: false,
            proof_generation: false,
            use_at_most_clauses: false,
            cnf_method: CnfMethod::PgOnSolver,
            initial_phase: false,
            clause_minimization: ClauseMinimization::Deep,
            low_level_config: SatSolverLowLevelConfig::new(),
        }
    }

    /// Returns whether proof generation is configured.
    pub const fn configured_proof_generation(&self) -> bool {
        self.proof_generation
    }

    /// Sets whether proof generation is enabled.
    pub const fn with_proof_generation(mut self, proof_generation: bool) -> Self {
        self.proof_generation = proof_generation;
        self
    }

    /// Sets whether proof generation is enabled.
    pub const fn proof_generation(self, proof_generation: bool) -> Self {
        self.with_proof_generation(proof_generation)
    }

    /// Sets whether incremental solver states are enabled.
    pub const fn incremental(mut self, incremental: bool) -> Self {
        self.incremental = incremental;
        self
    }

    /// Sets whether returned models contain auxiliary variables.
    pub const fn auxiliary_variables_in_models(mut self, value: bool) -> Self {
        self.auxiliary_variables_in_models = value;
        self
    }

    /// Returns whether native at-most clauses are configured.
    pub const fn configured_use_at_most_clauses(&self) -> bool {
        self.use_at_most_clauses
    }

    /// Sets whether native at-most clauses may be used.
    pub const fn with_use_at_most_clauses(mut self, use_at_most_clauses: bool) -> Self {
        self.use_at_most_clauses = use_at_most_clauses;
        self
    }

    /// Sets whether native at-most clauses may be used.
    pub const fn use_at_most_clauses(self, use_at_most_clauses: bool) -> Self {
        self.with_use_at_most_clauses(use_at_most_clauses)
    }

    /// Returns the configured CNF conversion method.
    pub const fn configured_cnf_method(&self) -> CnfMethod {
        self.cnf_method
    }

    /// Sets the CNF conversion method.
    pub const fn with_cnf_method(mut self, cnf_method: CnfMethod) -> Self {
        self.cnf_method = cnf_method;
        self
    }

    /// Sets the CNF conversion method.
    pub const fn cnf_method(self, cnf_method: CnfMethod) -> Self {
        self.with_cnf_method(cnf_method)
    }

    /// Returns the configured learnt-clause minimization strategy.
    pub const fn clause_minimization(&self) -> ClauseMinimization {
        self.clause_minimization
    }

    /// Sets the learnt-clause minimization strategy.
    pub const fn with_clause_minimization(
        mut self,
        clause_minimization: ClauseMinimization,
    ) -> Self {
        self.clause_minimization = clause_minimization;
        self
    }

    /// Sets the learnt-clause minimization strategy.
    pub const fn clause_min(self, clause_minimization: ClauseMinimization) -> Self {
        self.with_clause_minimization(clause_minimization)
    }

    /// Returns the configured initial variable phase.
    pub const fn configured_initial_phase(&self) -> bool {
        self.initial_phase
    }

    /// Sets the initial phase for newly created variables.
    pub const fn with_initial_phase(mut self, initial_phase: bool) -> Self {
        self.initial_phase = initial_phase;
        self
    }

    /// Sets the initial phase for newly created variables.
    pub const fn initial_phase(self, initial_phase: bool) -> Self {
        self.with_initial_phase(initial_phase)
    }

    /// Returns the low-level solver configuration.
    pub const fn low_level_config(&self) -> &SatSolverLowLevelConfig {
        &self.low_level_config
    }

    /// Replaces the low-level solver configuration.
    pub const fn with_low_level_config(
        mut self,
        low_level_config: SatSolverLowLevelConfig,
    ) -> Self {
        self.low_level_config = low_level_config;
        self
    }
}

/// Method used to translate formulas into CNF clauses for the solver.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum CnfMethod {
    /// Convert the complete formula to CNF in the formula factory.
    FactoryCnf,
    /// Apply Plaisted-Greenbaum encoding while adding the formula to the solver.
    PgOnSolver,
    /// Apply the full Plaisted-Greenbaum encoding on the solver.
    FullPgOnSolver,
}

/// Strategy used to minimize learnt clauses during conflict analysis.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum ClauseMinimization {
    /// Do not minimize learnt clauses.
    None,
    /// Remove literals with directly redundant reasons.
    Basic,
    /// Recursively detect redundant literals.
    Deep,
}

/// Low-level tuning parameters for CDCL search and database management.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct SatSolverLowLevelConfig {
    var_decay: f64,
    var_inc: f64,
    restart_first: isize,
    restart_inc: f64,
    clause_decay: f64,

    // Glucose-related configuration
    lb_lbd_minimizing_clause: usize,
    lb_lbd_frozen_clause: usize,
    lb_size_minimizing_clause: usize,
    first_reduce_db: usize,
    special_inc_reduce_db: isize,
    inc_reduce_db: isize,
    factor_k: f64,
    factor_r: f64,
    size_lbd_queue: usize,
    size_trail_queue: usize,
    reduce_on_size: bool,
    reduce_on_size_size: usize,
    max_var_decay: f64,
}

impl Default for SatSolverLowLevelConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl SatSolverLowLevelConfig {
    /// Creates the standard low-level configuration.
    pub const fn new() -> Self {
        Self {
            var_decay: 0.95,
            var_inc: 1.0,
            restart_first: 100,
            restart_inc: 2.0,
            clause_decay: 0.999,
            lb_lbd_minimizing_clause: 6,
            lb_lbd_frozen_clause: 30,
            lb_size_minimizing_clause: 30,
            first_reduce_db: 2000,
            special_inc_reduce_db: 1000,
            inc_reduce_db: 300,
            factor_k: 0.8,
            factor_r: 1.4,
            size_lbd_queue: 50,
            size_trail_queue: 5000,
            reduce_on_size: false,
            reduce_on_size_size: 12,
            max_var_decay: 0.95,
        }
    }

    /// Returns the variable-activity decay factor.
    pub const fn var_decay(&self) -> f64 {
        self.var_decay
    }

    /// Sets the variable-activity decay factor.
    pub const fn with_var_decay(mut self, var_decay: f64) -> Self {
        self.var_decay = var_decay;
        self
    }

    /// Returns the initial variable-activity increment.
    pub const fn var_inc(&self) -> f64 {
        self.var_inc
    }

    /// Sets the initial variable-activity increment.
    pub const fn with_var_inc(mut self, var_inc: f64) -> Self {
        self.var_inc = var_inc;
        self
    }

    /// Returns the initial restart interval.
    pub const fn restart_first(&self) -> isize {
        self.restart_first
    }

    /// Sets the initial restart interval.
    pub const fn with_restart_first(mut self, restart_first: isize) -> Self {
        self.restart_first = restart_first;
        self
    }

    /// Returns the restart-interval growth factor.
    pub const fn restart_inc(&self) -> f64 {
        self.restart_inc
    }

    /// Sets the restart-interval growth factor.
    pub const fn with_restart_inc(mut self, restart_inc: f64) -> Self {
        self.restart_inc = restart_inc;
        self
    }

    /// Returns the learnt-clause activity decay factor.
    pub const fn clause_decay(&self) -> f64 {
        self.clause_decay
    }

    /// Sets the learnt-clause activity decay factor.
    pub const fn with_clause_decay(mut self, clause_decay: f64) -> Self {
        self.clause_decay = clause_decay;
        self
    }

    /// Returns the LBD threshold for binary-resolution minimization.
    pub const fn lb_lbd_minimizing_clause(&self) -> usize {
        self.lb_lbd_minimizing_clause
    }

    /// Sets the LBD threshold for binary-resolution minimization.
    pub const fn with_lb_lbd_minimizing_clause(mut self, lb_lbd_minimizing_clause: usize) -> Self {
        self.lb_lbd_minimizing_clause = lb_lbd_minimizing_clause;
        self
    }

    /// Returns the LBD threshold used to freeze improved clauses.
    pub const fn lb_lbd_frozen_clause(&self) -> usize {
        self.lb_lbd_frozen_clause
    }

    /// Sets the LBD threshold used to freeze improved clauses.
    pub const fn with_lb_lbd_frozen_clause(mut self, lb_lbd_frozen_clause: usize) -> Self {
        self.lb_lbd_frozen_clause = lb_lbd_frozen_clause;
        self
    }

    /// Returns the maximum learnt-clause size considered for minimization.
    pub const fn lb_size_minimizing_clause(&self) -> usize {
        self.lb_size_minimizing_clause
    }

    /// Sets the maximum learnt-clause size considered for minimization.
    pub const fn with_lb_size_minimizing_clause(
        mut self,
        lb_size_minimizing_clause: usize,
    ) -> Self {
        self.lb_size_minimizing_clause = lb_size_minimizing_clause;
        self
    }

    /// Returns the conflict threshold for the first database reduction.
    pub const fn first_reduce_db(&self) -> usize {
        self.first_reduce_db
    }

    /// Sets the conflict threshold for the first database reduction.
    pub const fn with_first_reduce_db(mut self, first_reduce_db: usize) -> Self {
        self.first_reduce_db = first_reduce_db;
        self
    }

    /// Returns the extra database-reduction interval increment.
    pub const fn special_inc_reduce_db(&self) -> usize {
        self.special_inc_reduce_db as usize
    }

    /// Sets the extra database-reduction interval increment.
    pub const fn with_special_inc_reduce_db(mut self, special_inc_reduce_db: isize) -> Self {
        self.special_inc_reduce_db = special_inc_reduce_db;
        self
    }

    /// Returns the regular database-reduction interval increment.
    pub const fn inc_reduce_db(&self) -> usize {
        self.inc_reduce_db as usize
    }

    /// Sets the regular database-reduction interval increment.
    pub const fn with_inc_reduce_db(mut self, inc_reduce_db: isize) -> Self {
        self.inc_reduce_db = inc_reduce_db;
        self
    }

    /// Returns the factor used to trigger dynamic restarts.
    pub const fn factor_k(&self) -> f64 {
        self.factor_k
    }

    /// Sets the factor used to trigger dynamic restarts.
    pub const fn with_factor_k(mut self, factor_k: f64) -> Self {
        self.factor_k = factor_k;
        self
    }

    /// Returns the factor used to block dynamic restarts.
    pub const fn factor_r(&self) -> f64 {
        self.factor_r
    }

    /// Sets the factor used to block dynamic restarts.
    pub const fn with_factor_r(mut self, factor_r: f64) -> Self {
        self.factor_r = factor_r;
        self
    }

    /// Returns the moving LBD queue capacity.
    pub const fn size_lbd_queue(&self) -> usize {
        self.size_lbd_queue
    }

    /// Sets the moving LBD queue capacity.
    pub const fn with_size_lbd_queue(mut self, size_lbd_queue: usize) -> Self {
        self.size_lbd_queue = size_lbd_queue;
        self
    }

    /// Returns the moving trail-length queue capacity.
    pub const fn size_trail_queue(&self) -> usize {
        self.size_trail_queue
    }

    /// Sets the moving trail-length queue capacity.
    pub const fn with_size_trail_queue(mut self, size_trail_queue: usize) -> Self {
        self.size_trail_queue = size_trail_queue;
        self
    }

    /// Returns whether clause size contributes to the LBD score.
    pub const fn reduce_on_size(&self) -> bool {
        self.reduce_on_size
    }

    /// Sets whether clause size contributes to the LBD score.
    pub const fn with_reduce_on_size(mut self, reduce_on_size: bool) -> Self {
        self.reduce_on_size = reduce_on_size;
        self
    }

    /// Returns the size threshold for size-aware LBD scoring.
    pub const fn reduce_on_size_size(&self) -> usize {
        self.reduce_on_size_size
    }

    /// Sets the size threshold for size-aware LBD scoring.
    pub const fn with_reduce_on_size_size(mut self, reduce_on_size_size: usize) -> Self {
        self.reduce_on_size_size = reduce_on_size_size;
        self
    }

    /// Returns the maximum adaptive variable-decay factor.
    pub const fn max_var_decay(&self) -> f64 {
        self.max_var_decay
    }

    /// Sets the maximum adaptive variable-decay factor.
    pub const fn with_max_var_decay(mut self, max_var_decay: f64) -> Self {
        self.max_var_decay = max_var_decay;
        self
    }
}

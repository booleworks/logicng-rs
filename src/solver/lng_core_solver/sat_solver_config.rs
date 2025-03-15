#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct SatSolverConfig {
    pub proof_generation: bool,
    pub use_at_most_clauses: bool,
    pub cnf_method: CnfMethod,
    pub clause_minimization: ClauseMinimization,
    pub initial_phase: bool,
    pub low_level_config: SatSolverLowLevelConfig,
}

impl Default for SatSolverConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl SatSolverConfig {
    pub fn new() -> Self {
        Self {
            proof_generation: false,
            use_at_most_clauses: false,
            cnf_method: CnfMethod::PgOnSolver,
            initial_phase: false,
            clause_minimization: ClauseMinimization::Deep,
            low_level_config: SatSolverLowLevelConfig::new(),
        }
    }

    pub const fn proof_generation(&self) -> bool {
        self.proof_generation
    }

    pub const fn with_proof_generation(mut self, proof_generation: bool) -> Self {
        self.proof_generation = proof_generation;
        self
    }

    pub const fn use_at_most_clauses(&self) -> bool {
        self.use_at_most_clauses
    }

    pub const fn with_use_at_most_clauses(mut self, use_at_most_clauses: bool) -> Self {
        self.use_at_most_clauses = use_at_most_clauses;
        self
    }

    pub const fn cnf_method(&self) -> CnfMethod {
        self.cnf_method
    }

    pub const fn with_cnf_method(mut self, cnf_method: CnfMethod) -> Self {
        self.cnf_method = cnf_method;
        self
    }

    pub const fn clause_minimization(&self) -> ClauseMinimization {
        self.clause_minimization
    }

    pub const fn with_clause_minimization(mut self, clause_minimization: ClauseMinimization) -> Self {
        self.clause_minimization = clause_minimization;
        self
    }

    pub const fn initial_phase(&self) -> bool {
        self.initial_phase
    }

    pub const fn with_initial_phase(mut self, initial_phase: bool) -> Self {
        self.initial_phase = initial_phase;
        self
    }

    pub const fn low_level_config(&self) -> &SatSolverLowLevelConfig {
        &self.low_level_config
    }

    pub const fn with_low_level_config(mut self, low_level_config: SatSolverLowLevelConfig) -> Self {
        self.low_level_config = low_level_config;
        self
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum CnfMethod {
    FactoryCnf,
    PgOnSolver,
    FullPgOnSolver,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum ClauseMinimization {
    None,
    Basic,
    Deep,
}

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

    pub const fn var_decay(&self) -> f64 {
        self.var_decay
    }

    pub const fn with_var_decay(mut self, var_decay: f64) -> Self {
        self.var_decay = var_decay;
        self
    }

    pub const fn var_inc(&self) -> f64 {
        self.var_inc
    }

    pub const fn with_var_inc(mut self, var_inc: f64) -> Self {
        self.var_inc = var_inc;
        self
    }

    pub const fn restart_first(&self) -> isize {
        self.restart_first
    }

    pub const fn with_restart_first(mut self, restart_first: isize) -> Self {
        self.restart_first = restart_first;
        self
    }

    pub const fn restart_inc(&self) -> f64 {
        self.restart_inc
    }

    pub const fn with_restart_inc(mut self, restart_inc: f64) -> Self {
        self.restart_inc = restart_inc;
        self
    }

    pub const fn clause_decay(&self) -> f64 {
        self.clause_decay
    }

    pub const fn with_clause_decay(mut self, clause_decay: f64) -> Self {
        self.clause_decay = clause_decay;
        self
    }

    pub const fn lb_lbd_minimizing_clause(&self) -> usize {
        self.lb_lbd_minimizing_clause
    }

    pub const fn with_lb_lbd_minimizing_clause(mut self, lb_lbd_minimizing_clause: usize) -> Self {
        self.lb_lbd_minimizing_clause = lb_lbd_minimizing_clause;
        self
    }

    pub const fn lb_lbd_frozen_clause(&self) -> usize {
        self.lb_lbd_frozen_clause
    }

    pub const fn with_lb_lbd_frozen_clause(mut self, lb_lbd_frozen_clause: usize) -> Self {
        self.lb_lbd_frozen_clause = lb_lbd_frozen_clause;
        self
    }

    pub const fn lb_size_minimizing_clause(&self) -> usize {
        self.lb_size_minimizing_clause
    }

    pub const fn with_lb_size_minimizing_clause(mut self, lb_size_minimizing_clause: usize) -> Self {
        self.lb_size_minimizing_clause = lb_size_minimizing_clause;
        self
    }

    pub const fn first_reduce_db(&self) -> usize {
        self.first_reduce_db
    }

    pub const fn with_first_reduce_db(mut self, first_reduce_db: usize) -> Self {
        self.first_reduce_db = first_reduce_db;
        self
    }

    pub const fn special_inc_reduce_db(&self) -> usize {
        self.first_reduce_db
    }

    pub const fn with_special_inc_reduce_db(mut self, special_inc_reduce_db: isize) -> Self {
        self.special_inc_reduce_db = special_inc_reduce_db;
        self
    }

    pub const fn inc_reduce_db(&self) -> usize {
        self.first_reduce_db
    }

    pub const fn with_inc_reduce_db(mut self, inc_reduce_db: isize) -> Self {
        self.inc_reduce_db = inc_reduce_db;
        self
    }

    pub const fn factor_k(&self) -> f64 {
        self.factor_k
    }

    pub const fn with_factor_k(mut self, factor_k: f64) -> Self {
        self.factor_k = factor_k;
        self
    }

    pub const fn factor_r(&self) -> f64 {
        self.factor_r
    }

    pub const fn with_factor_r(mut self, factor_r: f64) -> Self {
        self.factor_r = factor_r;
        self
    }

    pub const fn size_lbd_queue(&self) -> usize {
        self.size_lbd_queue
    }

    pub const fn with_size_lbd_queue(mut self, size_lbd_queue: usize) -> Self {
        self.size_lbd_queue = size_lbd_queue;
        self
    }

    pub const fn size_trail_queue(&self) -> usize {
        self.size_trail_queue
    }

    pub const fn with_size_trail_queue(mut self, size_trail_queue: usize) -> Self {
        self.size_trail_queue = size_trail_queue;
        self
    }

    pub const fn reduce_on_size(&self) -> bool {
        self.reduce_on_size
    }

    pub const fn with_reduce_on_size(mut self, reduce_on_size: bool) -> Self {
        self.reduce_on_size = reduce_on_size;
        self
    }

    pub const fn reduce_on_size_size(&self) -> usize {
        self.reduce_on_size_size
    }

    pub const fn with_reduce_on_size_size(mut self, reduce_on_size_size: usize) -> Self {
        self.reduce_on_size_size = reduce_on_size_size;
        self
    }

    pub const fn max_var_decay(&self) -> f64 {
        self.max_var_decay
    }

    pub const fn with_max_var_decay(mut self, max_var_decay: f64) -> Self {
        self.max_var_decay = max_var_decay;
        self
    }
}

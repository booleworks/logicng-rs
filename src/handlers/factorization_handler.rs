use crate::formulas::EncodedFormula;
use crate::handlers::handler::ComputationHandler;

/// A handler trait for CNF/DNF factorization.
pub trait FactorizationHandler: ComputationHandler {
    /// Called when a distribution happened.
    fn performed_distribution(&mut self) -> Result<(), FactorizationError> {
        Ok(())
    }

    /// Called when a new clause was created.
    fn created_clause(&mut self, _clause: EncodedFormula) -> Result<(), FactorizationError> {
        Ok(())
    }
}

/// Reasons for a handler to abort.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactorizationError {
    /// The number of allowed clause is exceeded.
    ClauseLimitReached,
    /// The number of allowed distributions is exceeded.
    DistributionLimitReached,
}

/// A no-operation hander for factorizations. This handler does never abort or
/// interrupt a calculation.
pub struct NopFactorizationHandler {}

impl ComputationHandler for NopFactorizationHandler {}

impl FactorizationHandler for NopFactorizationHandler {}

/// A clause limiting handler. This handler does abort if the number of
/// distributions or the number of new clauses exceed the specified limits.
pub struct ClauseLimitFactorizationHandler {
    /// Indicates whether the handler is aborted.
    pub aborted: bool,
    /// Number of distribution already performed.
    pub dists: u64,
    /// Number of clauses already added.
    pub clauses: u64,
    dists_limit: u64,
    clauses_limit: u64,
}

impl ClauseLimitFactorizationHandler {
    /// Constructs a new handler which allows a maximum number of distributions
    /// and new clauses.
    pub const fn new(dists_limit: u64, clauses_limit: u64) -> Self {
        Self { aborted: false, dists: 0, clauses: 0, dists_limit, clauses_limit }
    }
}

impl ComputationHandler for ClauseLimitFactorizationHandler {
    fn started(&mut self) {
        self.aborted = false;
        self.dists = 0;
        self.clauses = 0;
    }

    fn aborted(&self) -> bool {
        self.aborted
    }
}

impl FactorizationHandler for ClauseLimitFactorizationHandler {
    fn performed_distribution(&mut self) -> Result<(), FactorizationError> {
        self.dists += 1;
        self.aborted = self.dists > self.dists_limit;
        if self.aborted { Err(FactorizationError::DistributionLimitReached) } else { Ok(()) }
    }

    fn created_clause(&mut self, _clause: EncodedFormula) -> Result<(), FactorizationError> {
        self.clauses += 1;
        self.aborted = self.clauses > self.clauses_limit;
        if self.aborted { Err(FactorizationError::ClauseLimitReached) } else { Ok(()) }
    }
}

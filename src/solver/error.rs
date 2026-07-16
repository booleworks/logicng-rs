#![allow(missing_docs)]
use logicng_open_wbo_sys::ffi;
use thiserror::Error;

use crate::formulas::EncodedFormula;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolverError {
    #[error("solver is in undef state, call 'sat' before")]
    NotSolved,

    #[error("unexpected formula in cnf: {formula:?}")]
    NotInCnf { formula: EncodedFormula },

    #[error("invalid solver state")]
    InvalidSolverState,

    #[error("save/load state requires incremental mode")]
    StateRequiresIncrementalMode,

    #[error("unsat core cannot be computed when proof generation is not enabled")]
    ProofGenerationRequired,

    #[error("unsat core cannot be computed on a satisfiable formula")]
    UnsatCoreOnSatFormula,

    #[error("unsat core cannot be computed when assumption solving was used")]
    UnsatCoreWithAssumptions,

    #[error("bound for optimization function was too large: {bound:?}")]
    OptimizationBoundTooLarge { bound: usize },

    #[error("openwbo error: {error:?}")]
    ExternalError { error: ffi::OpenWboError },

    #[error("invalid openwbo response")]
    InvalidExternalResponse,

    #[error("illegal openwbo configuration")]
    IllegalConfig,

    #[error("openwbo configuration does not support weighted clauses")]
    IllegalWeightedClause,

    #[error("openwbo solver does not have a model")]
    IllegalModelRequest,

    #[error("failed to initialize the openwbo solver")]
    InitializationError,
}

#![allow(missing_docs)]
#[cfg(feature = "open_wbo")]
use logicng_open_wbo_sys::ffi;
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolverError {
    #[error("solver is in undef state, call 'sat' before")]
    NotSolved,

    #[error("invalid solver state")]
    InvalidSolverState,

    #[error("unsat core cannot be computed when proof generation is not enabled")]
    ProofGenerationRequired,

    #[error("unsat core cannot be computed on a satisfiable formula")]
    UnsatCoreOnSatFormula,

    #[error("unsat core cannot be computed when assumption solving was used")]
    UnsatCoreWithAssumptions,

    #[error("bound for optimization function was too large: {bound:?}")]
    OptimizationBoundTooLarge { bound: usize },

    #[error("optimization requires a satisfiable solver state")]
    OptimizationOnUnsat,

    #[error("solver reported satisfiable but did not provide a model")]
    MissingModel,

    #[error("proof data is inconsistent with the solver state")]
    InvalidProofData,

    #[error("Plaisted-Greenbaum transformation violated an internal invariant")]
    InvalidPgTransformation,

    #[error("SAT solver violated an internal invariant")]
    InternalInvariant,

    #[cfg(feature = "open_wbo")]
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

#![allow(missing_docs)]
use thiserror::Error;

/// Errors produced by SAT solvers and SAT-based solver functions.
#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SatError {
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
    OptimizationBoundTooLarge {
        /// Bound which could not be represented.
        bound: usize,
    },

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

    #[error("invalid SAT solver response")]
    InvalidExternalResponse,
}

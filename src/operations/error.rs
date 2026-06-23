#![allow(missing_docs)]
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum OperationError {
    #[error("pure expansion for a PBC is not supported")]
    PureEncodingNoPbc,

    #[error("pure expansion for a CC of type other than amo or exo is not supported")]
    PureEncodingNoCc,

    #[error("the number of don't care variables is too large for an u32")]
    MCTooManyDontCares,

    #[error("expected model counting variables to contain all of the formulas' variables")]
    MCNotAllVars,

    #[error("the clause limit was reached during factorization")]
    FactorizationClauseLimit,

    #[error("the distribution limit was reached during factorization")]
    FactorizationDistributionLimit,

    #[error("the formula is not a clause or term")]
    NotClauseOrTerm,
}

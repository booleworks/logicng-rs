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

    #[error("factorization cannot be used as fallback algorithm")]
    FactorizationAsFallback,

    #[error("the formula is not a clause or term")]
    NotClauseOrTerm,

    #[error("substitution of a formula for a variable in a cc or pbc")]
    SubstFormCcPbc,

    #[error("subsumption can only be applied to cnf")]
    SubsumptionNoCnf,

    #[error("subsumption can only be applied to dnf")]
    SubsumptionNoDnf,
}

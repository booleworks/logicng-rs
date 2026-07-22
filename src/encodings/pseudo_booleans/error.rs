#![allow(missing_docs)]
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PbcError {
    #[error(
        "right hand side of pseudo-boolean constraint is too large for this architecture: {rhs:?}"
    )]
    TooLargeRhs { rhs: i64 },

    #[error(
        "coefficient of pseudo-boolean constraint is too large for this architecture: {coefficient:?}"
    )]
    TooLargeCoefficient { coefficient: i64 },

    #[error("integer overflow while normalizing pseudo-boolean constraint: {operation}")]
    NormalizationOverflow { operation: &'static str },

    #[error("normalization produced an unexpected formula type")]
    UnexpectedNormalizedFormula,
}

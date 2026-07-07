#![allow(missing_docs)]
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CcError {
    #[error(
        "right hand side of cardinality constraint is too large for this architecture: {rhs:?}"
    )]
    TooLargeRhs { rhs: u64 },

    #[error("incremental encodings are only supported for at-most-k and at-least k constraints")]
    IncrementalNotSupported,

    #[error("cardinality constraint config for parameter {param:?} is invalid: {value:?}")]
    InvalidConfig { param: &'static str, value: usize },

    #[error("new upper bound {rhs:?} does not tighten the current bound of {current:?}")]
    UpperBoundNotTighten { rhs: usize, current: usize },

    #[error("no valid amk-encoder for incremental encoding")]
    NoAmkEncoder,

    #[error("new lower bound {rhs:?} does not tighten the current bound of {current:?}")]
    LowerBoundNotTighten { rhs: usize, current: usize },

    #[error("no valid alk-encoder for incremental encoding")]
    NoAlkEncoder,
}

#![allow(missing_docs)]
use crate::{cardinality_constraints::CcError, operations::OperationError};

/// A generic LogicNG result which carries the result or an error
pub type LngResult<T> = Result<T, LngError>;

/// A generic LogicNG error
#[derive(thiserror::Error, Debug)]
#[non_exhaustive]
pub enum LngError {
    #[error("cardinality constraint: {0}")]
    Cc(#[from] CcError),

    #[error("operation: {0}")]
    Operation(#[from] OperationError),

    #[error("variable {var:?} is not known in the given formula factory")]
    UnknownVariable { var: String },
}

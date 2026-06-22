#![allow(missing_docs)]
use crate::cardinality_constraints::CcError;

/// A generic LogicNG result which carries the result or an error
pub type LngResult<T> = Result<T, LngError>;

/// A generic LogicNG error
#[derive(thiserror::Error, Debug)]
#[non_exhaustive]
pub enum LngError {
    #[error("cardinality constraint: {0}")]
    Cc(#[from] CcError),
}

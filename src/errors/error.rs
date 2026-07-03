#![allow(missing_docs)]
use crate::{cardinality_constraints::CcError, graphs::GraphError, operations::OperationError, pseudo_booleans::PbcError};

/// A generic LogicNG result which carries the result or an error
pub type LngResult<T> = Result<T, LngError>;

/// A generic LogicNG error
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LngError {
    #[error("cardinality constraint: {0}")]
    Cc(#[from] CcError),

    #[error("pseudo-boolean constraint: {0}")]
    Pbc(#[from] PbcError),

    #[error("operation: {0}")]
    Operation(#[from] OperationError),

    #[error("graph: {0}")]
    Graph(#[from] GraphError),

    #[error("variable {var:?} is not known in the given formula factory")]
    UnknownVariable { var: String },
}

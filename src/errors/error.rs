#![allow(missing_docs)]
use crate::{
    cardinality_constraints::CcError,
    graphs::GraphError,
    knowledge_compilation::{bdd::BddError, dnnf::DnnfError},
    operations::OperationError,
    parser::ParserError,
    pseudo_booleans::PbcError,
    util::UtilError,
};

/// A generic LogicNG result which carries the result or an error
pub type LngResult<T> = Result<T, LngError>;

/// A generic LogicNG error
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LngError {
    #[error("parser: {0}")]
    Parser(#[from] ParserError),

    #[error("cardinality constraint: {0}")]
    Cc(#[from] CcError),

    #[error("pseudo-boolean constraint: {0}")]
    Pbc(#[from] PbcError),

    #[error("operation: {0}")]
    Operation(#[from] OperationError),

    #[error("graph: {0}")]
    Graph(#[from] GraphError),

    #[error("util: {0}")]
    Util(#[from] UtilError),

    #[error("bdd: {0}")]
    Bdd(#[from] BddError),

    #[error("dnnf: {0}")]
    Dnnf(#[from] DnnfError),

    #[error("variable {var:?} is not known in the given formula factory")]
    UnknownVariable { var: String },
}

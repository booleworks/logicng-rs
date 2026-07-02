#![allow(missing_docs)]
use thiserror::Error;

use crate::formulas::EncodedFormula;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum GraphError {
    #[error("cannot find node with index {node_index:?}")]
    UnknownNode { node_index: usize },

    #[error("unexpected formula type in cnf: {formula:?}")]
    UnexpectedFormulaInCnf { formula: EncodedFormula },
}

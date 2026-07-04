#![allow(missing_docs)]
use thiserror::Error;

use crate::formulas::Variable;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BddError {
    #[error("invalid number of variables {num_vars:?}")]
    InvalidNumberOfVars { num_vars: usize },

    #[error("no free variables left")]
    NoFreeVars,

    #[error("invalid variable number {var_num:?}")]
    InvalidVarNum { var_num: usize },

    #[error("invalid node number {node_num:?}")]
    InvalidNodeNum { node_num: usize },

    #[error("invalid variable {var:?}")]
    InvalidVar { var: Variable },

    #[error("bdd has no unique path")]
    NoUniquePath,

    #[error("model contains negative variable")]
    ModelNegVar,
}

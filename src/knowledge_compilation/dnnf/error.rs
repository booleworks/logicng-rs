#![allow(missing_docs)]
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DnnfError {
    #[error("variables in formula and ordering are not the same")]
    VarsFormulaOrderingNeq,

    #[error("expected a cnf formula")]
    NonCnfFormula,

    #[error("dtree is already finished")]
    DTreeFinished,

    #[error("empty dtree leaf")]
    EmptyDTreeLeaf,

    #[error("empty list of trees")]
    EmptyTrees,
}

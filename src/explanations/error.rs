#![allow(missing_docs)]
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ExplanationError {
    #[error("cannot generate a mus from an empty list of propositions")]
    EmptyPropositions,

    #[error("cannot generate a mus for a satisfiable formula")]
    SatisfiableFormula,
}

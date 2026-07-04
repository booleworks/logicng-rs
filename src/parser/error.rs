#![allow(missing_docs)]
use thiserror::Error;

use crate::parser::pseudo_boolean_parser::Rule;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParserError {
    #[error("syntax error")]
    Syntax(Box<pest::error::Error<Rule>>),

    #[error("integer overflow for {value:?}")]
    IntegerOverflow { value: String },

    #[error("coefficient overflow for {value:?}")]
    CoefficientOverflow { value: String },

    #[error("unexpected rule {rule:?}")]
    UnexpectedRule { rule: String },

    #[error("unexpected end")]
    UnexpectedEnd,
}

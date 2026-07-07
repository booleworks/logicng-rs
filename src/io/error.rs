#![allow(missing_docs)]

use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum IoError {
    #[error("could not open file {path:?}: {reason}")]
    OpenFile { path: String, reason: String },

    #[error("could not create file {path:?}: {reason}")]
    CreateFile { path: String, reason: String },

    #[error("could not read from file {path:?}: {reason}")]
    ReadFile { path: String, reason: String },

    #[error("could not write to file {path:?}: {reason}")]
    WriteFile { path: String, reason: String },

    #[error("invalid formula in file {path:?} on line {line}: {reason}")]
    InvalidFormula {
        path: String,
        line: usize,
        reason: String,
    },

    #[error("DIMACS clause line in file {path:?} on line {line} does not end with 0")]
    DimacsLineWithoutTerminator { path: String, line: usize },

    #[error("invalid DIMACS literal {literal:?} in file {path:?} on line {line}")]
    InvalidDimacsLiteral {
        path: String,
        line: usize,
        literal: String,
    },

    #[error("DIMACS literal {literal:?} in file {path:?} on line {line} overflows")]
    DimacsLiteralOverflow {
        path: String,
        line: usize,
        literal: String,
    },

    #[error("path is not valid UTF-8")]
    InvalidPath,
}

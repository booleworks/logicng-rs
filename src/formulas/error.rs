#![allow(missing_docs)]
use thiserror::Error;

use crate::formulas::CType;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FormulaError {
    #[error("given values do not represent a valid cardinality constraint: {comp:?} {rhs:?}")]
    NoCc { comp: CType, rhs: u32 },

    #[error("pbc: number of literals {lits:?} != number of coefficients {coeffs:?}")]
    NoPbc { lits: usize, coeffs: usize },
}

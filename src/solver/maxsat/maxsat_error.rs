#![allow(missing_docs)]
use thiserror::Error;

use crate::backends::BackendId;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MaxSatError {
    #[error("invalid solver state")]
    InvalidSolverState,

    #[error("{backend} maxsat backend error: {message}")]
    BackendError { backend: BackendId, message: String },

    #[error("invalid maxsat solver response")]
    InvalidExternalResponse,

    #[error("illegal maxsat solver configuration")]
    IllegalConfig,

    #[error("maxsat configuration does not support weighted clauses")]
    IllegalWeightedClause,

    #[error("maxsat solver does not have a model")]
    IllegalModelRequest,

    #[error("failed to initialize the maxsat solver")]
    InitializationError,

    #[error("unsupported encoding for encoder method {method:?}")]
    UnsupportedEncoding { method: &'static str },

    #[error("no MaxSAT backend is configured")]
    NoBackendConfigured,

    #[error("cannot load state from maxsat backend {actual} into backend {expected}")]
    InvalidState {
        expected: BackendId,
        actual: BackendId,
    },
}

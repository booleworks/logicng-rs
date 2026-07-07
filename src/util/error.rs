#![allow(missing_docs)]

use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UtilError {
    #[error("formula randomizer config parameter {param:?} is invalid: {reason}")]
    InvalidRandomizerConfig { param: &'static str, reason: &'static str },
}

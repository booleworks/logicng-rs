/// Backend interfaces for MaxSAT computations.
pub mod maxsat;

pub use maxsat::*;

use std::sync::Arc;

use crate::solver::maxsat::{OpenWboConfig, RustOpenWboFactory};

/// Collection of backend factories available to computations.
#[derive(Clone)]
pub struct Backends {
    /// Factory used to create MaxSAT backends.
    maxsat: Arc<dyn MaxSatBackendFactory>,
}

impl Default for Backends {
    fn default() -> Self {
        Self {
            maxsat: Arc::new(RustOpenWboFactory::new(OpenWboConfig::default())),
        }
    }
}

impl Backends {
    /// Returns the backend for MaxSAT solving
    pub fn maxsat(&self) -> &dyn MaxSatBackendFactory {
        self.maxsat.as_ref()
    }
}

/// Global context selecting the backends used by algorithms.
#[derive(Default, Clone)]
pub struct ComputationContext {
    /// Configured backend factories.
    pub backends: Backends,
}

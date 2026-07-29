/// Backend interfaces for MaxSAT computations.
pub mod maxsat;

pub use maxsat::*;

use std::sync::Arc;

/// Collection of backend factories available to computations.
#[derive(Default, Clone)]
pub struct Backends {
    /// Factory used to create MaxSAT backends.
    pub maxsat: Option<Arc<dyn MaxSatBackendFactory>>,
}

/// Global context selecting the backends used by algorithms.
#[derive(Default, Clone)]
pub struct ComputationContext {
    /// Configured backend factories.
    pub backends: Backends,
}

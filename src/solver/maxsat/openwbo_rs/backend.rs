use std::any::Any;

use crate::backends::{
    BackendId, Capabilities, IncDecMaxSatBackend, MaxSatBackend, MaxSatBackendFactory, MaxSatResult,
};
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::handlers::{CancelableResult, ComputationHandler};
use crate::solver::maxsat::MaxSatError;
use crate::solver::maxsat::openwbo_rs::algorithms::{MaxSatState, OpenWboAlgorithm, Solver};
use crate::solver::maxsat::openwbo_rs::config::OpenWboConfig;

/// Backend identifier used by the Rust OpenWBO MaxSAT implementation.
pub const RUST_OPENWBO_BACKEND_ID: BackendId = "Rust OpenWBO";

/// Factory for pure-Rust OpenWBO backends with a fixed configuration.
pub struct RustOpenWboFactory {
    config: OpenWboConfig,
}

impl RustOpenWboFactory {
    /// Creates a factory using `config` for every backend it creates.
    pub fn new(config: OpenWboConfig) -> Self {
        Self { config }
    }
}

impl MaxSatBackendFactory for RustOpenWboFactory {
    fn new_backend(&self) -> LngResult<Box<dyn MaxSatBackend>> {
        Ok(Box::new(RustOpenWboBackend::new(self.config.clone())?))
    }
}

/// Low-level Rust OpenWBO implementation of [`MaxSatBackend`].
///
/// Applications usually construct a [`crate::solver::maxsat::MaxSatSolver`]
/// with [`RustOpenWboFactory`] instead of using this backend directly. This
/// type remains public for custom backend factories and infrastructure.
pub struct RustOpenWboBackend {
    config: OpenWboConfig,
    solver: Solver,
    algo: OpenWboAlgorithm,
}

impl RustOpenWboBackend {
    /// Creates a low-level backend with the given configuration.
    ///
    /// # Errors
    ///
    /// Returns an error if the configuration is invalid or the backend cannot
    /// be initialized.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// # use logicng::solver::maxsat::*;
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let config = OpenWboConfig::default().algorithm(Algorithm::Oll);
    /// let backend = RustOpenWboBackend::new(config)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(config: OpenWboConfig) -> LngResult<Self> {
        let algo = OpenWboAlgorithm::from_config(&config);
        let solver = Solver::new(&config);
        Ok(Self {
            config,
            solver,
            algo,
        })
    }
}

impl MaxSatBackend for RustOpenWboBackend {
    fn backend_id(&self) -> BackendId {
        RUST_OPENWBO_BACKEND_ID
    }

    fn backend_capabilities(&self) -> Capabilities {
        Capabilities {
            weights: self.config.algorithm.weighted(&self.config),
        }
    }

    fn as_inc_dec(&mut self) -> Option<&mut dyn IncDecMaxSatBackend> {
        Some(self)
    }

    fn add_hard_clause(&mut self, clause: EncodedFormula, f: &FormulaFactory) -> LngResult<()> {
        self.solver.add_formula_clause(None, clause, f)
    }

    fn add_soft_clause(
        &mut self,
        weight: u64,
        clause: EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()> {
        self.solver.add_formula_clause(Some(weight), clause, f)
    }

    fn search(
        &mut self,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>> {
        self.algo.search(&mut self.solver, handler)
    }

    fn reset(&mut self) {
        self.solver = Solver::new(&self.config);
        self.algo = OpenWboAlgorithm::from_config(&self.config);
    }
}

impl IncDecMaxSatBackend for RustOpenWboBackend {
    fn save_state(&mut self) -> Box<dyn Any + Send> {
        Box::new(self.solver.save_state())
    }

    fn load_state(&mut self, state: &(dyn Any + Send)) -> LngResult<()> {
        let state = state
            .downcast_ref::<MaxSatState>()
            .ok_or(MaxSatError::InvalidSolverState)?;
        self.solver.load_state(state)
    }
}

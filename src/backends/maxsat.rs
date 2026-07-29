use std::any::Any;

use crate::{
    datastructures::Model,
    errors::LngResult,
    formulas::{EncodedFormula, FormulaFactory},
    handlers::{CancelableResult, ComputationHandler},
};

/// Result returned by a MaxSAT algorithm.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MaxSatResult {
    /// The hard clauses on the solver are already unsatisfiable, optimization
    /// could not be performed.
    Unsatisfiable,

    /// An optimal solution was found. If the search was aborted by a handler,
    /// this result represents the best solution found so far and is not
    /// necessarily globally optimal.
    Optimum {
        /// Sum of the weights of the soft formulas not satisfied by `model`.
        bound: u64,
        /// Model satisfying every hard formula and attaining `bound`.
        model: Model,
    },

    /// The search did not produce a result or a model.
    Undef,
}

/// Stable identifier for a MaxSAT solver backend.
///
/// It is stored in [`MaxSatState`] so that a solver can reject a state created
/// by an incompatible backend.
pub type BackendId = &'static str;

/// Features supported by a particular MaxSAT backend and configuration.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct Capabilities {
    /// Whether soft formulas with weights greater than one are supported.
    pub weights: bool,
}

/// Factory for creating equally configured MaxSAT backends.
///
/// A factory is useful for algorithms which need a fresh solver for each
/// independent computation while remaining agnostic of the concrete solver
/// implementation.
pub trait MaxSatBackendFactory: Send + Sync {
    /// Creates a new, empty backend with the factory's configuration.
    ///
    /// # Errors
    ///
    /// Returns an error if the concrete solver cannot be initialized.
    fn new_backend(&self) -> LngResult<Box<dyn MaxSatBackend>>;
}

/// Low-level interface implemented by MaxSAT backends.
///
/// Applications normally use `solver::maxsat::MaxSatSolver`, which owns a
/// backend and provides formula encoding and computation orchestration.
pub trait MaxSatBackend {
    /// Returns the identifier of this solver's backend.
    ///
    /// All instances which can exchange [`MaxSatState`] values must return the
    /// same identifier.
    fn backend_id(&self) -> BackendId;

    /// Returns the features supported by this solver's current configuration.
    fn backend_capabilities(&self) -> Capabilities;

    /// Returns this backend's incremental/decremental interface, if supported.
    ///
    /// A return value of `None` means that states cannot be saved and restored.
    fn as_inc_dec(&mut self) -> Option<&mut dyn IncDecMaxSatBackend> {
        None
    }

    /// Adds one CNF clause as a hard constraint.
    ///
    /// This is an implementation hook. Applications should generally call
    /// [`Self::add_hard_formula`], which performs the necessary CNF conversion.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend rejects the clause.
    fn add_hard_clause(&mut self, clause: EncodedFormula, f: &FormulaFactory) -> LngResult<()>;

    /// Adds one CNF clause as a soft constraint with the given weight.
    ///
    /// This is an implementation hook. Applications should generally call
    /// [`Self::add_soft_formula`], which validates the weight and encodes
    /// arbitrary formulas.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend rejects the clause or weight.
    fn add_soft_clause(
        &mut self,
        weight: u64,
        clause: EncodedFormula,
        f: &FormulaFactory,
    ) -> LngResult<()>;

    /// Runs the backend search with a computation handler.
    ///
    /// This is an implementation hook used by [`Self::solve_with_handler`].
    /// Implementations should return a partial optimum, including its model,
    /// when cancellation occurs after a candidate solution was found.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend fails or returns an invalid response.
    fn search(
        &mut self,
        handler: &mut dyn ComputationHandler,
    ) -> LngResult<CancelableResult<MaxSatResult>>;

    /// Clears all formulas, auxiliary state, and results from this solver.
    ///
    /// The concrete solver type and its configuration are retained.
    fn reset(&mut self);
}

/// Additional backend operations for incremental/decremental MaxSAT solving.
pub trait IncDecMaxSatBackend: MaxSatBackend {
    /// Saves the current backend state as an opaque value.
    fn save_state(&mut self) -> Box<dyn Any + Send>;

    /// Restores a previously saved backend state.
    ///
    /// # Errors
    ///
    /// Returns an error if the state is invalid or cannot be restored.
    fn load_state(&mut self, state: &(dyn Any + Send)) -> LngResult<()>;
}

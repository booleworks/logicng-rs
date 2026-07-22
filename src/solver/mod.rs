/// The SAT solver of LogicNG
pub mod lng_core_solver;

/// Solver-specific errors
pub mod error;

pub use error::SolverError;

/// The Max-SAT solver of LogicNG
#[cfg(feature = "open_wbo")]
pub mod maxsat;

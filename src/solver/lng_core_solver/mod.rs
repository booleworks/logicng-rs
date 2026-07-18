/// Functions working directly on the SAT solver
pub mod functions;

mod minisat2;
mod minisat2_datastructures;
mod minisat_datastructures;
mod minisat_solver;
mod minisat_config;

pub use minisat2::*;
pub use minisat2_datastructures::*;
pub use minisat_datastructures::*;
pub use minisat_solver::*;
pub use minisat_config::*;

/// We deviate from the convention of putting unit tests in the source file in this case,
/// s.t. the file don't become too large
#[cfg(test)]
pub(crate) mod tests;

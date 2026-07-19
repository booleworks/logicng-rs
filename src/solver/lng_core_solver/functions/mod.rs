/// Backbone computation for formulas stored on a solver.
pub mod backbone_function;
/// Reconstruction of the formula currently stored on a solver.
pub mod formula_on_solver_function;
/// Model enumeration and model-counting operations.
pub mod model_enumeration_function;
/// Optimization of solver models with respect to selected literals.
pub mod optimization_function;
/// Extraction of unsatisfiable cores from proof-generating solvers.
pub mod unsat_core_function;
/// Extraction of literals propagated at decision level zero.
pub mod up_zero_literals_function;

pub use backbone_function::BackboneType;
pub use model_enumeration_function::*;
pub use optimization_function::OptimizationFunction;

#[cfg(test)]
pub(crate) mod tests;

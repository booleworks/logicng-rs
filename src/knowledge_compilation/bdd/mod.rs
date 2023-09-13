mod bdd_cache;
mod bdd_construction;
mod bdd_handler;
mod bdd_kernel;
mod bdd_main;
mod bdd_model_enumeration;
mod bdd_normalform;
mod bdd_operations;
mod bdd_prime;
/// Ordering strategies for BDDs.
pub mod orderings;

pub use bdd_handler::*;
pub use bdd_kernel::*;
pub use bdd_main::*;

/// We deviate from the convention of putting unit tests in the source file in this case,
/// s.t. the file don't become too large
#[cfg(test)]
#[allow(non_snake_case)]
mod tests;

mod sharpsat_solver;

/// Provides are solver of solver for the #SAT problem. It uses an external C++
/// solver based in the [implementation from Marc
/// Thurley](https://github.com/marcthurley/sharpSAT).
///
/// In order to use this module you need to enable the `sharp_sat` feature and
/// ensure the library compiles properly on your device (this is usually the
/// hard part).
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use num_bigint::BigUint;
/// use logicng::solver::sharpsat::SharpSatSolver;
///
/// let f = FormulaFactory::new();
/// let mut solver = SharpSatSolver::new();
///
/// solver.add_cnf("(a | c) & (~a | b | ~d)".to_formula(&f), &f);
/// solver.add_cnf("(~c | ~d)".to_formula(&f), &f);
///
/// let count = solver.solve();
/// assert_eq!(count, BigUint::from(7_u32));
/// ```
pub use sharpsat_solver::*;

/// We deviate from the convention of putting unit tests in the source file in this case,
/// s.t. the file don't become too large
#[cfg(test)]
pub(crate) mod tests;

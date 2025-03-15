use std::collections::HashMap;
use std::str::FromStr;

use logicng_sharp_sat_sys::ffi;
use num_bigint::BigUint;

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, Variable};

/// Wrapper for a [external #SAT
/// implementation](https://github.com/booleworks/logicng-sharp-sat). Allows for
/// adding clauses and formulas in CNF and counting the models of the
/// conjunction of all added clauses.
///
/// Use [`count_models()`](crate::operations::functions::count_models) and
/// [`count_models_conjunction()`](crate::operations::functions::count_models_conjunction)
/// (or related functions) for counting models of arbitrary formulas.
///
/// The external solver is based on this [implementation from Marc
/// Thurley](https://github.com/marcthurley/sharpSAT).
///
/// In order to use this solver you need to enable the `sharp_sat` feature and
/// ensure the library compiles properly on your device.
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
pub struct SharpSatSolver {
    solver: *mut ffi::Solver,
    var_map_down: HashMap<Variable, i32>,
    var_map_up: Vec<Variable>,
    constant: Option<bool>,
}

impl Default for SharpSatSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SharpSatSolver {
    /// Creates a new [`SharpSatSolver`] instance.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use logicng::solver::sharpsat::SharpSatSolver;
    ///
    /// let mut solver = SharpSatSolver::new();
    /// ```
    pub fn new() -> Self {
        Self { solver: unsafe { ffi::new_solver() }, var_map_down: HashMap::default(), var_map_up: Vec::default(), constant: None }
    }

    /// Adds a clause to the solver.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::solver::sharpsat::SharpSatSolver;
    ///
    /// let f = FormulaFactory::new();
    /// let mut solver = SharpSatSolver::new();
    ///
    /// solver.add_clause(&[f.lit("a", true), f.lit("b", true), f.lit("c", false)]);
    /// ```
    pub fn add_clause(&mut self, clause: &[Literal]) {
        if clause.is_empty() {
            self.constant = Some(false);
        } else {
            let mut new_clause = Vec::with_capacity(clause.len());
            for lit in clause {
                let var = lit.variable();
                let var_index = self.var_map_down.entry(var).or_insert_with_key(|k| {
                    let new_index = self.var_map_up.len() + 1;
                    self.var_map_up.push(*k);
                    new_index.try_into().expect("SharpSat FFI: The number of variables exceeds the limit")
                });

                if matches!(lit, Literal::Pos(_)) {
                    new_clause.push(*var_index);
                } else {
                    new_clause.push(-*var_index);
                }
            }

            unsafe {
                ffi::add_clause(
                    self.solver,
                    new_clause.as_ptr(),
                    new_clause.len().try_into().expect("SharpSat FFI: Size of clause exceeds the limit"),
                );
            }
        }
    }

    /// Add a formula in CNF to the solver. This function panics if the passed
    /// formula is not in CNF.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::{FormulaFactory, ToFormula};
    /// # use logicng::solver::sharpsat::SharpSatSolver;
    ///
    /// let f = FormulaFactory::new();
    /// let mut solver = SharpSatSolver::new();
    ///
    /// solver.add_cnf("(a | b) & (c | a | d) & (a | d)".to_formula(&f), &f);
    /// ```
    pub fn add_cnf(&mut self, cnf_formula: EncodedFormula, f: &FormulaFactory) {
        match cnf_formula.unpack(f) {
            Formula::Or(ops) => {
                self.add_clause(&ops.map(|formula| formula.as_literal().expect("SharpSat FFI: invalid cnf")).collect::<Box<_>>());
            }
            Formula::And(ops) => {
                for op in ops {
                    match op.unpack(f) {
                        Formula::Or(or_ops) => {
                            let mut constant_true = false;
                            let clause = or_ops
                                .filter_map(|formula| match formula.unpack(f) {
                                    Formula::Lit(lit) => Some(lit),
                                    Formula::True => {
                                        constant_true = true;
                                        None
                                    }
                                    Formula::False => None,
                                    _ => panic!("SharpSat FFI: invalid cnf"),
                                })
                                .collect::<Box<_>>();
                            if !constant_true {
                                self.add_clause(&clause);
                            }
                        }
                        Formula::And(_) => panic!("FF invariant broken: Nested And statement"),
                        Formula::Lit(lit) => self.add_clause(&[lit]),
                        Formula::False => {
                            self.constant = Some(false);
                            break;
                        }
                        Formula::True => {}
                        _ => panic!("invalid cnf"),
                    }
                }
            }
            Formula::Lit(lit) => self.add_clause(&[lit]),
            Formula::True => self.constant = Some(true),
            Formula::False => self.constant = Some(false),
            _ => panic!("Unexpected formula type {:?}", cnf_formula.formula_type()),
        }
    }

    /// Counts the models of the formula on this solver.
    ///
    /// Note that while adding formulas some preprocessing might have discovered
    /// that this formula is trivial. In this case, the result will be returned
    /// directly and the external solver will not be called.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use logicng::formulas::FormulaFactory;
    /// # use logicng::solver::sharpsat::SharpSatSolver;
    ///
    /// let f = FormulaFactory::new();
    /// let mut solver = SharpSatSolver::new();
    ///
    /// // add formulas to the solver ...
    ///
    /// let count = solver.solve();
    /// ```
    pub fn solve(self) -> BigUint {
        match self.constant {
            Some(true) => BigUint::from(1_u64),
            Some(false) => BigUint::from(0_u64),
            None => {
                if self.var_map_up.is_empty() {
                    BigUint::from(1_u64)
                } else {
                    let res = unsafe { ffi::solve(self.solver) };
                    BigUint::from_str(&format!("{res}"))
                        .unwrap_or_else(|_| panic!("SharpSat FFI: Returned value {res} is not a vaild result"))
                }
            }
        }
    }
}

impl Drop for SharpSatSolver {
    fn drop(&mut self) {
        unsafe { ffi::drop_solver(self.solver) };
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use crate::formulas::{FormulaFactory, ToFormula};
    use crate::util::read_model_counting_examples::read_cnf;

    use super::SharpSatSolver;


    #[test]
    fn empty_solver() {
        let solver = SharpSatSolver::new();
        let count = solver.solve();
        assert_eq!(count, BigUint::from(1_u64));
    }

    #[test]
    fn add_empty_clause() {
        let mut solver = SharpSatSolver::new();
        solver.add_clause(&[]);
        let count = solver.solve();
        assert_eq!(count, BigUint::from(0_u64));
    }

    #[test]
    fn with_empty_clause() {
        let f = FormulaFactory::new();
        let mut solver = SharpSatSolver::new();
        solver.add_cnf("(a | b) & (b | c)".to_formula(&f), &f);
        solver.add_clause(&[]);
        let count = solver.solve();
        assert_eq!(count, BigUint::from(0_u64));
    }

    #[test]
    fn test_cnf_formulas() {
        let f = FormulaFactory::new();
        let tests = read_cnf(&f);
        for (formula, expected) in tests {
            let mut solver = SharpSatSolver::new();
            solver.add_cnf(formula, &f);
            let count = solver.solve();
            assert_eq!(count, expected);
        }
    }
}

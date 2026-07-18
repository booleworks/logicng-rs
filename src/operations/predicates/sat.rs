use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory};
use crate::solver::lng_core_solver::SolverCnfMethod::FactoryCnf;
use crate::solver::lng_core_solver::Tristate::{False, True, Undef};
use crate::solver::lng_core_solver::{MiniSat, MiniSatConfig};

/// A predicate tests whether a formula is satisfiable. A formula is satisfiable
/// if there exists at least one assignment such that the formula evaluates to
/// `true` with this assignment. Such an assignment is called *satisfying
/// assignment* or *model*. For example `A & B | C` is satisfiable for the
/// assignment `{A, B, ~C}`. In order to check for satisfiability, the
/// predicate internally calls a SAT solver.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_sat;
/// let f = FormulaFactory::new();
///
/// let formula = "a & b | c".to_formula(&f);
///
/// assert!(is_sat(formula, &f).unwrap());
/// ```
///
/// # Errors
///
/// Returns an error if the formula cannot be added to the SAT solver, for
/// example because CNF conversion fails.
pub fn is_sat(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<bool> {
    match f.caches.sat.get(formula) {
        Some(c) => Ok(c),
        None => {
            let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(FactoryCnf));
            solver.add(formula, f)?;
            let sat = solver.sat();
            if f.config.caches.sat {
                match sat {
                    True => f.caches.sat.insert(formula, true),
                    False => f.caches.sat.insert(formula, false),
                    Undef => {}
                }
            }
            Ok(sat == True)
        }
    }
}

/// A predicate indicating whether a given formula is a tautology, that is,
/// always holds, regardless of the assignment. An example for a tautology is
/// `(A & B) | (~A & B) | (A & ~B) | (~A & ~B)`.
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_tautology;
/// let f = FormulaFactory::new();
///
/// let formula = "(a & b) | (~a & b) | (a & ~b) | (~a & ~b)".to_formula(&f);
///
/// assert!(is_tautology(formula, &f).unwrap());
/// ```
///
/// A very useful usage of the tautology predicate is to check whether two
/// formulas are semantically equivalent. To do this, create an equivalence
/// consisting of the two formulas to check. Then check whether this equivalence
/// is a tautology:
///
/// ```
/// use logicng::formulas::{FormulaFactory, ToFormula};
/// use logicng::operations::predicates::is_tautology;
/// let f = FormulaFactory::new();
///
/// let formula1 = "(a | b) & (a | c) & (c | d) & (b | ~d)".to_formula(&f);
/// let formula2 = "d & a & b | ~d & c & a | c & b".to_formula(&f);
/// let equivalence = f.equivalence(formula1, formula2);
///
/// assert!(is_tautology(equivalence, &f).unwrap());
/// ```
///
/// Also, testing if one formula is a logical implication of another formula can
/// be tested the same way by creating an implication `f.implication(f1, f2)`
/// instead.
///
/// # Errors
///
/// Returns an error if the negated formula cannot be added to the SAT solver,
/// for example because CNF conversion fails.
pub fn is_tautology(formula: EncodedFormula, f: &FormulaFactory) -> LngResult<bool> {
    let negated_formula = f.negate(formula);
    match f.caches.sat.get(negated_formula) {
        Some(c) => Ok(!c),
        None => {
            let mut solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(FactoryCnf));
            solver.add(negated_formula, f)?;
            let sat = solver.sat();
            if f.config.caches.sat {
                match sat {
                    True => f.caches.sat.insert(negated_formula, true),
                    False => f.caches.sat.insert(negated_formula, false),
                    Undef => {}
                }
            }
            Ok(sat == False)
        }
    }
}

use std::collections::HashSet;

use crate::formulas::{EncodedFormula, Formula, FormulaFactory};

/// Predicate to test whether a variable with a certain name is contained in the
/// formula.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::contains_var_name;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "(b & c) | (a & c)".to_formula(&f);
/// let formula3 = "(b & c) | (d & c)".to_formula(&f);
///
/// assert_eq!(contains_var_name(formula1, "a", &f), true);
/// assert_eq!(contains_var_name(formula2, "a", &f), true);
/// assert_eq!(contains_var_name(formula3, "a", &f), false);
/// ```
pub fn contains_var_name(formula: EncodedFormula, variable: &str, f: &FormulaFactory) -> bool {
    let mut seen = HashSet::new();
    let mut stack = Vec::new();
    stack.push(formula);
    seen.insert(formula);

    while let Some(current) = stack.pop() {
        use Formula::{Cc, Lit, Pbc};
        let result = match current.unpack(f) {
            Lit(lit) => lit.name(f) == variable,
            Cc(cc) => cc.variables.iter().any(|v| v.name(f) == variable),
            Pbc(pbc) => pbc.literals.iter().any(|l| l.name(f) == variable),
            _ => {
                for &op in &*current.operands(f) {
                    if seen.insert(op) {
                        stack.push(op);
                    }
                }
                false
            }
        };

        if result {
            return true;
        }
    }
    false
}

/// Predicate to test whether a sub-formula is contained in the formula.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::contains_node;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "(b & c) | (a & c)".to_formula(&f);
/// let formula3 = "(b & c) | (d & c)".to_formula(&f);
///
/// let sub_formula = "a & c".to_formula(&f);
///
/// assert_eq!(contains_node(formula1, sub_formula, &f), false);
/// assert_eq!(contains_node(formula2, sub_formula, &f), true);
/// assert_eq!(contains_node(formula3, sub_formula, &f), false);
/// ```
pub fn contains_node(formula: EncodedFormula, node: EncodedFormula, f: &FormulaFactory) -> bool {
    use Formula::{Cc, Pbc};

    let mut seen = HashSet::new();
    let mut stack = Vec::new();
    stack.push(formula);
    seen.insert(formula);

    while let Some(current) = stack.pop() {
        if current == node {
            return true;
        }

        let result = match current.unpack(f) {
            Cc(cc) => cc.variables.iter().any(|v| EncodedFormula::from(*v) == node),
            Pbc(pbc) => pbc.literals.iter().any(|l| EncodedFormula::from(*l) == node || EncodedFormula::from(l.variable()) == node),
            _ => {
                for &op in &*current.operands(f) {
                    if seen.insert(op) {
                        stack.push(op);
                    }
                }
                false
            }
        };

        if result {
            return true;
        }
    }
    false
}

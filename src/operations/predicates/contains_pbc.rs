use std::collections::HashSet;

use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType};

/// Predicate to test if a formula contains any sub-formula that is a
/// pseudo-Boolean constraint.
///
/// # Example
///
/// Basic usage:
///
/// ```
/// # use logicng::formulas::{FormulaFactory, ToFormula};
/// # use logicng::operations::predicates::contains_pbc;
/// # let f = FormulaFactory::new();
///
/// let formula1 = "a".to_formula(&f);
/// let formula2 = "a & b + c + d = 1".to_formula(&f);
/// let formula3 = "a & 1 * b + 2 * c + 3 * d = 3 ".to_formula(&f);
/// let formula4 = "a | ~b => (b & c)".to_formula(&f);
///
/// assert_eq!(contains_pbc(formula1, &f), false);
/// assert_eq!(contains_pbc(formula2, &f), true);
/// assert_eq!(contains_pbc(formula3, &f), true);
/// assert_eq!(contains_pbc(formula4, &f), false);
/// ```
pub fn contains_pbc(formula: EncodedFormula, f: &FormulaFactory) -> bool {
    let mut seen = HashSet::new();
    let mut stack = Vec::new();
    stack.push(formula);
    seen.insert(formula);

    while let Some(current) = stack.pop() {
        let result = f.caches.contains_pbc.get(current).map_or_else(
            || {
                use FormulaType::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
                match current.formula_type() {
                    Pbc | Cc => true,
                    Lit(_) | True | False => false,
                    Equiv | Impl | Not | Or | And => {
                        for &op in &*current.operands(f) {
                            if seen.insert(op) {
                                stack.push(op);
                            }
                        }
                        false
                    }
                }
            },
            |cached| cached,
        );

        if result && f.config.caches.contains_pbc {
            f.caches.contains_pbc.insert(formula, true);
        }

        if result {
            return true;
        }
    }
    false
}

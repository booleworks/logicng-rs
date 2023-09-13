use crate::formulas::{EncodedFormula, FormulaFactory};

use crate::knowledge_compilation::bdd::bdd_kernel::BddKernel;
use crate::knowledge_compilation::bdd::bdd_operations::{all_sat, all_unsat};

/// Computes a CNF/DNF from the given BDD.
pub fn normal_form(root: usize, cnf: bool, f: &FormulaFactory, kernel: &mut BddKernel) -> EncodedFormula {
    let paths_to_constant = if cnf { all_unsat(root, kernel) } else { all_sat(root, kernel) };
    let mut terms = Vec::new();
    for path in paths_to_constant {
        let mut literals = Vec::new();
        for (idx, val) in path.iter().enumerate() {
            let var = kernel.get_variable_for_index(idx).unwrap();
            if *val == 0 {
                literals.push(if cnf { var.into() } else { f.negate(var.into()) });
            } else if *val == 1 {
                literals.push(if cnf { f.negate(var.into()) } else { var.into() });
            }
        }
        let term = if cnf { f.or(&literals) } else { f.and(&literals) };
        terms.push(term);
    }
    if cnf {
        f.and(&terms)
    } else {
        f.or(&terms)
    }
}

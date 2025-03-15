use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::formulas::{Variable, AUX_CC};

/// An encoding of at-most-one cardinality constraints using the commander
/// encoding due to Klieber and Kwon.
pub fn build_amo_commander(k: usize, result: &mut dyn EncodingResult, vars: &[Variable]) {
    let literals = Vec::with_capacity(vars.len() * 2); // allocate here to avoid allocation in each recursion step
    let next_literals = Vec::with_capacity(vars.len() * 2); // allocate here to avoid allocation in each recursion step
    let current_literals = vars.iter().map(|var| (*var).into()).collect();
    encode_recursive(k, result, current_literals, literals, next_literals);
}

fn encode_recursive(
    k: usize,
    result: &mut dyn EncodingResult,
    mut current_literals: Vec<SolverExportLiteral>,
    mut literals: Vec<SolverExportLiteral>,
    mut next_literals: Vec<SolverExportLiteral>,
) {
    let mut is_exactly_one = false;
    while current_literals.len() > k {
        literals.clear();
        next_literals.clear();
        for i in 0..current_literals.len() {
            literals.push(current_literals[i]);
            if (i % k) == k - 1 || i == current_literals.len() - 1 {
                encode_non_recursive(result, &literals);
                let new_var = result.new_auxiliary_variable(AUX_CC);
                literals.push(new_var);
                next_literals.push(new_var.negate());
                if is_exactly_one {
                    result.add_clause(&literals);
                }
                for lit in literals.iter().take(literals.len() - 1) {
                    result.add_clause(&[new_var.negate(), lit.negate()]);
                }
                literals.clear();
            }
        }
        current_literals.clear();
        current_literals.append(&mut next_literals);
        is_exactly_one = true;
    }
    encode_non_recursive(result, &current_literals);
    if is_exactly_one && !current_literals.is_empty() {
        result.add_clause(&current_literals);
    }
}

fn encode_non_recursive(result: &mut dyn EncodingResult, literals: &[SolverExportLiteral]) {
    for i in 0..literals.len() {
        for j in (i + 1)..literals.len() {
            result.add_clause(&[literals[i].negate(), literals[j].negate()]);
        }
    }
}

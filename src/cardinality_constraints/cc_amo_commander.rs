use crate::cardinality_constraints::encoding_result::EncodingResult;
use crate::formulas::{FormulaFactory, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the commander
/// encoding due to Klieber and Kwon.
pub fn build_amo_commander<R: EncodingResult>(k: usize, result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    result.reset();
    let literals = Vec::with_capacity(vars.len() * 2); // allocate here to avoid allocation in each recursion step
    let next_literals = Vec::with_capacity(vars.len() * 2); // allocate here to avoid allocation in each recursion step
    let current_literals = vars.iter().map(|var| Literal::new(*var, true)).collect();
    encode_recursive(k, result, f, current_literals, literals, next_literals);
}

fn encode_recursive(
    k: usize,
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    mut current_literals: Vec<Literal>,
    mut literals: Vec<Literal>,
    mut next_literals: Vec<Literal>,
) {
    let mut is_exactly_one = false;
    while current_literals.len() > k {
        literals.clear();
        next_literals.clear();
        for i in 0..current_literals.len() {
            literals.push(current_literals[i]);
            if (i % k) == k - 1 || i == current_literals.len() - 1 {
                encode_non_recursive(result, f, &literals);
                let new_var = Literal::new(result.new_cc_variable(f), true);
                literals.push(new_var);
                next_literals.push(new_var.negate());
                if is_exactly_one {
                    result.add_clause(f, &literals);
                }
                for lit in literals.iter().take(literals.len() - 1) {
                    result.add_clause2(f, new_var.negate(), lit.negate());
                }
                literals.clear();
            }
        }
        current_literals.clear();
        current_literals.append(&mut next_literals);
        is_exactly_one = true;
    }
    encode_non_recursive(result, f, &current_literals);
    if is_exactly_one && !current_literals.is_empty() {
        result.add_clause(f, &current_literals);
    }
}

fn encode_non_recursive(result: &mut dyn EncodingResult, f: &FormulaFactory, literals: &[Literal]) {
    for i in 0..literals.len() {
        for j in (i + 1)..literals.len() {
            result.add_clause2(f, literals[i].negate(), literals[j].negate());
        }
    }
}

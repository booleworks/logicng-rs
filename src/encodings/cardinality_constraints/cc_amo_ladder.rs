use crate::datastructures::EncodingResult;
use crate::formulas::{FormulaFactory, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the ladder/regular
/// encoding.
pub fn build_amo_ladder<R: EncodingResult>(result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    result.reset();
    let seq_auxiliary: Vec<Variable> = (0..(vars.len() - 1)).map(|_| result.new_cc_variable(f)).collect();
    for i in 0..vars.len() {
        let variable_ref = vars[i];
        if i == 0 {
            result.add_clause2(f, Literal::new(variable_ref, false), Literal::new(seq_auxiliary[0], true));
        } else if i == vars.len() - 1 {
            result.add_clause2(f, Literal::new(variable_ref, false), Literal::new(seq_auxiliary[i - 1], false));
        } else {
            result.add_clause2(f, Literal::new(variable_ref, false), Literal::new(seq_auxiliary[i], true));
            result.add_clause2(f, Literal::new(seq_auxiliary[i - 1], false), Literal::new(seq_auxiliary[i], true));
            result.add_clause2(f, Literal::new(variable_ref, false), Literal::new(seq_auxiliary[i - 1], false));
        }
    }
}

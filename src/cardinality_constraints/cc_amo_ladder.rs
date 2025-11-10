use crate::datastructures::EncodingResult;
use crate::formulas::{AuxVarType, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the ladder/regular
/// encoding.
pub fn build_amo_ladder<R: EncodingResult>(result: &mut R, vars: &[Variable]) {
    let seq_auxiliary: Vec<Variable> = (0..(vars.len() - 1)).map(|_| result.new_auxiliary_variable(AuxVarType::CC)).collect();
    for i in 0..vars.len() {
        let variable_ref = vars[i];
        if i == 0 {
            result.add_clause(&[Literal::new(variable_ref, false), Literal::new(seq_auxiliary[0], true)]);
        } else if i == vars.len() - 1 {
            result.add_clause(&[Literal::new(variable_ref, false), Literal::new(seq_auxiliary[i - 1], false)]);
        } else {
            result.add_clause(&[Literal::new(variable_ref, false), Literal::new(seq_auxiliary[i], true)]);
            result.add_clause(&[Literal::new(seq_auxiliary[i - 1], false), Literal::new(seq_auxiliary[i], true)]);
            result.add_clause(&[Literal::new(variable_ref, false), Literal::new(seq_auxiliary[i - 1], false)]);
        }
    }
}

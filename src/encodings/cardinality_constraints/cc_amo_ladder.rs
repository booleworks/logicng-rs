use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::formulas::{Literal, Variable, AUX_CC};

/// An encoding of at-most-one cardinality constraints using the ladder/regular
/// encoding.
pub fn build_amo_ladder(result: &mut dyn EncodingResult, vars: &[Variable]) {
    let seq_auxiliary: Vec<SolverExportLiteral> = (0..(vars.len() - 1)).map(|_| result.new_auxiliary_variable(AUX_CC)).collect();
    for i in 0..vars.len() {
        let variable_ref = vars[i];
        if i == 0 {
            result.add_clause(&[Literal::new(variable_ref, false).into(), seq_auxiliary[0]]);
        } else if i == vars.len() - 1 {
            result.add_clause(&[Literal::new(variable_ref, false).into(), seq_auxiliary[i - 1].negate()]);
        } else {
            result.add_clause(&[Literal::new(variable_ref, false).into(), seq_auxiliary[i]]);
            result.add_clause(&[seq_auxiliary[i - 1].negate(), seq_auxiliary[i]]);
            result.add_clause(&[Literal::new(variable_ref, false).into(), seq_auxiliary[i - 1].negate()]);
        }
    }
}

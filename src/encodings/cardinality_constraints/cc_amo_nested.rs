use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::formulas::{Variable, AUX_CC};

/// An encoding of at-most-one cardinality constraints using the nested
/// encoding.
pub fn build_amo_nested(group_size: usize, result: &mut dyn EncodingResult, vars: &[Variable]) {
    encode_intern(group_size, result, vars.iter().map(|&var| var.into()).collect());
}

fn encode_intern(group_size: usize, result: &mut dyn EncodingResult, vars: Vec<SolverExportLiteral>) {
    if vars.len() < group_size {
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                result.add_clause(&[vars[i].negate(), vars[j].negate()]);
            }
        }
    } else {
        let new_variable = result.new_auxiliary_variable(AUX_CC);
        let split = vars.len() / 2;
        let mut l2 = vars[split..].to_vec();
        let mut l1 = vars;
        l1.truncate(split);
        l1.push(new_variable);
        l2.push(new_variable.negate());
        encode_intern(group_size, result, l1);
        encode_intern(group_size, result, l2);
    }
}

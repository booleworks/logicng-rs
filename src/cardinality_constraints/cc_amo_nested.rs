use crate::datastructures::EncodingResult;
use crate::formulas::{AuxVarType, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the nested
/// encoding.
pub fn build_amo_nested<R: EncodingResult>(group_size: usize, result: &mut R, vars: &[Variable]) {
    encode_intern(group_size, result, vars.iter().map(|var| Literal::new(*var, true)).collect());
}

fn encode_intern<R: EncodingResult>(group_size: usize, result: &mut R, vars: Vec<Literal>) {
    if vars.len() < group_size {
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                result.add_clause(&[vars[i].negate(), vars[j].negate()]);
            }
        }
    } else {
        let new_variable = result.new_auxiliary_variable(AuxVarType::CC);
        let split = vars.len() / 2;
        let mut l2 = vars[split..].to_vec();
        let mut l1 = vars;
        l1.truncate(split);
        l1.push(Literal::new(new_variable, true));
        l2.push(Literal::new(new_variable, false));
        encode_intern(group_size, result, l1);
        encode_intern(group_size, result, l2);
    }
}

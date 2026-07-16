use crate::datastructures::EncodingResult;
use crate::formulas::{Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the 'naive'
/// encoding with no introduction of new variables but quadratic size.
pub fn build_amo_pure<R: EncodingResult>(result: &mut R, vars: &[Variable]) {
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result.add_clause(&[Literal::new(vars[i], false), Literal::new(vars[j], false)]);
        }
    }
}

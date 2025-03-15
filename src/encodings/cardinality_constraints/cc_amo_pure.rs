use crate::datastructures::EncodingResult;
use crate::formulas::Variable;

/// An encoding of at-most-one cardinality constraints using the 'naive'
/// encoding with no introduction of new variables but quadratic size.
pub fn build_amo_pure(result: &mut dyn EncodingResult, vars: &[Variable]) {
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result.add_clause_literals(&[vars[i].negate(), vars[j].negate()]);
        }
    }
}

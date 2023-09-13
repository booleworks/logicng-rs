use crate::cardinality_constraints::encoding_result::EncodingResult;
use crate::formulas::{FormulaFactory, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the 'naive'
/// encoding with no introduction of new variables but quadratic size.
pub fn build_amo_pure<R: EncodingResult>(result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    result.reset();
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result.add_clause2(f, Literal::new(vars[i], false), Literal::new(vars[j], false));
        }
    }
}

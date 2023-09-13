#![allow(clippy::cast_possible_truncation, clippy::cast_precision_loss, clippy::cast_sign_loss)]

use crate::cardinality_constraints::encoding_result::EncodingResult;
use crate::formulas::{FormulaFactory, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the 2-product
/// method due to Chen.
pub fn build_amo_product<R: EncodingResult>(recursive_bound: usize, result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    result.reset();
    product_rec(recursive_bound, result, f, vars);
}

#[allow(clippy::many_single_char_names)]
fn product_rec<R: EncodingResult>(recursive_bound: usize, result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    let n = vars.len();
    let p = (n as f64).sqrt().ceil() as usize;
    let q = (n as f64 / p as f64).ceil() as usize;
    let us: Vec<Variable> = (0..p).map(|_| result.new_cc_variable(f)).collect();
    let vs: Vec<Variable> = (0..q).map(|_| result.new_cc_variable(f)).collect();

    if p <= recursive_bound {
        build_pure(result, f, &us);
    } else {
        product_rec(recursive_bound, result, f, &us);
    }
    if q <= recursive_bound {
        build_pure(result, f, &vs);
    } else {
        product_rec(recursive_bound, result, f, &vs);
    }

    for (i, u) in us.iter().enumerate().take(p) {
        for (j, v) in vs.iter().enumerate().take(q) {
            let k = i * q + j;
            if k < n {
                result.add_clause2(f, Literal::new(vars[k], false), Literal::new(*u, true));
                result.add_clause2(f, Literal::new(vars[k], false), Literal::new(*v, true));
            }
        }
    }
}

fn build_pure<R: EncodingResult>(result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result.add_clause2(f, Literal::new(vars[i], false), Literal::new(vars[j], false));
        }
    }
}

#![allow(clippy::cast_possible_truncation, clippy::cast_precision_loss, clippy::cast_sign_loss)]

use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::formulas::{Variable, AUX_CC};

/// An encoding of at-most-one cardinality constraints using the 2-product
/// method due to Chen.
pub fn build_amo_product(recursive_bound: usize, result: &mut dyn EncodingResult, vars: &[Variable]) {
    product_rec(recursive_bound, result, &vars.iter().map(|&v| v.into()).collect::<Box<[_]>>());
}

#[allow(clippy::many_single_char_names)]
fn product_rec(recursive_bound: usize, result: &mut dyn EncodingResult, vars: &[SolverExportLiteral]) {
    let n = vars.len();
    let p = (n as f64).sqrt().ceil() as usize;
    let q = (n as f64 / p as f64).ceil() as usize;
    let us: Vec<SolverExportLiteral> = (0..p).map(|_| result.new_auxiliary_variable(AUX_CC)).collect();
    let vs: Vec<SolverExportLiteral> = (0..q).map(|_| result.new_auxiliary_variable(AUX_CC)).collect();

    if p <= recursive_bound {
        build_pure(result, &us);
    } else {
        product_rec(recursive_bound, result, &us);
    }
    if q <= recursive_bound {
        build_pure(result, &vs);
    } else {
        product_rec(recursive_bound, result, &vs);
    }

    for (i, &u) in us.iter().enumerate().take(p) {
        for (j, &v) in vs.iter().enumerate().take(q) {
            let k = i * q + j;
            if k < n {
                result.add_clause(&[vars[k].negate(), u]);
                result.add_clause(&[vars[k].negate(), v]);
            }
        }
    }
}

fn build_pure(result: &mut dyn EncodingResult, vars: &[SolverExportLiteral]) {
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result.add_clause(&[vars[i].negate(), vars[j].negate()]);
        }
    }
}

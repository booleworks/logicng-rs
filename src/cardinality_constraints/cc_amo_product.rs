#![allow(clippy::cast_possible_truncation, clippy::cast_precision_loss, clippy::cast_sign_loss)]

use crate::datastructures::EncodingResult;
use crate::formulas::{AuxVarType, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the 2-product
/// method due to Chen.
pub fn build_amo_product<R: EncodingResult>(recursive_bound: usize, result: &mut R, vars: &[Variable]) {
    product_rec(recursive_bound, result, vars);
}

#[allow(clippy::many_single_char_names)]
fn product_rec<R: EncodingResult>(recursive_bound: usize, result: &mut R, vars: &[Variable]) {
    let n = vars.len();
    let p = (n as f64).sqrt().ceil() as usize;
    let q = (n as f64 / p as f64).ceil() as usize;
    let us: Vec<Variable> = (0..p).map(|_| result.new_auxiliary_variable(AuxVarType::CC)).collect();
    let vs: Vec<Variable> = (0..q).map(|_| result.new_auxiliary_variable(AuxVarType::CC)).collect();

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

    for (i, u) in us.iter().enumerate().take(p) {
        for (j, v) in vs.iter().enumerate().take(q) {
            let k = i * q + j;
            if k < n {
                result.add_clause(&[Literal::new(vars[k], false), Literal::new(*u, true)]);
                result.add_clause(&[Literal::new(vars[k], false), Literal::new(*v, true)]);
            }
        }
    }
}

fn build_pure<R: EncodingResult>(result: &mut R, vars: &[Variable]) {
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result.add_clause(&[Literal::new(vars[i], false), Literal::new(vars[j], false)]);
        }
    }
}

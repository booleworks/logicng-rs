#![allow(clippy::cast_possible_wrap)]

use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable, AUX_PBC};

#[allow(clippy::cast_sign_loss)]
pub fn encode_swc(lits: &[Literal], coeffs: &[i64], rhs: u64, f: &FormulaFactory) -> Vec<EncodedFormula> {
    let rhs: usize =
        rhs.try_into().unwrap_or_else(|_| panic!("Can only encode PBCs with right-hand-sides up to {} on this architecture", usize::MAX));
    let mut result = Vec::new();
    let n = lits.len();
    let seq_auxiliary: Vec<Vec<Variable>> = (0..n).map(|_| (0..rhs).map(|_| f.new_auxiliary_variable(AUX_PBC)).collect()).collect();
    for i in 0..n {
        let wi: isize =
            (coeffs[i]).try_into().unwrap_or_else(|_| panic!("Can only encode PBC coefficients up to {} on this architecture", usize::MAX));
        assert!(wi <= (rhs as isize));
        for j in 0..rhs {
            if i >= 1 {
                result.push(f.clause([seq_auxiliary[i - 1][j].neg_lit(), seq_auxiliary[i][j].pos_lit()]));
            }
            if (j as isize) < wi {
                result.push(f.clause([lits[i].negate(), seq_auxiliary[i][j].pos_lit()]));
            }
            if i >= 1 && (j as isize) < (rhs as isize) - wi {
                result.push(f.clause([
                    seq_auxiliary[i - 1][j].neg_lit(),
                    lits[i].negate(),
                    seq_auxiliary[i][(j as isize + wi) as usize].pos_lit(),
                ]));
            }
        }
        if i >= 1 {
            result.push(f.clause([seq_auxiliary[i - 1][(rhs as isize - wi) as usize].neg_lit(), lits[i].negate()]));
        }
    }
    result
}

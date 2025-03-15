#![allow(clippy::cast_possible_wrap)]

use crate::{
    datastructures::{EncodingResult, SolverExportLiteral},
    formulas::{Literal, AUX_PBC},
};

#[allow(clippy::cast_sign_loss)]
pub fn encode_swc(lits: &[Literal], coeffs: &[i64], rhs: u64, result: &mut dyn EncodingResult) {
    let rhs: usize =
        rhs.try_into().unwrap_or_else(|_| panic!("Can only encode PBCs with right-hand-sides up to {} on this architecture", usize::MAX));
    let n = lits.len();
    let seq_auxiliary: Vec<Vec<SolverExportLiteral>> =
        (0..n).map(|_| (0..rhs).map(|_| result.new_auxiliary_variable(AUX_PBC)).collect()).collect();
    for i in 0..n {
        let wi: isize =
            (coeffs[i]).try_into().unwrap_or_else(|_| panic!("Can only encode PBC coefficients up to {} on this architecture", usize::MAX));
        assert!(wi <= (rhs as isize));
        for j in 0..rhs {
            if i >= 1 {
                result.add_clause(&[seq_auxiliary[i - 1][j].negate(), seq_auxiliary[i][j]]);
            }
            if (j as isize) < wi {
                result.add_clause(&[lits[i].negate().into(), seq_auxiliary[i][j]]);
            }
            if i >= 1 && (j as isize) < (rhs as isize) - wi {
                result.add_clause(&[
                    seq_auxiliary[i - 1][j].negate(),
                    lits[i].negate().into(),
                    seq_auxiliary[i][(j as isize + wi) as usize],
                ]);
            }
        }
        if i >= 1 {
            result.add_clause(&[seq_auxiliary[i - 1][(rhs as isize - wi) as usize].negate(), lits[i].negate().into()]);
        }
    }
}

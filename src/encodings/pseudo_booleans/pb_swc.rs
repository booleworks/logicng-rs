use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};

pub fn encode_swc(
    lits: &[Literal],
    coeffs: &[usize],
    rhs: usize,
    f: &FormulaFactory,
) -> Vec<EncodedFormula> {
    let mut result = Vec::new();
    let n = lits.len();
    let seq_auxiliary: Vec<Vec<Variable>> = (0..n)
        .map(|_| (0..rhs).map(|_| f.new_pb_variable()).collect())
        .collect();
    for i in 0..n {
        let ci = coeffs[i];
        for j in 0..rhs {
            if i >= 1 {
                result.push(f.clause([
                    seq_auxiliary[i - 1][j].neg_lit(),
                    seq_auxiliary[i][j].pos_lit(),
                ]));
            }
            if j < ci {
                result.push(f.clause([lits[i].negate(), seq_auxiliary[i][j].pos_lit()]));
            }
            if i >= 1 && j < rhs - ci {
                result.push(f.clause([
                    seq_auxiliary[i - 1][j].neg_lit(),
                    lits[i].negate(),
                    seq_auxiliary[i][j + ci].pos_lit(),
                ]));
            }
        }
        if i >= 1 {
            result.push(f.clause([seq_auxiliary[i - 1][rhs - ci].neg_lit(), lits[i].negate()]));
        }
    }
    result
}

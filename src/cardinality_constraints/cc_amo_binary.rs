#![allow(clippy::cast_possible_truncation, clippy::cast_sign_loss, clippy::cast_precision_loss, clippy::cast_possible_wrap)]

use crate::cardinality_constraints::encoding_result::EncodingResult;
use crate::formulas::{FormulaFactory, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the binary
/// encoding due to Doggett, Frisch, Peugniez, and Nightingale.
pub fn build_amo_binary<R: EncodingResult>(result: &mut R, f: &FormulaFactory, vars: &[Variable]) {
    let vars: Vec<Literal> = vars.iter().map(|var| Literal::new(*var, true)).collect();
    result.reset();
    let number_of_bits = (vars.len() as f64).log2().ceil() as u32;
    let two_pow_n_bits = 2u64.pow(number_of_bits);
    let k = ((two_pow_n_bits - vars.len() as u64) * 2) as isize;
    let bits: Vec<Literal> = (0..number_of_bits).map(|_| Literal::new(result.new_cc_variable(f), true)).collect();

    let mut gray_code: isize;
    let mut next_gray: isize;
    let mut i = 0isize;
    let mut index = -1isize;
    while i < k {
        index += 1;
        gray_code = i ^ (i >> 1);
        i += 1;
        next_gray = i ^ (i >> 1);
        for j in 0..number_of_bits {
            if (gray_code & (1 << j)) == (next_gray & (1 << j)) {
                if (gray_code & (1 << j)) == 0 {
                    result.add_clause2(f, vars[index as usize].negate(), bits[j as usize].negate());
                } else {
                    result.add_clause2(f, vars[index as usize].negate(), bits[j as usize]);
                }
            }
        }
        i += 1;
    }
    while i < two_pow_n_bits as isize {
        index += 1;
        gray_code = i ^ (i >> 1);
        for j in 0..number_of_bits {
            if (gray_code & (1 << j)) == 0 {
                result.add_clause2(f, vars[index as usize].negate(), bits[j as usize].negate());
            } else {
                result.add_clause2(f, vars[index as usize].negate(), bits[j as usize]);
            }
        }
        i += 1;
    }
}

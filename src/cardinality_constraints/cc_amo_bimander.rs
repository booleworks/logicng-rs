#![allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation, clippy::cast_sign_loss, clippy::cast_precision_loss)]

use crate::datastructures::EncodingResult;
use crate::formulas::{AuxVarType, Literal, Variable};

/// An encoding of at-most-one cardinality constraints using the Bimander
/// encoding due to Hölldobler and Nguyen.
pub fn build_amo_bimander<R: EncodingResult>(m: usize, result: &mut R, vars: &[Variable]) {
    encode_intern(m, result, &vars.iter().map(|var| Literal::new(*var, true)).collect::<Box<[_]>>());
}

fn encode_intern<R: EncodingResult>(m: usize, result: &mut R, vars: &[Literal]) {
    let groups = initialize_groups(m, result, vars);
    let (bits, number_of_bits, two_pow_n_bits, k) = initialize_bits(m, result);
    let mut gray_code: isize;
    let mut next_gray: isize;
    let mut i = 0isize;
    let mut index = -1isize;
    while i < k as isize {
        index += 1;
        gray_code = i ^ (i >> 1);
        i += 1;
        next_gray = i ^ (i >> 1);
        for (j, bit) in bits.iter().enumerate().take(number_of_bits) {
            if (gray_code & (1 << j)) == (next_gray & (1 << j)) {
                handle_gray_code(result, &groups[index as usize], *bit, gray_code, j);
            }
        }
        i += 1;
    }
    while i < two_pow_n_bits as isize {
        index += 1;
        gray_code = i ^ (i >> 1);
        for (j, bit) in bits.iter().enumerate().take(number_of_bits) {
            handle_gray_code(result, &groups[index as usize], *bit, gray_code, j);
        }
        i += 1;
    }
}

fn initialize_groups<R: EncodingResult>(group_size: usize, result: &mut R, vars: &[Literal]) -> Box<[Vec<Literal>]> {
    let n = vars.len();
    let mut groups: Vec<Vec<Literal>> = (0..group_size).map(|_| Vec::new()).collect();

    let mut g = (n as f64 / group_size as f64).ceil() as usize;
    let mut ig = 0usize;
    let mut i = 0;
    while i < n {
        while i < g {
            groups[ig].push(vars[i]);
            i += 1;
        }
        ig += 1;
        g += ((n - i) as f64 / (group_size - ig) as f64).ceil() as usize;
    }

    for clause in &groups {
        encode_naive(result, clause);
    }
    groups.into()
}

fn initialize_bits<R: EncodingResult>(m: usize, result: &mut R) -> (Box<[Literal]>, usize, usize, usize) {
    let number_of_bits = (m as f64).log2().ceil() as usize;
    let two_pow_n_bits = 2usize.pow(number_of_bits as u32);
    let k = (two_pow_n_bits - m) * 2;
    let bits = (0..number_of_bits).map(|_| Literal::new(result.new_auxiliary_variable(AuxVarType::CC), true)).collect();
    (bits, number_of_bits, two_pow_n_bits, k)
}

fn encode_naive<R: EncodingResult>(result: &mut R, literals: &[Literal]) {
    for i in 0..literals.len() {
        for j in (i + 1)..literals.len() {
            result.add_clause(&[literals[i].negate(), literals[j].negate()]);
        }
    }
}

fn handle_gray_code(result: &mut dyn EncodingResult, group: &[Literal], bit: Literal, gray_code: isize, j: usize) {
    let b = if (gray_code & (1 << j)) == 0 { bit.negate() } else { bit };
    for p in group {
        result.add_clause(&[p.negate(), b]);
    }
}

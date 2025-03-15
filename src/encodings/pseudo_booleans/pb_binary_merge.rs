#![allow(
    clippy::too_many_arguments,
    clippy::many_single_char_names,
    clippy::if_not_else,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation
)]

use itertools::Itertools;

use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::encodings::cardinality_constraints::cc_sorter::ImplicationDirection::InputToOutput;
use crate::encodings::cardinality_constraints::cc_sorter::{cc_merge, cc_sort};
use crate::encodings::PbConfig;
use crate::formulas::{Literal, AUX_PBC};

pub fn encode_binary_merge(config: &PbConfig, mut lits: Vec<Literal>, mut coeffs: Vec<i64>, rhs: u64, result: &mut dyn EncodingResult) {
    let rhs =
        rhs.try_into().unwrap_or_else(|_| panic!("Can only encode PBCs with right-hand-sides up to {} on this architecture", usize::MAX));
    let max_weight = *coeffs.iter().max().unwrap();
    if !config.binary_merge_use_gac {
        let n = lits.len();
        binary_merge(&lits, &coeffs, rhs, max_weight, n, None, config, result);
    } else {
        let mut encode_complete_constraint = false;
        for i in 0..lits.len() {
            let tmp_coeff = coeffs[i];
            if config.binary_merge_no_support_for_single_bit && tmp_coeff.count_ones() == 1 {
                encode_complete_constraint = true;
            } else {
                let tmp_lit = lits[i];
                let last_lit = *lits.last().unwrap();
                let last_coeff = *coeffs.last().unwrap();
                lits[i] = last_lit;
                coeffs[i] = last_coeff;
                lits.pop();
                coeffs.pop();
                if max_weight == tmp_coeff {
                    let mw = *coeffs.iter().max().unwrap();
                    if rhs as i64 <= tmp_coeff {
                        for lit in &lits {
                            result.add_clause_literals(&[tmp_lit.negate(), lit.negate()]);
                        }
                    } else {
                        binary_merge(&lits, &coeffs, rhs - tmp_coeff as usize, mw, lits.len(), Some(tmp_lit.negate()), config, result);
                    }
                } else {
                    if rhs as i64 <= tmp_coeff {
                        for lit in &lits {
                            result.add_clause_literals(&[tmp_lit.negate(), lit.negate()]);
                        }
                    }
                    binary_merge(&lits, &coeffs, rhs - tmp_coeff as usize, max_weight, lits.len(), Some(tmp_lit.negate()), config, result);
                }
                if i < lits.len() {
                    lits.push(lits[i]);
                    lits[i] = tmp_lit;
                    coeffs.push(coeffs[i]);
                    coeffs[i] = tmp_coeff;
                }
            }
        }
        if config.binary_merge_no_support_for_single_bit && encode_complete_constraint {
            let n = lits.len();
            binary_merge(&lits, &coeffs, rhs, max_weight, n, None, config, result);
        }
    }
}

fn binary_merge(
    literals: &[Literal],
    coefficients: &[i64],
    leq: usize,
    max_weight: i64,
    n: usize,
    gac_lit: Option<Literal>,
    config: &PbConfig,
    result: &mut dyn EncodingResult,
) {
    let less_then = leq + 1;
    let p = usize::BITS - max_weight.leading_zeros() - 1;
    let m = div_ceil(less_then, 2_usize.pow(p));
    let new_less_then = m * 2_usize.pow(p);
    let t = new_less_then as i64 - less_then as i64;

    let true_lit = result.new_auxiliary_variable(AUX_PBC);
    result.add_clause(&[true_lit]);
    let mut buckets: Vec<Vec<_>> = Vec::new();
    for i in 0..=p {
        let bit = 1 << i;
        let mut bucket = Vec::new();
        if t & bit != 0 {
            bucket.push(true_lit);
        }
        for j in 0..n {
            let coeff_j = coefficients[j];
            if coeff_j & bit != 0 {
                let lit_j = literals[j];
                if let (Some(gac), true) = (gac_lit, coeff_j >= less_then as i64) {
                    result.add_clause_literals(&[gac, lit_j.negate()]);
                } else {
                    bucket.push(lit_j.into());
                }
            }
        }
        buckets.push(bucket);
    }

    let mut carries: Vec<SolverExportLiteral> = Vec::new();
    for (i, bucket_i) in buckets.iter().enumerate() {
        let k = div_ceil(new_less_then, 2_usize.pow(i as u32));
        let bucket_card_i = if config.binary_merge_use_watch_dog {
            totalizer(bucket_i.clone(), result)
        } else {
            cc_sort(k, bucket_i.clone(), result, InputToOutput)
        };
        if k <= bucket_i.len() {
            assert!(k == bucket_card_i.len() || config.binary_merge_use_watch_dog);
            if let Some(gac) = gac_lit {
                result.add_clause(&[gac.into(), bucket_card_i[k - 1].negate()]);
            } else {
                result.add_clause(&[bucket_card_i[k - 1].negate()]);
            }
        }
        let bucket_merge_i;
        if i > 0 {
            if !carries.is_empty() {
                if bucket_card_i.is_empty() {
                    bucket_merge_i = carries.clone();
                } else {
                    if config.binary_merge_use_watch_dog {
                        bucket_merge_i = unary_adder(bucket_card_i, carries.clone(), result);
                    } else {
                        bucket_merge_i = cc_merge(
                            k,
                            bucket_card_i.iter().copied().map_into().collect(),
                            carries.iter().copied().map_into().collect(),
                            result,
                            InputToOutput,
                        );
                    }
                    if k == bucket_merge_i.len() || config.binary_merge_use_watch_dog && k <= bucket_merge_i.len() {
                        if let Some(gac) = gac_lit {
                            result.add_clause(&[gac.into(), bucket_merge_i[k - 1].negate()]);
                        } else {
                            result.add_clause(&[bucket_merge_i[k - 1].negate()]);
                        }
                    }
                }
            } else {
                bucket_merge_i = bucket_card_i.clone();
            }
            carries = bucket_merge_i.into_iter().skip(1).step_by(2).collect();
        } else {
            carries = bucket_card_i.into_iter().skip(1).step_by(2).collect();
        }
    }
}

const fn div_ceil(a: usize, b: usize) -> usize {
    let q = a / b;
    if a % b == 0 {
        q
    } else {
        q + 1
    }
}

fn totalizer(x: Vec<SolverExportLiteral>, result: &mut dyn EncodingResult) -> Vec<SolverExportLiteral> {
    if x.len() <= 1 {
        x
    } else {
        let (x_1, x_2) = x.split_at(x.len() / 2);
        let u_x_1 = totalizer(x_1.to_vec(), result);
        let u_x_2 = totalizer(x_2.to_vec(), result);
        unary_adder(u_x_1, u_x_2, result)
    }
}

fn unary_adder(u: Vec<SolverExportLiteral>, v: Vec<SolverExportLiteral>, result: &mut dyn EncodingResult) -> Vec<SolverExportLiteral> {
    if u.is_empty() {
        v
    } else if v.is_empty() {
        u
    } else {
        let mut w = Vec::new();
        for _ in 0..(u.len() + v.len()) {
            w.push(result.new_auxiliary_variable(AUX_PBC));
        }
        for a in 0..u.len() {
            for b in 0..v.len() {
                result.add_clause(&[u[a].negate(), v[b].negate(), w[a + b + 1]]);
            }
        }
        for i in 0..v.len() {
            result.add_clause(&[v[i].negate(), w[i]]);
        }
        for i in 0..u.len() {
            result.add_clause(&[u[i].negate(), w[i]]);
        }
        w
    }
}

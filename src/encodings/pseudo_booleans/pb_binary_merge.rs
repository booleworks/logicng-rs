#![allow(
    clippy::too_many_arguments,
    clippy::many_single_char_names,
    clippy::if_not_else,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation
)]

use crate::encodings::cardinality_constraints::cc_sorter::ImplicationDirection::InputToOutput;
use crate::encodings::cardinality_constraints::cc_sorter::{cc_merge, cc_sort};
use crate::encodings::PbConfig;
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, AUX_PBC};

pub fn encode_binary_merge(
    config: &PbConfig,
    mut lits: Vec<Literal>,
    mut coeffs: Vec<i64>,
    rhs: u64,
    f: &FormulaFactory,
) -> Vec<EncodedFormula> {
    let rhs =
        rhs.try_into().unwrap_or_else(|_| panic!("Can only encode PBCs with right-hand-sides up to {} on this architecture", usize::MAX));
    let mut formula = Vec::new();
    let max_weight = *coeffs.iter().max().unwrap();
    if !config.binary_merge_use_gac {
        let n = lits.len();
        formula.extend(binary_merge(&lits, &coeffs, rhs, max_weight, n, None, config, f));
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
                            formula.push(f.clause([tmp_lit.negate(), lit.negate()]));
                        }
                    } else {
                        formula.extend(binary_merge(
                            &lits,
                            &coeffs,
                            rhs - tmp_coeff as usize,
                            mw,
                            lits.len(),
                            Some(tmp_lit.negate()),
                            config,
                            f,
                        ));
                    }
                } else {
                    if rhs as i64 <= tmp_coeff {
                        for lit in &lits {
                            formula.push(f.clause([tmp_lit.negate(), lit.negate()]));
                        }
                    }
                    formula.extend(binary_merge(
                        &lits,
                        &coeffs,
                        rhs - tmp_coeff as usize,
                        max_weight,
                        lits.len(),
                        Some(tmp_lit.negate()),
                        config,
                        f,
                    ));
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
            formula.extend(binary_merge(&lits, &coeffs, rhs, max_weight, n, None, config, f));
        }
    }
    formula
}

fn binary_merge(
    literals: &[Literal],
    coefficients: &[i64],
    leq: usize,
    max_weight: i64,
    n: usize,
    gac_lit: Option<Literal>,
    config: &PbConfig,
    f: &FormulaFactory,
) -> Vec<EncodedFormula> {
    let mut formula = Vec::new();
    let less_then = leq + 1;
    let p = usize::BITS - max_weight.leading_zeros() - 1;
    let m = div_ceil(less_then, 2_usize.pow(p));
    let new_less_then = m * 2_usize.pow(p);
    let t = new_less_then as i64 - less_then as i64;

    let true_lit = f.new_auxiliary_variable(AUX_PBC).pos_lit();
    formula.push(true_lit.into());
    let mut buckets: Vec<Vec<Literal>> = Vec::new();
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
                    formula.push(f.clause([gac, lit_j.negate()]));
                } else {
                    bucket.push(lit_j);
                }
            }
        }
        buckets.push(bucket);
    }

    let mut carries: Vec<Literal> = Vec::new();
    for (i, bucket_i) in buckets.iter().enumerate() {
        let k = div_ceil(new_less_then, 2_usize.pow(i as u32));
        let bucket_card_i = if config.binary_merge_use_watch_dog {
            let (formula_extension, new_bucket_card) = totalizer(bucket_i.clone(), f);
            formula.extend(formula_extension);
            new_bucket_card
        } else {
            let mut temp_result = vec![];
            let sorted = cc_sort(k, bucket_i.clone(), &mut temp_result, f, InputToOutput);
            formula.extend(temp_result);
            sorted
        };
        if k <= bucket_i.len() {
            assert!(k == bucket_card_i.len() || config.binary_merge_use_watch_dog);
            if let Some(gac) = gac_lit {
                formula.push(f.clause([gac, bucket_card_i[k - 1].negate()]));
            } else {
                formula.push(bucket_card_i[k - 1].negate().into());
            }
        }
        let bucket_merge_i;
        if i > 0 {
            if !carries.is_empty() {
                if bucket_card_i.is_empty() {
                    bucket_merge_i = carries.clone();
                } else {
                    if config.binary_merge_use_watch_dog {
                        let (formula_extension, new_merge_bucket) = unary_adder(bucket_card_i, carries.clone(), f);
                        formula.extend(formula_extension);
                        bucket_merge_i = new_merge_bucket;
                    } else {
                        let mut temp_result = vec![];
                        bucket_merge_i = cc_merge(k, bucket_card_i.clone(), carries.clone(), &mut temp_result, f, InputToOutput);
                        formula.extend(temp_result);
                    }
                    if k == bucket_merge_i.len() || config.binary_merge_use_watch_dog && k <= bucket_merge_i.len() {
                        if let Some(gac) = gac_lit {
                            formula.push(f.clause([gac, bucket_merge_i[k - 1].negate()]));
                        } else {
                            formula.push(bucket_merge_i[k - 1].negate().into());
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
    formula
}

const fn div_ceil(a: usize, b: usize) -> usize {
    let q = a / b;
    if a % b == 0 {
        q
    } else {
        q + 1
    }
}

fn totalizer(x: Vec<Literal>, f: &FormulaFactory) -> (Vec<EncodedFormula>, Vec<Literal>) {
    if x.len() <= 1 {
        (Vec::new(), x)
    } else {
        let (x_1, x_2) = x.split_at(x.len() / 2);
        let (mut formula, u_x_1) = totalizer(x_1.to_vec(), f);
        let (formula_extension, u_x_2) = totalizer(x_2.to_vec(), f);
        formula.extend(formula_extension);
        let (formula_extension, u_x) = unary_adder(u_x_1, u_x_2, f);
        formula.extend(formula_extension);
        (formula, u_x)
    }
}

fn unary_adder(u: Vec<Literal>, v: Vec<Literal>, f: &FormulaFactory) -> (Vec<EncodedFormula>, Vec<Literal>) {
    if u.is_empty() {
        (Vec::new(), v)
    } else if v.is_empty() {
        (Vec::new(), u)
    } else {
        let mut formula = Vec::new();
        let mut w = Vec::new();
        for _ in 0..(u.len() + v.len()) {
            w.push(f.new_auxiliary_variable(AUX_PBC).pos_lit());
        }
        for a in 0..u.len() {
            for b in 0..v.len() {
                formula.push(f.clause([u[a].negate(), v[b].negate(), w[a + b + 1]]));
            }
        }
        for i in 0..v.len() {
            formula.push(f.clause([v[i].negate(), w[i]]));
        }
        for i in 0..u.len() {
            formula.push(f.clause([u[i].negate(), w[i]]));
        }
        (formula, w)
    }
}

use std::collections::VecDeque;
use std::iter::repeat;

use crate::{
    datastructures::{EncodingResult, SolverExportLiteral},
    formulas::{Literal, AUX_PBC},
};

pub fn encode_adder_networks(lits: &[Literal], coeffs: &[i64], rhs: u64, enc_result: &mut dyn EncodingResult) {
    let rhs =
        rhs.try_into().unwrap_or_else(|_| panic!("Can only encode PBCs with right-hand-sides up to {} on this architecture", usize::MAX));
    let nb = ld_int(rhs);
    let mut result: Vec<Option<_>> = repeat(None).take(nb).collect();
    let mut buckets = Vec::new();
    for i_bit in 0..nb {
        let mut bucket = VecDeque::new();
        for i_var in 0..lits.len() {
            if (1 << i_bit) & coeffs[i_var] != 0 {
                bucket.push_front(lits[i_var].into());
            }
        }
        buckets.push(bucket);
    }
    adder_tree(&mut buckets, &mut result, enc_result);
    less_than_or_equal(&result, rhs, enc_result);
}

#[allow(clippy::many_single_char_names)]
fn adder_tree(
    buckets: &mut Vec<VecDeque<SolverExportLiteral>>,
    result: &mut Vec<Option<SolverExportLiteral>>,
    enc_result: &mut dyn EncodingResult,
) {
    let mut i = 0;
    while i < buckets.len() {
        if !buckets[i].is_empty() {
            if i == buckets.len() - 1 && buckets[i].len() >= 2 {
                buckets.push(VecDeque::new());
                result.push(None);
            }
            while buckets[i].len() >= 3 {
                let bucket = &mut buckets[i];
                let x = bucket.pop_front().unwrap();
                let y = bucket.pop_front().unwrap();
                let z = bucket.pop_front().unwrap();
                let xs = fa_sum(x, y, z, enc_result);
                let xc = fa_carry(x, y, z, enc_result);
                buckets[i].push_back(xs);
                buckets[i + 1].push_back(xc);
                fa_extra(xs, xc, x, y, z, enc_result);
            }
            if buckets[i].len() == 2 {
                let x = buckets[i].pop_front().unwrap();
                let y = buckets[i].pop_front().unwrap();
                let xs = ha_sum(x, y, enc_result);
                buckets[i].push_back(xs);
                let xc = ha_carry(x, y, enc_result);
                buckets[i + 1].push_back(xc);
            }
            result[i] = buckets[i].pop_front();
        }
        i += 1;
    }
}

#[allow(clippy::many_single_char_names)]
fn fa_sum(a: SolverExportLiteral, b: SolverExportLiteral, c: SolverExportLiteral, result: &mut dyn EncodingResult) -> SolverExportLiteral {
    let x = result.new_auxiliary_variable(AUX_PBC);
    result.add_clause(&[a, b, c, x.negate()]);
    result.add_clause(&[a, b.negate(), c.negate(), x.negate()]);
    result.add_clause(&[a.negate(), b, c.negate(), x.negate()]);
    result.add_clause(&[a.negate(), b.negate(), c, x.negate()]);
    result.add_clause(&[a.negate(), b.negate(), c.negate(), x]);
    result.add_clause(&[a.negate(), b, c, x]);
    result.add_clause(&[a, b.negate(), c, x]);
    result.add_clause(&[a, b, c.negate(), x]);
    x
}

#[allow(clippy::many_single_char_names)]
fn fa_carry(
    a: SolverExportLiteral,
    b: SolverExportLiteral,
    c: SolverExportLiteral,
    result: &mut dyn EncodingResult,
) -> SolverExportLiteral {
    let x = result.new_auxiliary_variable(AUX_PBC);
    result.add_clause(&[b, c, x.negate()]);
    result.add_clause(&[a, c, x.negate()]);
    result.add_clause(&[a, b, x.negate()]);
    result.add_clause(&[b.negate(), c.negate(), x]);
    result.add_clause(&[a.negate(), c.negate(), x]);
    result.add_clause(&[a.negate(), b.negate(), x]);
    x
}

fn fa_extra(
    xs: SolverExportLiteral,
    xc: SolverExportLiteral,
    a: SolverExportLiteral,
    b: SolverExportLiteral,
    c: SolverExportLiteral,
    result: &mut dyn EncodingResult,
) {
    result.add_clause(&[xc.negate(), xs.negate(), a]);
    result.add_clause(&[xc.negate(), xs.negate(), b]);
    result.add_clause(&[xc.negate(), xs.negate(), c]);
    result.add_clause(&[xc, xs, a.negate()]);
    result.add_clause(&[xc, xs, b.negate()]);
    result.add_clause(&[xc, xs, c.negate()]);
}

fn ha_sum(a: SolverExportLiteral, b: SolverExportLiteral, result: &mut dyn EncodingResult) -> SolverExportLiteral {
    let x = result.new_auxiliary_variable(AUX_PBC);
    result.add_clause(&[a.negate(), b.negate(), x.negate()]);
    result.add_clause(&[a, b, x.negate()]);
    result.add_clause(&[a.negate(), b, x]);
    result.add_clause(&[a, b.negate(), x]);
    x
}

fn ha_carry(a: SolverExportLiteral, b: SolverExportLiteral, result: &mut dyn EncodingResult) -> SolverExportLiteral {
    let x = result.new_auxiliary_variable(AUX_PBC);
    result.add_clause(&[a, x.negate()]);
    result.add_clause(&[b, x.negate()]);
    result.add_clause(&[a.negate(), b.negate(), x]);
    x
}

fn less_than_or_equal(xs: &[Option<SolverExportLiteral>], rhs: usize, result: &mut dyn EncodingResult) {
    for i in 0..xs.len() {
        let xi = xs.get(i).unwrap();
        if !(xi.is_none() || rhs & (1 << i) > 0) {
            let mut clause: Vec<_> = Vec::with_capacity(xs.len() - i);
            let mut skip = false;
            for j in (i + 1)..xs.len() {
                let xj = xs.get(j).unwrap();
                if rhs & (1 << j) > 0 {
                    if let Some(lit) = xj {
                        clause.push(lit.negate());
                    } else {
                        skip = true;
                        break;
                    }
                } else if let Some(lit) = xj {
                    clause.push(*lit);
                }
            }
            if !skip {
                clause.push(xs.get(i).unwrap().unwrap().negate());
                result.add_clause(&clause);
            }
        }
    }
}

const fn ld_int(x: usize) -> usize {
    (usize::BITS - x.leading_zeros()) as usize
}

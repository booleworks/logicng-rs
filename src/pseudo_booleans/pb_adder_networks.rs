use std::collections::VecDeque;
use std::iter::repeat;

use crate::formulas::{EncodedFormula, FormulaFactory, Literal};

pub fn encode_adder_networks(lits: &[Literal], coeffs: &[i64], rhs: u64, f: &FormulaFactory) -> Vec<EncodedFormula> {
    let rhs =
        rhs.try_into().unwrap_or_else(|_| panic!("Can only encode PBCs with right-hand-sides up to {} on this architecture", usize::MAX));
    let mut formula: Vec<EncodedFormula> = Vec::new();
    let nb = ld_int(rhs);
    let mut result: Vec<Option<Literal>> = repeat(None).take(nb).collect();
    let mut buckets = Vec::new();
    for i_bit in 0..nb {
        let mut bucket = VecDeque::new();
        for i_var in 0..lits.len() {
            if (1 << i_bit) & coeffs[i_var] != 0 {
                bucket.push_front(lits[i_var]);
            }
        }
        buckets.push(bucket);
    }
    formula.extend(adder_tree(&mut buckets, &mut result, f));
    formula.extend(less_than_or_equal(&result, rhs, f));
    formula
}

#[allow(clippy::many_single_char_names)]
fn adder_tree(buckets: &mut Vec<VecDeque<Literal>>, result: &mut Vec<Option<Literal>>, f: &FormulaFactory) -> Vec<EncodedFormula> {
    let mut formula = Vec::new();
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
                let (xs, constraints) = fa_sum(x, y, z, f);
                formula.extend(constraints);
                let (xc, constraints) = fa_carry(x, y, z, f);
                formula.extend(constraints);
                buckets[i].push_back(xs);
                buckets[i + 1].push_back(xc);
                formula.extend(fa_extra(xs, xc, x, y, z, f));
            }
            if buckets[i].len() == 2 {
                let x = buckets[i].pop_front().unwrap();
                let y = buckets[i].pop_front().unwrap();
                let (xs, constraints) = ha_sum(x, y, f);
                formula.extend(constraints);
                buckets[i].push_back(xs);
                let (xc, constraints) = ha_carry(x, y, f);
                formula.extend(constraints);
                buckets[i + 1].push_back(xc);
            }
            result[i] = buckets[i].pop_front();
        }
        i += 1;
    }
    formula
}

#[allow(clippy::many_single_char_names)]
fn fa_sum(a: Literal, b: Literal, c: Literal, f: &FormulaFactory) -> (Literal, Vec<EncodedFormula>) {
    let x = f.new_pb_variable().pos_lit();
    (
        x,
        vec![
            f.clause([a, b, c, x.negate()]),
            f.clause([a, b.negate(), c.negate(), x.negate()]),
            f.clause([a.negate(), b, c.negate(), x.negate()]),
            f.clause([a.negate(), b.negate(), c, x.negate()]),
            f.clause([a.negate(), b.negate(), c.negate(), x]),
            f.clause([a.negate(), b, c, x]),
            f.clause([a, b.negate(), c, x]),
            f.clause([a, b, c.negate(), x]),
        ],
    )
}

#[allow(clippy::many_single_char_names)]
fn fa_carry(a: Literal, b: Literal, c: Literal, f: &FormulaFactory) -> (Literal, Vec<EncodedFormula>) {
    let x = f.new_pb_variable().pos_lit();
    (
        x,
        vec![
            f.clause([b, c, x.negate()]),
            f.clause([a, c, x.negate()]),
            f.clause([a, b, x.negate()]),
            f.clause([b.negate(), c.negate(), x]),
            f.clause([a.negate(), c.negate(), x]),
            f.clause([a.negate(), b.negate(), x]),
        ],
    )
}

fn fa_extra(xs: Literal, xc: Literal, a: Literal, b: Literal, c: Literal, f: &FormulaFactory) -> Vec<EncodedFormula> {
    vec![
        f.clause([xc.negate(), xs.negate(), a]),
        f.clause([xc.negate(), xs.negate(), b]),
        f.clause([xc.negate(), xs.negate(), c]),
        f.clause([xc, xs, a.negate()]),
        f.clause([xc, xs, b.negate()]),
        f.clause([xc, xs, c.negate()]),
    ]
}

fn ha_sum(a: Literal, b: Literal, f: &FormulaFactory) -> (Literal, Vec<EncodedFormula>) {
    let x = f.new_pb_variable().pos_lit();
    (
        x,
        vec![
            f.clause([a.negate(), b.negate(), x.negate()]),
            f.clause([a, b, x.negate()]),
            f.clause([a.negate(), b, x]),
            f.clause([a, b.negate(), x]),
        ],
    )
}

fn ha_carry(a: Literal, b: Literal, f: &FormulaFactory) -> (Literal, Vec<EncodedFormula>) {
    let x = f.new_pb_variable().pos_lit();
    (x, vec![f.clause([a, x.negate()]), f.clause([b, x.negate()]), f.clause([a.negate(), b.negate(), x])])
}

fn less_than_or_equal(xs: &[Option<Literal>], rhs: usize, f: &FormulaFactory) -> Vec<EncodedFormula> {
    let mut result = Vec::new();
    for i in 0..xs.len() {
        let xi = xs.get(i).unwrap();
        if !(xi.is_none() || rhs & (1 << i) > 0) {
            let mut clause: Vec<Literal> = Vec::with_capacity(xs.len() - i);
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
                result.push(f.clause(&clause));
            }
        }
    }
    result
}

const fn ld_int(x: usize) -> usize {
    (usize::BITS - x.leading_zeros()) as usize
}

#![allow(clippy::cast_possible_truncation, clippy::cast_sign_loss, clippy::cast_precision_loss)]

use crate::cardinality_constraints::cc_incremental_data::CcIncrementalData;
use std::cmp::Ordering;

use crate::cardinality_constraints::encoding_result::EncodingResult;
use crate::formulas::AuxVarType::TMP;
use crate::formulas::{FormulaFactory, Literal, Variable};

struct ModularTotalizerState {
    n: usize,
    h0: Variable,
    md: usize,
    cardinality_up_outvars: Vec<Literal>,
    cardinality_lw_outvars: Vec<Literal>,
    inlits: Vec<Literal>,
    current_cardinality_rhs: usize,
}

pub(super) fn build_amk(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    vars: &[Variable],
    rhs: usize,
    with_inc: bool,
) -> Option<CcIncrementalData> {
    let mut state = initialize(result, f, rhs, vars.len());
    for var in vars {
        state.inlits.push(var.pos_lit());
    }
    to_cnf(
        result,
        f,
        state.md,
        &state.cardinality_up_outvars.clone(),
        &state.cardinality_lw_outvars.clone(),
        state.n,
        state.h0.pos_lit(),
        &mut state.inlits,
        state.current_cardinality_rhs,
    ); // yes, `n` and not `rhs`
    assert!(state.inlits.is_empty());
    encode_output(result, f, rhs, state.md, &state.cardinality_up_outvars, &state.cardinality_lw_outvars);
    state.current_cardinality_rhs += 1;
    if with_inc {
        Some(CcIncrementalData::for_amk_modular_totalizer(rhs, state.cardinality_up_outvars, state.cardinality_lw_outvars, state.md))
    } else {
        None
    }
}

pub fn build_alk(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    vars: &[Variable],
    rhs: usize,
    with_inc: bool,
) -> Option<CcIncrementalData> {
    let new_rhs = vars.len() - rhs;
    let mut state = initialize(result, f, new_rhs, vars.len());
    for var in vars {
        state.inlits.push(var.neg_lit());
    }
    to_cnf(
        result,
        f,
        state.md,
        &state.cardinality_up_outvars.clone(),
        &state.cardinality_lw_outvars.clone(),
        state.n,
        state.h0.pos_lit(),
        &mut state.inlits,
        state.current_cardinality_rhs,
    ); // yes, `n` and not `rhs`
    assert!(state.inlits.is_empty());
    encode_output(result, f, new_rhs, state.md, &state.cardinality_up_outvars, &state.cardinality_lw_outvars);
    state.current_cardinality_rhs += 1;
    if with_inc {
        Some(CcIncrementalData::for_alk_modular_totalizer(
            rhs,
            vars.len(),
            state.cardinality_up_outvars,
            state.cardinality_lw_outvars,
            state.md,
        ))
    } else {
        None
    }
}

fn initialize(result: &mut dyn EncodingResult, f: &FormulaFactory, rhs: usize, n: usize) -> ModularTotalizerState {
    result.reset();
    let h0 = Variable::Aux(TMP, 0);
    let md = (rhs as f64 + 1.0).sqrt().ceil() as usize;
    let mut cardinality_up_outvars: Vec<Literal> = Vec::with_capacity(n / md);
    for _ in 0..(n / md) {
        cardinality_up_outvars.push(result.new_cc_variable(f).pos_lit());
    }
    let mut cardinality_lw_outvars: Vec<Literal> = Vec::with_capacity(md - 1);
    for _ in 0..(md - 1) {
        cardinality_lw_outvars.push(result.new_cc_variable(f).pos_lit());
    }
    let inlits = Vec::with_capacity(n);
    let current_cardinality_rhs = rhs + 1;
    if cardinality_up_outvars.is_empty() {
        cardinality_up_outvars.push(h0.pos_lit());
    }
    ModularTotalizerState { n, h0, md, cardinality_up_outvars, cardinality_lw_outvars, inlits, current_cardinality_rhs }
}

#[allow(clippy::too_many_arguments)]
fn to_cnf(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    md: usize,
    ubvars: &[Literal],
    lwvars: &[Literal],
    rhs: usize,
    h0: Literal,
    inlits: &mut Vec<Literal>,
    current_cardinality_rhs: usize,
) {
    let mut lupper = Vec::new();
    let mut llower = Vec::new();
    let mut rupper = Vec::new();
    let mut rlower = Vec::new();

    assert!(rhs > 1);
    let split = rhs / 2;
    let mut left = 1;
    let mut right = 1;
    if split == 1 {
        assert!(!inlits.is_empty());
        lupper.push(h0);
        llower.push(inlits.pop().unwrap());
    } else {
        left = split / md;
        for _ in 0..left {
            lupper.push(result.new_cc_variable(f).pos_lit());
        }
        let limit = if left % md == 0 && split < md - 1 { split } else { md - 1 };
        for _ in 0..limit {
            llower.push(result.new_cc_variable(f).pos_lit());
        }
    }

    if rhs - split == 1 {
        assert!(!inlits.is_empty());
        rupper.push(h0);
        rlower.push(inlits.pop().unwrap());
    } else {
        right = (rhs - split) / md;
        for _ in 0..right {
            rupper.push(result.new_cc_variable(f).pos_lit());
        }
        let limit = if right % md == 0 && rhs - split < md - 1 { rhs - split } else { md - 1 };
        for _ in 0..limit {
            rlower.push(result.new_cc_variable(f).pos_lit());
        }
    }

    if lupper.is_empty() {
        lupper.push(h0);
    }
    if rupper.is_empty() {
        rupper.push(h0);
    }

    adder(result, f, md, ubvars, lwvars, &rupper, &rlower, &lupper, &llower, h0, current_cardinality_rhs);
    let val = left * md + split - left * md;
    if val > 1 {
        to_cnf(result, f, md, &lupper, &llower, val, h0, inlits, current_cardinality_rhs);
    }
    let val = right * md + rhs - split - right * md;
    if val > 1 {
        to_cnf(result, f, md, &rupper, &rlower, val, h0, inlits, current_cardinality_rhs);
    }
}

#[allow(clippy::too_many_arguments)]
fn adder(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    md: usize,
    upper: &[Literal],
    lower: &[Literal],
    lupper: &[Literal],
    llower: &[Literal],
    rupper: &[Literal],
    rlower: &[Literal],
    h0: Literal,
    current_cardinality_rhs: usize,
) {
    assert!(!upper.is_empty());
    assert!(lower.len() >= llower.len() && lower.len() >= rlower.len());
    let carry = if upper[0] == h0 { None } else { Some(result.new_cc_variable(f).pos_lit()) };
    for i in 0..=llower.len() {
        for j in 0..=rlower.len() {
            if i + j > current_cardinality_rhs + 1 && current_cardinality_rhs + 1 < md {
                continue;
            }
            match (i + j).cmp(&md) {
                Ordering::Less => {
                    if i == 0 && j != 0 {
                        if let Some(carry) = carry {
                            result.add_clause3(f, rlower[j - 1].negate(), lower[i + j - 1], carry);
                        } else {
                            result.add_clause2(f, rlower[j - 1].negate(), lower[i + j - 1]);
                        }
                    } else if j == 0 && i != 0 {
                        if let Some(carry) = carry {
                            result.add_clause3(f, llower[i - 1].negate(), lower[i + j - 1], carry);
                        } else {
                            result.add_clause2(f, llower[i - 1].negate(), lower[i + j - 1]);
                        }
                    } else if i != 0 {
                        if let Some(carry) = carry {
                            result.add_clause4(f, llower[i - 1].negate(), rlower[j - 1].negate(), lower[i + j - 1], carry);
                        } else {
                            assert!(i + j - 1 < lower.len());
                            result.add_clause3(f, llower[i - 1].negate(), rlower[j - 1].negate(), lower[i + j - 1]);
                        }
                    }
                }
                Ordering::Greater => {
                    assert!(i + j > 0);
                    result.add_clause3(f, llower[i - 1].negate(), rlower[j - 1].negate(), lower[(i + j) % md - 1]);
                }
                Ordering::Equal => {
                    assert_eq!(i + j, md);
                    result.add_clause3(f, llower[i - 1].negate(), rlower[j - 1].negate(), carry.unwrap());
                }
            }
        }
    }
    if let Some(carry) = carry {
        final_adder(result, f, md, upper, lupper, rupper, carry, h0, current_cardinality_rhs);
    }
}

#[allow(clippy::many_single_char_names, clippy::too_many_arguments)]
fn final_adder(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    md: usize,
    upper: &[Literal],
    lupper: &[Literal],
    rupper: &[Literal],
    carry: Literal,
    h0: Literal,
    current_cardinality_rhs: usize,
) {
    for i in 0..=lupper.len() {
        for j in 0..=rupper.len() {
            let close_mod = current_cardinality_rhs / md + usize::from(current_cardinality_rhs % md != 0);
            if md * (i + j) > close_mod * md {
                continue;
            }
            let a = if i == 0 { None } else { Some(lupper[i - 1]) };
            let b = if j == 0 { None } else { Some(rupper[j - 1]) };
            let c = if i + j != 0 && i + j - 1 < upper.len() { Some(upper[i + j - 1]) } else { None };
            let d = if i + j < upper.len() { Some(upper[i + j]) } else { None };
            let a_present = a.is_some() && a.unwrap() != h0;
            let b_present = b.is_some() && b.unwrap() != h0;
            let c_present = c.is_some() && c.unwrap() != h0;
            let d_present = d.is_some() && d.unwrap() != h0;
            if c_present && (a_present || b_present) {
                let mut clause = Vec::with_capacity(3);
                if a_present {
                    clause.push(a.unwrap().negate());
                }
                if b_present {
                    clause.push(b.unwrap().negate());
                }
                clause.push(c.unwrap());
                result.add_clause(f, &clause);
            }
            if a_present || b_present || d_present {
                let mut clause = Vec::with_capacity(4);
                clause.push(carry.negate());
                if a_present {
                    clause.push(a.unwrap().negate());
                }
                if b_present {
                    clause.push(b.unwrap().negate());
                }
                if d_present {
                    clause.push(d.unwrap());
                }
                result.add_clause(f, &clause);
            }
        }
    }
}

fn encode_output(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    rhs: usize,
    md: usize,
    cardinality_up_outvars: &[Literal],
    cardinality_lw_outvars: &[Literal],
) {
    assert!(!cardinality_up_outvars.is_empty() || !cardinality_lw_outvars.is_empty());
    let ulimit = (rhs + 1) / md;
    let llimit = (rhs + 1) - ulimit * md;
    assert!(ulimit <= cardinality_up_outvars.len());
    assert!(llimit <= cardinality_lw_outvars.len());
    for outvar in cardinality_up_outvars.iter().skip(ulimit) {
        result.add_clause1(f, outvar.negate());
    }
    if ulimit != 0 && llimit != 0 {
        for outvar in cardinality_lw_outvars.iter().skip(llimit - 1) {
            result.add_clause2(f, cardinality_up_outvars[ulimit - 1].negate(), outvar.negate());
        }
    } else if ulimit == 0 {
        assert_ne!(llimit, 0);
        for outvar in cardinality_lw_outvars.iter().skip(llimit - 1) {
            result.add_clause1(f, outvar.negate());
        }
    } else {
        result.add_clause1(f, cardinality_up_outvars[ulimit - 1].negate());
    }
}

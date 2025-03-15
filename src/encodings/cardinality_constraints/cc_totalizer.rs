use crate::datastructures::{EncodingResult, SolverExportLiteral};
use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder};
use crate::encodings::cardinality_constraints::cc_incremental_data::CcIncrementalData;
use crate::encodings::cardinality_constraints::cc_totalizer::Bound::{Both, Lower, Upper};
use crate::formulas::{Variable, AUX_CC};

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
enum Bound {
    Lower,
    Upper,
    Both,
}

pub fn build_amk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, vars);
    let inc_data = if with_inc {
        let vector1 = cardinality_outvars.clone();
        Some(CcIncrementalData::for_amk(AmkEncoder::Totalizer, vector1, rhs))
    } else {
        None
    };
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, rhs, Upper);
    debug_assert!(cardinality_invars.is_empty());
    for &var in cardinality_outvars.iter().skip(rhs) {
        result.add_clause(&[var.negate()]);
    }
    inc_data
}

pub fn build_alk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, vars);
    let inc_data = if with_inc {
        let vector1 = cardinality_outvars.clone();
        Some(CcIncrementalData::for_alk(AlkEncoder::Totalizer, vector1, rhs, vars.len()))
    } else {
        None
    };
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, rhs, Lower);
    debug_assert!(cardinality_invars.is_empty());
    for &var in cardinality_outvars.iter().take(rhs) {
        result.add_clause(&[var]);
    }
    inc_data
}

pub fn build_exk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize) {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, vars);
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, rhs, Both);
    debug_assert!(cardinality_invars.is_empty());
    for &var in cardinality_outvars.iter().take(rhs) {
        result.add_clause(&[var]);
    }
    for &var in cardinality_outvars.iter().skip(rhs) {
        result.add_clause(&[var.negate()]);
    }
}

fn initialize_constraint(result: &mut dyn EncodingResult, vars: &[Variable]) -> (Vec<Variable>, Vec<SolverExportLiteral>) {
    let mut cardinality_invars = Vec::with_capacity(vars.len());
    let mut cardinality_outvars = Vec::with_capacity(vars.len());
    for &var in vars {
        cardinality_invars.push(var);
        cardinality_outvars.push(result.new_auxiliary_variable(AUX_CC));
    }
    (cardinality_invars, cardinality_outvars)
}

fn to_cnf(cardinality_invars: &mut Vec<Variable>, vars: &[SolverExportLiteral], result: &mut dyn EncodingResult, rhs: usize, bound: Bound) {
    let mut left = Vec::new();
    let mut right = Vec::new();
    debug_assert!(vars.len() > 1);
    let split = vars.len() / 2;
    for i in 0..vars.len() {
        if i < split {
            if split == 1 {
                debug_assert!(!cardinality_invars.is_empty());
                left.push(cardinality_invars.pop().unwrap().into());
            } else {
                left.push(result.new_auxiliary_variable(AUX_CC));
            }
        } else if vars.len() - split == 1 {
            debug_assert!(!cardinality_invars.is_empty());
            right.push(cardinality_invars.pop().unwrap().into());
        } else {
            right.push(result.new_auxiliary_variable(AUX_CC));
        }
    }
    if bound == Upper || bound == Both {
        adder_amk(&left, &right, vars, rhs, result);
    }
    if bound == Lower || bound == Both {
        adder_alk(&left, &right, vars, result);
    }
    if left.len() > 1 {
        to_cnf(cardinality_invars, &left, result, rhs, bound);
    }
    if right.len() > 1 {
        to_cnf(cardinality_invars, &right, result, rhs, bound);
    }
}

fn adder_amk(
    left: &[SolverExportLiteral],
    right: &[SolverExportLiteral],
    output: &[SolverExportLiteral],
    rhs: usize,
    result: &mut dyn EncodingResult,
) {
    debug_assert!(output.len() == left.len() + right.len());
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            if i == 0 && j == 0 || i + j > rhs + 1 {
                continue;
            }
            if i == 0 {
                result.add_clause(&[right[j - 1].negate(), output[j - 1]]);
            } else if j == 0 {
                result.add_clause(&[left[i - 1].negate(), output[i - 1]]);
            } else {
                result.add_clause(&[left[i - 1].negate(), right[j - 1].negate(), output[i + j - 1]]);
            }
        }
    }
}

fn adder_alk(left: &[SolverExportLiteral], right: &[SolverExportLiteral], output: &[SolverExportLiteral], result: &mut dyn EncodingResult) {
    debug_assert!(output.len() == left.len() + right.len());
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            if i == 0 && j == 0 {
                continue;
            }
            if i == 0 {
                result.add_clause(&[right[j - 1], output[left.len() + j - 1].negate()]);
            } else if j == 0 {
                result.add_clause(&[left[i - 1], output[right.len() + i - 1].negate()]);
            } else {
                result.add_clause(&[left[i - 1], right[j - 1], output[i + j - 2].negate()]);
            }
        }
    }
}

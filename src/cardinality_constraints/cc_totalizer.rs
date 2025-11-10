use crate::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder};
use crate::cardinality_constraints::cc_incremental_data::CcIncrementalData;
use crate::cardinality_constraints::cc_totalizer::Bound::{Both, Lower, Upper};
use crate::datastructures::EncodingResult;
use crate::formulas::{AuxVarType, Literal, Variable};

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
enum Bound {
    Lower,
    Upper,
    Both,
}

pub fn build_amk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, vars);
    let inc_data = if with_inc {
        let vector1 = cardinality_outvars.iter().map(Variable::pos_lit).collect();
        Some(CcIncrementalData::for_amk(AmkEncoder::Totalizer, vector1, rhs))
    } else {
        None
    };
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, rhs, Upper);
    debug_assert!(cardinality_invars.is_empty());
    for var in cardinality_outvars.iter().skip(rhs) {
        result.add_clause(&[Literal::Neg(*var)]);
    }
    inc_data
}

pub fn build_alk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize, with_inc: bool) -> Option<CcIncrementalData> {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, vars);
    let inc_data = if with_inc {
        let vector1 = cardinality_outvars.iter().map(Variable::pos_lit).collect();
        Some(CcIncrementalData::for_alk(AlkEncoder::Totalizer, vector1, rhs, vars.len()))
    } else {
        None
    };
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, rhs, Lower);
    debug_assert!(cardinality_invars.is_empty());
    for var in cardinality_outvars.iter().take(rhs) {
        result.add_clause(&[Literal::Pos(*var)]);
    }
    inc_data
}

pub fn build_exk(result: &mut dyn EncodingResult, vars: &[Variable], rhs: usize) {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, vars);
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, rhs, Both);
    debug_assert!(cardinality_invars.is_empty());
    for var in cardinality_outvars.iter().take(rhs) {
        result.add_clause(&[Literal::Pos(*var)]);
    }
    for var in cardinality_outvars.iter().skip(rhs) {
        result.add_clause(&[Literal::Neg(*var)]);
    }
}

fn initialize_constraint(result: &mut dyn EncodingResult, vars: &[Variable]) -> (Vec<Variable>, Vec<Variable>) {
    let mut cardinality_invars = Vec::with_capacity(vars.len());
    let mut cardinality_outvars = Vec::with_capacity(vars.len());
    for &var in vars {
        cardinality_invars.push(var);
        cardinality_outvars.push(result.new_auxiliary_variable(AuxVarType::CC));
    }
    (cardinality_invars, cardinality_outvars)
}

fn to_cnf(cardinality_invars: &mut Vec<Variable>, vars: &[Variable], result: &mut dyn EncodingResult, rhs: usize, bound: Bound) {
    let mut left = Vec::new();
    let mut right = Vec::new();
    debug_assert!(vars.len() > 1);
    let split = vars.len() / 2;
    for i in 0..vars.len() {
        if i < split {
            if split == 1 {
                debug_assert!(!cardinality_invars.is_empty());
                left.push(cardinality_invars.pop().unwrap());
            } else {
                left.push(result.new_auxiliary_variable(AuxVarType::CC));
            }
        } else if vars.len() - split == 1 {
            debug_assert!(!cardinality_invars.is_empty());
            right.push(cardinality_invars.pop().unwrap());
        } else {
            right.push(result.new_auxiliary_variable(AuxVarType::CC));
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

fn adder_amk(left: &[Variable], right: &[Variable], output: &[Variable], rhs: usize, result: &mut dyn EncodingResult) {
    debug_assert!(output.len() == left.len() + right.len());
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            if i == 0 && j == 0 || i + j > rhs + 1 {
                continue;
            }
            if i == 0 {
                result.add_clause(&[Literal::new(right[j - 1], false), Literal::new(output[j - 1], true)]);
            } else if j == 0 {
                result.add_clause(&[Literal::new(left[i - 1], false), Literal::new(output[i - 1], true)]);
            } else {
                result.add_clause(&[
                    Literal::new(left[i - 1], false),
                    Literal::new(right[j - 1], false),
                    Literal::new(output[i + j - 1], true),
                ]);
            }
        }
    }
}

fn adder_alk(left: &[Variable], right: &[Variable], output: &[Variable], result: &mut dyn EncodingResult) {
    debug_assert!(output.len() == left.len() + right.len());
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            if i == 0 && j == 0 {
                continue;
            }
            if i == 0 {
                result.add_clause(&[Literal::new(right[j - 1], true), Literal::new(output[left.len() + j - 1], false)]);
            } else if j == 0 {
                result.add_clause(&[Literal::new(left[i - 1], true), Literal::new(output[right.len() + i - 1], false)]);
            } else {
                result.add_clause(&[
                    Literal::new(left[i - 1], true),
                    Literal::new(right[j - 1], true),
                    Literal::new(output[i + j - 2], false),
                ]);
            }
        }
    }
}

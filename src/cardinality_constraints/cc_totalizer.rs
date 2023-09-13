use crate::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder};
use crate::cardinality_constraints::cc_incremental_data::CcIncrementalData;
use crate::cardinality_constraints::cc_totalizer::Bound::{Both, Lower, Upper};
use crate::cardinality_constraints::encoding_result::EncodingResult;
use crate::formulas::{FormulaFactory, Literal, Variable};

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
enum Bound {
    Lower,
    Upper,
    Both,
}

pub fn build_amk(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    vars: &[Variable],
    rhs: usize,
    with_inc: bool,
) -> Option<CcIncrementalData> {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, f, vars);
    let inc_data = if with_inc {
        let vector1 = cardinality_outvars.iter().map(Variable::pos_lit).collect();
        Some(CcIncrementalData::for_amk(AmkEncoder::Totalizer, vector1, rhs))
    } else {
        None
    };
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, f, rhs, Upper);
    debug_assert!(cardinality_invars.is_empty());
    for var in cardinality_outvars.iter().skip(rhs) {
        result.add_clause1(f, Literal::Neg(*var));
    }
    inc_data
}

pub fn build_alk(
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    vars: &[Variable],
    rhs: usize,
    with_inc: bool,
) -> Option<CcIncrementalData> {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, f, vars);
    let inc_data = if with_inc {
        let vector1 = cardinality_outvars.iter().map(Variable::pos_lit).collect();
        Some(CcIncrementalData::for_alk(AlkEncoder::Totalizer, vector1, rhs, vars.len()))
    } else {
        None
    };
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, f, rhs, Lower);
    debug_assert!(cardinality_invars.is_empty());
    for var in cardinality_outvars.iter().take(rhs) {
        result.add_clause1(f, Literal::Pos(*var));
    }
    inc_data
}

pub fn build_exk(result: &mut dyn EncodingResult, f: &FormulaFactory, vars: &[Variable], rhs: usize) {
    let (mut cardinality_invars, cardinality_outvars) = initialize_constraint(result, f, vars);
    to_cnf(&mut cardinality_invars, &cardinality_outvars, result, f, rhs, Both);
    debug_assert!(cardinality_invars.is_empty());
    for var in cardinality_outvars.iter().take(rhs) {
        result.add_clause1(f, Literal::Pos(*var));
    }
    for var in cardinality_outvars.iter().skip(rhs) {
        result.add_clause1(f, Literal::Neg(*var));
    }
}

fn initialize_constraint(result: &mut dyn EncodingResult, f: &FormulaFactory, vars: &[Variable]) -> (Vec<Variable>, Vec<Variable>) {
    result.reset();
    let mut cardinality_invars = Vec::with_capacity(vars.len());
    let mut cardinality_outvars = Vec::with_capacity(vars.len());
    for &var in vars {
        cardinality_invars.push(var);
        cardinality_outvars.push(result.new_cc_variable(f));
    }
    (cardinality_invars, cardinality_outvars)
}

fn to_cnf(
    cardinality_invars: &mut Vec<Variable>,
    vars: &Vec<Variable>,
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
    rhs: usize,
    bound: Bound,
) {
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
                left.push(result.new_cc_variable(f));
            }
        } else if vars.len() - split == 1 {
            debug_assert!(!cardinality_invars.is_empty());
            right.push(cardinality_invars.pop().unwrap());
        } else {
            right.push(result.new_cc_variable(f));
        }
    }
    if bound == Upper || bound == Both {
        adder_amk(&mut left, &mut right, vars, rhs, result, f);
    }
    if bound == Lower || bound == Both {
        adder_alk(&mut left, &mut right, vars, result, f);
    }
    if left.len() > 1 {
        to_cnf(cardinality_invars, &left, result, f, rhs, bound);
    }
    if right.len() > 1 {
        to_cnf(cardinality_invars, &right, result, f, rhs, bound);
    }
}

fn adder_amk(
    left: &mut Vec<Variable>,
    right: &mut Vec<Variable>,
    output: &Vec<Variable>,
    rhs: usize,
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
) {
    debug_assert!(output.len() == left.len() + right.len());
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            if i == 0 && j == 0 || i + j > rhs + 1 {
                continue;
            }
            if i == 0 {
                result.add_clause2(f, Literal::new(right[j - 1], false), Literal::new(output[j - 1], true));
            } else if j == 0 {
                result.add_clause2(f, Literal::new(left[i - 1], false), Literal::new(output[i - 1], true));
            } else {
                result.add_clause3(
                    f,
                    Literal::new(left[i - 1], false),
                    Literal::new(right[j - 1], false),
                    Literal::new(output[i + j - 1], true),
                );
            }
        }
    }
}

fn adder_alk(
    left: &mut Vec<Variable>,
    right: &mut Vec<Variable>,
    output: &Vec<Variable>,
    result: &mut dyn EncodingResult,
    f: &FormulaFactory,
) {
    debug_assert!(output.len() == left.len() + right.len());
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            if i == 0 && j == 0 {
                continue;
            }
            if i == 0 {
                result.add_clause2(f, Literal::new(right[j - 1], true), Literal::new(output[left.len() + j - 1], false));
            } else if j == 0 {
                result.add_clause2(f, Literal::new(left[i - 1], true), Literal::new(output[right.len() + i - 1], false));
            } else {
                result.add_clause3(
                    f,
                    Literal::new(left[i - 1], true),
                    Literal::new(right[j - 1], true),
                    Literal::new(output[i + j - 2], false),
                );
            }
        }
    }
}

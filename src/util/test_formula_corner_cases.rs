use crate::formulas::CType::{EQ, GE, GT, LE, LT};
use crate::formulas::{CType, EncodedFormula, FormulaFactory, Literal, Variable};
use std::collections::BTreeSet;

pub fn formula_corner_cases(f: &FormulaFactory) -> (Vec<EncodedFormula>, BTreeSet<Variable>) {
    let a = f.variable("a");
    let b = f.variable("b");
    let c = f.variable("c");
    let na = f.literal("a", false);
    let nb = f.literal("b", false);
    let nc = f.literal("c", false);
    let not_a = f.not(a);
    let not_not_a = f.not(not_a);
    let mut formulas = vec![f.falsum(), f.not(f.falsum()), f.verum(), f.not(f.verum()), a, na, not_a, not_not_a, f.not(not_not_a)];
    for (left, right) in binary_corner_cases(f, a, b, na, nb) {
        formulas.push(f.implication(left, right));
    }
    for (left, right) in binary_corner_cases(f, a, b, na, nb) {
        formulas.push(f.equivalence(left, right));
    }
    for ops in nary_corner_cases(f, a, b, c, na, nb, nc) {
        formulas.push(f.or(&ops));
    }
    for ops in nary_corner_cases(f, a, b, c, na, nb, nc) {
        formulas.push(f.and(&ops));
    }
    add_pbc_corner_cases(&mut formulas, f, a, b, c, na, nb);
    (formulas, BTreeSet::from([a.as_variable().unwrap(), b.as_variable().unwrap(), c.as_variable().unwrap()]))
}

fn binary_corner_cases(
    f: &FormulaFactory,
    a: EncodedFormula,
    b: EncodedFormula,
    na: EncodedFormula,
    nb: EncodedFormula,
) -> Vec<(EncodedFormula, EncodedFormula)> {
    vec![
        (f.verum(), f.verum()),
        (f.falsum(), f.verum()),
        (f.verum(), f.falsum()),
        (f.falsum(), f.falsum()),
        (f.verum(), a),
        (a, f.verum()),
        (f.verum(), na),
        (na, f.verum()),
        (f.falsum(), a),
        (a, f.falsum()),
        (f.falsum(), na),
        (na, f.falsum()),
        (a, a),
        (a, na),
        (na, a),
        (na, na),
        (a, b),
        (a, nb),
        (na, b),
        (na, nb),
    ]
}

fn nary_corner_cases(
    f: &FormulaFactory,
    a: EncodedFormula,
    b: EncodedFormula,
    c: EncodedFormula,
    na: EncodedFormula,
    nb: EncodedFormula,
    nc: EncodedFormula,
) -> Vec<Vec<EncodedFormula>> {
    vec![
        vec![],
        vec![f.falsum()],
        vec![f.verum()],
        vec![f.falsum(), f.verum()],
        vec![a],
        vec![na],
        vec![f.verum(), a],
        vec![f.verum(), na],
        vec![f.falsum(), na],
        vec![f.falsum(), na],
        vec![a, na],
        vec![a, b],
        vec![a, b, c],
        vec![na, nb, nc],
        vec![a, b, c, na],
    ]
}

fn add_pbc_corner_cases(
    formulas: &mut Vec<EncodedFormula>,
    f: &FormulaFactory,
    a: EncodedFormula,
    b: EncodedFormula,
    c: EncodedFormula,
    na: EncodedFormula,
    nb: EncodedFormula,
) {
    for &c_type in &[EQ, GT, GE, LT, LE] {
        add_pbc_corner_cases_for_c_type(
            formulas,
            f,
            c_type,
            a.as_literal().unwrap(),
            b.as_literal().unwrap(),
            c.as_literal().unwrap(),
            na.as_literal().unwrap(),
            nb.as_literal().unwrap(),
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn add_pbc_corner_cases_for_c_type(
    formulas: &mut Vec<EncodedFormula>,
    f: &FormulaFactory,
    c_type: CType,
    a: Literal,
    b: Literal,
    c: Literal,
    na: Literal,
    nb: Literal,
) {
    add_pbc_corner_cases_for(formulas, f, c_type, &[], &[]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a], &[-1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a], &[0]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a], &[1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[na], &[-1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[na], &[0]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[na], &[1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b], &[-1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b], &[0, 0]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b], &[1, 1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b], &[1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, nb], &[-1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, nb], &[0, 0]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, nb], &[1, 1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, nb], &[1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, na], &[-1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, na], &[0, 0]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, na], &[1, 1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, na], &[1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b, c], &[-1, -1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b, c], &[0, 0, 0]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b, c], &[1, 1, 1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[a, b, c], &[-1, 1, -1]);
    add_pbc_corner_cases_for(formulas, f, c_type, &[na, nb, c], &[-1, 1, -1]);
}

fn add_pbc_corner_cases_for(
    formulas: &mut Vec<EncodedFormula>,
    f: &FormulaFactory,
    c_type: CType,
    literals: &[Literal],
    coefficients: &[i64],
) {
    for &rhs in &[-1, 0, 1, -3, -4, 3, 4] {
        formulas.push(f.pbc(c_type, rhs, literals, coefficients));
    }
}

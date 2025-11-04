use crate::formulas::{EncodedFormula, FormulaFactory, FormulaType, Literal};
use crate::operations::functions::sub_nodes;
use crate::operations::transformations::cnf::factorization::factorization_cnf;
use crate::operations::transformations::restrict_lit;
use crate::util::exceptions::panic_unexpected_formula_type;
use Literal::{Neg, Pos};

use super::TseitinState;

pub(super) fn tseitin_cnf_with_boundary(
    formula: EncodedFormula,
    f: &FormulaFactory,
    factorization_boundary: u64,
    state: &mut TseitinState,
) -> EncodedFormula {
    let nnf = f.nnf_of(formula);
    if nnf.is_cnf(f) {
        nnf
    } else if nnf.number_of_atoms(f) < factorization_boundary {
        factorization_cnf(nnf, f)
    } else {
        for &sub in &*sub_nodes(nnf, f) {
            compute_tseitin(sub, f, state);
        }
        let tseitin = state.formula[&nnf];
        let top_level = state.variable[&nnf];
        restrict_lit(tseitin, top_level, f)
    }
}

#[allow(clippy::map_entry)] // Using entry would borrow `state`, but we need to pass it to `handle_nary`.
fn compute_tseitin(formula: EncodedFormula, f: &FormulaFactory, state: &mut TseitinState) {
    if !state.formula.contains_key(&formula) {
        match formula.formula_type() {
            FormulaType::Lit(_) => {
                state.formula.insert(formula, formula);
                state.variable.insert(formula, formula.as_literal().unwrap());
            }
            FormulaType::And | FormulaType::Or => {
                let num_ops = formula.number_of_operands(f);
                let ts_variable = f.new_cnf_variable();
                let ts_literal = EncodedFormula::from(Pos(ts_variable));
                let neg_ts_literal = EncodedFormula::from(Neg(ts_variable));
                let mut nops = Vec::new();
                let mut operands = Vec::with_capacity(num_ops);
                let mut neg_operands = Vec::with_capacity(num_ops);
                if formula.is_and() {
                    neg_operands.push(ts_literal);
                    handle_nary(formula, f, &mut nops, &mut operands, &mut neg_operands, state);
                    for operand in &operands {
                        nops.push(f.or([neg_ts_literal, *operand]));
                    }
                    nops.push(f.or(&neg_operands));
                } else {
                    operands.push(neg_ts_literal);
                    handle_nary(formula, f, &mut nops, &mut operands, &mut neg_operands, state);
                    for operand in &neg_operands {
                        nops.push(f.or([ts_literal, *operand]));
                    }
                    nops.push(f.or(&operands));
                }
                state.variable.insert(formula, Pos(ts_variable));
                let result = f.and(&nops);
                state.formula.insert(formula, result);
            }
            _ => panic_unexpected_formula_type(formula, Some(f)),
        }
    }
}

fn handle_nary(
    formula: EncodedFormula,
    f: &FormulaFactory,
    nops: &mut Vec<EncodedFormula>,
    operands: &mut Vec<EncodedFormula>,
    neg_operands: &mut Vec<EncodedFormula>,
    state: &mut TseitinState,
) {
    for &op in &*formula.operands(f) {
        if !op.is_literal() {
            compute_tseitin(op, f, state);
            nops.push(state.formula[&op]);
        }
        let tseitin_var = state.variable[&op];
        operands.push(tseitin_var.into());
        neg_operands.push(tseitin_var.negate().into());
    }
}

#[cfg(test)]
mod tests {
    use std::fs::read_to_string;

    use crate::formulas::{EncodedFormula, FormulaFactory};
    use crate::operations::transformations::cnf::tseitin::{TseitinState, tseitin_cnf_with_boundary};

    #[test]
    fn test() {
        let f = &FormulaFactory::new();
        let formula = f.parse("~(~(a | b) <=> ~(x | y))").unwrap();
        let mut state = TseitinState::default();
        let tseitin = tseitin_cnf_with_boundary(formula, f, 0, &mut state);
        assert!(tseitin.is_cnf(f));
    }

    #[test]
    fn test_large_formula() {
        let formula_string = read_to_string("resources/formulas/large_formula.txt").unwrap();
        let f = &FormulaFactory::new();
        let formula: EncodedFormula = f.parse(&formula_string).unwrap();
        let mut state = TseitinState::default();
        let cnf = tseitin_cnf_with_boundary(formula, f, 0, &mut state);
        assert!(cnf.is_cnf(f));
    }
}

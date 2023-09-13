#![allow(clippy::cast_possible_truncation)]

use num_bigint::{BigUint, ToBigUint};

use crate::formulas::operation_cache::OperationCache;
use crate::formulas::{EncodedFormula, Formula, FormulaFactory, LIT_PRECEDENCE};
use crate::util::exceptions::panic_unexpected_formula_type;

use super::DnnfFormula;

/// Counts the number of models satisfying the given [`DnnfFormula`].
pub fn count(dnnf: &DnnfFormula, f: &FormulaFactory) -> BigUint {
    let simple_result = count_rec(dnnf.formula, f, &mut OperationCache::new());
    let dnnf_variables = dnnf.formula.variables(f);
    let dont_care_count = dnnf.original_variables.difference(&dnnf_variables).count();
    let factor = 2.to_biguint().unwrap().pow(dont_care_count as u32);
    simple_result * factor
}

fn count_rec(dnnf: EncodedFormula, f: &FormulaFactory, cache: &mut OperationCache<BigUint>) -> BigUint {
    if dnnf.is_falsum() {
        0_u32.to_biguint().unwrap()
    } else if dnnf.precedence() >= LIT_PRECEDENCE {
        1_u32.to_biguint().unwrap()
    } else {
        cache.get(dnnf).unwrap_or_else(|| {
            let result = match dnnf.unpack(f) {
                Formula::And(ops) => ops.map(|op| count_rec(op, f, cache)).product(),
                Formula::Or(ops) => {
                    let vars = dnnf.variables(f).len();
                    ops.map(|op| handle_or_op(op, vars, f, cache)).sum::<BigUint>()
                }
                _ => panic_unexpected_formula_type(dnnf, Some(f)),
            };
            cache.insert(dnnf, result.clone());
            result
        })
    }
}

fn handle_or_op(op: EncodedFormula, all_variables: usize, f: &FormulaFactory, cache: &mut OperationCache<BigUint>) -> BigUint {
    let op_count = count_rec(op, f, cache);
    let op_vars = op.variables(f).len();
    let factor = 2.to_biguint().unwrap().pow((all_variables - op_vars) as u32);
    factor * op_count
}

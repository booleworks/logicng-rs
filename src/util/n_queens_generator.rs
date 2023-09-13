use crate::cardinality_constraints::{AmoEncoder, CcConfig};
use crate::formulas::{EncodedFormula, FormulaFactory, Variable};

/// A generator for the n-queens problem.
#[allow(dead_code)]
#[allow(clippy::needless_range_loop)] // the range loop is clearer in this case
pub fn generate_n_queens(n: usize, f: &mut FormulaFactory) -> EncodedFormula {
    f.config.cc_config = CcConfig::new().amo_encoder(AmoEncoder::Pure);
    let var_names = generate_vars(n, f);
    let mut operands = Vec::new();
    for name_vec in &*var_names {
        let vars = &name_vec[0..n];
        let formula = f.exo(vars);
        operands.push(f.nnf_of(formula));
    }
    for i in 0..n {
        let mut vars = Vec::new();
        for name_vec in &*var_names {
            vars.push(name_vec[i]);
        }
        let formula = f.exo(vars);
        operands.push(f.nnf_of(formula));
    }
    for i in 0..n - 1 {
        let mut vars = Vec::new();
        for j in 0..n - i {
            vars.push(var_names[j][i + j]);
        }
        let formula = f.amo(vars);
        operands.push(f.nnf_of(formula));
    }
    for i in 1..n - 1 {
        let mut vars = Vec::new();
        for j in 0..n - i {
            vars.push(var_names[j + i][j]);
        }
        let formula = f.amo(vars);
        operands.push(f.nnf_of(formula));
    }
    for i in 0..n - 1 {
        let mut vars = Vec::new();
        for j in 0..n - i {
            vars.push(var_names[j][n - 1 - (i + j)]);
        }
        let formula = f.amo(vars);
        operands.push(f.nnf_of(formula));
    }
    for i in 1..n - 1 {
        let mut vars = Vec::new();
        for j in 0..n - i {
            vars.push(var_names[j + i][n - 1 - j]);
        }
        let formula = f.amo(vars);
        operands.push(f.nnf_of(formula));
    }
    f.and(&operands)
}

fn generate_vars(n: usize, f: &FormulaFactory) -> Vec<Vec<Variable>> {
    let mut kk = 1;
    let mut var_names = Vec::new();
    for _ in 0..n {
        let mut name_vec = Vec::new();
        for _ in 0..n {
            name_vec.push(f.var(&format!("v{kk}")));
            kk += 1;
        }
        var_names.push(name_vec);
    }
    var_names
}

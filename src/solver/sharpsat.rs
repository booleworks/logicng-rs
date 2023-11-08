use std::collections::HashMap;
use std::str::FromStr;

use logicng_sharp_sat_sys::ffi;
use num_bigint::BigUint;

use crate::formulas::{EncodedFormula, Formula, FormulaFactory, Literal, Variable};
use crate::operations::transformations::{pure_expansion, AdvancedFactorizationConfig, CnfAlgorithm, CnfEncoder};

pub struct SharpSatSolver {
    solver: *mut ffi::Solver,
    var_map_down: HashMap<Variable, i32>,
    var_map_up: Vec<Variable>,
    constant: Option<bool>,
}

impl SharpSatSolver {
    pub fn new() -> Self {
        Self { solver: unsafe { ffi::new_solver() }, var_map_down: HashMap::default(), var_map_up: Vec::default(), constant: None }
    }

    pub fn add_clause(&mut self, clause: &[Literal]) {
        let mut new_clause = Vec::with_capacity(clause.len());
        for lit in clause {
            let var = lit.variable();
            let var_index = self.var_map_down.entry(var).or_insert_with_key(|k| {
                let new_index = self.var_map_up.len() + 1;
                self.var_map_up.push(*k);
                new_index.try_into().expect("SharpSat FFI: The number of variables exceeds the limit")
            });

            if matches!(lit, Literal::Pos(_)) {
                new_clause.push(*var_index);
            } else {
                new_clause.push(-*var_index);
            }
        }

        unsafe {
            ffi::add_clause(
                self.solver,
                new_clause.as_ptr(),
                new_clause.len().try_into().expect("SharpSat FFI: Size of clause exceeds the limit"),
            );
        }
    }

    pub fn add_formula(&mut self, formula: EncodedFormula, f: &FormulaFactory) {
        let expanded = pure_expansion(formula, f);
        let mut cnf_encoder =
            CnfEncoder::new(CnfAlgorithm::Advanced(AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin)));
        let cnf_formula = cnf_encoder.transform(expanded, f);
        match cnf_formula.unpack(f) {
            Formula::Or(ops) => self.add_clause(&ops.map(|formula| formula.as_literal().expect("invalid cnf")).collect::<Box<_>>()),
            Formula::And(ops) => {
                for op in ops {
                    match op.unpack(f) {
                        Formula::Or(or_ops) => {
                            self.add_clause(&or_ops.map(|formula| formula.as_literal().expect("invalid cnf")).collect::<Box<_>>());
                        }
                        Formula::And(_) => panic!("FF invariant broken: Nested And statement"),
                        Formula::Lit(lit) => self.add_clause(&[lit]),
                        _ => panic!("invalid cnf"),
                    }
                }
            }
            Formula::Lit(lit) => self.add_clause(&[lit]),
            Formula::True => self.constant = Some(true),
            Formula::False => self.constant = Some(false),
            _ => panic!("Unexpected formula type {:?}", cnf_formula.formula_type()),
        }
    }

    pub fn solve(&mut self) -> BigUint {
        match self.constant {
            Some(true) => BigUint::from(1_u64),
            Some(false) => BigUint::from(0_u64),
            None => {
                let res = unsafe { ffi::solve(self.solver) };
                BigUint::from_str(&format!("{res}")).unwrap_or_else(|_| panic!("SharpSat FFI: Returned value {res} is not a vaild result"))
            }
        }
    }
}

impl Drop for SharpSatSolver {
    fn drop(&mut self) {
        unsafe { ffi::drop_solver(self.solver) };
    }
}

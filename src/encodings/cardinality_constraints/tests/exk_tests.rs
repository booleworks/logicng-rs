use crate::encodings::cardinality_constraints::cc_config::{CcConfig, ExkEncoder};
use crate::formulas::{CType, FormulaFactory, Variable};
use crate::solver::lng_core_solver::functions::model_enumeration_function::{enumerate_models_with_config, ModelEnumerationConfig};
use crate::solver::lng_core_solver::SatSolver;

fn configs() -> Vec<CcConfig> {
    vec![CcConfig::new().exk_encoder(ExkEncoder::Totalizer), CcConfig::new().exk_encoder(ExkEncoder::CardinalityNetwork)]
}

#[test]
fn test_exk() {
    let mut f = FormulaFactory::new();
    for config in configs() {
        f.config.cc_config = config;
        test_cc(10, 0, 1, &f);
        test_cc(10, 1, 10, &f);
        test_cc(10, 2, 45, &f);
        test_cc(10, 3, 120, &f);
        test_cc(10, 4, 210, &f);
        test_cc(10, 5, 252, &f);
        test_cc(10, 6, 210, &f);
        test_cc(10, 7, 120, &f);
        test_cc(10, 8, 45, &f);
        test_cc(10, 9, 10, &f);
        test_cc(10, 10, 1, &f);
        test_cc(10, 12, 0, &f);
    }
}

fn test_cc(num_lits: u64, rhs: u32, expected: u64, f: &FormulaFactory) {
    let problem_vars: Box<[Variable]> = (0..num_lits).map(|i| f.variable(format!("v{i}")).as_variable().unwrap()).collect();
    let mut solver = SatSolver::<()>::new();
    let cc = f.cc(CType::EQ, rhs, problem_vars.clone());
    solver.add_formula(cc, f);
    if expected == 0 {
        assert!(!solver.sat(f));
    } else {
        assert!(solver.sat(f));
    }
    let models = enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::new(problem_vars).max_models(12000), f);
    assert_eq!(models.len() as u64, expected);
}

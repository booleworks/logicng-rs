use crate::cardinality_constraints::cc_config::{AmkEncoder, CcConfig};
use crate::formulas::{CType, FormulaFactory, Variable};
use crate::solver::functions::{enumerate_models_with_config, ModelEnumerationConfig};
use crate::solver::minisat::sat::Tristate::{False, True};
use crate::solver::minisat::MiniSat;

fn configs() -> Vec<CcConfig> {
    vec![
        CcConfig::new().amk_encoder(AmkEncoder::Totalizer),
        CcConfig::new().amk_encoder(AmkEncoder::ModularTotalizer),
        CcConfig::new().amk_encoder(AmkEncoder::CardinalityNetwork),
    ]
}

#[test]
fn test_amk() {
    let mut f = FormulaFactory::new();
    for config in configs() {
        f.config.cc_config = config;
        test_cc(10, 0, 1, &f);
        test_cc(10, 1, 11, &f);
        test_cc(10, 2, 56, &f);
        test_cc(10, 3, 176, &f);
        #[cfg(feature = "long_running_tests")]
        {
            test_cc(10, 4, 386, &f);
            test_cc(10, 5, 638, &f);
            test_cc(10, 6, 848, &f);
            test_cc(10, 7, 968, &f);
            test_cc(10, 8, 1013, &f);
            test_cc(10, 9, 1023, &f);
        }
        test_cc(10, 10, 1024, &f);
        test_cc(10, 15, 1024, &f);
    }
}

fn test_cc(num_lits: u64, rhs: u32, expected: u64, f: &FormulaFactory) {
    let problem_vars: Box<[Variable]> = (0..num_lits).map(|i| f.variable(format!("v{i}")).as_variable().unwrap()).collect();
    let cc = f.cc(CType::LE, rhs, problem_vars.clone());
    let mut solver = MiniSat::new();
    solver.add(cc, f);
    if expected == 0 {
        assert_eq!(solver.sat(), False);
    } else {
        assert_eq!(solver.sat(), True);
    }
    let models = enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(problem_vars).max_models(12000));
    assert_eq!(models.len() as u64, expected);
}

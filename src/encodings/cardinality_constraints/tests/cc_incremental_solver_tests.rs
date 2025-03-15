use crate::datastructures::EncodingResultFF;
use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder, CcConfig};
use crate::formulas::CType::{GE, LE};
use crate::formulas::{FormulaFactory, Variable};
use crate::solver::lng_core_solver::EncodingResultSatSolver;
use crate::solver::lng_core_solver::{SatSolver, SatSolverConfig};

const fn configs() -> [CcConfig; 3] {
    [
        CcConfig::new().amk_encoder(AmkEncoder::Totalizer).alk_encoder(AlkEncoder::Totalizer),
        CcConfig::new().amk_encoder(AmkEncoder::CardinalityNetwork).alk_encoder(AlkEncoder::CardinalityNetwork),
        CcConfig::new().amk_encoder(AmkEncoder::ModularTotalizer).alk_encoder(AlkEncoder::ModularTotalizer),
    ]
}

fn solvers() -> [SatSolver; 1] {
    [SatSolver::from_config(SatSolverConfig::default())]
}

#[test]
fn test_simple_incremental_amk() {
    for config in configs() {
        for solver in &mut solvers() {
            let f = &mut FormulaFactory::new();
            let mut result = EncodingResultSatSolver::new(solver, None);
            f.config.cc_config = configs()[2].clone();
            let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
            result.solver.add_formula(f.cc(GE, 4, vars.clone()), f);
            result.solver.add_formula(f.cc(LE, 7, vars.clone()), f);
            f.config.cc_config = config.clone();

            let mut inc_data = result.solver.add_incremental_cc(f.cc(LE, 9, vars).as_cc(f).unwrap()).unwrap();
            assert!(result.solver.sat(f));
            inc_data.new_upper_bound(&mut result, 8);
            assert!(result.solver.sat(f));
            inc_data.new_upper_bound(&mut result, 7);
            assert!(result.solver.sat(f));
            inc_data.new_upper_bound(&mut result, 6);
            assert!(result.solver.sat(f));
            inc_data.new_upper_bound(&mut result, 5);
            assert!(result.solver.sat(f));
            inc_data.new_upper_bound(&mut result, 4);
            assert!(result.solver.sat(f));

            let state = result.solver.save_state();
            inc_data.new_upper_bound(&mut result, 3);
            assert!(!result.solver.sat(f));
            result.solver.load_state(&state);
            assert!(result.solver.sat(f));
            inc_data.new_upper_bound(&mut result, 2);
            assert!(!solver.sat(f));
        }
    }
}

#[test]
fn test_simple_incremental_alk() {
    for config in configs() {
        for solver in &mut solvers() {
            let f = &mut FormulaFactory::new();
            f.config.cc_config = configs()[2].clone();
            let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
            solver.add_formula(f.cc(GE, 4, vars.clone()), f);
            solver.add_formula(f.cc(LE, 7, vars.clone()), f);
            f.config.cc_config = config.clone();

            let mut result = EncodingResultSatSolver::new(solver, None);
            let mut inc_data = result.solver.add_incremental_cc(f.cc(GE, 2, vars).as_cc(f).unwrap()).unwrap();
            assert!(result.solver.sat(f));
            inc_data.new_lower_bound(&mut result, 3);
            assert!(result.solver.sat(f));
            inc_data.new_lower_bound(&mut result, 4);
            assert!(result.solver.sat(f));
            inc_data.new_lower_bound(&mut result, 5);
            assert!(result.solver.sat(f));
            inc_data.new_lower_bound(&mut result, 6);
            assert!(result.solver.sat(f));
            inc_data.new_lower_bound(&mut result, 7);
            assert!(result.solver.sat(f));

            let state = result.solver.save_state();
            inc_data.new_lower_bound(&mut result, 8);
            assert!(!result.solver.sat(f));
            result.solver.load_state(&state);
            assert!(result.solver.sat(f));
            inc_data.new_lower_bound(&mut result, 9);
            assert!(!result.solver.sat(f));
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_upper_bound_amk() {
    for config in [&configs()[0], &configs()[2]] {
        for mut solver in solvers() {
            let f = &mut FormulaFactory::new();
            let mut result = EncodingResultSatSolver::new(&mut solver, None);
            f.config.cc_config = configs()[2].clone();
            let num_lits = 100;
            let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
            let mut current_bound = num_lits - 1;
            result.solver.add_formula(f.cc(GE, 42, vars.clone()), f);
            f.config.cc_config = config.clone();
            let mut inc_data = result.solver.add_incremental_cc(f.cc(LE, current_bound, vars).as_cc(f).unwrap()).unwrap();
            while result.solver.sat(f) {
                current_bound -= 1;
                inc_data.new_upper_bound(&mut result, current_bound);
            }
            assert_eq!(current_bound, 41);
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_lower_bound_alk() {
    for config in [&configs()[0], &configs()[2]] {
        for mut solver in solvers() {
            let f = &mut FormulaFactory::new();
            f.config.cc_config = configs()[2].clone();
            let num_lits = 100;
            let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
            let mut current_bound = 2;
            solver.add_formula(f.cc(LE, 87, vars.clone()), f);
            f.config.cc_config = config.clone();
            let mut result = EncodingResultFF::new(f);
            let mut inc_data = solver.add_incremental_cc(f.cc(GE, current_bound, vars).as_cc(f).unwrap()).unwrap();
            while solver.sat(f) {
                current_bound += 1;
                inc_data.new_lower_bound(&mut result, current_bound);
            }
            assert_eq!(current_bound, 88);
        }
    }
}

#[test]
#[ignore = "Too large for MiniSat, requires Glucose"]
fn test_very_large_modular_totalizer_amk() {
    let f = &mut FormulaFactory::new();
    f.config.cc_config = configs()[2].clone();
    let num_lits = 300;
    let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
    let mut current_bound = num_lits - 1;
    let mut solver = SatSolver::<()>::new();
    let mut result = EncodingResultSatSolver::new(&mut solver, None);
    result.solver.add_formula(f.cc(GE, 234, vars.clone()), f);
    let mut inc_data = result.solver.add_incremental_cc(f.cc(LE, current_bound, vars).as_cc(f).unwrap()).unwrap();
    while result.solver.sat(f) {
        current_bound -= 1;
        inc_data.new_upper_bound(&mut result, current_bound);
    }
    assert_eq!(current_bound, 233);
}

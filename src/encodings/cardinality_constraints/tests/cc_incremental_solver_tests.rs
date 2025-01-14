use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder, CcConfig};
use crate::formulas::CType::{GE, LE};
use crate::formulas::{FormulaFactory, Variable};
use crate::solver::minisat::sat::Tristate::{False, True};
use crate::solver::minisat::{MiniSat, MiniSatConfig};

const fn configs() -> [CcConfig; 3] {
    [
        CcConfig::new().amk_encoder(AmkEncoder::Totalizer).alk_encoder(AlkEncoder::Totalizer),
        CcConfig::new().amk_encoder(AmkEncoder::CardinalityNetwork).alk_encoder(AlkEncoder::CardinalityNetwork),
        CcConfig::new().amk_encoder(AmkEncoder::ModularTotalizer).alk_encoder(AlkEncoder::ModularTotalizer),
    ]
}

fn solvers() -> [MiniSat; 2] {
    [MiniSat::from_config(MiniSatConfig::default()), MiniSat::from_config(MiniSatConfig::default().incremental(false))]
}

#[test]
fn test_simple_incremental_amk() {
    for config in configs() {
        for solver in &mut solvers() {
            let f = &mut FormulaFactory::new();
            f.config.cc_config = configs()[2].clone();
            let vars: Box<[Variable]> = (0..10).map(|i| f.var(format!("v{i}"))).collect();
            solver.add(f.cc(GE, 4, vars.clone()), f);
            solver.add(f.cc(LE, 7, vars.clone()), f);
            f.config.cc_config = config.clone();

            let mut inc_data = solver.add_incremental_cc(&f.cc(LE, 9, vars).as_cc(f).unwrap(), f).unwrap();
            assert_eq!(solver.sat(), True);
            inc_data.new_upper_bound_for_solver(solver, f, 8);
            assert_eq!(solver.sat(), True);
            inc_data.new_upper_bound_for_solver(solver, f, 7);
            assert_eq!(solver.sat(), True);
            inc_data.new_upper_bound_for_solver(solver, f, 6);
            assert_eq!(solver.sat(), True);
            inc_data.new_upper_bound_for_solver(solver, f, 5);
            assert_eq!(solver.sat(), True);
            inc_data.new_upper_bound_for_solver(solver, f, 4);
            assert_eq!(solver.sat(), True);

            if solver.underlying_solver.config.incremental {
                let state = solver.save_state();
                inc_data.new_upper_bound_for_solver(solver, f, 3);
                assert_eq!(solver.sat(), False);
                solver.load_state(&state);
                assert_eq!(solver.sat(), True);
                inc_data.new_upper_bound_for_solver(solver, f, 2);
                assert_eq!(solver.sat(), False);
            }
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
            solver.add(f.cc(GE, 4, vars.clone()), f);
            solver.add(f.cc(LE, 7, vars.clone()), f);
            f.config.cc_config = config.clone();

            let mut inc_data = solver.add_incremental_cc(&f.cc(GE, 2, vars).as_cc(f).unwrap(), f).unwrap();
            assert_eq!(solver.sat(), True);
            inc_data.new_lower_bound_for_solver(solver, f, 3);
            assert_eq!(solver.sat(), True);
            inc_data.new_lower_bound_for_solver(solver, f, 4);
            assert_eq!(solver.sat(), True);
            inc_data.new_lower_bound_for_solver(solver, f, 5);
            assert_eq!(solver.sat(), True);
            inc_data.new_lower_bound_for_solver(solver, f, 6);
            assert_eq!(solver.sat(), True);
            inc_data.new_lower_bound_for_solver(solver, f, 7);
            assert_eq!(solver.sat(), True);

            if solver.underlying_solver.config.incremental {
                let state = solver.save_state();
                inc_data.new_lower_bound_for_solver(solver, f, 8);
                assert_eq!(solver.sat(), False);
                solver.load_state(&state);
                assert_eq!(solver.sat(), True);
                inc_data.new_lower_bound_for_solver(solver, f, 9);
                assert_eq!(solver.sat(), False);
            }
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_upper_bound_amk() {
    for config in [&configs()[0], &configs()[2]] {
        for mut solver in solvers() {
            let f = &mut FormulaFactory::new();
            f.config.cc_config = configs()[2].clone();
            let num_lits = 100;
            let vars: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
            let mut current_bound = num_lits - 1;
            solver.add(f.cc(GE, 42, vars.clone()), f);
            f.config.cc_config = config.clone();
            let mut inc_data = solver.add_incremental_cc(&f.cc(LE, current_bound, vars).as_cc(f).unwrap(), f).unwrap();
            while solver.sat() == True {
                current_bound -= 1;
                inc_data.new_upper_bound_for_solver(&mut solver, f, current_bound);
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
            solver.add(f.cc(LE, 87, vars.clone()), f);
            f.config.cc_config = config.clone();
            let mut inc_data = solver.add_incremental_cc(&f.cc(GE, current_bound, vars).as_cc(f).unwrap(), f).unwrap();
            while solver.sat() == True {
                current_bound += 1;
                inc_data.new_lower_bound_for_solver(&mut solver, f, current_bound);
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
    let mut solver = MiniSat::new();
    solver.add(f.cc(GE, 234, vars.clone()), f);
    let mut inc_data = solver.add_incremental_cc(&f.cc(LE, current_bound, vars).as_cc(f).unwrap(), f).unwrap();
    while solver.sat() == True {
        current_bound -= 1;
        inc_data.new_upper_bound_for_solver(&mut solver, f, current_bound);
    }
    assert_eq!(current_bound, 233);
}

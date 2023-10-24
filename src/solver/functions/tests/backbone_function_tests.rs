use crate::backbones::Backbone;
use crate::formulas::{FormulaFactory, Literal, ToFormula, Variable};
use crate::io::read_formula;
use crate::solver::functions::backbone_function::BackboneConfig;
use crate::solver::functions::backbone_function::BackboneType::{OnlyNegative, OnlyPositive};
use crate::solver::minisat::MiniSat;
use crate::solver::minisat_config::MiniSatConfig;
use crate::solver::minisat_config::SolverCnfMethod::{FactoryCnf, PgOnSolver};
use std::collections::BTreeSet;
use std::fs::File;
use std::io::{BufRead, BufReader};

fn solvers() -> [(MiniSat, &'static str); 10] {
    let config_no_pg1 = MiniSatConfig::default()
        .cnf_method(FactoryCnf)
        .bb_check_for_rotatable_literals(false)
        .bb_check_for_complement_model_literals(false)
        .bb_initial_ubcheck_for_rotatable_literals(false);
    let config_no_pg2 = MiniSatConfig::default()
        .cnf_method(FactoryCnf)
        .bb_check_for_rotatable_literals(true)
        .bb_check_for_complement_model_literals(false)
        .bb_initial_ubcheck_for_rotatable_literals(false);
    let config_no_pg3 = MiniSatConfig::default()
        .cnf_method(FactoryCnf)
        .bb_check_for_rotatable_literals(false)
        .bb_check_for_complement_model_literals(true)
        .bb_initial_ubcheck_for_rotatable_literals(false);
    let config_no_pg4 = MiniSatConfig::default()
        .cnf_method(FactoryCnf)
        .bb_check_for_rotatable_literals(false)
        .bb_check_for_complement_model_literals(false)
        .bb_initial_ubcheck_for_rotatable_literals(true);
    let config_no_pg5 = MiniSatConfig::default()
        .cnf_method(FactoryCnf)
        .bb_check_for_rotatable_literals(true)
        .bb_check_for_complement_model_literals(true)
        .bb_initial_ubcheck_for_rotatable_literals(true);
    let config_pg1 = MiniSatConfig::default()
        .cnf_method(PgOnSolver)
        .bb_check_for_rotatable_literals(false)
        .bb_check_for_complement_model_literals(false)
        .bb_initial_ubcheck_for_rotatable_literals(false);
    let config_pg2 = MiniSatConfig::default()
        .cnf_method(PgOnSolver)
        .bb_check_for_rotatable_literals(true)
        .bb_check_for_complement_model_literals(false)
        .bb_initial_ubcheck_for_rotatable_literals(false);
    let config_pg3 = MiniSatConfig::default()
        .cnf_method(PgOnSolver)
        .bb_check_for_rotatable_literals(false)
        .bb_check_for_complement_model_literals(true)
        .bb_initial_ubcheck_for_rotatable_literals(false);
    let config_pg4 = MiniSatConfig::default()
        .cnf_method(PgOnSolver)
        .bb_check_for_rotatable_literals(false)
        .bb_check_for_complement_model_literals(false)
        .bb_initial_ubcheck_for_rotatable_literals(true);
    let config_pg5 = MiniSatConfig::default()
        .cnf_method(PgOnSolver)
        .bb_check_for_rotatable_literals(true)
        .bb_check_for_complement_model_literals(true)
        .bb_initial_ubcheck_for_rotatable_literals(true);
    [
        (MiniSat::from_config(config_no_pg1), "FF CNF -ROT -COMP -UB"),
        (MiniSat::from_config(config_no_pg2), "FF CNF +ROT -COMP -UB"),
        (MiniSat::from_config(config_no_pg3), "FF CNF -ROT +COMP -UB"),
        (MiniSat::from_config(config_no_pg4), "FF CNF -ROT -COMP +UB"),
        (MiniSat::from_config(config_no_pg5), "FF CNF +ROT +COMP +UB"),
        (MiniSat::from_config(config_pg1), "PG CNF -ROT -COMP -UB"),
        (MiniSat::from_config(config_pg2), "PG CNF +ROT -COMP -UB"),
        (MiniSat::from_config(config_pg3), "PG CNF -ROT +COMP -UB"),
        (MiniSat::from_config(config_pg4), "PG CNF -ROT -COMP +UB"),
        (MiniSat::from_config(config_pg5), "PG CNF +ROT +COMP +UB"),
    ]
}

#[test]
fn test_constant() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        let state = solver.save_state();
        solver.add(f.falsum(), f);
        let backbone = BackboneConfig::new(v("a b c", f)).compute_backbone(&mut solver);
        assert!(!backbone.sat);
        solver.load_state(&state);
        solver.add(f.verum(), f);
        let backbone = BackboneConfig::new(v("a b c", f)).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert!(backbone.complete_backbone().is_empty());
    }
}

#[test]
fn test_simple_backbones() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        let state = solver.save_state();
        solver.add("a & b & ~c".to_formula(f), f);
        let backbone = BackboneConfig::new(v("a b c", f)).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert_eq!(l("a b ~c", f), backbone.complete_backbone());
        solver.load_state(&state);
        solver.add("~a & ~b & c".to_formula(f), f);
        let backbone = BackboneConfig::new(v("a c", f)).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert_eq!(l("~a c", f), backbone.complete_backbone());
    }
}

#[test]
fn test_simple_formulas() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        solver.add("(a => c | d) & (b => d | ~e) & (a | b)".to_formula(f), f);
        let backbone = BackboneConfig::new(v("a b c d e f", f)).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert!(backbone.complete_backbone().is_empty());
        assert_eq!(Some(v("a b c d e f", f).iter().copied().collect()), backbone.optional_variables);
        solver.add("a => b".to_formula(f), f);
        solver.add("b => a".to_formula(f), f);
        solver.add("~d".to_formula(f), f);
        let backbone = BackboneConfig::new(v("a b c d e f g h", f)).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert_eq!(l("a b c ~d ~e", f), backbone.complete_backbone());
        assert_eq!(Some(v("f g h", f).iter().copied().collect()), backbone.optional_variables);

        let backbone = BackboneConfig::new(v("a b c d e f g h", f)).backbone_type(OnlyPositive).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert_eq!(l("a b c", f), backbone.complete_backbone());
        assert_eq!(None, backbone.optional_variables);
        let backbone = BackboneConfig::new(v("a b c d e f g h", f)).backbone_type(OnlyNegative).compute_backbone(&mut solver);
        assert!(backbone.sat);
        assert_eq!(l("~d ~e", f), backbone.complete_backbone());
        assert_eq!(None, backbone.optional_variables);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_real_formula_incremental1() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        let formula = read_formula("resources/formulas/large_formula.txt", f).unwrap();
        let vars: Vec<Variable> = (*formula.variables(f)).iter().copied().collect();
        solver.add(formula, f);

        let expected_backbones: Vec<BTreeSet<Literal>> =
            BufReader::new(File::open("resources/backbones/backbone_large_formula.txt").unwrap())
                .lines()
                .map(|line| line.unwrap().split(' ').map(|lit| lit.to_formula(f).as_literal().unwrap()).collect::<BTreeSet<Literal>>())
                .collect();

        assert_eq!(expected_backbones[0], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v411"), f);
        assert_eq!(expected_backbones[1], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v385"), f);
        assert_eq!(expected_backbones[2], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v275"), f);
        assert_eq!(expected_backbones[3], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v188"), f);
        assert_eq!(expected_backbones[4], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v103"), f);
        assert_eq!(expected_backbones[5], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v404"), f);
        assert_eq!(Backbone::new_unsat(), BackboneConfig::new(vars.clone()).compute_backbone(&mut solver));
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_real_formula_incremental2() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        let formula = read_formula("resources/formulas/small_formulas.txt", f).unwrap();
        let vars: Vec<Variable> = (*formula.variables(f)).iter().copied().collect();
        solver.add(formula, f);

        let expected_backbones: Vec<BTreeSet<Literal>> =
            BufReader::new(File::open("resources/backbones/backbone_small_formulas.txt").unwrap())
                .lines()
                .map(|line| line.unwrap().split(' ').map(|lit| lit.to_formula(f).as_literal().unwrap()).collect::<BTreeSet<Literal>>())
                .collect();

        assert_eq!(expected_backbones[0], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v2609"), f);
        assert_eq!(expected_backbones[1], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v2416"), f);
        assert_eq!(expected_backbones[2], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v2048"), f);
        assert_eq!(expected_backbones[3], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v39"), f);
        assert_eq!(expected_backbones[4], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v1663"), f);
        assert_eq!(expected_backbones[5], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
        solver.add(f.variable("v2238"), f);
        assert_eq!(Backbone::new_unsat(), BackboneConfig::new(vars.clone()).compute_backbone(&mut solver));
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_real_formula_incremental_decremental1() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        if solver.config.incremental {
            let formula = read_formula("resources/formulas/large_formula.txt", f).unwrap();
            let vars: Vec<Variable> = (*formula.variables(f)).iter().copied().collect();
            solver.add(formula, f);
            let state = &solver.save_state();
            let expected_backbones: Vec<BTreeSet<Literal>> =
                BufReader::new(File::open("resources/backbones/backbone_large_formula.txt").unwrap())
                    .lines()
                    .map(|line| line.unwrap().split(' ').map(|lit| lit.to_formula(f).as_literal().unwrap()).collect::<BTreeSet<Literal>>())
                    .collect();

            assert_eq!(expected_backbones[0], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v411".to_formula(f), f);
            assert_eq!(expected_backbones[1], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v411 & v385".to_formula(f), f);
            assert_eq!(expected_backbones[2], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v411 & v385 & v275".to_formula(f), f);
            assert_eq!(expected_backbones[3], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v411 & v385 & v275 & v188".to_formula(f), f);
            assert_eq!(expected_backbones[4], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v411 & v385 & v275 & v188 & v103".to_formula(f), f);
            assert_eq!(expected_backbones[5], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v411 & v385 & v275 & v188 & v103 & v404".to_formula(f), f);
            assert_eq!(Backbone::new_unsat(), BackboneConfig::new(vars.clone()).compute_backbone(&mut solver));
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_real_formula_incremental_decremental2() {
    let f = &FormulaFactory::new();
    for (mut solver, _) in solvers() {
        if solver.config.incremental {
            let formula = read_formula("resources/formulas/small_formulas.txt", f).unwrap();
            let vars: Vec<Variable> = (*formula.variables(f)).iter().copied().collect();
            solver.add(formula, f);
            let state = &solver.save_state();
            let expected_backbones: Vec<BTreeSet<Literal>> =
                BufReader::new(File::open("resources/backbones/backbone_small_formulas.txt").unwrap())
                    .lines()
                    .map(|line| line.unwrap().split(' ').map(|lit| lit.to_formula(f).as_literal().unwrap()).collect::<BTreeSet<Literal>>())
                    .collect();

            assert_eq!(expected_backbones[0], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add(f.variable("v2609"), f);
            assert_eq!(expected_backbones[1], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v2609 & v2416".to_formula(f), f);
            assert_eq!(expected_backbones[2], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v2609 & v2416 & v2048".to_formula(f), f);
            assert_eq!(expected_backbones[3], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v2609 & v2416 & v2048 & v39".to_formula(f), f);
            assert_eq!(expected_backbones[4], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v2609 & v2416 & v2048 & v39 & v1663".to_formula(f), f);
            assert_eq!(expected_backbones[5], BackboneConfig::new(vars.clone()).compute_backbone(&mut solver).complete_backbone());
            solver.load_state(state);
            solver.add("v2609 & v2416 & v2048 & v39 & v1663 & v2238".to_formula(f), f);
            assert_eq!(Backbone::new_unsat(), BackboneConfig::new(vars.clone()).compute_backbone(&mut solver));
        }
    }
}

fn v(var_string: &str, f: &FormulaFactory) -> Vec<Variable> {
    var_string.split(' ').map(|s| f.var(s)).collect()
}

fn l(lit_string: &'static str, f: &FormulaFactory) -> BTreeSet<Literal> {
    lit_string.split(' ').map(|s| s.to_formula(f).as_literal().unwrap()).collect()
}

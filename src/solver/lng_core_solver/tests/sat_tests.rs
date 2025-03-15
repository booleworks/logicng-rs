use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Duration;

use itertools::Itertools;

use crate::datastructures::{Assignment, Model};
use crate::formulas::CType::{EQ, GE};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, ToFormula, Variable};
use crate::handlers::{TimeoutHandler, Timer};
use crate::io::read_cnf;
use crate::propositions::StandardProposition;
use crate::solver::lng_core_solver::functions::model_enumeration_function::{enumerate_models_with_config, ModelEnumerationConfig};
use crate::solver::lng_core_solver::tests::generate_pigeon_hole;
use crate::solver::lng_core_solver::{CnfMethod, SatSolver, SatSolverConfig};
use crate::util::test_util::{lits, lits_list, vars_list};

use super::{solver_configuration_cross_product, solver_cross_product, SatSolverConfigParam};

fn solvers<B>() -> Vec<SatSolver<B>> {
    solver_cross_product::<B>(&[
        SatSolverConfigParam::UseAtMostClauses,
        SatSolverConfigParam::CnfMethod,
        SatSolverConfigParam::ClauseMinimization,
        SatSolverConfigParam::ProofGeneration,
        SatSolverConfigParam::InitialPhase,
    ])
}

fn solver_configs() -> Vec<SatSolverConfig> {
    solver_configuration_cross_product(&[
        SatSolverConfigParam::UseAtMostClauses,
        SatSolverConfigParam::CnfMethod,
        SatSolverConfigParam::ClauseMinimization,
        SatSolverConfigParam::ProofGeneration,
        SatSolverConfigParam::InitialPhase,
    ])
}

#[test]
fn test_true() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula(f.verum(), f);
        assert_eq!(solver.sat_call().model(&[], f).unwrap().len(), 0);
    }
}

#[test]
fn test_false() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula(f.falsum(), f);
        assert_eq!(solver.sat_call().model(&[], f), None);
    }
}

#[test]
fn test_literals1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let a = f.var("a");
        solver.add_formula(a.into(), f);
        let model = solver.sat_call().model(&[a], f).unwrap();
        assert_eq!(model.len(), 1);
        assert!(Assignment::from(model).evaluate_lit(a.into()));
        solver.add_formula(a.neg_lit().into(), f);
        assert!(!solver.sat(f));
    }
}

#[test]
fn test_literals2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let na = f.lit("a", false);
        solver.add_formula(na.into(), f);
        let model = solver.sat_call().model(&[na.variable()], f).unwrap();
        assert_eq!(model.len(), 1);
        assert!(Assignment::from(model).evaluate_lit(na));
    }
}

#[test]
fn test_and1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula("a & b".to_formula(f), f);
        let vars = [f.var("a"), f.var("b")];
        let model = Assignment::from(solver.sat_call().model(&vars, f).unwrap());
        assert_eq!(model.len(), 2);
        assert!(model.evaluate_lit(f.lit("a", true)));
        assert!(model.evaluate_lit(f.lit("b", true)));
        solver.add_formula("~(a & b)".to_formula(f), f);
        assert!(!solver.sat(f));
        assert!(solver.sat_call().model(&vars, f).is_none());
    }
}

#[test]
fn test_and2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<String>() {
        let prop = StandardProposition::new("a & ~b & c & ~d".to_formula(f));
        let vars = [f.var("a"), f.var("b"), f.var("c"), f.var("d")];
        solver.add_proposition(prop, f);
        let model = Assignment::from(solver.sat_call().model(&vars, f).unwrap());
        assert_eq!(model.len(), 4);
        assert!(model.evaluate_lit(f.lit("a", true)));
        assert!(!model.evaluate_lit(f.lit("b", true)));
        assert!(model.evaluate_lit(f.lit("c", true)));
        assert!(!model.evaluate_lit(f.lit("d", true)));
    }
}

#[test]
fn test_and3() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formulas = vec![f.lit("a", true), f.lit("b", false), f.lit("a", false), f.lit("d", false)];
        solver.add_formulas(formulas, f);
        assert!(!solver.sat(f));
    }
}

#[test]
fn test_formula1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formula = "(x => y) & (~x => y) & (y => z) & (z => ~x)".to_formula(f);
        solver.add_formula(formula, f);
        let model = Assignment::from(solver.sat_call().model(&[f.var("x"), f.var("y"), f.var("z")], f).unwrap());
        assert_eq!(model.len(), 3);
        assert!(!model.evaluate_lit(f.lit("x", true)));
        assert!(model.evaluate_lit(f.lit("y", true)));
        assert!(model.evaluate_lit(f.lit("z", true)));
        solver.add_formula(f.literal("x", true), f);
        assert!(!solver.sat(f));
    }
}

#[test]
fn test_formula2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula("(x => y) & (~x => y) & (y => z) & (z => ~x)".to_formula(f), f);
        let vars = [f.var("x"), f.var("y"), f.var("z")];
        let models = solver.enumerate_all_models(&vars, f);
        assert_eq!(models.len(), 1);
        let model = Assignment::from(&models[0]);
        assert!(!model.evaluate_lit(f.lit("x", true)));
        assert!(model.evaluate_lit(f.lit("y", true)));
        assert!(model.evaluate_lit(f.lit("z", true)));
        solver.add_formula(f.literal("x", true), f);
        assert!(!solver.sat(f));
    }
}

#[test]
fn test_formula3() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula("a | b".to_formula(f), f);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::new([f.var("a"), f.var("b")]).additional_variables([f.var("c")]),
            f,
        );
        assert_eq!(models.len(), 3);
        for model in models {
            assert_eq!(model.len(), 3);
            assert!(model.literals().contains(&f.lit("c", false)));
        }
    }
}

#[test]
fn test_cc1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let vars = (0..100).map(|i| f.var(format!("x{i}"))).collect::<Box<[_]>>();
        solver.add_formula(f.exo(vars.clone()), f);
        let models = solver.enumerate_all_models(&vars, f);
        assert_eq!(models.len(), 100);
        assert!(models.iter().all(|m| m.pos().len() == 1));
    }
}

#[test]
fn test_pbc() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let mut lits = vec![];
        let mut coeffs = vec![];
        for i in 0..5 {
            lits.push(f.lit(&format!("x{i}"), i % 2 == 0));
            coeffs.push(i + 1);
        }
        solver.add_formula(f.pbc(GE, 10, lits, coeffs), f);
        assert!(solver.sat(f));
    }
}

#[test]
fn test_partial_model() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula("a".to_formula(f), f);
        solver.add_formula("b".to_formula(f), f);
        solver.add_formula("c".to_formula(f), f);
        let relevant_vars = [f.var("a"), f.var("b")].to_vec();
        assert!(solver.sat(f));
        let model = solver.sat_call().model(&relevant_vars, f).unwrap();
        assert!(model.neg().is_empty());
        assert!(!model.literals().contains(&f.lit("c", true)));
    }
}

#[test]
fn test_variables_removed_by_simplification_occurs_in_models() {
    let f = &FormulaFactory::new();
    let mut solver = SatSolver::<()>::from_config(SatSolverConfig::default().with_cnf_method(CnfMethod::PgOnSolver));
    let a = f.var("A");
    let b = f.var("B");
    let formula = "A & B => A".to_formula(f);
    solver.add_formula(formula, f);
    assert!(solver.sat(f));
    assert!(solver.underlying_solver().known_variables().is_empty());
    assert_eq!(vec![a, b], solver.sat_call().model(&[a, b], f).unwrap().literals().into_iter().map(|l| l.variable()).collect::<Vec<_>>());
}

#[test]
fn test_unknown_variable_not_occurring_in_model() {
    let f = &FormulaFactory::new();
    let mut solver = SatSolver::<()>::new();
    let a = "A".to_formula(f);
    solver.add_formula(a, f);
    assert_eq!(vec![f.lit("A", true), f.lit("X", false)], solver.sat_call().model(&[f.var("A"), f.var("X")], f).unwrap().literals());
}

#[test]
fn test_relaxation_formulas() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formula = "a & (b | c)".to_formula(f);
        solver.add_formula(formula, f);
        assert!(solver.sat(f));
        solver.add_formula_with_relaxation(f.var("x"), "~a & ~b".to_formula(f), f);
        assert!(solver.sat(f));
        assert!(solver.sat_call().model(&[f.var("a"), f.var("b"), f.var("c"), f.var("x")], f).unwrap().pos().contains(&f.var("x")));
        solver.add_formula(f.negate(f.variable("x")), f);
        assert!(!solver.sat(f));
    }
}

#[test]
fn test_pigeon_hole() {
    let f = &FormulaFactory::new();
    for i in 1..=6 {
        for mut solver in solvers::<()>() {
            let formula = generate_pigeon_hole(i, f);
            solver.add_formula(formula, f);
            assert!(!solver.sat(f));
            assert!(solver.sat_call().model(formula.variables(f).iter().copied().collect::<Box<[_]>>().as_ref(), f).is_none());
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_pigeon_hole_large() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula(generate_pigeon_hole(7, f), f);
        assert!(!solver.sat(f));
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_different_clause_minimizations() {
    let f = &FormulaFactory::new();
    let solvers = solver_cross_product::<()>(&[SatSolverConfigParam::ClauseMinimization, SatSolverConfigParam::UseAtMostClauses]);
    for mut solver in solvers {
        solver.add_formula(generate_pigeon_hole(7, f), f);
        assert!(solver.sat(f));
    }
}

#[test]
fn test_timeout_sat_handler_small() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula("A => B".to_formula(f), f);
        let mut handler = TimeoutHandler::new(Timer::SingleTimeout(Duration::from_millis(1000)));
        let result = solver.sat_call().handler(&mut handler).sat(f);
        assert!(result.is_success());
        assert!(result.result().unwrap());
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_timeout_sat_handler_large() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula(generate_pigeon_hole(10, f), f);
        let mut handler = TimeoutHandler::new(Timer::SingleTimeout(Duration::from_millis(1000)));
        let result = solver.sat_call().handler(&mut handler).sat(f);
        assert!(!result.is_success());
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn test_dimacs_files() {
    let f = &FormulaFactory::new();
    let expected_results: HashMap<String, bool> = BufReader::new(File::open("resources/sat/results.txt").unwrap())
        .lines()
        .map(|l| {
            let tokens: Vec<String> = l.unwrap().split(';').map(std::string::ToString::to_string).collect();
            (tokens[0].to_string(), tokens[1].parse().unwrap())
        })
        .collect();
    for file in fs::read_dir("resources/sat").unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name().to_str().unwrap().to_string();
        if file_name.ends_with(".cnf") {
            let cnf = read_cnf(file.path().to_str().unwrap(), f).unwrap();
            for mut solver in solvers::<()>() {
                cnf.iter().for_each(|&clause| solver.add_formula(clause, f));
                assert_eq!(solver.sat(f), *expected_results.get(&file_name).unwrap());
            }
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_timeout_model_enumeration_handler_with_unsat_instance() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formula = generate_pigeon_hole(10, f);
        solver.add_formula(formula, f);
        let handler = TimeoutHandler::new(Timer::SingleTimeout(Duration::from_millis(1000)));
        todo!("Model enumeration with handler")
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_timeout_model_enumeration_handler_with_sat_instance1() {
    todo!()
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_timeout_model_enumeration_handler_with_sat_instance2() {
    todo!()
}

#[test]
fn test_model_enumeration() {
    let f = &FormulaFactory::new();
    let vars: Box<[Variable]> = (0..20).map(|i| f.var(format!("x{i}"))).collect();
    let first_five = &vars[..5];
    for mut solver in solvers::<()>() {
        solver.add_formula(f.cc(GE, 1, vars.clone()), f);
        let models =
            enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::new(first_five).additional_variables(vars.clone()), f);
        assert_eq!(models.len(), 32);
        for model in models {
            for var in &*vars {
                assert!(model.pos().contains(var) || model.neg().contains(var));
            }
        }
    }
}

#[test]
fn test_model_enumeration_with_handler01() {
    todo!()
}

#[test]
fn test_model_enumeration_with_handler02() {
    todo!()
}

#[test]
fn test_empty_enumeration() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        solver.add_formula(f.falsum(), f);
        assert!(solver.enumerate_all_models(&[], f).is_empty());
    }
}

#[test] //TODO: Use handler for this
fn test_number_of_models_handler() {
    let f = &FormulaFactory::new();
    let vars: Box<[Variable]> = (0..100).map(|i| f.var(format!("x{i}"))).collect();
    for config in solver_configs() {
        let mut solver1 = SatSolver::<()>::from_config(config.clone());
        solver1.add_formula(f.exo(vars.clone()), f);
        let models = enumerate_models_with_config(&mut solver1, &ModelEnumerationConfig::new(vars.clone()).max_models(100), f);
        assert_eq!(models.len(), 100);
        assert!(models.iter().all(|m| m.pos().len() == 1));

        let mut solver2 = SatSolver::<()>::from_config(config.clone());
        solver2.add_formula(f.exo(vars.clone()), f);
        let models = enumerate_models_with_config(&mut solver2, &ModelEnumerationConfig::new(vars.clone()).max_models(200), f);
        assert_eq!(models.len(), 100);
        assert!(models.iter().all(|m| m.pos().len() == 1));

        let mut solver3 = SatSolver::<()>::from_config(config.clone());
        solver3.add_formula(f.exo(vars.clone()), f);
        let models = enumerate_models_with_config(&mut solver3, &ModelEnumerationConfig::new(vars.clone()).max_models(50), f);
        assert_eq!(models.len(), 50);
        assert!(models.iter().all(|m| m.pos().len() == 1));

        let mut solver4 = SatSolver::<()>::from_config(config);
        solver4.add_formula(f.exo(vars.clone()), f);
        let models = enumerate_models_with_config(&mut solver4, &ModelEnumerationConfig::new(vars.clone()).max_models(1), f);
        assert_eq!(models.len(), 1);
    }
}

#[test]
fn test_known_variables() {
    let f = &FormulaFactory::new();
    let mut solver_without_at_most = SatSolver::<()>::from_config(SatSolverConfig::default().with_use_at_most_clauses(false));
    let mut solver_with_at_most = SatSolver::<()>::from_config(SatSolverConfig::default().with_use_at_most_clauses(true));
    let phi = "x1 & x2 & x3 & (x4 | ~x5)".to_formula(f);
    let mut vars = phi.variables(f).iter().copied().collect::<BTreeSet<_>>();
    solver_without_at_most.add_formula(phi, f);
    solver_with_at_most.add_formula(phi, f);
    assert_eq!(&solver_without_at_most.underlying_solver().known_variables(), &vars);
    assert_eq!(&solver_with_at_most.underlying_solver().known_variables(), &vars);

    let state = solver_without_at_most.save_state();
    let state_card = solver_with_at_most.save_state();
    solver_without_at_most.add_formula(f.variable("x6"), f);
    solver_with_at_most.add_formula(f.variable("x6"), f);
    vars.insert(f.var("x6"));
    assert_eq!(&solver_without_at_most.underlying_solver().known_variables(), &vars);
    assert_eq!(&solver_with_at_most.underlying_solver().known_variables(), &vars);

    solver_without_at_most.load_state(&state);
    solver_with_at_most.load_state(&state_card);
    vars.remove(&f.var("x6"));
    assert_eq!(&solver_without_at_most.underlying_solver().known_variables(), &vars);
    assert_eq!(&solver_with_at_most.underlying_solver().known_variables(), &vars);
}

#[test]
fn test_up_zero_literals_unsat() {
    let f = &FormulaFactory::new();
    let formula = "a & (a => b) & (b => c) & (c => ~a)".to_formula(f);
    for mut solver in solvers::<()>() {
        solver.add_formula(formula, f);
        solver.sat(f);
        assert!(solver.up_zero_literals(f).is_empty());
    }
}

#[test]
fn test_up_zero_literals() {
    let f = &FormulaFactory::new();
    let expected_subsets = [
        (f.verum(), BTreeSet::new()),
        ("a".to_formula(f), lits("a", f)),
        ("a | b".to_formula(f), BTreeSet::new()),
        ("a & b".to_formula(f), lits("a b", f)),
        ("a & ~b".to_formula(f), lits("a ~b", f)),
        ("(a | c) & ~b".to_formula(f), lits("~b", f)),
        ("(b | c) & ~b & (~c | d)".to_formula(f), lits("~b c d", f)),
    ];
    for config in solver_configs() {
        for (formula, expected) in &expected_subsets {
            let mut solver = SatSolver::<()>::from_config(config.clone());
            solver.add_formula(*formula, f);
            assert!(solver.sat(f));
            assert_eq!(&solver.up_zero_literals(f), expected);
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn test_up_zero_literals_dimacs_files() {
    let f = &FormulaFactory::new();
    for file in fs::read_dir("resources/sat").unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name().to_str().unwrap().to_string();
        if file_name.ends_with(".cnf") {
            let cnf = read_cnf(file.path().to_str().unwrap(), f).unwrap();
            for mut solver in solvers::<()>() {
                cnf.iter().for_each(|&clause| solver.add_formula(clause, f));
                if solver.sat(f) {
                    let up_zero_literals = solver.up_zero_literals(f);
                    let negations = up_zero_literals.iter().map(|lit| EncodedFormula::from(lit.negate()));
                    solver.add_formula(f.or(negations), f);
                    assert!(!solver.sat(f));
                }
            }
        }
    }
}

#[test]
fn test_formula_on_solver1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formulas = vec!["A | B | C".to_formula(f), "~A | ~B | ~C".to_formula(f), "A | ~B".to_formula(f), "A".to_formula(f)];
        solver.add_formulas(&formulas, f);
        compare_formulas(&formulas, &solver.formula_on_solver(f), f);
    }
}

#[test]
fn test_formula_on_solver2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formulas = vec!["A | B | C".to_formula(f), "~A | ~B | ~C".to_formula(f), "A | ~B".to_formula(f), "A".to_formula(f)];
        solver.add_formulas(&formulas, f);
        compare_formulas(&formulas, &solver.formula_on_solver(f), f);
        let formula = "C + D + E <= 2".to_formula(f);
        solver.add_formula(formula, f);
        compare_formulas(&formulas, &solver.formula_on_solver(f), f);
    }
}

#[test]
fn test_formula_on_solver_with_contradiction1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formulas = vec!["A".to_formula(f), "B".to_formula(f), "C & (~A | ~B)".to_formula(f)];
        solver.add_formulas(&formulas, f);
        let formula = solver.formula_on_solver(f);
        assert!(formula.contains(&f.variable("A")));
        assert!(formula.contains(&f.variable("B")));
        assert!(formula.contains(&f.variable("C")));
        assert!(formula.contains(&f.falsum()));
        assert_eq!(formula.len(), 4);
    }
}

#[test]
fn test_formula_on_solver_with_contradiction2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formulas = vec!["A <=> B".to_formula(f), "B <=> ~A".to_formula(f)];
        solver.add_formulas(&formulas, f);
        let formula = solver.formula_on_solver(f);
        assert!(formula.contains(&"A | ~B".to_formula(f)));
        assert!(formula.contains(&"~A | B".to_formula(f)));
        assert!(formula.contains(&"~A | ~B".to_formula(f)));
        assert!(formula.contains(&"B | A".to_formula(f)));
        assert_eq!(formula.len(), 4);
        solver.sat(f);
        let formula = solver.formula_on_solver(f);
        assert!(formula.contains(&"A | ~B".to_formula(f)));
        assert!(formula.contains(&"~A | B".to_formula(f)));
        assert!(formula.contains(&"~B | ~A".to_formula(f)));
        assert!(formula.contains(&"B | A".to_formula(f)));
        assert!(formula.contains(&f.literal("A", !solver.config().initial_phase())));
        assert!(formula.contains(&f.literal("B", !solver.config().initial_phase())));
        assert!(formula.contains(&f.falsum()));
        assert_eq!(formula.len(), 7);
    }
}

#[test]
fn test_selection_order_simple01() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let formula = "~(x <=> y)".to_formula(f);
        solver.add_formula(formula, f);
        let selection_order = lits_list("x y", f);
        let model = solver.sat_call().selection_order(Some(selection_order.clone())).model(&[f.var("x"), f.var("y")], f).unwrap();
        assert!(model.literals().contains(&f.lit("x", true)));
        assert!(model.literals().contains(&f.lit("y", false)));
        test_local_minimum(&mut solver, &model, &selection_order, f);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order, f);

        let selection_order = lits_list("y x", f);
        let model = solver.sat_call().selection_order(Some(selection_order.clone())).model(&[f.var("x"), f.var("y")], f).unwrap();
        assert!(model.literals().contains(&f.lit("y", true)));
        assert!(model.literals().contains(&f.lit("x", false)));
        test_local_minimum(&mut solver, &model, &selection_order, f);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order, f);

        let selection_order = lits_list("~x", f);
        let model = solver.sat_call().selection_order(Some(selection_order.clone())).model(&[f.var("x"), f.var("y")], f).unwrap();
        assert!(model.literals().contains(&f.lit("y", true)));
        assert!(model.literals().contains(&f.lit("x", false)));
        test_local_minimum(&mut solver, &model, &selection_order, f);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order, f);

        let selection_order = lits_list("~y ~x", f);
        let model = solver.sat_call().selection_order(Some(selection_order.clone())).model(&[f.var("x"), f.var("y")], f).unwrap();
        assert!(model.literals().contains(&f.lit("x", true)));
        assert!(model.literals().contains(&f.lit("y", false)));
        test_local_minimum(&mut solver, &model, &selection_order, f);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order, f);
    }
}

#[test]
fn test_selection_order_simple02() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let vars: Box<[Variable]> = (0..5).map(|i| f.var(format!("x{i}"))).collect();
        let selection_order: Vec<Literal> = vars.iter().map(Variable::pos_lit).collect();
        let cc = f.cc(EQ, 2, vars.clone());
        solver.add_formula(cc, f);

        for _ in 0..10 {
            assert!(solver.sat_call().selection_order(Some(selection_order.clone())).sat(f).result().unwrap());
            let model = solver.sat_call().selection_order(Some(selection_order.clone())).model(&vars, f).unwrap();
            test_local_minimum(&mut solver, &model, &selection_order, f);
            test_highest_lexicographical_assignment(&mut solver, &model, &selection_order, f);
            solver.add_formula(Assignment::from(model).blocking_clause(f, Some(&vars)), f);
        }
    }
}

#[test]
fn test_selection_order_simple03() {
    let f = &FormulaFactory::new();
    for mut solver in solvers::<()>() {
        let vars: Box<[Variable]> = (0..5).map(|i| f.var(format!("x{i}"))).collect();
        let cc = f.cc(EQ, 2, vars.clone());
        solver.add_formula(cc, f);
        let selection_order2 = lits_list("x4 ~x0 x1 x2 x3", f);
        for _ in 0..10 {
            assert!(solver.sat_call().selection_order(Some(selection_order2.clone())).sat(f).result().unwrap());
            let model = solver.sat_call().selection_order(Some(selection_order2.clone())).model(&vars, f).unwrap();
            test_local_minimum(&mut solver, &model, &selection_order2, f);
            test_highest_lexicographical_assignment(&mut solver, &model, &selection_order2, f);
            solver.add_formula(Assignment::from(model).blocking_clause(f, None), f);
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn test_dimacs_files_with_selection_order() {
    let f = &FormulaFactory::new();
    let expected_results: HashMap<String, bool> = BufReader::new(File::open("resources/sat/results.txt").unwrap())
        .lines()
        .map(|l| {
            let tokens: Vec<String> = l.unwrap().split(';').map(std::string::ToString::to_string).collect();
            (tokens[0].to_string(), tokens[1].parse().unwrap())
        })
        .collect();
    for file in fs::read_dir("resources/sat").unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name().to_str().unwrap().to_string();
        if file_name.ends_with(".cnf") {
            let cnf = read_cnf(file.path().to_str().unwrap(), f).unwrap();
            for mut solver in solvers::<()>() {
                cnf.iter().for_each(|&clause| solver.add_formula(clause, f));
                let selection_order = (*f.and(&cnf).variables(f)).iter().take(10).map(Variable::pos_lit).collect::<Vec<Literal>>();
                let expected = *expected_results.get(&file_name).unwrap();
                let res = solver.sat_call().selection_order(Some(selection_order.clone())).sat(f).result().unwrap();
                assert_eq!(res, expected);
                if expected {
                    let vs = solver.underlying_solver().known_variables().into_iter().collect::<Box<[_]>>();
                    let model = solver.sat_call().model(&vs, f).unwrap();
                    test_local_minimum(&mut solver, &model, &selection_order.clone(), f);
                    test_highest_lexicographical_assignment(&mut solver, &model, &selection_order, f);
                }
            }
        }
    }
}

#[test]
fn test_model_enumeration_with_additional_variables() {
    let f = &FormulaFactory::new();
    let mut solver = SatSolver::<()>::new();
    solver.add_formula("A | B | C | D | E".to_formula(f), f);
    let models = enumerate_models_with_config(
        &mut solver,
        &ModelEnumerationConfig::new(vars_list("a b", f)).additional_variables(vars_list("b c", f)),
        f,
    );
    for model in models {
        let pos_count_b = model.pos().iter().filter(|&&v| v.name(f) == "B").count();
        let neg_count_b = model.neg().iter().filter(|&&v| v.name(f) == "B").count();
        assert!(pos_count_b < 2);
        assert!(neg_count_b < 2);
    }
}

fn test_local_minimum<B: Clone>(solver: &mut SatSolver<B>, model: &Model, selection_order: &[Literal], f: &FormulaFactory) {
    let model_lits: BTreeSet<Literal> = model.literals().iter().copied().collect();
    for &lit in selection_order {
        if !model_lits.contains(&lit) {
            let mut model_with_flip = model_lits.clone();
            model_with_flip.remove(&lit.negate());
            model_with_flip.insert(lit);
            assert!(!solver.sat_call().add_formulas(model_with_flip).sat(f).result().unwrap());
        }
    }
}

fn test_highest_lexicographical_assignment<B: Clone>(
    solver: &mut SatSolver<B>,
    model: &Model,
    selection_order: &[Literal],
    f: &FormulaFactory,
) {
    let model_lits: HashSet<Literal> = model.literals().iter().copied().collect();
    let mut order_sublist = vec![];
    for &lit in selection_order {
        if model_lits.contains(&lit) {
            order_sublist.push(lit);
        } else {
            let mut order_sublist_with_flip: BTreeSet<Literal> = order_sublist.iter().copied().collect();
            order_sublist_with_flip.remove(&lit.negate());
            order_sublist_with_flip.insert(lit);
            assert!(!solver.sat_call().add_formulas(order_sublist_with_flip).sat(f).result().unwrap());
            order_sublist.push(lit.negate());
        }
    }
}

fn compare_formulas(original: &[EncodedFormula], from_solver: &BTreeSet<EncodedFormula>, f: &FormulaFactory) {
    let vars = original.iter().flat_map(|formula| (*formula.variables(f)).clone()).dedup().collect::<Vec<_>>();
    let mut solver1 = SatSolver::<()>::new();
    solver1.add_formulas(original, f);
    let models1 = solver1.enumerate_all_models(&vars, f).into_iter().collect::<HashSet<_>>();
    let mut solver2 = SatSolver::<()>::new();
    solver2.add_formulas(from_solver, f);
    let models2 = solver2.enumerate_all_models(&vars, f).into_iter().collect::<HashSet<_>>();
    for model in &models1 {
        assert!(models2.contains(model));
    }
    for model in &models2 {
        assert!(models1.contains(model));
    }
}

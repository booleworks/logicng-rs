use crate::datastructures::Model;
use crate::formulas::CType::{GT, LT};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
use crate::solver::functions::OptimizationFunction;
use crate::solver::minisat::sat::Tristate::True;
use crate::solver::minisat::{MiniSat, MiniSatConfig, SolverCnfMethod};
use crate::util::formula_randomizer::{FormulaRandomizer, FormulaRandomizerConfig};
use crate::util::test_formula_corner_cases::formula_corner_cases;
use fastrand::Rng;
use itertools::Itertools;
use std::cmp::min;
use std::collections::{BTreeSet, HashSet};
use std::fs::File;
use std::hash::Hash;
use std::io::{BufRead, BufReader};

fn solvers() -> [MiniSat; 5] {
    [
        MiniSat::from_config(MiniSatConfig::default().initial_phase(true)),
        MiniSat::from_config(MiniSatConfig::default().initial_phase(false)),
        MiniSat::from_config(MiniSatConfig::default().initial_phase(true).cnf_method(SolverCnfMethod::PgOnSolver)),
        MiniSat::from_config(MiniSatConfig::default().initial_phase(true).cnf_method(SolverCnfMethod::PgOnSolver).proof_generation(true)),
        MiniSat::from_config(MiniSatConfig::default().incremental(false)),
    ]
}

#[test]
fn test_unsat_formula() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let formula = f.parse("a & b & (a => ~b)").unwrap();
        let lits = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let minimum_model = optimize(&[formula], &lits, &[], false, solver, f);
        assert!(minimum_model.is_none());
        let maximum_model = optimize(&[formula], &lits, &[], true, solver, f);
        assert!(maximum_model.is_none());
    }
}

#[test]
fn test_single_model() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let formula = f.parse("~a & ~b & ~c").unwrap();
        let lits = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let minimum_model = optimize(&[formula], &lits, &[], false, solver, f);
        test_minimum_model(formula, minimum_model, &lits, f);
        let maximum_model = optimize(&[formula], &lits, &[], true, solver, f);
        test_maximum_model(formula, maximum_model, &lits, f);
    }
}

#[test]
fn test_exo_model() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let vars: Box<[Variable]> = Box::new([f.var("a"), f.var("b"), f.var("c")]);
        let formula = f.exo(vars);
        let lits = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let minimum_model = optimize(&[formula], &lits, &[], false, solver, f);
        test_minimum_model(formula, minimum_model, &lits, f);
        let maximum_model = optimize(&[formula], &lits, &[], true, solver, f);
        test_maximum_model(formula, maximum_model, &lits, f);
    }
}

#[test]
fn test_corner_cases() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let (corner_cases, vars) = formula_corner_cases(f);
        let lits = vars.iter().map(|&v| v.pos_lit()).collect::<Vec<Literal>>();
        for formula in corner_cases {
            let minimum_model = optimize(&[formula], &lits, &[], false, solver, f);
            test_minimum_model(formula, minimum_model, &lits, f);
            let maximum_model = optimize(&[formula], &lits, &[], true, solver, f);
            test_maximum_model(formula, maximum_model, &lits, f);
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_random_small() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let randomizer_config = FormulaRandomizerConfig::default_with_num_vars(6).weight_pbc(2.0).seed(42);
        let mut randomizer = FormulaRandomizer::new(randomizer_config);
        let random = &mut Rng::with_seed(42);
        for _ in 0..1000 {
            let formula = randomizer.formula(f, 2);
            let variables: Vec<Variable> = formula.variables(f).iter().copied().collect();
            let var_subset = random_subset(random, &variables, min(variables.len(), 5));
            let target_literals = random_target_literals(random, &var_subset);
            let additional_variables = random_subset(random, &variables, min(variables.len(), 3)).into_iter().collect::<Vec<Variable>>();

            let minimum_model = optimize(&[formula], &target_literals, &additional_variables, false, solver, f);
            test_minimum_model(formula, minimum_model, &target_literals, f);
            let maximum_model = optimize(&[formula], &target_literals, &additional_variables, true, solver, f);
            test_maximum_model(formula, maximum_model, &target_literals, f);
        }
    }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn test_incrementality_minimize_and_maximize() {
    for solver in &mut solvers().iter_mut().filter(|s| s.config.incremental) {
        let f = &FormulaFactory::new();
        let formula = f.parse("(a|b|c|d|e) & (p|q) & (x|y|z)").unwrap();
        let mut literals: Vec<Literal> = formula.variables(f).iter().map(Variable::pos_lit).collect();

        solver.add(formula, f);

        let minimum_model = solver.optimize(f, &OptimizationFunction::minimize(literals.clone())).unwrap();
        let maximum_model = solver.optimize(f, &OptimizationFunction::maximize(literals.clone())).unwrap();
        assert_eq!(minimum_model.pos().len(), 3);
        assert_eq!(maximum_model.pos().len(), 10);

        let formula = f.parse("~p").unwrap();
        literals.push(f.lit("p", true));
        solver.add(formula, f);
        let minimum_model = solver.optimize(f, &OptimizationFunction::minimize(literals.clone())).unwrap();
        let maximum_model = solver.optimize(f, &OptimizationFunction::maximize(literals.clone())).unwrap();
        assert_eq!(minimum_model.pos().len(), 3);
        assert!(minimum_model.pos().contains(&f.var("q")));
        assert_eq!(maximum_model.pos().len(), 9);
        assert!(maximum_model.pos().contains(&f.var("q")));

        let formula = f.parse("(x => n) & (y => m) & (a => ~b & ~c)").unwrap();
        formula.variables(f).iter().map(Variable::pos_lit).for_each(|l| literals.push(l));
        solver.add(formula, f);
        let minimum_model = solver.optimize(f, &OptimizationFunction::minimize(literals.clone())).unwrap();
        let maximum_model = solver.optimize(f, &OptimizationFunction::maximize(literals.clone())).unwrap();
        assert_eq!(minimum_model.pos().len(), 3);
        assert!(minimum_model.pos().contains(&f.var("q")));
        assert!(minimum_model.pos().contains(&f.var("z")));
        assert_eq!(maximum_model.pos().len(), 10);
        assert!(maximum_model.pos().contains(&f.var("q")));
        assert!(maximum_model.pos().contains(&f.var("z")));
        assert!(!maximum_model.pos().contains(&f.var("a")));

        let formula = f.parse("(z => v & w) & (m => v) & (b => ~c & ~d & ~e)").unwrap();
        formula.variables(f).iter().map(Variable::pos_lit).for_each(|l| literals.push(l));
        solver.add(formula, f);
        let minimum_model = solver.optimize(f, &OptimizationFunction::minimize(literals.clone())).unwrap();
        let maximum_model = solver.optimize(f, &OptimizationFunction::maximize(literals.clone())).unwrap();
        assert_eq!(minimum_model.pos().len(), 4);
        assert!(minimum_model.pos().contains(&f.var("q")));
        assert!(minimum_model.pos().contains(&f.var("x")));
        assert!(minimum_model.pos().contains(&f.var("n")));
        assert_eq!(maximum_model.pos().len(), 11);
        assert!(maximum_model.pos().contains(&f.var("q")));
        assert!(maximum_model.pos().contains(&f.var("x")));
        assert!(maximum_model.pos().contains(&f.var("n")));
        assert!(maximum_model.pos().contains(&f.var("v")));
        assert!(maximum_model.pos().contains(&f.var("w")));
        assert!(!maximum_model.pos().contains(&f.var("b")));

        let formula = f.parse("~q").unwrap();
        formula.variables(f).iter().map(Variable::pos_lit).for_each(|l| literals.push(l));
        solver.add(formula, f);
        let minimum_model = solver.optimize(f, &OptimizationFunction::minimize(literals.clone()));
        let maximum_model = solver.optimize(f, &OptimizationFunction::maximize(literals.clone()));
        assert!(minimum_model.is_none());
        assert!(maximum_model.is_none());
    }
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_additional_variables() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let a = f.var("a").pos_lit();
        let na = a.negate();
        let b = f.var("b").pos_lit();
        let nb = b.negate();
        let c = f.var("c").pos_lit();
        let x = f.var("x").pos_lit();
        let nx = x.negate();
        let y = f.var("y").pos_lit();

        let formula = f.parse("(a|b) & (~a => c) & (x|y)").unwrap();

        let literals_a_nb_x = vec![a, nb, x];
        let minimum_model = optimize(&[formula], &literals_a_nb_x, &[], false, solver, f).unwrap();
        assert_same_elements(&minimum_model, &[na, b, nx]);
        let minimum_model_with_y = optimize(&[formula], &literals_a_nb_x, &[y.variable()], false, solver, f).unwrap();
        assert_same_elements(&minimum_model_with_y, &[na, b, nx, y]);
        let minimum_model_with_cy = optimize(&[formula], &literals_a_nb_x, &[c.variable(), y.variable()], false, solver, f).unwrap();
        assert_same_elements(&minimum_model_with_cy, &[na, b, c, nx, y]);

        let literals_na_nx = vec![na, nx];
        let maximum_model = optimize(&[formula], &literals_na_nx, &[], true, solver, f).unwrap();
        assert_same_elements(&maximum_model, &[na, nx]);
        let maximum_model_with_c = optimize(&[formula], &literals_na_nx, &[c.variable()], true, solver, f).unwrap();
        assert_same_elements(&maximum_model_with_c, &[na, c, nx]);
        let maximum_model_with_acy =
            optimize(&[formula], &literals_na_nx, &[a.variable(), c.variable(), y.variable()], true, solver, f).unwrap();
        assert_same_elements(&maximum_model_with_acy, &[na, c, nx, y]);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_formula_minimize() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let file = File::open("resources/formulas/large_formula.txt").unwrap();
        let reader = BufReader::new(file);
        let formula = f.parse(&reader.lines().map(Result::unwrap).collect::<Vec<String>>()[0]).unwrap();
        let literals = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let minimum_model = optimize(&[formula], &literals, &[], false, solver, f);
        test_minimum_model(formula, minimum_model, &literals, f);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_large_formula_maximize() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let file = File::open("resources/formulas/large_formula.txt").unwrap();
        let reader = BufReader::new(file);
        let formula = f.parse(&reader.lines().map(Result::unwrap).collect::<Vec<String>>()[0]).unwrap();
        let literals = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let maximum_model = optimize(&[formula], &literals, &[], true, solver, f);
        test_maximum_model(formula, maximum_model, &literals, f);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_larger_formula_minimize() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let file = File::open("resources/formulas/small_formulas.txt").unwrap();
        let reader = BufReader::new(file);
        let ops = reader.lines().filter(|s| !s.as_ref().unwrap().trim().is_empty()).map(|s| f.parse(&s.unwrap()).unwrap());
        let formula = f.and(ops);
        let literals = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let minimum_model = optimize(&[formula], &literals, &[], false, solver, f);
        test_minimum_model(formula, minimum_model, &literals, f);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_larger_formula_maximize() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let file = File::open("resources/formulas/small_formulas.txt").unwrap();
        let reader = BufReader::new(file);
        let ops = reader.lines().filter(|s| !s.as_ref().unwrap().trim().is_empty()).map(|s| f.parse(&s.unwrap()).unwrap());
        let formula = f.and(ops);
        let literals = formula.variables(f).iter().map(Variable::pos_lit).collect::<Vec<Literal>>();
        let maximum_model = optimize(&[formula], &literals, &[], true, solver, f);
        test_maximum_model(formula, maximum_model, &literals, f);
    }
}

fn optimize(
    formulas: &[EncodedFormula],
    literals: &[Literal],
    additional_variables: &[Variable],
    maximize: bool,
    solver: &mut MiniSat,
    f: &FormulaFactory,
) -> Option<Model> {
    solver.reset();
    solver.add_all(formulas, f);
    if maximize {
        solver.optimize(f, &OptimizationFunction::maximize(literals.into()).additional_variables(additional_variables.iter()))
    } else {
        solver.optimize(f, &OptimizationFunction::minimize(literals.into()).additional_variables(additional_variables.iter()))
    }
}

fn test_minimum_model(formula: EncodedFormula, optimum_model: Option<Model>, literals: &[Literal], f: &FormulaFactory) {
    test_optimum_model(formula, optimum_model, literals, false, f);
}

fn test_maximum_model(formula: EncodedFormula, optimum_model: Option<Model>, literals: &[Literal], f: &FormulaFactory) {
    test_optimum_model(formula, optimum_model, literals, true, f);
}

fn test_optimum_model(formula: EncodedFormula, optimum_model: Option<Model>, literals: &[Literal], maximize: bool, f: &FormulaFactory) {
    let mut solver = MiniSat::new();
    solver.add(formula, f);
    if solver.sat() == True {
        let with_formula = solver.save_state();
        solver.add(f.and(optimum_model.as_ref().unwrap().literals().iter().map(|l| EncodedFormula::from(*l))), f);
        assert_eq!(solver.sat(), True);
        solver.load_state(&with_formula);
        let num_satisfied_literals = satisfied_literals(&optimum_model.unwrap(), literals).len() as u64;
        let sel_vars = literals
            .iter()
            .enumerate()
            .map(|(i, &lit)| {
                let sel_var = f.variable(format!("SEL_VAR_{i}"));
                solver.add(f.equivalence(sel_var, lit.into()), f);
                sel_var.as_variable().unwrap()
            })
            .collect::<Box<[_]>>();
        if maximize || num_satisfied_literals > 0 {
            solver.add(f.cc(if maximize { GT } else { LT }, num_satisfied_literals, sel_vars), f);
        }
    } else {
        assert!(optimum_model.is_none());
    }
}

fn satisfied_literals(model: &Model, literals: &[Literal]) -> BTreeSet<Literal> {
    let model_lits = model.literals();
    let set: HashSet<&Literal> = model_lits.iter().collect();
    literals.iter().filter(|&l| set.contains(l)).copied().collect()
}

fn random_subset<T: Clone + Eq + Hash>(random: &mut Rng, elements: &[T], subset_size: usize) -> HashSet<T> {
    assert!(subset_size <= elements.len());
    let mut subset = HashSet::new();
    while subset.len() < subset_size {
        subset.insert(elements[random.usize(0..elements.len())].clone());
    }
    subset
}

fn random_target_literals(random: &mut Rng, variables: &HashSet<Variable>) -> Vec<Literal> {
    variables.iter().map(|&v| Literal::new(v, random.bool())).collect()
}

fn assert_same_elements(model: &Model, literals: &[Literal]) {
    assert_eq!(
        model.literals().iter().copied().sorted().collect::<Vec<Literal>>(),
        literals.iter().copied().sorted().collect::<Vec<Literal>>()
    );
}

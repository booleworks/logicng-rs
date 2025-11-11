use std::collections::HashSet;

use itertools::Itertools;

use crate::datastructures::Assignment;
use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
use crate::solver::functions::{ModelEnumerationConfig, enumerate_models_for_formula_with_config};
use crate::solver::minisat::MiniSat;
use crate::solver::minisat_config::MiniSatConfig;
use crate::solver::minisat_config::SolverCnfMethod::{FullPgOnSolver, PgOnSolver};

fn solvers() -> [MiniSat; 5] {
    [
        MiniSat::from_config(MiniSatConfig::default().incremental(true)),
        MiniSat::from_config(MiniSatConfig::default().incremental(false)),
        MiniSat::from_config(MiniSatConfig::default().cnf_method(PgOnSolver)),
        MiniSat::from_config(MiniSatConfig::default().cnf_method(PgOnSolver).auxiliary_variables_in_models(false)),
        MiniSat::from_config(MiniSatConfig::default().cnf_method(FullPgOnSolver).auxiliary_variables_in_models(false)),
    ]
}

#[test]
fn test_formula_on_solver() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let mut formulas =
            vec![f.parse("A | B | C").unwrap(), f.parse("~A | ~B | ~C").unwrap(), f.parse("A | ~B").unwrap(), f.parse("A").unwrap()];
        solver.add_all(&formulas, f);
        compare_formulas(&formulas, &solver.formula_on_solver(f), f);

        formulas.push(f.parse("~A | C").unwrap());
        solver.reset();
        solver.add_all(&formulas, f);
        compare_formulas(&formulas, &solver.formula_on_solver(f), f);

        let formula = f.parse("C + D + E <= 2").unwrap();
        formulas.push(formula);
        solver.add(formula, f);
        compare_formulas(&formulas, &solver.formula_on_solver(f), f);
    }
}

#[test]
fn test_formula_on_solver_with_contradiction() {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        solver.add(f.parse("A").unwrap(), f);
        solver.add(f.parse("B").unwrap(), f);
        solver.add(f.parse("C & (~A | ~B)").unwrap(), f);
        assert_eq!(solver.formula_on_solver(f).as_ref(), &[f.variable("A"), f.variable("B"), f.variable("C"), f.falsum()]);

        solver.reset();
        solver.add(f.parse("A <=> B").unwrap(), f);
        solver.add(f.parse("B <=> ~A").unwrap(), f);
        let on_solver = solver.formula_on_solver(f).iter().copied().collect::<HashSet<EncodedFormula>>();
        let expected = [f.parse("A | B").unwrap(), f.parse("~A | B").unwrap(), f.parse("A | ~B").unwrap(), f.parse("~A | ~B").unwrap()]
            .iter()
            .copied()
            .collect::<HashSet<EncodedFormula>>();
        assert_eq!(on_solver.len(), expected.len());
        for fm in &expected {
            assert!(on_solver.contains(fm));
        }

        solver.sat();
        let on_solver = solver.formula_on_solver(f).iter().copied().collect::<HashSet<EncodedFormula>>();
        let expected = [
            f.parse("A | B").unwrap(),
            f.parse("~A | B").unwrap(),
            f.parse("A | ~B").unwrap(),
            f.parse("~A | ~B").unwrap(),
            f.parse("A").unwrap(),
            f.parse("B").unwrap(),
            f.falsum(),
        ]
        .iter()
        .copied()
        .collect::<HashSet<EncodedFormula>>();
        assert_eq!(on_solver.len(), expected.len());
        for fm in &expected {
            assert!(on_solver.contains(fm));
        }
    }
}

fn compare_formulas(original: &[EncodedFormula], from_solver: &[EncodedFormula], f: &FormulaFactory) {
    let vars: Box<[Variable]> = original.iter().flat_map(|formula| (*formula.variables(f)).clone()).unique().collect();
    let models1 = enumerate_models_for_formula_with_config(f.and(original), f, &ModelEnumerationConfig::default().variables(vars.clone()))
        .iter()
        .map(Assignment::from)
        .collect::<HashSet<Assignment>>();
    let models2 = enumerate_models_for_formula_with_config(f.and(from_solver), f, &ModelEnumerationConfig::default().variables(vars))
        .iter()
        .map(Assignment::from)
        .collect::<HashSet<Assignment>>();
    assert_eq!(models1.len(), models2.len());
    for m in &models1 {
        assert!(models2.contains(m));
    }
}

use std::collections::HashSet;

use itertools::Itertools;

use crate::datastructures::Assignment;
use crate::errors::LngResult;
use crate::formulas::{EncodedFormula, FormulaFactory, Variable};
use crate::solver::lng_core_solver::CnfMethod::{FullPgOnSolver, PgOnSolver};
use crate::solver::lng_core_solver::functions::{
    ModelEnumerationConfig, enumerate_models_for_formula_with_config,
};
use crate::solver::lng_core_solver::{SatSolver, SatSolverConfig};

fn solvers() -> [SatSolver; 5] {
    [
        SatSolver::from_config(SatSolverConfig::default().incremental(true)),
        SatSolver::from_config(SatSolverConfig::default().incremental(false)),
        SatSolver::from_config(SatSolverConfig::default().cnf_method(PgOnSolver)),
        SatSolver::from_config(
            SatSolverConfig::default()
                .cnf_method(PgOnSolver)
                .auxiliary_variables_in_models(false),
        ),
        SatSolver::from_config(
            SatSolverConfig::default()
                .cnf_method(FullPgOnSolver)
                .auxiliary_variables_in_models(false),
        ),
    ]
}

#[test]
fn test_formula_on_solver() -> LngResult<()> {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        let mut formulas = vec![
            f.parse("A | B | C").unwrap(),
            f.parse("~A | ~B | ~C").unwrap(),
            f.parse("A | ~B").unwrap(),
            f.parse("A").unwrap(),
        ];
        solver.add_all(&formulas, f)?;
        compare_formulas(&formulas, &solver.formula_on_solver(f)?, f)?;

        formulas.push(f.parse("~A | C").unwrap());
        solver.reset();
        solver.add_all(&formulas, f)?;
        compare_formulas(&formulas, &solver.formula_on_solver(f)?, f)?;

        let formula = f.parse("C + D + E <= 2").unwrap();
        formulas.push(formula);
        solver.add(formula, f)?;
        compare_formulas(&formulas, &solver.formula_on_solver(f)?, f)?;
    }

    Ok(())
}

#[test]
fn test_formula_on_solver_with_contradiction() -> LngResult<()> {
    for solver in &mut solvers() {
        let f = &FormulaFactory::new();
        solver.add(f.parse("A").unwrap(), f)?;
        solver.add(f.parse("B").unwrap(), f)?;
        solver.add(f.parse("C & (~A | ~B)").unwrap(), f)?;
        assert_eq!(
            solver.formula_on_solver(f)?,
            [
                f.variable("A"),
                f.variable("B"),
                f.variable("C"),
                f.falsum()
            ]
            .into_iter()
            .collect()
        );

        solver.reset();
        solver.add(f.parse("A <=> B").unwrap(), f)?;
        solver.add(f.parse("B <=> ~A").unwrap(), f)?;
        let on_solver = solver.formula_on_solver(f)?;
        let expected = [
            f.parse("A | B").unwrap(),
            f.parse("~A | B").unwrap(),
            f.parse("A | ~B").unwrap(),
            f.parse("~A | ~B").unwrap(),
        ]
        .iter()
        .copied()
        .collect::<HashSet<EncodedFormula>>();
        assert_eq!(on_solver.len(), expected.len());
        for fm in &expected {
            assert!(on_solver.contains(fm));
        }

        solver.sat();
        let on_solver = solver.formula_on_solver(f)?;
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

    Ok(())
}

fn compare_formulas(
    original: &[EncodedFormula],
    from_solver: &HashSet<EncodedFormula>,
    f: &FormulaFactory,
) -> LngResult<()> {
    let vars: Box<[Variable]> = original
        .iter()
        .flat_map(|formula| (*formula.variables(f)).clone())
        .unique()
        .collect();
    let models1 = enumerate_models_for_formula_with_config(
        f.and(original),
        f,
        &ModelEnumerationConfig::default().variables(vars.clone()),
    )?
    .iter()
    .map(Assignment::from)
    .collect::<HashSet<Assignment>>();
    let models2 = enumerate_models_for_formula_with_config(
        f.and(from_solver.iter()),
        f,
        &ModelEnumerationConfig::default().variables(vars),
    )?
    .iter()
    .map(Assignment::from)
    .collect::<HashSet<Assignment>>();
    assert_eq!(models1.len(), models2.len());
    for m in &models1 {
        assert!(models2.contains(m));
    }
    Ok(())
}

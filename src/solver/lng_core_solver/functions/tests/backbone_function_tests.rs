use std::collections::BTreeSet;

use crate::backbones::Backbone;
use crate::errors::LngResult;
use crate::formulas::{FormulaFactory, Literal, ToFormula, Variable};
use crate::handlers::{CancelableResult, ComputationHandler, LngComputation, LngEvent, NopHandler};
use crate::solver::lng_core_solver::functions::BackboneType::{
    OnlyNegative, OnlyPositive, PositiveAndNegative,
};
use crate::solver::lng_core_solver::{CnfMethod, SatSolver, SatSolverConfig};

fn solvers() -> [SatSolver; 2] {
    [
        SatSolver::from_config(SatSolverConfig::default().cnf_method(CnfMethod::FactoryCnf)),
        SatSolver::from_config(SatSolverConfig::default().cnf_method(CnfMethod::PgOnSolver)),
    ]
}

#[test]
fn test_constants_and_state_restoration() -> LngResult<()> {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        let initial_state = solver.save_state()?;
        solver.add(f.falsum(), f)?;
        assert_eq!(
            Backbone::new_unsat(),
            solver.backbone(vars("a b c", f), PositiveAndNegative)?
        );

        solver.load_state(&initial_state)?;
        solver.add(f.verum(), f)?;
        let backbone = solver.backbone(vars("a b c", f), PositiveAndNegative)?;
        assert!(backbone.sat);
        assert!(backbone.complete_backbone().is_empty());
        assert_eq!(
            Some(vars("a b c", f).into_iter().collect()),
            backbone.optional_variables
        );
    }
    Ok(())
}

#[test]
fn test_backbone_types() -> LngResult<()> {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("a & b & ~c & (d | e)".to_formula(f), f)?;

        let complete = solver.backbone(vars("a b c d e", f), PositiveAndNegative)?;
        assert_eq!(literals("a b ~c", f), complete.complete_backbone());
        assert_eq!(
            Some(vars("d e", f).into_iter().collect()),
            complete.optional_variables
        );

        let positive = solver.backbone(vars("a b c d e", f), OnlyPositive)?;
        assert_eq!(literals("a b", f), positive.complete_backbone());
        assert!(positive.optional_variables.is_none());

        let negative = solver.backbone(vars("a b c d e", f), OnlyNegative)?;
        assert_eq!(literals("~c", f), negative.complete_backbone());
        assert!(negative.optional_variables.is_none());
    }
    Ok(())
}

#[test]
fn test_handler_aware_backbone_returns_cancelable_result() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = SatSolver::new();
    solver.add("a & (b | c)".to_formula(f), f)?;

    let result = solver.backbone_with_handler(
        vars("a b c", f),
        PositiveAndNegative,
        &mut NopHandler::new(),
    )?;
    let backbone = result.result().expect("nop handler must not cancel");
    assert_eq!(literals("a", f), backbone.complete_backbone());

    let mut cancel = CancelImmediately;
    let canceled =
        solver.backbone_with_handler(vars("a b c", f), PositiveAndNegative, &mut cancel)?;
    assert!(matches!(
        canceled,
        CancelableResult::Canceled(LngEvent::ComputationStarted(LngComputation::Backbone))
    ));
    Ok(())
}

struct CancelImmediately;

impl ComputationHandler for CancelImmediately {
    fn should_resume(&mut self, _event: LngEvent) -> bool {
        false
    }
}

fn vars(names: &str, f: &FormulaFactory) -> Vec<Variable> {
    names.split_whitespace().map(|name| f.var(name)).collect()
}

fn literals(names: &str, f: &FormulaFactory) -> BTreeSet<Literal> {
    names
        .split_whitespace()
        .map(|name| name.to_formula(f).as_literal().expect("literal"))
        .collect()
}

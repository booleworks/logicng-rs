use crate::errors::LngResult;
use crate::formulas::{FormulaFactory, ToFormula};
use crate::propositions::{Proposition, StandardProposition};
use crate::solver::lng_core_solver::Tristate::{False, True};
use crate::solver::lng_core_solver::{SatSolver, SatSolverConfig};

/// Creates a proof-generating solver with a `String` backpack.
fn solver() -> SatSolver<String> {
    SatSolver::from_config_with_backpack(SatSolverConfig::default().proof_generation(true))
}

/// Shortcut for a `String`-backpacked proposition from a formula string.
fn sp(f: &FormulaFactory, formula: &str, description: &str) -> StandardProposition {
    Proposition::standard_proposition(formula.to_formula(f), description)
}

#[test]
fn test_add_proposition_registers_and_core() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = solver();

    let p1 = sp(f, "a", "P1");
    let p2 = sp(f, "a => b", "P2");
    let p3 = sp(f, "~b", "P3");
    solver.add_proposition(p1.clone(), f)?;
    solver.add_proposition(p2.clone(), f)?;
    solver.add_proposition(p3.clone(), f)?;

    assert_eq!(solver.propositions().len(), 3);

    assert_eq!(solver.sat(), False);
    let core = solver.unsat_core(f)?;
    assert_eq!(core.propositions.len(), 3);
    assert!(core.propositions.contains(&p1));
    assert!(core.propositions.contains(&p2));
    assert!(core.propositions.contains(&p3));

    let recovered = core
        .propositions
        .iter()
        .find(|p| **p == p1)
        .expect("proposition present");
    assert_eq!(recovered.backpack.as_ref().map(|b| b.as_str()), Some("P1"));

    Ok(())
}

#[test]
fn test_add_with_proposition_and_plain_formulas() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = solver();

    solver.add_formula("x | y".to_formula(f), f)?;

    let pa = sp(f, "a", "PA");
    let pna = sp(f, "~a", "PNA");
    solver.add_with_proposition(pa.formula, pa.clone(), f)?;
    solver.add_with_proposition(pna.formula, pna.clone(), f)?;

    assert_eq!(solver.propositions().len(), 2);

    assert_eq!(solver.sat(), False);
    let core = solver.unsat_core(f)?;
    assert!(core.propositions.contains(&pa));
    assert!(core.propositions.contains(&pna));

    Ok(())
}

#[test]
fn test_add_propositions_preserves_order() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = solver();

    let p1 = sp(f, "a", "P1");
    let p2 = sp(f, "b", "P2");
    let p3 = sp(f, "c", "P3");
    solver.add_propositions([p1.clone(), p2.clone(), p3.clone()], f)?;

    assert_eq!(solver.propositions(), &vec![p1, p2, p3]);

    Ok(())
}

#[test]
fn test_save_load_reverts_propositions() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = solver();

    let p1 = sp(f, "a", "P1");
    let p2 = sp(f, "a => b", "P2");
    solver.add_propositions([p1.clone(), p2.clone()], f)?;
    let state = solver.save_state()?;
    assert_eq!(solver.propositions().len(), 2);

    let p3 = sp(f, "~b", "P3");
    solver.add_proposition(p3, f)?;
    assert_eq!(solver.propositions().len(), 3);
    assert_eq!(solver.sat(), False);

    solver.load_state(&state)?;
    assert_eq!(solver.propositions().len(), 2);
    assert_eq!(solver.sat(), True);

    Ok(())
}

#[test]
fn test_sat_call_scoped_formula_reverted() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = solver();

    let base = sp(f, "a", "BASE");
    solver.add_proposition(base.clone(), f)?;
    let base_len = solver.propositions().len();

    {
        let tmp = sp(f, "~a & c", "TMP");
        let mut call = solver.sat_call().add_propositions([tmp.clone()]).solve(f)?;
        let core = call.unsat_core(f)?.expect("call is unsatisfiable");
        assert!(core.propositions.contains(&base));
        assert!(core.propositions.contains(&tmp));
    }

    assert_eq!(solver.propositions().len(), base_len);
    assert_eq!(solver.sat(), True);

    Ok(())
}

#[test]
fn test_sat_call_repeated_assumptions_no_leak() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver = solver();

    solver.add_proposition(sp(f, "~b", "BASE"), f)?;
    let base_len = solver.propositions().len();

    for _ in 0..5 {
        {
            let assume = sp(f, "b", "ASSUME");
            let mut call = solver.sat_call().add_propositions([assume]).solve(f)?;
            assert_eq!(call.get_sat_result()?.result(), Some(false));
            let core = call.unsat_core(f)?.expect("call is unsatisfiable");
            assert!(!core.propositions.is_empty());
        }
        assert_eq!(solver.propositions().len(), base_len);
    }

    Ok(())
}

#[test]
fn test_typed_backpack_round_trip() -> LngResult<()> {
    let f = &FormulaFactory::new();
    let mut solver: SatSolver<u32> =
        SatSolver::from_config_with_backpack(SatSolverConfig::default().proof_generation(true));

    solver.add_with_proposition(
        "a".to_formula(f),
        Proposition::with_backpack("a".to_formula(f), 1),
        f,
    )?;
    solver.add_with_proposition(
        "~a".to_formula(f),
        Proposition::with_backpack("~a".to_formula(f), 2),
        f,
    )?;

    assert_eq!(solver.sat(), False);
    let core = solver.unsat_core(f)?;
    let backpacks: Vec<u32> = core
        .propositions
        .iter()
        .filter_map(|p| p.backpack.as_ref().map(|b| **b))
        .collect();
    assert!(backpacks.contains(&1));
    assert!(backpacks.contains(&2));

    Ok(())
}

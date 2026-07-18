use crate::errors::LngResult;
use crate::solver::lng_core_solver::tests::generate_pigeon_hole;
use crate::solver::lng_core_solver::Tristate;
use crate::solver::lng_core_solver::Tristate::False;
use crate::solver::lng_core_solver::{SatSolver, SatSolverConfig};
use crate::util::test_util::F;
use Tristate::True;

#[test]
fn test_inc_dec() -> LngResult<()> {
    let ff = F::new();
    let f = &ff.f;
    let mut s = SatSolver::new();
    s.add(f.variable("a"), f)?;
    let state1 = s.save_state().unwrap();
    assert_eq!(s.sat().unwrap(), True);

    s.add(generate_pigeon_hole(5, f), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state1)?;
    assert_eq!(s.sat().unwrap(), True);

    s.add(f.literal("a", false), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state1)?;
    assert_eq!(s.sat().unwrap(), True);

    s.add(generate_pigeon_hole(5, f), f)?;
    let state2 = s.save_state().unwrap();
    s.add(generate_pigeon_hole(4, f), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state2)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state1)?;
    assert_eq!(s.sat().unwrap(), True);

    Ok(())
}

#[test]
fn test_inc_dec_deep_1() -> LngResult<()> {
    let ff = F::new();
    let f = &ff.f;
    let mut s = SatSolver::new();
    s.add(f.variable("a"), f)?;
    let state1 = s.save_state().unwrap();
    s.add(f.variable("b"), f)?;
    assert_eq!(s.sat().unwrap(), True);

    let state2 = s.save_state().unwrap();
    s.add(f.literal("a", false), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state1)?;
    assert!(s.load_state(&state2).is_err());

    Ok(())
}

#[test]
fn test_inc_dec_deep_2() -> LngResult<()> {
    let ff = F::new();
    let f = &ff.f;
    let mut s = SatSolver::new();
    s.add(f.variable("a"), f)?;
    let state1 = s.save_state().unwrap();
    s.add(f.variable("b"), f)?;
    assert_eq!(s.sat().unwrap(), True);

    let _state2 = s.save_state().unwrap();
    s.add(f.literal("a", false), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state1)?;

    s.add(f.literal("b", false), f)?;
    assert_eq!(s.sat().unwrap(), True);
    let state3 = s.save_state().unwrap();
    s.add(f.literal("a", false), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state3)?;
    s.add(f.variable("c"), f)?;
    let state4 = s.save_state().unwrap();
    let state5 = s.save_state().unwrap();
    s.load_state(&state4)?;
    assert!(s.load_state(&state5).is_err());

    Ok(())
}

#[test]
fn test_inc_dec_deep_3() -> LngResult<()> {
    let ff = F::new();
    let f = &ff.f;
    let mut s = SatSolver::new();
    s.add(f.variable("a"), f)?;
    let state1 = s.save_state().unwrap();
    s.add(f.variable("b"), f)?;
    assert_eq!(s.sat().unwrap(), True);

    let _state2 = s.save_state().unwrap();
    s.add(f.literal("a", false), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state1)?;

    s.add(f.literal("b", false), f)?;
    assert_eq!(s.sat().unwrap(), True);
    let state3 = s.save_state().unwrap();
    s.add(f.literal("a", false), f)?;
    assert_eq!(s.sat().unwrap(), False);
    s.load_state(&state3)?;
    s.add(f.variable("c"), f)?;
    let state4 = s.save_state().unwrap();
    let _state5 = s.save_state().unwrap();
    s.load_state(&state4)?;
    assert_eq!(s.sat().unwrap(), True);
    s.load_state(&state1)?;
    assert_eq!(s.sat().unwrap(), True);
    assert!(s.load_state(&state3).is_err());

    Ok(())
}

#[test]
fn test_not_incremental_1() {
    let mut s = SatSolver::from_config(SatSolverConfig::default().incremental(false));
    assert!(s.save_state().is_err());
}

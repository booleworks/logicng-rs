use crate::solver::minisat::sat::Tristate;
use crate::solver::minisat::sat::Tristate::False;
use crate::solver::minisat::{MiniSat, MiniSatConfig, SolverState};
use crate::solver::tests::generate_pigeon_hole;
use crate::util::test_util::F;
use Tristate::True;

#[test]
fn test_inc_dec() {
    let ff = F::new();
    let f = &ff.f;
    let mut s = MiniSat::new();
    s.add(f.variable("a"), f);
    let state1 = s.save_state();
    assert_eq!(state1, SolverState::new(0, [1, 1, 0, 0, 1, 0, 0]));
    assert_eq!(s.sat(), True);

    s.add(generate_pigeon_hole(5, f), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state1);
    assert_eq!(s.sat(), True);

    s.add(f.literal("a", false), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state1);
    assert_eq!(s.sat(), True);

    s.add(generate_pigeon_hole(5, f), f);
    let state2 = s.save_state();
    assert_eq!(state2, SolverState::new(1, [1, 31, 81, 0, 1, 0, 0]));
    s.add(generate_pigeon_hole(4, f), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state2);
    assert_eq!(s.sat(), False);
    s.load_state(&state1);
    assert_eq!(s.sat(), True);
}

#[test]
#[should_panic(expected = "The given solver state is not valid anymore.")]
fn test_inc_dec_deep_1() {
    let ff = F::new();
    let f = &ff.f;
    let mut s = MiniSat::new();
    s.add(f.variable("a"), f);
    let state1 = s.save_state();
    s.add(f.variable("b"), f);
    assert_eq!(s.sat(), True);

    let state2 = s.save_state();
    s.add(f.literal("a", false), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state1);
    s.load_state(&state2);
}

#[test]
#[should_panic(expected = "The given solver state is not valid anymore.")]
fn test_inc_dec_deep_2() {
    let ff = F::new();
    let f = &ff.f;
    let mut s = MiniSat::new();
    s.add(f.variable("a"), f);
    let state1 = s.save_state();
    s.add(f.variable("b"), f);
    assert_eq!(s.sat(), True);

    let _state2 = s.save_state();
    s.add(f.literal("a", false), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state1);

    s.add(f.literal("b", false), f);
    assert_eq!(s.sat(), True);
    let state3 = s.save_state();
    s.add(f.literal("a", false), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state3);
    s.add(f.variable("c"), f);
    let state4 = s.save_state();
    let state5 = s.save_state();
    s.load_state(&state4);
    s.load_state(&state5);
}

#[test]
#[should_panic(expected = "The given solver state is not valid anymore.")]
fn test_inc_dec_deep_3() {
    let ff = F::new();
    let f = &ff.f;
    let mut s = MiniSat::new();
    s.add(f.variable("a"), f);
    let state1 = s.save_state();
    s.add(f.variable("b"), f);
    assert_eq!(s.sat(), True);

    let _state2 = s.save_state();
    s.add(f.literal("a", false), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state1);

    s.add(f.literal("b", false), f);
    assert_eq!(s.sat(), True);
    let state3 = s.save_state();
    s.add(f.literal("a", false), f);
    assert_eq!(s.sat(), False);
    s.load_state(&state3);
    s.add(f.variable("c"), f);
    let state4 = s.save_state();
    let _state5 = s.save_state();
    s.load_state(&state4);
    assert_eq!(s.sat(), True);
    s.load_state(&state1);
    assert_eq!(s.sat(), True);
    s.load_state(&state3);
}

#[test]
#[should_panic(expected = "Cannot save a state when the incremental mode is deactivated")]
fn test_not_incremental_1() {
    let mut s = MiniSat::from_config(MiniSatConfig::default().incremental(false));
    s.save_state();
}

#[test]
#[should_panic(expected = "Cannot load a state when the incremental mode is deactivated")]
fn test_not_incremental_2() {
    let mut s = MiniSat::from_config(MiniSatConfig::default().incremental(false));
    s.underlying_solver.load_state([0, 0, 0, 0, 0, 0, 0]);
}

use crate::{
    solver::lng_core_solver::{tests::generate_pigeon_hole, LngState, SolverState},
    util::test_util::F,
};

use super::{solver_cross_product, SatSolverConfigParam};

#[test]
fn test_inc_dec() {
    let ff = F::new();
    let f = &ff.f;
    let solvers = solver_cross_product::<()>(&[SatSolverConfigParam::UseAtMostClauses]);

    for mut s in solvers {
        s.add_formula(f.variable("a"), f);
        let state1 = s.save_state();
        assert_eq!(
            state1,
            SolverState {
                id: LngState(0),
                ok: true,
                vars_size: 1,
                all_clause_size: 0,
                clause_size: 0,
                unit_clause_size: 1,
                pg_original_size: 0,
                pg_proof_size: 0,
            }
        );
        assert!(s.sat(f));

        s.add_formula(generate_pigeon_hole(5, f), f);
        assert!(!s.sat(f));
        s.load_state(&state1);
        assert!(s.sat(f));

        s.add_formula(f.literal("a", false), f);
        assert!(!s.sat(f));
        s.load_state(&state1);
        assert!(s.sat(f));

        s.add_formula(generate_pigeon_hole(5, f), f);
        let state2 = s.save_state();
        assert_eq!(
            state2,
            SolverState {
                id: LngState(1),
                ok: true,
                vars_size: 31,
                all_clause_size: 81,
                clause_size: 81,
                unit_clause_size: 1,
                pg_original_size: 0,
                pg_proof_size: 0
            }
        );
        s.add_formula(generate_pigeon_hole(4, f), f);
        assert!(!s.sat(f));
        s.load_state(&state2);
        assert!(!s.sat(f));
        s.load_state(&state1);
        assert!(s.sat(f));
    }
}

#[test]
#[should_panic(expected = "The given solver state is not valid anymore")]
fn test_inc_dec_deep_1() {
    let ff = F::new();
    let f = &ff.f;
    let solvers = solver_cross_product::<()>(&[SatSolverConfigParam::UseAtMostClauses]);

    for mut s in solvers {
        s.add_formula(f.variable("a"), f);
        let state1 = s.save_state();
        s.add_formula(f.variable("b"), f);
        assert!(s.sat(f));

        let state2 = s.save_state();
        s.add_formula(f.literal("a", false), f);
        assert!(!s.sat(f));
        s.load_state(&state1);
        s.load_state(&state2);
    }
}

#[test]
#[should_panic(expected = "The given solver state is not valid anymore")]
fn test_inc_dec_deep_2() {
    let ff = F::new();
    let f = &ff.f;
    let solvers = solver_cross_product::<()>(&[SatSolverConfigParam::UseAtMostClauses]);

    for mut s in solvers {
        s.add_formula(f.variable("a"), f);
        let state1 = s.save_state();
        s.add_formula(f.variable("b"), f);
        assert!(s.sat(f));

        let _state2 = s.save_state();
        s.add_formula(f.literal("a", false), f);
        assert!(!s.sat(f));
        s.load_state(&state1);

        s.add_formula(f.literal("b", false), f);
        assert!(s.sat(f));
        let state3 = s.save_state();
        s.add_formula(f.literal("a", false), f);
        assert!(!s.sat(f));
        s.load_state(&state3);
        s.add_formula(f.variable("c"), f);
        let state4 = s.save_state();
        let state5 = s.save_state();
        s.load_state(&state4);
        s.load_state(&state5);
    }
}

#[test]
#[should_panic(expected = "The given solver state is not valid anymore")]
fn test_inc_dec_deep_3() {
    let ff = F::new();
    let f = &ff.f;

    let solvers = solver_cross_product::<()>(&[SatSolverConfigParam::UseAtMostClauses]);

    for mut s in solvers {
        s.add_formula(f.variable("a"), f);
        let state1 = s.save_state();
        s.add_formula(f.variable("b"), f);
        assert!(s.sat(f));

        let _state2 = s.save_state();
        s.add_formula(f.literal("a", false), f);
        assert!(!s.sat(f));
        s.load_state(&state1);

        s.add_formula(f.literal("b", false), f);
        assert!(s.sat(f));
        let state3 = s.save_state();
        s.add_formula(f.literal("a", false), f);
        assert!(!s.sat(f));
        s.load_state(&state3);
        s.add_formula(f.variable("c"), f);
        let state4 = s.save_state();
        let _state5 = s.save_state();
        s.load_state(&state4);
        assert!(s.sat(f));
        s.load_state(&state1);
        assert!(s.sat(f));
        s.load_state(&state3);
    }
}

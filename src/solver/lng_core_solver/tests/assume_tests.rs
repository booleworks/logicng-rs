use crate::formulas::ToFormula;
use crate::handlers::LngResult;
use crate::util::test_util::F;

use super::{solver_cross_product, SatSolverConfigParam};

#[test]
fn test_assume() {
    let ff = F::new();
    let f = &ff.f;
    let solvers = solver_cross_product::<()>(&[
        SatSolverConfigParam::UseAtMostClauses,
        SatSolverConfigParam::ProofGeneration,
        SatSolverConfigParam::CnfMethod,
    ]);
    let assumptions1 = [f.lit("c", true), f.lit("d", true)];
    let assumptions2 = [f.lit("x", false), f.lit("y", true), f.lit("d", true)];
    let assumptions3 = [f.lit("a", false), f.lit("c", true), f.lit("a", false)];
    let assumptions4 = [f.lit("c", false), f.lit("d", true)];
    let assumptions5 = [f.lit("x", true), f.lit("x", false)];
    let assumptions6 = [f.lit("a", true), f.lit("a", false)];

    for mut s in solvers {
        s.add_formula("~a".to_formula(f), f);
        s.add_formula("b".to_formula(f), f);
        s.add_formula("b => c".to_formula(f), f);
        s.add_formula("c => d".to_formula(f), f);
        s.add_formula("d => e".to_formula(f), f);
        s.add_formula("e => f".to_formula(f), f);

        assert_eq!(s.sat_call().add_formulas([f.lit("a", false)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("b", true)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("c", true)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("d", true)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("e", true)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("f", true)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("g", true)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas([f.lit("a", true)]).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas([f.lit("b", false)]).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas([f.lit("c", false)]).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas([f.lit("d", false)]).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas([f.lit("e", false)]).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas([f.lit("f", false)]).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas([f.lit("g", false)]).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas(assumptions1).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas(assumptions2).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas(assumptions3).sat(f), LngResult::Ok(true));
        assert_eq!(s.sat_call().add_formulas(assumptions4).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas(assumptions5).sat(f), LngResult::Ok(false));
        assert_eq!(s.sat_call().add_formulas(assumptions6).sat(f), LngResult::Ok(false));
    }
}

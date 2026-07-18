use crate::errors::LngResult;
use crate::formulas::ToFormula;
use crate::solver::lng_core_solver::Tristate::{False, True};
use crate::solver::lng_core_solver::{SatBuilder, SatSolver, SatSolverConfig};
use crate::util::test_util::F;

#[test]
fn test_assume() -> LngResult<()> {
    let ff = F::new();
    let f = &ff.f;
    let solvers = [
        SatSolver::from_config(SatSolverConfig::default().incremental(true)),
        SatSolver::from_config(SatSolverConfig::default().incremental(false)),
    ];

    let assumptions1 = [f.lit("c", true), f.lit("d", true)];
    let assumptions2 = [f.lit("x", false), f.lit("y", true), f.lit("d", true)];
    let assumptions3 = [f.lit("a", false), f.lit("c", true), f.lit("a", false)];
    let assumptions4 = [f.lit("c", false), f.lit("d", true)];
    let assumptions5 = [f.lit("x", true), f.lit("x", false)];
    let assumptions6 = [f.lit("a", true), f.lit("a", false)];

    for mut s in solvers {
        s.add("~a".to_formula(f), f)?;
        s.add("b".to_formula(f), f)?;
        s.add("b => c".to_formula(f), f)?;
        s.add("c => d".to_formula(f), f)?;
        s.add("d => e".to_formula(f), f)?;
        s.add("e => f".to_formula(f), f)?;

        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("a", false)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("b", true)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("c", true)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("d", true)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("e", true)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("f", true)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("g", true)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("a", true)]))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("b", false)]))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("c", false)]))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("d", false)]))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("e", false)]))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("f", false)]))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&vec![f.lit("g", false)]))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&assumptions1))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&assumptions2))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&assumptions3))
                .unwrap(),
            True
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&assumptions4))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&assumptions5))
                .unwrap(),
            False
        );
        assert_eq!(
            s.sat_with(&SatBuilder::new().assumptions(&assumptions6))
                .unwrap(),
            False
        );
    }

    Ok(())
}

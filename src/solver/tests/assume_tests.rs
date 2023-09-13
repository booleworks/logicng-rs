use crate::formulas::ToFormula;
use crate::solver::minisat::sat::Tristate::{False, True};
use crate::solver::minisat::{MiniSat, MiniSatConfig, SatBuilder};
use crate::util::test_util::F;

#[test]
fn test_assume() {
    let ff = F::new();
    let f = &ff.f;
    let solvers = [
        MiniSat::new_with_config(MiniSatConfig::default().incremental(true)),
        MiniSat::new_with_config(MiniSatConfig::default().incremental(false)),
    ];

    let assumptions1 = [f.lit("c", true), f.lit("d", true)];
    let assumptions2 = [f.lit("x", false), f.lit("y", true), f.lit("d", true)];
    let assumptions3 = [f.lit("a", false), f.lit("c", true), f.lit("a", false)];
    let assumptions4 = [f.lit("c", false), f.lit("d", true)];
    let assumptions5 = [f.lit("x", true), f.lit("x", false)];
    let assumptions6 = [f.lit("a", true), f.lit("a", false)];

    for mut s in solvers {
        s.add("~a".to_formula(f), f);
        s.add("b".to_formula(f), f);
        s.add("b => c".to_formula(f), f);
        s.add("c => d".to_formula(f), f);
        s.add("d => e".to_formula(f), f);
        s.add("e => f".to_formula(f), f);

        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("a", false))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("b", true))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("c", true))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("d", true))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("e", true))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("f", true))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("g", true))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("a", true))), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("b", false))), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("c", false))), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("d", false))), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("e", false))), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("f", false))), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumption(f.lit("g", false))), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumptions(&assumptions1)), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumptions(&assumptions2)), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumptions(&assumptions3)), True);
        assert_eq!(s.sat_with(&SatBuilder::new().assumptions(&assumptions4)), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumptions(&assumptions5)), False);
        assert_eq!(s.sat_with(&SatBuilder::new().assumptions(&assumptions6)), False);
    }
}

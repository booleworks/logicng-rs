use crate::encodings::cardinality_constraints::cc_config::{AlkEncoder, AmkEncoder, CcConfig};
use crate::formulas::CType::LE;
use crate::formulas::{FormulaFactory, Variable};
use crate::solver::lng_core_solver::SatSolver;

const fn configs() -> [CcConfig; 3] {
    [
        CcConfig::new().amk_encoder(AmkEncoder::Totalizer).alk_encoder(AlkEncoder::Totalizer),
        CcConfig::new().amk_encoder(AmkEncoder::CardinalityNetwork).alk_encoder(AlkEncoder::CardinalityNetwork),
        CcConfig::new().amk_encoder(AmkEncoder::ModularTotalizer).alk_encoder(AlkEncoder::ModularTotalizer),
    ]
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_amk_performance() {
    for config in configs() {
        let f = &mut FormulaFactory::new();
        f.config.cc_config = config;
        test_build_amk(10_000, f);
    }
}

fn test_build_amk(num_lits: u32, f: &FormulaFactory) {
    let problem_lits: Box<[Variable]> = (0..num_lits).map(|i| f.var(format!("v{i}"))).collect();
    let mut solver = SatSolver::<()>::new();
    for i in (10..100).step_by(10) {
        let cc = f.cc(LE, i, problem_lits.clone());
        solver.add_formula(cc, f);
        assert!(solver.sat(f));
        let model = solver.sat_call().model(&problem_lits, f).unwrap();
        assert!(f.evaluate(cc, &model.into()));
    }
}

use crate::cardinality_constraints::cc_config::BimanderGroupSize::{Fixed, Half, Sqrt};
use crate::cardinality_constraints::cc_config::{AmoEncoder, CcConfig};
use crate::cardinality_constraints::cc_encoder::CcEncoder;
use crate::formulas::CType::EQ;
use crate::formulas::{FormulaFactory, Variable};
use crate::solver::functions::{ModelEnumerationConfig, enumerate_models_with_config};
use crate::solver::minisat::MiniSat;
use crate::solver::minisat::sat::Tristate::True;

fn configs() -> Vec<CcConfig> {
    vec![
        CcConfig::new().amo_encoder(AmoEncoder::Pure),
        CcConfig::new().amo_encoder(AmoEncoder::Ladder),
        CcConfig::new().amo_encoder(AmoEncoder::Product { recursive_bound: CcConfig::DEFAULT_PRODUCT_RECURSIVE_BOUND }),
        CcConfig::new().amo_encoder(AmoEncoder::Binary),
        CcConfig::new().amo_encoder(AmoEncoder::Nested { group_size: CcConfig::DEFAULT_NESTING_GROUP_SIZE }),
        CcConfig::new().amo_encoder(AmoEncoder::Commander { group_size: 3 }),
        CcConfig::new().amo_encoder(AmoEncoder::Commander { group_size: 7 }),
        CcConfig::new().amo_encoder(AmoEncoder::Bimander { group_size: Half }),
        CcConfig::new().amo_encoder(AmoEncoder::Bimander { group_size: Sqrt }),
        CcConfig::new().amo_encoder(AmoEncoder::Bimander { group_size: Fixed(2) }),
        CcConfig::new().amo_encoder(AmoEncoder::Nested { group_size: 5 }),
        CcConfig::new().amo_encoder(AmoEncoder::Product { recursive_bound: 10 }),
        CcConfig::new().amo_encoder(AmoEncoder::Best),
    ]
}

#[test]
fn test_exo_0() {
    let mut f = FormulaFactory::new();
    for config in configs() {
        f.config.cc_config = config.clone();
        let cc = f.cc(EQ, 0, (&[]) as &[Variable]);
        assert!(f.nnf_of(cc).is_verum());
    }
}

#[test]
fn test_exo_1() {
    let mut f = FormulaFactory::new();
    for config in configs() {
        f.config.cc_config = config.clone();
        let var = f.variable("v0").as_variable().unwrap();
        let cc = f.cc(EQ, 1, &([var]) as &[Variable]);
        assert_eq!(f.nnf_of(cc), f.variable("v0"));
        assert_eq!(CcEncoder::new(config).encode(&cc.as_cc(&f).unwrap(), &f), vec![f.variable("v0")]);
    }
}

#[test]
fn test_exo_k() {
    let mut f = FormulaFactory::new();
    for config in configs() {
        f.config.cc_config = config;
        test_exo(2, &f);
        test_exo(10, &f);
        test_exo(100, &f);
    }
}

fn test_exo(num_lits: usize, f: &FormulaFactory) {
    let problem_lits: Box<[Variable]> = (0..num_lits).map(|i| f.variable(format!("v{i}")).as_variable().unwrap()).collect();
    let mut solver = MiniSat::new();
    let cc = f.cc(EQ, 1, problem_lits.clone());
    solver.add(cc, f);
    assert_eq!(solver.sat(), True);
    let models = enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(problem_lits).max_models(12000));
    assert_eq!(models.len(), num_lits);
    for model in models {
        assert_eq!(model.pos().len(), 1);
    }
}

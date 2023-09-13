use crate::datastructures::Assignment;
use crate::formulas::CType::{EQ, GE, GT, LE, LT};
use crate::formulas::{FormulaFactory, Literal};
use crate::pseudo_booleans::pb_config::{PbAlgorithm, PbConfig};
use crate::solver::functions::{enumerate_models_with_config, ModelEnumerationConfig};
use crate::solver::minisat::sat::Tristate;
use crate::solver::minisat::MiniSat;
use crate::util::test_util::F;

fn configs() -> Vec<PbConfig> {
    vec![
        PbConfig::new().pb_encoder(PbAlgorithm::Swc),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(true)
            .binary_merge_no_support_for_single_bit(true)
            .binary_merge_use_watch_dog(true),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(true)
            .binary_merge_no_support_for_single_bit(true)
            .binary_merge_use_watch_dog(false),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(true)
            .binary_merge_no_support_for_single_bit(false)
            .binary_merge_use_watch_dog(true),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(true)
            .binary_merge_no_support_for_single_bit(false)
            .binary_merge_use_watch_dog(false),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(false)
            .binary_merge_no_support_for_single_bit(true)
            .binary_merge_use_watch_dog(true),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(false)
            .binary_merge_no_support_for_single_bit(true)
            .binary_merge_use_watch_dog(false),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(false)
            .binary_merge_no_support_for_single_bit(false)
            .binary_merge_use_watch_dog(true),
        PbConfig::new()
            .pb_encoder(PbAlgorithm::BinaryMerge)
            .binary_merge_use_gac(false)
            .binary_merge_no_support_for_single_bit(false)
            .binary_merge_use_watch_dog(false),
        PbConfig::new().pb_encoder(PbAlgorithm::AdderNetworks),
    ]
}

fn literals(n: usize, f: &FormulaFactory) -> Box<[Literal]> {
    (0..n).map(|n| f.variable(&format!("v{n}")).as_literal().unwrap()).collect()
}

#[test]
fn test_pb_eq() {
    for config in configs() {
        let f = &mut FormulaFactory::new();
        f.config.pb_config = config;
        let mut solver = MiniSat::new();
        let coeffs10: Box<[i64]> = Box::new([3, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
        let literals10 = literals(10, f);
        solver.add(f.pbc(EQ, 5, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 9);
        for model in models {
            assert_eq!(model.pos().len(), 2);
            assert!(Assignment::from(model).contains_pos(f.variable("v0").as_literal().unwrap().variable()));
        }

        solver.reset();
        solver.add(f.pbc(EQ, 7, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 36);
        for model in models {
            assert_eq!(model.pos().len(), 3);
            assert!(Assignment::from(model).contains_pos(f.variable("v0").as_literal().unwrap().variable()));
        }

        solver.reset();
        solver.add(f.pbc(EQ, 0, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(EQ, 1, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::False);

        solver.reset();
        solver.add(f.pbc(EQ, 21, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(EQ, 22, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::False);
    }
}

#[test]
fn test_pb_less() {
    for config in configs() {
        let mut F = F::new();
        let f = &mut F.f;
        f.config.pb_config = config;
        let mut solver = MiniSat::new();
        let coeffs10: Box<[i64]> = Box::new([3, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
        let literals10 = literals(10, f);

        solver.add(f.pbc(LE, 6, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 140);
        for model in models {
            assert!(model.pos().len() <= 3);
        }

        solver.reset();
        solver.add(f.pbc(LT, 7, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 140);
        for model in models {
            assert!(model.pos().len() <= 3);
        }

        solver.reset();
        solver.add(f.pbc(LE, 0, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(LE, 1, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(LT, 2, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(LT, 1, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(LE, 2, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 10);

        solver.reset();
        solver.add(f.pbc(LE, 3, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 11);

        solver.reset();
        solver.add(f.pbc(LE, 4, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 47);
    }
}

#[test]
fn test_pb_greater() {
    for config in configs() {
        let mut F = F::new();
        let f = &mut F.f;
        f.config.pb_config = config;
        let mut solver = MiniSat::new();
        let coeffs10: Box<[i64]> = Box::new([3, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
        let literals10 = literals(10, f);

        solver.add(f.pbc(GE, 17, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 47);
        for model in models {
            assert!(model.pos().len() >= 8);
        }

        solver.reset();
        solver.add(f.pbc(GT, 16, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 47);
        for model in models {
            assert!(model.pos().len() >= 8);
        }

        solver.reset();
        solver.add(f.pbc(GE, 21, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(GE, 20, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(GT, 19, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(GT, 20, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);

        solver.reset();
        solver.add(f.pbc(GE, 19, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 10);

        solver.reset();
        solver.add(f.pbc(GE, 18, literals10.clone(), coeffs10.clone()), f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 11);
    }
}

#[test]
fn test_pb_negative() {
    for config in configs() {
        let mut F = F::new();
        let f = &mut F.f;
        f.config.pb_config = config;
        let mut solver = MiniSat::new();
        let coeffs10: Box<[i64]> = Box::new([2, 2, 2, 2, 2, 2, 2, 2, 2, -2]);
        let literals10 = literals(10, f);

        let pbc = f.pbc(EQ, 2, literals10.clone(), coeffs10.clone());
        solver.add(pbc, f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 45);
        for model in models {
            assert!(f.evaluate(pbc, &model.into()));
        }

        solver.reset();
        let pbc = f.pbc(EQ, 4, literals10.clone(), coeffs10.clone());
        solver.add(pbc, f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 120);
        for model in models {
            assert!(f.evaluate(pbc, &model.into()));
        }

        solver.reset();
        let coeffs10: Box<[i64]> = Box::new([2, 2, -3, 2, -7, 2, 2, 2, 2, -2]);
        let pbc = f.pbc(EQ, 4, literals10.clone(), coeffs10.clone());
        solver.add(pbc, f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 57);
        for model in models {
            assert!(f.evaluate(pbc, &model.into()));
        }

        solver.reset();
        let coeffs10: Box<[i64]> = Box::new([2, 2, -3, 2, -7, 2, 2, 2, 2, -2]);
        let pbc = f.pbc(EQ, -10, literals10.clone(), coeffs10.clone());
        solver.add(pbc, f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 8);
        for model in models {
            assert!(f.evaluate(pbc, &model.into()));
        }

        solver.reset();
        let coeffs10: Box<[i64]> = Box::new([2, 2, -4, 2, -6, 2, 2, 2, 2, -2]);
        let pbc = f.pbc(EQ, -12, literals10.clone(), coeffs10.clone());
        solver.add(pbc, f);
        assert_eq!(solver.sat(), Tristate::True);
        let models = enumerate_models_with_config(
            &mut solver,
            &ModelEnumerationConfig::default().variables(literals10.iter().map(Literal::variable).collect::<Box<[_]>>()),
        );
        assert_eq!(models.len(), 1);
        for model in models {
            assert!(f.evaluate(pbc, &model.into()));
        }
    }
}

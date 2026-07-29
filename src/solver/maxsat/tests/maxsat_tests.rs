use std::collections::HashMap;
use std::io::BufRead;

#[cfg(test)]
use crate::backends::MaxSatResult;
#[cfg(test)]
use crate::datastructures::Model;
#[cfg(test)]
use crate::errors::LngResult;
#[cfg(test)]
use crate::formulas::FormulaFactory;
#[cfg(test)]
use crate::solver::maxsat::{MaxSatSolver, OpenWboConfig, RustOpenWboFactory};

#[cfg(test)]
mod handler_tests {
    use crate::backends::MaxSatResult;
    use crate::formulas::FormulaFactory;
    use crate::handlers::{
        CancelableResult, ComputationHandler, LngComputation, LngEvent, TimeoutHandler,
    };
    use crate::solver::maxsat::openwbo_rs::config::{Algorithm, OpenWboConfig};
    use crate::solver::maxsat::tests::maxsat_tests::read_cnf_to_solver;
    use crate::solver::maxsat::{MaxSatSolver, RustOpenWboFactory};
    use std::path::Path;
    use std::time::{Duration, Instant};

    struct CancelInSatSolver;

    impl ComputationHandler for CancelInSatSolver {
        fn should_resume(&mut self, event: LngEvent) -> bool {
            !matches!(event, LngEvent::SatConflictDetected)
        }
    }

    #[test]
    fn timeout_can_cancel_at_start() {
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Oll);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        let result = solver
            .solve_with_handler(&mut TimeoutHandler::new(0))
            .unwrap();
        assert!(matches!(
            result,
            CancelableResult::Canceled(LngEvent::ComputationStarted(_))
        ));
    }

    #[test]
    fn cancellation_in_glucose_keeps_best_bound_and_model() {
        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default().algorithm(Algorithm::LinearSu);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        for i in 0..100 {
            let variable = f.var(format!("x{i}"));
            solver.add_soft_formula(1, variable.into(), &f).unwrap();
            solver
                .add_soft_formula(1, variable.negate().into(), &f)
                .unwrap();
        }

        let result = solver.solve_with_handler(&mut CancelInSatSolver).unwrap();
        match result {
            CancelableResult::Partial(
                MaxSatResult::Optimum { model, .. },
                LngEvent::SatConflictDetected,
            ) => assert!(!model.literals().is_empty()),
            result => panic!("unexpected result: {result:?}"),
        }
    }

    #[test]
    fn real_timeout_on_large_maxsat_instance() {
        const TIMEOUT: Duration = Duration::from_millis(300);
        const MAX_CANCELLATION_DELAY: Duration = Duration::from_millis(500);

        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Wbo);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        let instance =
            Path::new("resources/partialweightedmaxsat/large/mancoosi-test-i40d0u98-17.wcnf");
        read_cnf_to_solver(&mut solver, instance, &f).unwrap();

        let started = Instant::now();
        let result = solver
            .solve_with_handler(&mut TimeoutHandler::new(
                TIMEOUT.as_millis().try_into().unwrap(),
            ))
            .unwrap();
        let elapsed = started.elapsed();

        assert!(
            elapsed >= TIMEOUT,
            "solver canceled before the configured timeout: {elapsed:?}"
        );
        assert!(
            elapsed < TIMEOUT + MAX_CANCELLATION_DELAY,
            "native cancellation was not observed promptly: {elapsed:?}"
        );

        match result {
            CancelableResult::Partial(MaxSatResult::Optimum { model, .. }, cause) => {
                assert!(matches!(
                    cause,
                    LngEvent::MaxSatSolverCall
                        | LngEvent::SatConflictDetected
                        | LngEvent::ComputationFinished(LngComputation::MaxSat)
                ));
                assert!(!model.literals().is_empty());
            }
            CancelableResult::Canceled(cause) => {
                panic!("timeout did not preserve a best-so-far result: {cause:?}")
            }
            CancelableResult::Ok(result) => {
                panic!("large instance unexpectedly finished before timeout: {result:?}")
            }
            CancelableResult::Partial(result, cause) => {
                panic!("unexpected partial result {result:?} caused by {cause:?}")
            }
        }
    }

    #[test]
    fn large_maxsat_instance_finishes_with_sufficient_timeout() {
        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Wbo);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        let instance =
            Path::new("resources/partialweightedmaxsat/large/mancoosi-test-i40d0u98-17.wcnf");
        read_cnf_to_solver(&mut solver, instance, &f).unwrap();

        let result = solver
            .solve_with_handler(&mut TimeoutHandler::new(100_000))
            .unwrap();

        match result {
            CancelableResult::Ok(MaxSatResult::Optimum { bound, model }) => {
                assert_eq!(bound, 1_780_852);
                assert!(!model.literals().is_empty());
            }
            result => panic!("unexpected result: {result:?}"),
        }
    }
}

#[cfg(test)]
mod pure_maxsat_tests {
    use crate::backends::MaxSatResult;
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::openwbo_rs::config::{Algorithm, OpenWboConfig};
    use crate::solver::maxsat::tests::maxsat_tests::read_cnf_to_solver;
    use crate::solver::maxsat::{
        CardinalEncoding, MaxSatSolver, RustOpenWboFactory, Symmetry, WeightStrategy,
    };

    use super::{assert_optimum, test_on_files};

    static FILES: &[(&str, u64)] = &[
        (
            "resources/maxsat/c5315-bug-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
        (
            "resources/maxsat/c6288-bug-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
        (
            "resources/maxsat/c7552-bug-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
        (
            "resources/maxsat/mot_comb1._red-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
        (
            "resources/maxsat/mot_comb2._red-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
        (
            "resources/maxsat/mot_comb3._red-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
        (
            "resources/maxsat/s15850-bug-onevec-gate-0.dimacs.seq.filtered.cnf",
            1,
        ),
    ];

    static SAT_FILES: &[(&str, u64)] = &[("resources/sat/9symml_gr_rcs_w6.shuffled.cnf", 0)];

    #[test]
    fn corner_case() {
        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Wbo);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        solver
            .add_hard_formula(f.parse("a | b").unwrap(), &f)
            .unwrap();
        solver.add_hard_formula(f.verum(), &f).unwrap();
        solver
            .add_soft_formula(1, f.parse("a").unwrap(), &f)
            .unwrap();
        let result = solver.solve().unwrap();
        assert!(matches!(result, MaxSatResult::Optimum { .. }));
    }

    #[test]
    fn test_wbo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default()
            .algorithm(Algorithm::Wbo)
            .weight(WeightStrategy::None)
            .symmetry(Symmetry::Sym(i32::MAX));
        cs.push(c.clone());
        cs.push(c.symmetry(Symmetry::None));

        test_on_files(&cs, &f, FILES);
        test_on_files(&cs, &f, SAT_FILES);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "requires a release build because the debug build exhausts the stack"
    )]
    fn test_linear_su() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default()
            .algorithm(Algorithm::LinearSu)
            .cardinal(CardinalEncoding::Totalizer);
        cs.push(c.clone());
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_msu_3() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default()
            .algorithm(Algorithm::Msu3)
            .cardinal(CardinalEncoding::Totalizer);
        cs.push(c.clone());
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&cs, &f, FILES);
        test_on_files(&cs, &f, SAT_FILES);
    }

    #[test]
    fn test_oll() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::Oll);
        cs.push(c);

        test_on_files(&cs, &f, FILES);
        test_on_files(&cs, &f, SAT_FILES);
    }

    #[test]
    fn test_single() {
        let file = std::path::PathBuf::from("resources/maxsat/c-fat200-2.clq.cnf");
        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default()
            .algorithm(Algorithm::Msu3)
            .cardinal(CardinalEncoding::MTotalizer);

        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        read_cnf_to_solver(&mut solver, &file, &f).unwrap();
        assert_optimum(solver.solve(), 26);
    }

    #[test]
    fn test_model() {
        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Msu3);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();

        solver.add_hard_formula(f.parse("y").unwrap(), &f).unwrap();
        solver.add_hard_formula(f.parse("~z").unwrap(), &f).unwrap();
        solver
            .add_soft_formula(1, f.parse("a => b").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("b => c").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("c => d").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("d => e").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("a => x").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("~e").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("~x").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("a").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("~y").unwrap(), &f)
            .unwrap();
        solver
            .add_soft_formula(1, f.parse("z").unwrap(), &f)
            .unwrap();
        let model = assert_optimum(solver.solve(), 3);
        assert_eq!(model.len(), 8);
        assert_eq!(model.pos().len(), 1);
        assert!(model.pos().contains(&f.var("y")));
        assert_eq!(model.neg().len(), 7);
        for n in ["a", "b", "c", "d", "e", "x", "z"] {
            assert!(model.neg().contains(&f.var(n)));
        }
    }

    #[test]
    fn test_unsatisfiable_has_no_model() {
        let f = FormulaFactory::new();
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Msu3);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();

        solver
            .add_hard_formula(f.parse("a & ~a").unwrap(), &f)
            .unwrap();

        assert_eq!(solver.solve(), Ok(MaxSatResult::Unsatisfiable));
    }
}

#[cfg(test)]
mod partial_maxsat_tests {
    use super::test_on_files;
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::{Algorithm, CardinalEncoding, OpenWboConfig};

    static FILES: &[(&str, u64)] = &[
        ("resources/partialmaxsat/c1355_F176gat-1278gat@1.wcnf", 13),
        ("resources/partialmaxsat/c1355_F1001gat-1048gat@1.wcnf", 21),
        ("resources/partialmaxsat/c1355_F1183gat-1262gat@1.wcnf", 33),
        ("resources/partialmaxsat/c1355_F1229gat@1.wcnf", 33),
        ("resources/partialmaxsat/normalized-s3-3-3-1pb.wcnf", 36),
        ("resources/partialmaxsat/normalized-s3-3-3-2pb.wcnf", 36),
        ("resources/partialmaxsat/normalized-s3-3-3-3pb.wcnf", 36),
        ("resources/partialmaxsat/term1_gr_2pin_w4.shuffled.cnf", 0),
    ];

    #[test]
    fn test_wbo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::Wbo);
        cs.push(c);

        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_oll() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::Oll);
        cs.push(c);

        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_linear_su() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::LinearSu);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer).bmo(false));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer).bmo(false));
        cs.push(c.clone().cardinal(CardinalEncoding::CNetworks).bmo(false));
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer).bmo(true));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer).bmo(true));
        cs.push(c.cardinal(CardinalEncoding::CNetworks).bmo(true));

        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_msu3() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::Msu3);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&cs, &f, FILES);
    }
}

#[cfg(test)]
mod partial_weighted_tests {
    use super::{assert_optimum, test_on_files};
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::{
        Algorithm, CardinalEncoding, MaxSatSolver, OpenWboConfig, RustOpenWboFactory,
        WeightStrategy,
    };
    use std::collections::HashSet;

    static FILES: &[(&str, u64)] = &[
        ("resources/partialweightedmaxsat/8.wcsp.log.wcnf", 2),
        ("resources/partialweightedmaxsat/54.wcsp.log.wcnf", 37),
        ("resources/partialweightedmaxsat/404.wcsp.log.wcnf", 114),
        (
            "resources/partialweightedmaxsat/term1_gr_2pin_w4.shuffled.cnf",
            0,
        ),
    ];

    static BMO_FILES: &[(&str, u64)] = &[
        (
            "resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=11-Q=283.opb.wcnf",
            11,
        ),
        (
            "resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=11-Q=53.opb.wcnf",
            11,
        ),
        (
            "resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=13-Q=179.opb.wcnf",
            13,
        ),
        (
            "resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=17-Q=347.opb.wcnf",
            17,
        ),
        (
            "resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=17-Q=487.opb.wcnf",
            17,
        ),
        (
            "resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=23-Q=293.opb.wcnf",
            23,
        ),
    ];

    #[test]
    fn test_wbo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::Wbo);
        //cs.push(c.clone().weight(WeightStrategy::Normal)); //takes too long
        //cs.push(c.clone().weight(WeightStrategy::Diversify)); //takes too long
        cs.push(c.weight(WeightStrategy::None));

        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_linear_su() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default()
            .algorithm(Algorithm::LinearSu)
            .bmo(false);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_linear_su_bmo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default()
            .algorithm(Algorithm::LinearSu)
            .bmo(true);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&cs, &f, BMO_FILES);
    }

    #[test]
    fn test_oll() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = OpenWboConfig::default().algorithm(Algorithm::Oll).bmo(true);
        cs.push(c);

        test_on_files(&cs, &f, BMO_FILES);
        test_on_files(&cs, &f, FILES);
    }

    #[test]
    fn test_weighted_non_clause_soft_constraints() {
        let f = FormulaFactory::new();
        let solvers = vec![
            MaxSatSolver::from_factory(&RustOpenWboFactory::new(
                OpenWboConfig::default().algorithm(Algorithm::LinearSu),
            ))
            .unwrap(),
            MaxSatSolver::from_factory(&RustOpenWboFactory::new(
                OpenWboConfig::default().algorithm(Algorithm::Wbo),
            ))
            .unwrap(),
        ];

        for mut solver in solvers {
            solver
                .add_hard_formula(f.parse("a & b & c").unwrap(), &f)
                .unwrap();
            solver
                .add_soft_formula(2, f.parse("~a & ~b & ~c").unwrap(), &f)
                .unwrap();
            let model = assert_optimum(solver.solve(), 2);
            let literals: HashSet<_> = model.pos().iter().chain(model.neg()).collect();
            assert_eq!(literals.len(), 3);
            assert!(literals.contains(&f.var("a")));
            assert!(literals.contains(&f.var("b")));
            assert!(literals.contains(&f.var("c")));
        }
    }

    #[test]
    fn test_weighted_soft_constraints_corner_case_verum() {
        let f = FormulaFactory::new();
        let solvers = vec![
            MaxSatSolver::from_factory(&RustOpenWboFactory::new(
                OpenWboConfig::default().algorithm(Algorithm::LinearSu),
            ))
            .unwrap(),
            MaxSatSolver::from_factory(&RustOpenWboFactory::new(
                OpenWboConfig::default().algorithm(Algorithm::Wbo),
            ))
            .unwrap(),
        ];

        for mut solver in solvers {
            solver
                .add_hard_formula(f.parse("a & b & c").unwrap(), &f)
                .unwrap();
            solver
                .add_soft_formula(2, f.parse("$true").unwrap(), &f)
                .unwrap();
            solver
                .add_soft_formula(3, f.parse("~a & ~b & ~c").unwrap(), &f)
                .unwrap();
            let model = assert_optimum(solver.solve(), 3);
            let literals: HashSet<_> = model.pos().iter().chain(model.neg()).collect();
            assert_eq!(literals.len(), 3);
            assert!(literals.contains(&f.var("a")));
            assert!(literals.contains(&f.var("b")));
            assert!(literals.contains(&f.var("c")));
        }
    }

    #[test]
    fn test_weighted_soft_constraints_cors_case_falsum() {
        let f = FormulaFactory::new();
        let solvers = vec![
            MaxSatSolver::from_factory(&RustOpenWboFactory::new(
                OpenWboConfig::default().algorithm(Algorithm::LinearSu),
            ))
            .unwrap(),
            MaxSatSolver::from_factory(&RustOpenWboFactory::new(
                OpenWboConfig::default().algorithm(Algorithm::Wbo),
            ))
            .unwrap(),
        ];

        for mut solver in solvers {
            solver
                .add_hard_formula(f.parse("a & b & c").unwrap(), &f)
                .unwrap();
            solver
                .add_soft_formula(2, f.parse("$false").unwrap(), &f)
                .unwrap();
            solver
                .add_soft_formula(3, f.parse("~a & ~b & ~c").unwrap(), &f)
                .unwrap();
            let model = assert_optimum(solver.solve(), 5);
            let literals: HashSet<_> = model.pos().iter().chain(model.neg()).collect();
            assert_eq!(literals.len(), 3);
            assert!(literals.contains(&f.var("a")));
            assert!(literals.contains(&f.var("b")));
            assert!(literals.contains(&f.var("c")));
        }
    }
}

#[cfg(test)]
mod long_running_tests {
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::tests::maxsat_tests::{read_cnf_to_solver, read_result};
    use crate::solver::maxsat::{Algorithm, MaxSatSolver, OpenWboConfig, RustOpenWboFactory};

    use super::assert_optimum;

    #[test]
    fn test() {
        let f = FormulaFactory::new();
        let dir_path = std::path::PathBuf::from("resources/longrunning/wms");
        let dir = std::fs::read_dir(&dir_path).expect("Failed reading dir!");
        let result = read_result(&dir_path.join("result.txt")).expect("Failed reading result!");
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Oll);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();

        let start = std::time::Instant::now();
        for file in dir {
            let fi = file.expect("Invalid DirEntry");
            if fi.file_name().to_string_lossy().ends_with(".wcnf") {
                solver.reset();
                read_cnf_to_solver(&mut solver, &fi.path(), &f).unwrap();
                let expected_res = result[fi.file_name().to_str().unwrap()];
                assert_optimum(solver.solve(), expected_res);
            }
        }
        println!("OLL\t: {}", start.elapsed().as_secs_f32());
    }

    #[test]
    fn test_large_oll_1() {
        let f = FormulaFactory::new();
        let file_path =
            std::path::PathBuf::from("resources/partialweightedmaxsat/large/large_industrial.wcnf");
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Oll);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        read_cnf_to_solver(&mut solver, &file_path, &f).unwrap();
        assert_optimum(solver.solve(), 68974);
    }

    #[test]
    fn test_large_oll_2() {
        let f = FormulaFactory::new();
        let file_path =
            std::path::PathBuf::from("resources/partialweightedmaxsat/large/t3g3-5555.spn.wcnf");
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Oll);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        read_cnf_to_solver(&mut solver, &file_path, &f).unwrap();
        assert_optimum(solver.solve(), 1_100_610);
    }

    #[test]
    fn test_oll_large_weights() {
        let f = FormulaFactory::new();
        let file_path =
            std::path::PathBuf::from("resources/partialweightedmaxsat/large/large_weights.wcnf");
        let cfg = OpenWboConfig::default().algorithm(Algorithm::Oll);
        let mut solver = MaxSatSolver::from_factory(&RustOpenWboFactory::new(cfg)).unwrap();
        read_cnf_to_solver(&mut solver, &file_path, &f).unwrap();
        assert_optimum(solver.solve(), 90912);
    }
}

#[cfg(test)]
fn read_cnf_to_solver(
    solver: &mut MaxSatSolver,
    path: &std::path::Path,
    f: &FormulaFactory,
) -> Result<(), Box<dyn std::error::Error>> {
    let file = std::fs::File::open(path).unwrap();
    let mut lines = std::io::BufReader::new(file).lines();

    let mut pure_maxsat = false;
    let mut hard_weight: u64 = u64::MAX;
    for line in &mut lines {
        let l = line?;
        if l.starts_with("p wcnf") {
            let mut header = l.split_whitespace();
            if let Some(hw) = header.nth(4) {
                hard_weight = hw.parse()?;
            }
            break;
        } else if l.starts_with("p cnf") {
            pure_maxsat = true;
            break;
        }
    }

    for line in &mut lines {
        let l = line?;

        if l.is_empty() {
            continue;
        }

        let mut tokens = l.split_whitespace();
        let weight: Option<u64> = if pure_maxsat {
            None
        } else {
            Some(tokens.next().expect("Wrong input format!").parse::<u64>()?)
        };

        let mut lits = vec![];
        for token in tokens {
            let p_lit: i64 = token.parse()?;

            if p_lit == 0 {
                continue;
            }

            let mut var = String::from("v");
            var.push_str(&p_lit.abs().to_string());
            lits.push(f.literal(&var, p_lit > 0));
        }

        if pure_maxsat {
            solver.add_soft_formula(1, f.or(&lits), f)?;
        } else if let Some(w) = weight {
            if w == hard_weight {
                solver.add_hard_formula(f.or(&lits), f)?;
            } else {
                solver.add_soft_formula(w, f.or(&lits), f)?;
            }
        } else {
            panic!("Wring input formant!");
        }
    }
    Ok(())
}
#[allow(dead_code)]
fn read_result(path: &std::path::Path) -> Result<HashMap<String, u64>, Box<dyn std::error::Error>> {
    let mut map = HashMap::new();
    let file = std::fs::File::open(path).unwrap();
    let lines = std::io::BufReader::new(file).lines();

    for line in lines {
        let l = line?;
        let tokens: Vec<_> = l.trim().split(';').collect();
        if tokens.len() != 2 {
            continue;
        }
        map.insert(String::from(tokens[0]), tokens[1].parse()?);
    }
    Ok(map)
}

#[cfg(test)]
fn test_on_files(configs: &Vec<OpenWboConfig>, f: &FormulaFactory, source: &[(&str, u64)]) {
    for config in configs {
        for (file, result) in source {
            let mut solver =
                MaxSatSolver::from_factory(&RustOpenWboFactory::new(config.clone())).unwrap();
            let path = std::path::PathBuf::from(file);
            read_cnf_to_solver(&mut solver, &path, f).unwrap();
            assert_optimum(solver.solve(), *result);
        }
    }
}

#[cfg(test)]
fn assert_optimum(result: LngResult<MaxSatResult>, expected_bound: u64) -> Model {
    match result.unwrap() {
        MaxSatResult::Optimum { bound, model } => {
            assert_eq!(bound, expected_bound);
            model
        }
        result => panic!("expected optimum result, got {result:?}"),
    }
}

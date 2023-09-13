use crate::formulas::FormulaFactory;
use crate::solver::maxsat::{Algorithm, MaxSatResult, MaxSatSolver};
use crate::solver::maxsat_config::MaxSatConfig;
use std::collections::HashMap;
use std::io::BufRead;

mod pure_maxsat_tests {
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::{Algorithm, MaxSatResult, MaxSatSolver};
    use crate::solver::maxsat_config::{CardinalEncoding, GraphType, MaxSatConfig, MergeStrategy, Symmetry, Verbosity, WeightStrategy};
    use crate::solver::maxsat_ffi::MaxSatError;
    use crate::solver::tests::maxsat_tests::read_cnf_to_solver;

    use super::test_on_files;

    static FILES: &[(&str, u64)] = &[
        ("resources/maxsat/c5315-bug-gate-0.dimacs.seq.filtered.cnf", 1),
        ("resources/maxsat/c6288-bug-gate-0.dimacs.seq.filtered.cnf", 1),
        ("resources/maxsat/c7552-bug-gate-0.dimacs.seq.filtered.cnf", 1),
        ("resources/maxsat/mot_comb1._red-gate-0.dimacs.seq.filtered.cnf", 1),
        ("resources/maxsat/mot_comb2._red-gate-0.dimacs.seq.filtered.cnf", 1),
        ("resources/maxsat/mot_comb3._red-gate-0.dimacs.seq.filtered.cnf", 1),
        ("resources/maxsat/s15850-bug-onevec-gate-0.dimacs.seq.filtered.cnf", 1),
    ];

    static SAT_FILES: &[(&str, u64)] = &[("resources/sat/9symml_gr_rcs_w6.shuffled.cnf", 0)];

    #[test]
    fn corner_case() {
        let f = FormulaFactory::new();
        let mut solver = MaxSatSolver::new(Algorithm::Wbo).unwrap();
        solver.add_hard_formula(f.parse("a | b").unwrap(), &f).unwrap();
        solver.add_hard_formula(f.verum(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("a").unwrap(), &f).unwrap();
        let mut result = solver.solve().unwrap();
        assert!(matches!(result, MaxSatResult::Optimum(_)));
        result = solver.solve().unwrap();
        assert!(matches!(result, MaxSatResult::Optimum(_)));
    }

    #[test]
    fn test_wbo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().weight(WeightStrategy::None).symmetry(Symmetry::Sym(i32::MAX)).verbosity(Verbosity::None);
        cs.push(c.clone());
        cs.push(c.symmetry(Symmetry::None));

        test_on_files(&Algorithm::Wbo, &cs, &f, FILES);
        test_on_files(&Algorithm::Wbo, &cs, &f, SAT_FILES);
    }

    #[test]
    fn test_linear_su() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().cardinal(CardinalEncoding::Totalizer).verbosity(Verbosity::None);
        cs.push(c.clone());
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&Algorithm::LinearSu, &cs, &f, FILES);
    }

    #[test]
    fn test_msu_3() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().cardinal(CardinalEncoding::Totalizer).verbosity(Verbosity::None);
        cs.push(c.clone());
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&Algorithm::Msu3, &cs, &f, FILES);
        test_on_files(&Algorithm::Msu3, &cs, &f, SAT_FILES);
    }

    #[test]
    fn test_part_msu_3() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().cardinal(CardinalEncoding::Totalizer).verbosity(Verbosity::None);
        cs.push(c.clone().merge(MergeStrategy::Sequential).graph(GraphType::Res));
        cs.push(c.clone().merge(MergeStrategy::Sequential).graph(GraphType::CVig));
        cs.push(c.clone().merge(MergeStrategy::Sequential).graph(GraphType::Vig));
        cs.push(c.clone().merge(MergeStrategy::Binary).graph(GraphType::Res));
        cs.push(c.clone().merge(MergeStrategy::Binary).graph(GraphType::CVig));
        cs.push(c.clone().merge(MergeStrategy::Binary).graph(GraphType::Vig));
        cs.push(c.clone().merge(MergeStrategy::SequentialSorted).graph(GraphType::Res));
        cs.push(c.clone().merge(MergeStrategy::SequentialSorted).graph(GraphType::CVig));
        cs.push(c.merge(MergeStrategy::SequentialSorted).graph(GraphType::Vig));

        test_on_files(&Algorithm::PartMsu3, &cs, &f, FILES);
        test_on_files(&Algorithm::PartMsu3, &cs, &f, SAT_FILES);
    }

    #[test]
    fn test_oll() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default();
        cs.push(c);

        test_on_files(&Algorithm::Oll, &cs, &f, FILES);
        test_on_files(&Algorithm::Oll, &cs, &f, SAT_FILES);
    }

    #[test]
    fn test_single() {
        let file = std::path::PathBuf::from("resources/maxsat/c-fat200-2.clq.cnf");
        let f = FormulaFactory::new();
        let c = MaxSatConfig::default().cardinal(CardinalEncoding::MTotalizer).verbosity(Verbosity::None);

        let mut solver = MaxSatSolver::from_config(Algorithm::Msu3, c).unwrap();
        read_cnf_to_solver(&mut solver, &file, &f).unwrap();
        assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(26)));
    }

    #[test]
    fn test_assignment() {
        let config = MaxSatConfig::default().verbosity(Verbosity::None);
        let f = FormulaFactory::new();
        let mut solver = MaxSatSolver::from_config(Algorithm::Msu3, config).unwrap();

        solver.add_hard_formula(f.parse("y").unwrap(), &f).unwrap();
        solver.add_hard_formula(f.parse("~z").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("a => b").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("b => c").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("c => d").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("d => e").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("a => x").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("~e").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("~x").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("a").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("~y").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("z").unwrap(), &f).unwrap();
        assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(3)));

        let model = solver.assignment().unwrap();
        assert_eq!(model.len(), 8);
        assert_eq!(model.pos.len(), 1);
        assert!(model.contains_pos(f.var("y")));
        assert_eq!(model.neg.len(), 7);
        for n in &["a", "b", "c", "d", "e", "x", "z"] {
            assert!(model.contains_neg(f.var(n)));
        }
    }

    #[test]
    fn test_illegal_model() {
        let config = MaxSatConfig::default().verbosity(Verbosity::None);
        let f = FormulaFactory::new();
        let mut solver = MaxSatSolver::from_config(Algorithm::Msu3, config).unwrap();

        solver.add_soft_formula(1, f.parse("a => b").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("b => c").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("c => d").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("d => e").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("a => x").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("~e").unwrap(), &f).unwrap();
        solver.add_soft_formula(1, f.parse("~x").unwrap(), &f).unwrap();

        assert_eq!(solver.model().unwrap_err(), MaxSatError::IllegalModelRequest);
    }
}

mod partial_maxsat_tests {
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::Algorithm;
    use crate::solver::maxsat_config::{CardinalEncoding, GraphType, MaxSatConfig, MergeStrategy, Verbosity};

    use super::test_on_files;

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
        let c = MaxSatConfig::default().verbosity(Verbosity::None);
        cs.push(c);

        test_on_files(&Algorithm::Wbo, &cs, &f, FILES);
    }

    #[test]
    fn test_oll() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None);
        cs.push(c);

        test_on_files(&Algorithm::Oll, &cs, &f, FILES);
    }

    #[test]
    fn test_linear_su() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer).bmo(false));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer).bmo(false));
        cs.push(c.clone().cardinal(CardinalEncoding::CNetworks).bmo(false));
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer).bmo(true));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer).bmo(true));
        cs.push(c.cardinal(CardinalEncoding::CNetworks).bmo(true));

        test_on_files(&Algorithm::LinearSu, &cs, &f, FILES);
    }

    #[test]
    fn test_msu3() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&Algorithm::Msu3, &cs, &f, FILES);
    }

    #[test]
    fn test_part_msu3() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().cardinal(CardinalEncoding::Totalizer).verbosity(Verbosity::None);
        cs.push(c.clone().merge(MergeStrategy::Sequential).graph(GraphType::Res));
        cs.push(c.clone().merge(MergeStrategy::Sequential).graph(GraphType::CVig));
        cs.push(c.clone().merge(MergeStrategy::Sequential).graph(GraphType::Vig));
        cs.push(c.clone().merge(MergeStrategy::Binary).graph(GraphType::Res));
        cs.push(c.clone().merge(MergeStrategy::Binary).graph(GraphType::CVig));
        cs.push(c.clone().merge(MergeStrategy::Binary).graph(GraphType::Vig));
        cs.push(c.clone().merge(MergeStrategy::SequentialSorted).graph(GraphType::Res));
        cs.push(c.clone().merge(MergeStrategy::SequentialSorted).graph(GraphType::CVig));
        cs.push(c.merge(MergeStrategy::SequentialSorted).graph(GraphType::Vig));

        test_on_files(&Algorithm::PartMsu3, &cs, &f, FILES);
    }
}

mod partial_weighted_tests {
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::{Algorithm, MaxSatResult, MaxSatSolver};
    use crate::solver::maxsat_config::{CardinalEncoding, MaxSatConfig, Verbosity, WeightStrategy};
    use std::collections::HashSet;

    use super::test_on_files;

    static FILES: &[(&str, u64)] = &[
        ("resources/partialweightedmaxsat/8.wcsp.log.wcnf", 2),
        ("resources/partialweightedmaxsat/54.wcsp.log.wcnf", 37),
        ("resources/partialweightedmaxsat/404.wcsp.log.wcnf", 114),
        ("resources/partialweightedmaxsat/term1_gr_2pin_w4.shuffled.cnf", 0),
    ];

    static BMO_FILES: &[(&str, u64)] = &[
        ("resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=11-Q=283.opb.wcnf", 11),
        ("resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=11-Q=53.opb.wcnf", 11),
        ("resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=13-Q=179.opb.wcnf", 13),
        ("resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=17-Q=347.opb.wcnf", 17),
        ("resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=17-Q=487.opb.wcnf", 17),
        ("resources/partialweightedmaxsat/bmo/normalized-factor-size=9-P=23-Q=293.opb.wcnf", 23),
    ];

    #[test]
    fn test_wbo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None);
        //cs.push(c.clone().weight(WeightStrategy::Normal)); //takes too long
        //cs.push(c.clone().weight(WeightStrategy::Diversify)); //takes too long
        cs.push(c.weight(WeightStrategy::None));

        test_on_files(&Algorithm::Wbo, &cs, &f, FILES);
    }

    #[test]
    fn test_linear_su() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None).bmo(false);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&Algorithm::LinearSu, &cs, &f, FILES);
    }

    #[test]
    fn test_linear_su_bmo() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None).bmo(true);
        cs.push(c.clone().cardinal(CardinalEncoding::Totalizer));
        cs.push(c.clone().cardinal(CardinalEncoding::MTotalizer));
        cs.push(c.cardinal(CardinalEncoding::CNetworks));

        test_on_files(&Algorithm::LinearSu, &cs, &f, BMO_FILES);
    }

    #[test]
    fn test_oll() {
        let f = FormulaFactory::new();
        let mut cs = vec![];
        let c = MaxSatConfig::default().verbosity(Verbosity::None).bmo(true);
        cs.push(c);

        test_on_files(&Algorithm::LinearSu, &cs, &f, BMO_FILES);
        test_on_files(&Algorithm::LinearSu, &cs, &f, FILES);
    }

    #[test]
    fn test_weighted_non_clause_soft_constraints() {
        let f = FormulaFactory::new();
        let solvers = vec![MaxSatSolver::new(Algorithm::LinearSu).unwrap(), MaxSatSolver::new(Algorithm::Wbo).unwrap()];

        for mut solver in solvers {
            solver.add_hard_formula(f.parse("a & b & c").unwrap(), &f).unwrap();
            solver.add_soft_formula(2, f.parse("~a & ~b & ~c").unwrap(), &f).unwrap();
            assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(2)));
            let model = solver.assignment().unwrap();
            let literals: HashSet<_> = model.pos.union(&model.neg).collect();
            assert_eq!(literals.len(), 3);
            assert!(literals.contains(&f.var("a")));
            assert!(literals.contains(&f.var("b")));
            assert!(literals.contains(&f.var("c")));
        }
    }

    #[test]
    fn test_weighted_soft_constraints_corner_case_verum() {
        let f = FormulaFactory::new();
        let solvers = vec![MaxSatSolver::new(Algorithm::LinearSu).unwrap(), MaxSatSolver::new(Algorithm::Wbo).unwrap()];

        for mut solver in solvers {
            solver.add_hard_formula(f.parse("a & b & c").unwrap(), &f).unwrap();
            solver.add_soft_formula(2, f.parse("$true").unwrap(), &f).unwrap();
            solver.add_soft_formula(3, f.parse("~a & ~b & ~c").unwrap(), &f).unwrap();
            assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(3)));
            let model = solver.assignment().unwrap();
            let literals: HashSet<_> = model.pos.union(&model.neg).collect();
            assert_eq!(literals.len(), 3);
            assert!(literals.contains(&f.var("a")));
            assert!(literals.contains(&f.var("b")));
            assert!(literals.contains(&f.var("c")));
        }
    }

    #[test]
    fn test_weighted_soft_constraints_cors_case_falsum() {
        let f = FormulaFactory::new();
        let solvers = vec![MaxSatSolver::new(Algorithm::LinearSu).unwrap(), MaxSatSolver::new(Algorithm::Wbo).unwrap()];

        for mut solver in solvers {
            solver.add_hard_formula(f.parse("a & b & c").unwrap(), &f).unwrap();
            solver.add_soft_formula(2, f.parse("$false").unwrap(), &f).unwrap();
            solver.add_soft_formula(3, f.parse("~a & ~b & ~c").unwrap(), &f).unwrap();
            assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(5)));
            let model = solver.assignment().unwrap();
            let literals: HashSet<_> = model.pos.union(&model.neg).collect();
            assert_eq!(literals.len(), 3);
            assert!(literals.contains(&f.var("a")));
            assert!(literals.contains(&f.var("b")));
            assert!(literals.contains(&f.var("c")));
        }
    }
}

mod long_running_tests {
    use crate::formulas::FormulaFactory;
    use crate::solver::maxsat::{Algorithm, MaxSatResult, MaxSatSolver};
    use crate::solver::tests::maxsat_tests::{read_cnf_to_solver, read_result};

    #[test]
    fn test() {
        let f = FormulaFactory::new();
        let dir_path = std::path::PathBuf::from("resources/longrunning/wms");
        let dir = std::fs::read_dir(&dir_path).expect("Failed reading dir!");
        let result = read_result(&dir_path.join("result.txt")).expect("Failed reading result!");
        let mut solver = MaxSatSolver::new(Algorithm::Oll).expect("Failed to build solver!");

        let start = std::time::Instant::now();
        for file in dir {
            let fi = file.expect("Invalid DirEntry");
            if fi.file_name().to_string_lossy().ends_with(".wcnf") {
                solver.reset();
                read_cnf_to_solver(&mut solver, &fi.path(), &f).unwrap();
                let expected_res = result[fi.file_name().to_str().unwrap()];
                assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(expected_res)));
            }
        }
        println!("OLL\t: {}", start.elapsed().as_secs_f32());
    }

    #[test]
    fn test_large_oll_1() {
        let f = FormulaFactory::new();
        let file_path = std::path::PathBuf::from("resources/partialweightedmaxsat/large/large_industrial.wcnf");
        let mut solver = MaxSatSolver::new(Algorithm::Oll).unwrap();
        read_cnf_to_solver(&mut solver, &file_path, &f).unwrap();
        assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(68974)));
    }

    #[test]
    fn test_large_oll_2() {
        let f = FormulaFactory::new();
        let file_path = std::path::PathBuf::from("resources/partialweightedmaxsat/large/t3g3-5555.spn.wcnf");
        let mut solver = MaxSatSolver::new(Algorithm::Oll).unwrap();
        read_cnf_to_solver(&mut solver, &file_path, &f).unwrap();
        assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(1_100_610)));
    }

    #[test]
    fn test_oll_large_weights() {
        let f = FormulaFactory::new();
        let file_path = std::path::PathBuf::from("resources/partialweightedmaxsat/large/large_weights.wcnf");
        let mut solver = MaxSatSolver::new(Algorithm::Oll).unwrap();
        read_cnf_to_solver(&mut solver, &file_path, &f).unwrap();
        assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(90912)));
    }
}

fn read_cnf_to_solver(solver: &mut MaxSatSolver, path: &std::path::Path, f: &FormulaFactory) -> Result<(), Box<dyn std::error::Error>> {
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
        let weight: Option<u64> = if pure_maxsat { None } else { Some(tokens.next().expect("Wrong input format!").parse::<u64>()?) };

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

fn test_on_files(algorithm: &Algorithm, configs: &Vec<MaxSatConfig>, f: &FormulaFactory, source: &[(&str, u64)]) {
    for config in configs {
        for (file, result) in source {
            let mut solver = MaxSatSolver::from_config(algorithm.clone(), config.clone()).unwrap();
            let path = std::path::PathBuf::from(file);
            read_cnf_to_solver(&mut solver, &path, f).unwrap();
            assert_eq!(solver.solve(), Ok(MaxSatResult::Optimum(*result)));
        }
    }
}

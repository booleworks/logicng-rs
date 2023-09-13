mod drup_tests {
    use crate::explanations::unsat_core::UnsatCore;
    use crate::formulas::{EncodedFormula, FormulaFactory, ToFormula};
    use crate::io::{read_cnf, read_cnf_with_prefix};
    use crate::propositions::Proposition;
    use crate::solver::minisat::sat::Tristate::{False, True};
    use crate::solver::minisat::SolverCnfMethod::{FactoryCnf, PgOnSolver};
    use crate::solver::minisat::{MiniSat, MiniSatConfig, SatBuilder};
    use std::collections::HashSet;
    use std::fs::read_dir;

    fn solvers() -> [MiniSat; 2] {
        [
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(true).cnf_method(FactoryCnf)),
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(false).cnf_method(FactoryCnf)),
        ]
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore)]
    pub fn test_unsat_core_from_dimacs() {
        let f = FormulaFactory::new();
        let cnfs = [
            read_cnf("resources/drup/simple_input.cnf", &f).unwrap(),
            read_cnf("resources/drup/pg4_input.cnf", &f).unwrap(),
            read_cnf_with_prefix("resources/drup/avg_input.cnf", &f, "var").unwrap(),
        ];
        let solvers = solvers();
        for mut solver in solvers {
            for cnf in &cnfs {
                solver.add_all(cnf, &f);
                assert_eq!(solver.sat(), False);
                let unsat_core = solver.unsat_core(&f);
                verify_core(&unsat_core, cnf, &f);
                solver.reset();
            }
        }
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore)]
    pub fn test_unsat_cores_from_large_testset() {
        let f = &FormulaFactory::new();
        let mut count = 0;
        let mut solvers = solvers();
        for solver in &mut solvers {
            for path_result in read_dir("resources/sat").unwrap() {
                let path = path_result.unwrap().path();
                let extension = path.extension().map_or("", |s| s.to_str().unwrap());
                if extension == "cnf" {
                    let cnf = read_cnf(path.to_str().unwrap(), f).unwrap();
                    solver.add_all(&cnf, f);
                    if solver.sat() == False {
                        let unsat_core = solver.unsat_core(f);
                        verify_core(&unsat_core, &cnf, f);
                        count += 1;
                    }
                }
                solver.reset();
            }
        }
        assert_eq!(count, 11 * solvers.len());
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore)]
    pub fn test_unsat_cores_aim_testset() {
        let f = &FormulaFactory::new();
        let mut solvers = solvers();
        for solver in &mut solvers {
            for path_result in read_dir("resources/sat/unsat").unwrap() {
                let path = path_result.unwrap().path();
                let extension = path.extension().map_or("", |s| s.to_str().unwrap());
                if extension == "cnf" {
                    let cnf = read_cnf(path.to_str().unwrap(), f).unwrap();
                    solver.add_all(&cnf, f);
                    assert_eq!(solver.sat(), False);
                    let unsat_core = solver.unsat_core(f);
                    verify_core(&unsat_core, &cnf, f);
                }
                solver.reset();
            }
        }
    }

    #[test]
    pub fn test_proposition_handling() {
        let f = &FormulaFactory::new();
        let propositions = [
            &Proposition::new("((a & b) => c) &  ((a & b) => d)".to_formula(f)).description("P1"),
            &Proposition::new("(c & d) <=> ~e".to_formula(f)).description("P2"),
            &Proposition::new("~e => f | g".to_formula(f)).description("P3"),
            &Proposition::new("(f => ~a) & (g => ~b) & p & q".to_formula(f)).description("P4"),
            &Proposition::new("a => b".to_formula(f)).description("P5"),
            &Proposition::new("a".to_formula(f)).description("P6"),
            &Proposition::new("g | h".to_formula(f)).description("P7"),
            &Proposition::new("(x => ~y | z) & (z | w)".to_formula(f)).description("P8"),
            &Proposition::new("a1 | a2".to_formula(f)).description("P9"),
        ];

        for mut solver in solvers() {
            solver.add_propositions(&propositions, f);
            assert_eq!(solver.sat(), False);
            let unsat_core = solver.unsat_core(f);
            let expected_result = [
                propositions[0].clone(),
                propositions[1].clone(),
                propositions[2].clone(),
                propositions[3].clone(),
                propositions[4].clone(),
                propositions[5].clone(),
            ];
            assert_eq!(unsat_core.propositions.len(), expected_result.len());
            assert!(unsat_core.propositions.iter().all(|p| expected_result.contains(p)));
        }
    }

    #[test]
    pub fn test_proposition_inc_dec() {
        let f = &FormulaFactory::new();
        let p1 = &Proposition::new("((a & b) => c) &  ((a & b) => d)".to_formula(f)).description("P1");
        let p2 = &Proposition::new("(c & d) <=> ~e".to_formula(f)).description("P2");
        let p3 = &Proposition::new("~e => f | g".to_formula(f)).description("P3");
        let p4 = &Proposition::new("(f => ~a) & (g => ~b) & p & q".to_formula(f)).description("P4");
        let p5 = &Proposition::new("a => b".to_formula(f)).description("P5");
        let p6 = &Proposition::new("a".to_formula(f)).description("P6");
        let p7 = &Proposition::new("g | h".to_formula(f)).description("P7");
        let p8 = &Proposition::new("(x => ~y | z) & (z | w)".to_formula(f)).description("P8");
        let p9 = &Proposition::new("a & b".to_formula(f)).description("P9");
        let p10 = &Proposition::new("(p => q) & p".to_formula(f)).description("P10");
        let p11 = &Proposition::new("a & ~q".to_formula(f)).description("P11");

        let solver = &mut solvers()[0];
        solver.add_propositions(&[p1, p2, p3, p4], f);
        let state1 = solver.save_state();
        solver.add_propositions(&[p5, p6], f);
        let state2 = solver.save_state();
        solver.add_propositions(&[p7, p8], f);

        assert_unsat_core(solver, &[p1, p2, p3, p4, p5, p6], f);

        solver.load_state(&state2);
        assert_unsat_core(solver, &[p1, p2, p3, p4, p5, p6], f);

        solver.load_state(&state1);
        solver.add_proposition(p9, f);
        assert_unsat_core(solver, &[p1, p2, p3, p4, p9], f);

        solver.load_state(&state1);
        solver.add_proposition(p5, f);
        solver.add_proposition(p6, f);
        assert_unsat_core(solver, &[p1, p2, p3, p4, p5, p6], f);

        solver.load_state(&state1);
        solver.add_proposition(p10, f);
        solver.add_proposition(p11, f);
        assert_unsat_core(solver, &[p4, p11], f);
    }

    #[test]
    pub fn test_trivial_cases_propositions() {
        let f = &FormulaFactory::new();
        for mut solver in solvers() {
            assert_eq!(solver.sat(), True);
            let p1 = Proposition::new(f.falsum()).description("P1");
            solver.add_proposition(&p1, f);
            assert_unsat_core(&mut solver, &[&p1], f);

            solver.reset();
            assert_eq!(solver.sat(), True);
            let p2 = Proposition::new(f.variable("a")).description("P2");
            solver.add_proposition(&p2, f);
            assert_eq!(solver.sat(), True);
            let p3 = Proposition::new(f.literal("a", false)).description("P3");
            solver.add_proposition(&p3, f);
            assert_unsat_core(&mut solver, &[&p2, &p3], f);
        }
    }

    #[test]
    fn test_core_and_assumptions() {
        let f = &FormulaFactory::new();
        let solvers = [
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(true).cnf_method(PgOnSolver)),
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(false).cnf_method(PgOnSolver)),
        ];

        for mut solver in solvers {
            let p1 = Proposition::new("A => B".to_formula(f));
            let p2 = Proposition::new("A & B => G".to_formula(f));
            let p3 = Proposition::new("~X | A".to_formula(f));
            let p4 = Proposition::new("~X | ~G".to_formula(f));
            let p5 = Proposition::new("~G".to_formula(f));
            let p6 = Proposition::new("A".to_formula(f));
            solver.add_proposition(&p1, f);
            solver.add_proposition(&p2, f);
            solver.add_proposition(&p3, f);
            solver.add_proposition(&p4, f);

            solver.sat_with(&SatBuilder::new().assumption(f.lit("X", true)));

            solver.add_proposition(&p5, f);
            solver.add_proposition(&p6, f);
            solver.sat();
            assert_unsat_core(&mut solver, &[&p1, &p2, &p5, &p6], f);
        }
    }

    #[test]
    fn test_core_and_assumptions2() {
        let f = &FormulaFactory::new();
        let solvers = [
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(true).cnf_method(PgOnSolver)),
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(false).cnf_method(PgOnSolver)),
        ];

        for mut solver in solvers {
            solver.add_proposition(&Proposition::new("~C => D".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("C => D".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("D => B | A".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("B => X".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("B => ~X".to_formula(f)), f);

            solver.sat_with(&SatBuilder::new().assumption(f.lit("A", true)));

            solver.add_proposition(&Proposition::new("~A".to_formula(f)), f);
            solver.sat();
            assert!(!solver.unsat_core(f).propositions.is_empty());
        }
    }

    #[test]
    fn test_core_and_assumptions3() {
        // Unit test for DRUP issue which led to java.lang.ArrayIndexOutOfBoundsException: -1
        let f = &FormulaFactory::new();
        let solvers = [
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(true).cnf_method(PgOnSolver)),
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(false).cnf_method(PgOnSolver)),
        ];

        for mut solver in solvers {
            solver.add_proposition(&Proposition::new("X => Y".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("X => Z".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("C => E".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("D => ~F".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("B => M".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("D => N".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("G => O".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("A => B".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("T1 <=> A & K & ~B & ~C".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("T2 <=> A & B & C & K".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("T1 + T2 = 1".to_formula(f)), f);
            solver.sat(); // required for DRUP issue

            solver.add_proposition(&Proposition::new("Y => ~X & D".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("X".to_formula(f)), f);

            solver.sat();
            assert!(!solver.unsat_core(f).propositions.is_empty());
        }
    }

    #[test]
    fn test_core_and_assumptions4() {
        let f = &FormulaFactory::new();
        let solvers = [
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(true).cnf_method(PgOnSolver)),
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(false).cnf_method(PgOnSolver)),
        ];

        for mut solver in solvers {
            solver.add_proposition(&Proposition::new("~X1".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("X1".to_formula(f)), f); // caused the bug
            solver.add_proposition(&Proposition::new("A1".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("A1 => A2".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("R & A2 => A3".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("L & A2 => A3".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("R & A3 => A4".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("L & A3 => A4".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("~A4".to_formula(f)), f);
            solver.add_proposition(&Proposition::new("L | R".to_formula(f)), f);
            solver.sat();
            assert!(!solver.unsat_core(f).propositions.is_empty());
        }
    }

    #[test]
    fn test_with_cc_propositions() {
        let f = &FormulaFactory::new();
        let mut solver = MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).cnf_method(PgOnSolver));

        let p1 = Proposition::new("A + B + C <= 1".to_formula(f)).description("CC");
        let p2 = Proposition::new("A".to_formula(f));
        let p3 = Proposition::new("B".to_formula(f));
        let p4 = Proposition::new("X & Y".to_formula(f));
        solver.add_proposition(&p1, f);
        solver.add_proposition(&p2, f);
        solver.add_proposition(&p3, f);
        solver.add_proposition(&p4, f);
        assert_unsat_core(&mut solver, &[&p1, &p2, &p3], f);
    }

    #[test]
    fn test_with_special_unit_case_mini_sat() {
        let f = &FormulaFactory::new();
        let solvers = [
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(true).cnf_method(PgOnSolver)),
            MiniSat::new_with_config(MiniSatConfig::default().proof_generation(true).incremental(false).cnf_method(PgOnSolver)),
        ];

        for mut solver in solvers {
            let p1 = Proposition::new("a => b".to_formula(f));
            let p2 = Proposition::new("a => c | d".to_formula(f));
            let p3 = Proposition::new("b => c | d".to_formula(f));
            let p4 = Proposition::new("e | f | g | h => i".to_formula(f));
            let p5 = Proposition::new("~j => k | j".to_formula(f));
            let p6 = Proposition::new("b => ~(e | f)".to_formula(f));
            let p7 = Proposition::new("c => ~j".to_formula(f));
            let p8 = Proposition::new("l | m => ~i".to_formula(f));
            let p9 = Proposition::new("j => (f + g + h = 1)".to_formula(f));
            let p10 = Proposition::new("d => (l + m + e + f = 1)".to_formula(f));
            let p11 = Proposition::new("~k".to_formula(f));
            solver.add_propositions(&[&p1, &p2, &p3, &p4, &p5, &p6, &p7, &p8, &p9, &p10, &p11], f);
            assert_eq!(True, solver.sat());
            solver.add("a".to_formula(f), f);
            assert_unsat_core(&mut solver, &[&p1, &p2, &p4, &p5, &p6, &p7, &p8, &p9, &p10, &p11, &Proposition::new("a".to_formula(f))], f);
        }
    }

    fn verify_core(original_core: &UnsatCore, cnf: &[EncodedFormula], f: &FormulaFactory) {
        let core: Vec<EncodedFormula> = original_core.propositions.iter().map(|p| p.formula).collect();
        let cnf_set: HashSet<EncodedFormula> = cnf.iter().map(EncodedFormula::clone).collect();
        assert!(core.iter().all(|c| cnf_set.contains(c)), "Core must contain only original clauses");
        let mut solver = MiniSat::new();
        solver.add_all(&core, f);
        assert_eq!(solver.sat(), False, "Core must be unsatisfiable");
    }

    fn assert_unsat_core(solver: &mut MiniSat, expected: &[&Proposition], f: &FormulaFactory) {
        assert_eq!(solver.sat(), False);
        assert_eq!(
            solver.unsat_core(f).propositions.iter().cloned().collect::<HashSet<Proposition>>(),
            expected.iter().map(|&p| p.clone()).collect::<HashSet<Proposition>>()
        );
    }
}

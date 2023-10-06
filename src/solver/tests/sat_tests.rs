use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader};

use crate::datastructures::{Assignment, Model};
use crate::formulas::CType::{EQ, GE};
use crate::formulas::{EncodedFormula, FormulaFactory, Literal, ToFormula, Variable};
use crate::io::read_cnf;
use crate::solver::functions::{enumerate_models, enumerate_models_with_config, ModelEnumerationConfig};
use crate::solver::minisat::sat::ClauseMinimization;
use crate::solver::minisat::sat::Tristate::{False, True};
use crate::solver::minisat::SolverCnfMethod::{FactoryCnf, FullPgOnSolver, PgOnSolver};
use crate::solver::minisat::{MiniSat, MiniSatConfig, SatBuilder};
use crate::solver::tests::generate_pigeon_hole;
use crate::util::test_util::{lits, lits_list, vars_list};

fn solvers() -> [MiniSat; 5] {
    [
        MiniSat::new_with_config(MiniSatConfig::default().cnf_method(FactoryCnf).incremental(true)),
        MiniSat::new_with_config(MiniSatConfig::default().cnf_method(FactoryCnf).incremental(false)),
        MiniSat::new_with_config(MiniSatConfig::default().cnf_method(PgOnSolver)),
        MiniSat::new_with_config(MiniSatConfig::default().cnf_method(PgOnSolver).auxiliary_variables_in_models(false)),
        MiniSat::new_with_config(MiniSatConfig::default().cnf_method(FullPgOnSolver).auxiliary_variables_in_models(false)),
    ]
}

#[test]
fn test_true() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add(f.verum(), f);
        assert_eq!(solver.sat(), True);
        assert_eq!(solver.model(None).unwrap().len(), 0);
    }
}

#[test]
fn test_false() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add(f.falsum(), f);
        assert_eq!(solver.sat(), False);
        assert!(solver.model(None).is_none());
    }
}

#[test]
fn test_literals() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("a".to_formula(f), f);
        assert_eq!(solver.sat(), True);
        assert_eq!(solver.model(None).unwrap().literals(), Model::from_names(&["a"], &[], f).unwrap().literals());
        solver.add("~a".to_formula(f), f);
        assert_eq!(solver.sat(), False);
        solver.reset();
        solver.add("~a".to_formula(f), f);
        assert_eq!(solver.sat(), True);
        assert_eq!(solver.model(None).unwrap().literals(), Model::from_names(&[], &["a"], f).unwrap().literals());
    }
}

#[test]
fn test_and1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("a & b".to_formula(f), f);
        assert_eq!(solver.sat(), True);
        let model = Assignment::from(solver.model(None).unwrap());
        assert_eq!(model.len(), 2);
        assert!(model.evaluate_lit(f.lit("a", true)));
        assert!(model.evaluate_lit(f.lit("b", true)));
        solver.add("~(a & b)".to_formula(f), f);
        assert_eq!(solver.sat(), False);
        assert!(solver.model(None).is_none());
    }
}

#[test]
fn test_and2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("a & ~b & c & ~d".to_formula(f), f);
        assert_eq!(solver.sat(), True);
        let model = Assignment::from(solver.model(None).unwrap());
        assert_eq!(model.len(), 4);
        assert!(model.evaluate_lit(f.lit("a", true)));
        assert!(!model.evaluate_lit(f.lit("b", true)));
        assert!(model.evaluate_lit(f.lit("c", true)));
        assert!(!model.evaluate_lit(f.lit("d", true)));
    }
}

#[test]
fn test_and3() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("a".to_formula(f), f);
        solver.add("~b".to_formula(f), f);
        solver.add("~a".to_formula(f), f);
        solver.add("d".to_formula(f), f);
        assert_eq!(solver.sat(), False);
        solver.reset();
        assert_eq!(solver.sat(), True);
        solver.add_all(&["a".to_formula(f), "~b".to_formula(f), "~a".to_formula(f), "d".to_formula(f)], f);
        assert_eq!(solver.sat(), False);
    }
}

#[test]
fn test_formula1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("(x => y) & (~x => y) & (y => z) & (z => ~x)".to_formula(f), f);
        assert_eq!(solver.sat(), True);
        let model = Assignment::from(solver.model(None).unwrap());
        assert_eq!(model.len(), 3);
        assert!(!model.evaluate_lit(f.lit("x", true)));
        assert!(model.evaluate_lit(f.lit("y", true)));
        assert!(model.evaluate_lit(f.lit("z", true)));
        solver.add(f.literal("x", true), f);
        assert_eq!(solver.sat(), False);
    }
}

#[test]
fn test_formula2() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        if solver.config.incremental {
            solver.add("(x => y) & (~x => y) & (y => z) & (z => ~x)".to_formula(f), f);
            let models = enumerate_models(&mut solver);
            assert_eq!(models.len(), 1);
            let model = Assignment::from(&models[0]);
            assert!(!model.evaluate_lit(f.lit("x", true)));
            assert!(model.evaluate_lit(f.lit("y", true)));
            assert!(model.evaluate_lit(f.lit("z", true)));
            solver.add(f.literal("x", true), f);
            assert_eq!(solver.sat(), False);
        }
    }
}

#[test]
fn test_formula3() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        if solver.config.incremental {
            solver.add("a | b".to_formula(f), f);
            let models = enumerate_models(&mut solver);
            assert_eq!(models.len(), 3);
            assert_eq!(models[0].len(), 2);
            assert_eq!(models[1].len(), 2);
            assert_eq!(models[2].len(), 2);
        }
    }
}

#[test]
fn test_cc1() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        if solver.config.incremental {
            let vars = (0..100).map(|i| f.var(&format!("x{i}"))).collect::<Box<[_]>>();
            solver.add(f.exo(vars), f);
            let models = enumerate_models(&mut solver);
            assert_eq!(models.len(), 100);
            assert!(models.iter().all(|m| m.pos().len() == 1));
        }
    }
}

#[test]
fn test_pbc() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        let mut lits = vec![];
        let mut coeffs = vec![];
        for i in 0..5 {
            lits.push(f.lit(&format!("x{i}"), i % 2 == 0));
            coeffs.push(i + 1);
        }
        solver.add(f.pbc(GE, 10, lits, coeffs), f);
        assert_eq!(solver.sat(), True);
    }
}

#[test]
fn test_partial_model() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add("a".to_formula(f), f);
        solver.add("b".to_formula(f), f);
        solver.add("c".to_formula(f), f);
        let relevant_vars = [f.var("a"), f.var("b")].to_vec();
        assert_eq!(solver.sat(), True);
        let model = solver.model(Some(&relevant_vars)).unwrap();
        assert!(model.neg().is_empty());
        assert!(!model.literals().contains(&f.lit("c", true)));
    }
}

#[test]
fn test_variables_removed_by_simplification_occurs_in_models() {
    let f = &FormulaFactory::new();
    let mut solver = MiniSat::new_with_config(MiniSatConfig::default().cnf_method(PgOnSolver));
    let a = f.var("A");
    let b = f.var("B");
    let formula = "A & B => A".to_formula(f);
    solver.add(formula, f);
    assert_eq!(True, solver.sat());
    assert_eq!(vec![a, b], solver.known_variables());
    assert_eq!(vec![a, b], solver.model(None).unwrap().literals().iter().map(Literal::variable).collect::<Vec<Variable>>());
}

#[test]
fn test_unknown_variable_not_occurring_in_model() {
    let f = &FormulaFactory::new();
    let mut solver = MiniSat::new();
    let a = "A".to_formula(f);
    solver.add(a, f);
    assert_eq!(True, solver.sat());
    assert_eq!(
        vec![f.var("A")],
        solver.model(Some(&[f.var("A"), f.var("B")])).unwrap().literals().iter().map(Literal::variable).collect::<Vec<Variable>>()
    );
}

// @Test
//     public void testModelEnumerationHandler() {
//         for (final SATSolver s : this.solvers) {
//             s.add(this.IMP3);
//             try {
//                 final ModelEnumerationHandler handler = new ModelEnumerationHandler() {
//                     private boolean aborted;
//
//                     @Override
//                     public boolean aborted() {
//                         return this.aborted;
//                     }
//
//                     @Override
//                     public void started() {
//                         this.aborted = false;
//                     }
//
//                     @Override
//                     public SATHandler satHandler() {
//                         return null;
//                     }
//
//                     @Override
//                     public boolean foundModel(final Assignment assignment) {
//                         this.aborted = assignment.negativeLiterals().isEmpty();
//                         return !this.aborted;
//                     }
//                 };
//                 final List<Assignment> models = s.execute(ModelEnumerationFunction.builder().handler(handler).build());
//                 assertThat(models.isEmpty()).isFalse();
//                 assertThat(models.get(models.size() - 1).negativeLiterals().isEmpty()).isTrue();
//                 models.remove(models.size() - 1);
//                 for (final Assignment model : models) {
//                     assertThat(model.negativeLiterals().isEmpty()).isFalse();
//                 }
//             } catch (final Exception e) {
//                 assertThat(e instanceof UnsupportedOperationException).isTrue();
//             }
//
//             s.reset();
//         }
//     }
//
//     @Test
//     @SuppressWarnings("deprecation")
//     public void testWithRelaxation() throws ParserException {
//         final PropositionalParser parser = new PropositionalParser(this.f);
//         final Formula one = parser.parse("a & b & (c | ~d)");
//         final Formula two = parser.parse("~a | ~c");
//
//         for (final SATSolver s : this.solvers) {
//             s.add(one);
//             s.addWithRelaxation(this.f.variable("d"), two);
//             assertSolverSat(s);
//             try {
//                 assertThat(s.enumerateAllModels().size()).isEqualTo(2);
//             } catch (final Exception e) {
//                 assertThat(e instanceof UnsupportedOperationException).isTrue();
//             }
//             s.reset();
//
//             s.add(one);
//             s.addWithRelaxation(this.f.variable("d"), new StandardProposition(two));
//             assertSolverSat(s);
//             try {
//                 assertThat(s.enumerateAllModels().size()).isEqualTo(2);
//             } catch (final Exception e) {
//                 assertThat(e instanceof UnsupportedOperationException).isTrue();
//             }
//             s.reset();
//
//             s.add(one);
//             s.addWithRelaxation(this.f.variable("d"), two);
//             assertSolverSat(s);
//             try {
//                 assertThat(s.enumerateAllModels().size()).isEqualTo(2);
//             } catch (final Exception e) {
//                 assertThat(e instanceof UnsupportedOperationException).isTrue();
//             }
//             s.reset();
//
//             s.add(one);
//             s.addWithRelaxation(this.f.variable("d"), Arrays.asList(two, this.f.verum()));
//             assertSolverSat(s);
//             try {
//                 assertThat(s.enumerateAllModels().size()).isEqualTo(2);
//             } catch (final Exception e) {
//                 assertThat(e instanceof UnsupportedOperationException).isTrue();
//             }
//             s.reset();
//         }
//     }
//
//     @Test
//     public void testRelaxationFormulas() throws ParserException {
//         for (final SATSolver s : this.solvers) {
//             s.add(this.f.parse("a & (b | c)"));
//             assertSolverSat(s);
//             s.addWithRelaxation(this.f.variable("x"), this.f.parse("~a & ~b"));
//             assertSolverSat(s);
//             assertThat(s.model().positiveVariables()).contains(this.f.variable("x"));
//             s.add(this.f.variable("x").negate());
//             assertSolverUnsat(s);
//         }
//     }

#[test]
fn test_pigeon_hole() {
    let f = &FormulaFactory::new();
    for i in 1..=6 {
        for mut solver in solvers() {
            solver.add(generate_pigeon_hole(i, f), f);
            assert_eq!(solver.sat(), False);
        }
    }
}

#[test]
fn test_pigeon_hole_with_reset() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        for i in 1..=6 {
            solver.add(generate_pigeon_hole(i, f), f);
            assert_eq!(solver.sat(), False);
        }
        solver.reset();
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_pigeon_hole_large() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        solver.add(generate_pigeon_hole(7, f), f);
        assert_eq!(solver.sat(), False);
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn test_different_clause_minimizations() {
    let f = &FormulaFactory::new();
    let solvers = [
        MiniSat::new_with_config(MiniSatConfig::default().clause_min(ClauseMinimization::None)),
        MiniSat::new_with_config(MiniSatConfig::default().clause_min(ClauseMinimization::Basic)),
        MiniSat::new_with_config(MiniSatConfig::default().clause_min(ClauseMinimization::Deep)),
    ];
    for mut solver in solvers {
        solver.add(generate_pigeon_hole(7, f), f);
        assert_eq!(solver.sat(), False);
    }
}

// @Test
//     public void testTimeoutSATHandlerSmall() {
//         for (final SATSolver s : this.solvers) {
//             s.add(this.IMP1);
//             final TimeoutSATHandler handler = new TimeoutSATHandler(1000L);
//             final Tristate result = s.sat(handler);
//             assertThat(handler.aborted()).isFalse();
//             assertThat(result).isEqualTo(Tristate.TRUE);
//             s.reset();
//         }
//     }
//
//     @Test
//     public void testTimeoutSATHandlerLarge() {
//         for (final SATSolver s : this.solvers) {
//             s.add(this.pg.generate(10));
//             final TimeoutSATHandler handler = new TimeoutSATHandler(1000L);
//             final Tristate result = s.sat(handler);
//             assertThat(handler.aborted()).isTrue();
//             assertThat(result).isEqualTo(UNDEF);
//             s.reset();
//         }
//     }

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn test_dimacs_files() {
    let f = &FormulaFactory::new();
    let expected_results: HashMap<String, bool> = BufReader::new(File::open("resources/sat/results.txt").unwrap())
        .lines()
        .map(|l| {
            let tokens: Vec<String> = l.unwrap().split(';').map(std::string::ToString::to_string).collect();
            (tokens[0].to_string(), tokens[1].parse().unwrap())
        })
        .collect();
    for file in fs::read_dir("resources/sat").unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name().to_str().unwrap().to_string();
        if file_name.ends_with(".cnf") {
            let cnf = read_cnf(file.path().to_str().unwrap(), f).unwrap();
            for mut solver in solvers() {
                cnf.iter().for_each(|&clause| solver.add(clause, f));
                assert_eq!(solver.sat() == True, *expected_results.get(&file_name).unwrap());
            }
        }
    }
}

// @Test
//     public void testTimeoutModelEnumerationHandlerWithUNSATInstance() {
//         for (final SATSolver solver : this.solvers) {
//             solver.add(this.pg.generate(10));
//             final TimeoutModelEnumerationHandler handler = new TimeoutModelEnumerationHandler(1000L);
//             final List<Assignment> assignments = solver.execute(ModelEnumerationFunction.builder().handler(handler).build());
//             assertThat(assignments).isEmpty();
//             assertThat(handler.aborted()).isTrue();
//             solver.reset();
//         }
//     }
//
//     @Test
//     public void testTimeoutModelEnumerationHandlerWithSATInstance() {
//         for (final SATSolver solver : this.solvers) {
//             final List<Variable> variables = new ArrayList<>();
//             for (int i = 0; i < 1000; i++) {
//                 variables.add(this.f.variable("x" + i));
//             }
//
//             solver.add(this.f.exo(variables));
//             TimeoutModelEnumerationHandler handler = new TimeoutModelEnumerationHandler(50L);
//             solver.execute(ModelEnumerationFunction.builder().handler(handler).build());
//             assertThat(handler.aborted()).isTrue();
//             solver.reset();
//
//             solver.add(this.f.exo(variables.subList(0, 5)));
//             handler = new TimeoutModelEnumerationHandler(1000L);
//             final List<Assignment> assignments = solver.execute(ModelEnumerationFunction.builder().handler(handler).build());
//             assertThat(assignments).hasSize(5);
//             assertThat(handler.aborted()).isFalse();
//             solver.reset();
//         }
//     }

#[test]
fn test_model_enumeration() {
    let f = &FormulaFactory::new();
    let vars: Box<[Variable]> = (0..20).map(|i| f.var(&format!("x{i}"))).collect();
    let first_five = &vars[..5];
    for mut solver in solvers() {
        if solver.config.incremental {
            solver.add(f.cc(GE, 1, vars.clone()), f);
            let models = enumerate_models_with_config(
                &mut solver,
                &ModelEnumerationConfig::default().variables(first_five).additional_variables(vars.clone()),
            );
            assert_eq!(models.len(), 32);
            for model in models {
                for var in &*vars {
                    assert!(model.pos().contains(var) || model.neg().contains(var));
                }
            }
        }
    }
}

// @Test
//     public void testModelEnumerationWithHandler01() {
//         for (int i = 0; i < this.solvers.length - 1; i++) {
//             final SATSolver s = this.solvers[i];
//             final SortedSet<Variable> lits = new TreeSet<>();
//             final SortedSet<Variable> firstFive = new TreeSet<>();
//             for (int j = 0; j < 20; j++) {
//                 final Variable lit = this.f.variable("x" + j);
//                 lits.add(lit);
//                 if (j < 5) {
//                     firstFive.add(lit);
//                 }
//             }
//             s.add(this.f.cc(CType.GE, 1, lits));
//
//             final NumberOfModelsHandler handler = new NumberOfModelsHandler(29);
//             final List<Assignment> modelsWithHandler = s.execute(ModelEnumerationFunction.builder().variables(firstFive).additionalVariables(lits).handler(handler).build());
//             assertThat(handler.aborted()).isTrue();
//             assertThat(modelsWithHandler.size()).isEqualTo(29);
//             for (final Assignment model : modelsWithHandler) {
//                 for (final Variable lit : lits) {
//                     assertThat(model.positiveVariables().contains(lit) || model.negativeVariables().contains(lit)).isTrue();
//                 }
//             }
//             s.reset();
//         }
//     }
//
//     @Test
//     public void testModelEnumerationWithHandler02() {
//         for (int i = 0; i < this.solvers.length - 1; i++) {
//             final SATSolver s = this.solvers[i];
//             final SortedSet<Variable> lits = new TreeSet<>();
//             final SortedSet<Variable> firstFive = new TreeSet<>();
//             for (int j = 0; j < 20; j++) {
//                 final Variable lit = this.f.variable("x" + j);
//                 lits.add(lit);
//                 if (j < 5) {
//                     firstFive.add(lit);
//                 }
//             }
//             s.add(this.f.cc(CType.GE, 1, lits));
//
//             final NumberOfModelsHandler handler = new NumberOfModelsHandler(29);
//             final List<Assignment> modelsWithHandler = s.execute(ModelEnumerationFunction.builder().additionalVariables(Collections.singletonList(firstFive.first())).handler(handler).build());
//             assertThat(handler.aborted()).isTrue();
//             assertThat(modelsWithHandler.size()).isEqualTo(29);
//             for (final Assignment model : modelsWithHandler) {
//                 for (final Variable lit : lits) {
//                     assertThat(model.positiveVariables().contains(lit) || model.negativeVariables().contains(lit)).isTrue();
//                 }
//             }
//             s.reset();
//         }
//     }

#[test]
fn test_empty_enumeration() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        if solver.config.incremental {
            solver.add(f.falsum(), f);
            assert!(enumerate_models(&mut solver).is_empty());
        }
    }
}

#[test]
fn test_number_of_models_handler() {
    let f = &FormulaFactory::new();
    let vars: Box<[Variable]> = (0..100).map(|i| f.var(&format!("x{i}"))).collect();
    for mut solver in solvers() {
        if solver.config.incremental {
            solver.add(f.exo(vars.clone()), f);
            let models =
                enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(vars.clone()).max_models(100));
            assert_eq!(models.len(), 100);
            assert!(models.iter().all(|m| m.pos().len() == 1));
            solver.reset();

            solver.add(f.exo(vars.clone()), f);
            let models =
                enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(vars.clone()).max_models(200));
            assert_eq!(models.len(), 100);
            assert!(models.iter().all(|m| m.pos().len() == 1));
            solver.reset();

            solver.add(f.exo(vars.clone()), f);
            let models =
                enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(vars.clone()).max_models(50));
            assert_eq!(models.len(), 50);
            assert!(models.iter().all(|m| m.pos().len() == 1));
            solver.reset();

            solver.add(f.exo(vars.clone()), f);
            let models =
                enumerate_models_with_config(&mut solver, &ModelEnumerationConfig::default().variables(vars.clone()).max_models(1));
            assert_eq!(models.len(), 1);
        }
    }
}

#[test]
#[should_panic(expected = "Cannot get a model as long as the formula is not solved.  Call 'sat' first.")]
fn test_model_before_solving() {
    MiniSat::new().model(None);
}

#[test]
fn test_known_variables() {
    let f = &FormulaFactory::new();
    let mut solver = MiniSat::new();
    let phi = "x1 & x2 & x3 & (x4 | ~x5)".to_formula(f);
    let mut vars = phi.variables(f).iter().copied().collect::<Vec<Variable>>();
    solver.add(phi, f);
    assert_eq!(&solver.known_variables(), &vars);

    let state = solver.save_state();
    solver.add(f.variable("x6"), f);
    vars.push(f.var("x6"));
    assert_eq!(&solver.known_variables(), &vars);

    solver.load_state(&state);
    vars.pop().unwrap();
    assert_eq!(&solver.known_variables(), &vars);
}

#[test]
#[should_panic(expected = "Cannot get unit propagated literals on level 0 as long as the formula is not solved.  Call 'sat' first.")]
fn test_up_zero_literals_for_undef_state() {
    let f = &FormulaFactory::new();
    let mut solver = MiniSat::new();
    solver.add("a & b".to_formula(f), f);
    solver.up_zero_literals();
}

#[test]
fn test_up_zero_literals_unsat() {
    let f = &FormulaFactory::new();
    let formula = "a & (a => b) & (b => c) & (c => ~a)".to_formula(f);
    for mut solver in solvers() {
        solver.add(formula, f);
        solver.sat();
        assert_eq!(solver.up_zero_literals(), None);
    }
}

#[test]
fn test_up_zero_literals() {
    let f = &FormulaFactory::new();
    let expected_subsets = [
        (f.verum(), BTreeSet::new()),
        ("a".to_formula(f), lits("a", f)),
        ("a | b".to_formula(f), BTreeSet::new()),
        ("a & b".to_formula(f), lits("a b", f)),
        ("a & ~b".to_formula(f), lits("a ~b", f)),
        ("(a | c) & ~b".to_formula(f), lits("~b", f)),
        ("(b | c) & ~b & (~c | d)".to_formula(f), lits("~b c d", f)),
    ];
    for mut solver in solvers() {
        for (formula, expected) in &expected_subsets {
            solver.reset();
            solver.add(*formula, f);
            assert_eq!(solver.sat(), True);
            assert_eq!(solver.up_zero_literals().as_ref(), Some(expected));
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn test_up_zero_literals_dimacs_files() {
    let f = &FormulaFactory::new();
    for file in fs::read_dir("resources/sat").unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name().to_str().unwrap().to_string();
        if file_name.ends_with(".cnf") {
            let cnf = read_cnf(file.path().to_str().unwrap(), f).unwrap();
            for mut solver in solvers() {
                cnf.iter().for_each(|&clause| solver.add(clause, f));
                if solver.sat() == True {
                    let up_zero_literals = solver.up_zero_literals().unwrap();
                    let negations = up_zero_literals.iter().map(|lit| EncodedFormula::from(lit.negate()));
                    solver.add(f.or(negations), f);
                    assert_eq!(solver.sat(), False);
                }
            }
        }
    }
}

#[test]
fn test_selection_order_simple01() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        let formula = "~(x <=> y)".to_formula(f);
        solver.add(formula, f);
        let selection_order = lits_list("x y", f);
        assert_eq!(True, solver.sat_with(&SatBuilder::new().selection_order(&selection_order)));
        let model = solver.model(None).unwrap();
        assert!(Model::from_literals(&lits_list("x ~y", f)).compare(&model));
        test_local_minimum(&mut solver, &model, &selection_order);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order);

        solver.set_solver_to_undef();
        let selection_order = lits_list("y x", f);
        assert_eq!(True, solver.sat_with(&SatBuilder::new().selection_order(&selection_order)));
        let model = solver.model(None).unwrap();
        assert!(Model::from_literals(&lits_list("y ~x", f)).compare(&model));
        test_local_minimum(&mut solver, &model, &selection_order);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order);

        solver.set_solver_to_undef();
        let selection_order = lits_list("~x", f);
        assert_eq!(True, solver.sat_with(&SatBuilder::new().selection_order(&selection_order)));
        let model = solver.model(None).unwrap();
        assert!(Model::from_literals(&lits_list("y ~x", f)).compare(&model));
        test_local_minimum(&mut solver, &model, &selection_order);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order);

        solver.set_solver_to_undef();
        let selection_order = lits_list("~y ~x", f);
        assert_eq!(True, solver.sat_with(&SatBuilder::new().selection_order(&selection_order)));
        let model = solver.model(None).unwrap();
        assert!(Model::from_literals(&lits_list("x ~y", f)).compare(&model));
        test_local_minimum(&mut solver, &model, &selection_order);
        test_highest_lexicographical_assignment(&mut solver, &model, &selection_order);
    }
}

#[test]
fn test_selection_order_simple02() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        let vars: Box<[Variable]> = (0..5).map(|i| f.var(&format!("x{i}"))).collect();
        let selection_order: Vec<Literal> = vars.iter().map(Variable::pos_lit).collect();
        let cc = f.cc(EQ, 2, vars);
        solver.add(cc, f);

        for _ in 0..10 {
            assert_eq!(True, solver.sat_with(&SatBuilder::new().selection_order(&selection_order)));
            let model = solver.model(None).unwrap();
            test_local_minimum(&mut solver, &model, &selection_order);
            test_highest_lexicographical_assignment(&mut solver, &model, &selection_order);
            solver.add(Assignment::from(model).blocking_clause(f, None), f);
        }

        solver.reset();
        solver.add(cc, f);
        let selection_order2 = lits_list("x4 ~x0 x1 x2 x3", f);
        for _ in 0..10 {
            assert_eq!(True, solver.sat_with(&SatBuilder::new().selection_order(&selection_order2)));
            let model = solver.model(None).unwrap();
            test_local_minimum(&mut solver, &model, &selection_order2);
            test_highest_lexicographical_assignment(&mut solver, &model, &selection_order2);
            solver.add(Assignment::from(model).blocking_clause(f, None), f);
        }
    }
}

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn test_dimacs_files_with_selection_order() {
    let f = &FormulaFactory::new();
    let expected_results: HashMap<String, bool> = BufReader::new(File::open("resources/sat/results.txt").unwrap())
        .lines()
        .map(|l| {
            let tokens: Vec<String> = l.unwrap().split(';').map(std::string::ToString::to_string).collect();
            (tokens[0].to_string(), tokens[1].parse().unwrap())
        })
        .collect();
    for file in fs::read_dir("resources/sat").unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name().to_str().unwrap().to_string();
        if file_name.ends_with(".cnf") {
            let cnf = read_cnf(file.path().to_str().unwrap(), f).unwrap();
            for mut solver in solvers() {
                cnf.iter().for_each(|&clause| solver.add(clause, f));
                let selection_order = (*f.and(&cnf).variables(f)).iter().take(10).map(Variable::pos_lit).collect::<Vec<Literal>>();
                let expected = *expected_results.get(&file_name).unwrap();
                assert_eq!(solver.sat_with(&SatBuilder::new().selection_order(&selection_order)) == True, expected);
                if expected {
                    let model = solver.model(None).unwrap();
                    test_local_minimum(&mut solver, &model, &selection_order);
                    test_highest_lexicographical_assignment(&mut solver, &model, &selection_order);
                }
            }
        }
    }
}

#[test]
fn test_model_enumeration_with_additional_variables() {
    let f = &FormulaFactory::new();
    for mut solver in solvers() {
        if solver.config.incremental {
            solver.add("A | B | C | D | E".to_formula(f), f);
            let models = enumerate_models_with_config(
                &mut solver,
                &ModelEnumerationConfig::default().variables(vars_list("a b", f)).additional_variables(vars_list("b c", f)),
            );
            for model in models {
                let pos_count_b = model.pos().iter().filter(|&&v| v.name(f) == "B").count();
                let neg_count_b = model.neg().iter().filter(|&&v| v.name(f) == "B").count();
                assert!(pos_count_b < 2);
                assert!(neg_count_b < 2);
            }
        }
    }
}

fn test_local_minimum(solver: &mut MiniSat, model: &Model, selection_order: &[Literal]) {
    let model_lits: HashSet<Literal> = model.literals().iter().copied().collect();
    for &lit in selection_order {
        if !model_lits.contains(&lit) {
            let mut model_with_flip = model_lits.clone();
            model_with_flip.remove(&lit.negate());
            model_with_flip.insert(lit);
            assert_eq!(False, solver.sat_with(&SatBuilder::new().assumptions(&model_with_flip.into_iter().collect::<Vec<Literal>>())));
        }
    }
}

fn test_highest_lexicographical_assignment(solver: &mut MiniSat, model: &Model, selection_order: &[Literal]) {
    let model_lits: HashSet<Literal> = model.literals().iter().copied().collect();
    let mut order_sublist = vec![];
    for &lit in selection_order {
        if model_lits.contains(&lit) {
            order_sublist.push(lit);
        } else {
            let mut order_sublist_with_flip: BTreeSet<Literal> = order_sublist.iter().copied().collect();
            order_sublist_with_flip.remove(&lit.negate());
            order_sublist_with_flip.insert(lit);
            assert_eq!(
                False,
                solver.sat_with(&SatBuilder::new().assumptions(&order_sublist_with_flip.into_iter().collect::<Vec<Literal>>()))
            );
            order_sublist.push(lit.negate());
        }
    }
}

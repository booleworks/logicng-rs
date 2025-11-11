mod tests {
    use std::time::Instant;

    use num_bigint::ToBigUint;

    use crate::cardinality_constraints::{AmoEncoder, CcConfig};
    use crate::formulas::{CType, EncodedFormula, FormulaFactory, Variable};
    use crate::knowledge_compilation::bdd::bdd_kernel::BddKernel;
    use crate::knowledge_compilation::bdd::bdd_main::Bdd;
    use crate::knowledge_compilation::bdd::orderings::{
        bfs_ordering, dfs_ordering, force_ordering, max_to_min_ordering, min_to_max_ordering,
    };
    use crate::solver::minisat::MiniSat;
    use crate::solver::minisat::sat::Tristate;
    use crate::util::n_queens_generator::generate_n_queens;

    #[test]
    fn test_exo() {
        let mut f = FormulaFactory::new();
        f.config.cc_config = CcConfig::new().amo_encoder(AmoEncoder::Pure);
        let variables = generate_variables(100, &f);
        let constraint = f.exo(variables);
        let constraint = f.nnf_of(constraint);
        let mut kernel = BddKernel::new_with_num_vars(100, 100_000, 1_000_000);
        let bdd = Bdd::from_formula(constraint, &f, &mut kernel);
        assert_eq!(bdd.model_count(&mut kernel), 100.to_biguint().unwrap());
        assert_eq!(bdd.enumerate_all_models(&mut kernel).len(), 100);
    }

    #[test]
    fn test_amo() {
        let mut f = FormulaFactory::new();
        f.config.cc_config = CcConfig::new().amo_encoder(AmoEncoder::Pure);
        let variables = generate_variables(100, &f);
        let constraint = f.amo(variables);
        let constraint = f.nnf_of(constraint);
        let mut kernel = BddKernel::new_with_num_vars(100, 100_000, 1_000_000);
        let bdd = Bdd::from_formula(constraint, &f, &mut kernel);
        assert_eq!(bdd.model_count(&mut kernel), 101.to_biguint().unwrap());
        assert_eq!(bdd.enumerate_all_models(&mut kernel).len(), 101);
    }

    #[test]
    fn test_exk() {
        let mut f = FormulaFactory::new();
        f.config.cc_config = CcConfig::new().amo_encoder(AmoEncoder::Pure);
        let variables = generate_variables(15, &f);
        let constraint = f.cc(CType::EQ, 8, variables);
        let constraint = f.nnf_of(constraint);
        let mut kernel = BddKernel::new_with_num_vars(constraint.variables(&f).len(), 100_000, 1_000_000);
        let bdd = Bdd::from_formula(constraint, &f, &mut kernel);
        assert_eq!(bdd.model_count(&mut kernel), 6435.to_biguint().unwrap());
        assert_eq!(bdd.enumerate_all_models(&mut kernel).len(), 6435);
    }

    #[test]
    #[cfg_attr(not(feature = "long_running_tests"), ignore = "long running test")]
    fn large_bdd_test() {
        let mut f = FormulaFactory::new();
        let expected_count = [0, 2, 10, 4, 40, 92, 352];
        for n in 3..=9 {
            let n_queens = generate_n_queens(n, &mut f);
            let dfs = dfs_ordering(n_queens, &f);
            let bfs = bfs_ordering(n_queens, &f);
            let min2max = min_to_max_ordering(n_queens, &f);
            let max2min = max_to_min_ordering(n_queens, &f);
            let force = force_ordering(n_queens, &f);

            let orderings = vec![dfs, bfs, min2max, max2min, force];

            for ordering in orderings {
                let mut kernel = BddKernel::new_with_var_ordering(&ordering, 10_000, 10_000);

                let start = Instant::now();
                let bdd = Bdd::from_formula(n_queens, &f, &mut kernel);
                let duration = start.elapsed();
                println!("Constructed BDD for {n} queens in {duration:?}");

                let start = Instant::now();
                assert_eq!(bdd.model_count(&mut kernel), expected_count[n - 3].to_biguint().unwrap());
                let duration = start.elapsed();
                println!("Computed model count for {n} queens in {duration:?}");

                let start = Instant::now();
                let models = bdd.enumerate_all_models(&mut kernel);
                let duration = start.elapsed();
                println!("Computed model enumeration for {n} queens in {duration:?}");
                assert_eq!(models.len(), expected_count[n - 3]);
                for model in models {
                    assert!(f.evaluate(n_queens, &model.into()));
                }

                let cnf = bdd.cnf(&f, &mut kernel);
                assert!(cnf.is_cnf(&f));
                check_equiv(n_queens, cnf, &f);

                let dnf = bdd.dnf(&f, &mut kernel);
                assert!(dnf.is_dnf(&f));
                check_equiv(n_queens, dnf, &f);

                let formula = bdd.to_formula(&f, &mut kernel);
                check_equiv(n_queens, formula, &f);
            }
            println!("\n");
        }
    }

    fn check_equiv(original: EncodedFormula, cnf: EncodedFormula, f: &FormulaFactory) {
        let mut solver = MiniSat::new();
        let formula = f.equivalence(original, cnf);
        solver.add(f.negate(formula), f);
        assert_eq!(solver.sat(), Tristate::False);
    }

    fn generate_variables(n: usize, f: &FormulaFactory) -> Vec<Variable> {
        let mut result = Vec::new();
        for i in 0..n {
            result.push(f.var(format!("v{i}")));
        }
        result
    }
}

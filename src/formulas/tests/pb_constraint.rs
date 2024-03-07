mod pb_constraint_tests {
    use crate::datastructures::Assignment;
    use crate::formulas::CType::{EQ, GE, GT, LE, LT};
    use crate::formulas::{EncodedFormula, FormulaFactory, Literal, Variable};
    use crate::util::test_util::lits;
    use std::collections::BTreeSet;

    #[test]
    #[should_panic(expected = "The number of literals and coefficients in a pseudo-boolean constraint must be the same.")]
    fn test_illegal_pb() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let coeffs: Box<[i64]> = Box::new([3, -2, 7, 2]);
        f.pbc(EQ, 3, lits, coeffs);
    }

    #[test]
    fn maximal_value_pb_and_cc() {
        let f = FormulaFactory::new();

        let formula = f.cc(GE, 4_294_967_295, vec![]);
        assert!(formula.is_falsum());

        let formula = f.pbc(GE, 4_294_967_295, vec![], vec![]);
        assert!(formula.is_falsum());

        let formula = f.cc(GE, 4_294_967_295, vec![f.var("a"), f.var("b")]);
        assert!(formula.is_cc());
        assert_eq!(formula.as_cc(&f).unwrap().rhs, 4_294_967_295);

        let formula = f.pbc(GT, 4_294_967_295, vec![f.lit("a", true), f.lit("b", true)], vec![1, 1]);
        assert!(formula.is_cc());
        assert_eq!(formula.as_cc(&f).unwrap().rhs, 4_294_967_295);

        let formula = f.pbc(GT, 4_294_967_295, vec![f.lit("a", true), f.lit("b", true)], vec![2, 1]);
        assert!(formula.is_pbc());
        assert_eq!(formula.as_pbc(&f).unwrap().rhs, 4_294_967_295);
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_type_and_getters() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        let vars1: Box<[Variable]> = Box::new([f.var("a")]);
        let lits1: Box<[Literal]> = Box::new([f.lit("a", true)]);
        let vars2: Box<[Variable]> = Box::new([f.var("a"), f.var("b"), f.var("c")]);
        let lits2: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let coeffs1: Box<[i64]> = Box::new([3]);
        let coeffs2: Box<[i64]> = Box::new([3, -2, 7]);

        assert!(pb1.is_pbc());
        assert!(pb2.is_pbc());
        assert!(cc1.is_cc());
        assert!(cc2.is_cc());
        assert!(amo1.is_cc());
        assert!(amo2.is_cc());
        assert!(exo1.is_cc());
        assert!(exo2.is_cc());

        let pb1 = pb1.as_pbc(f).unwrap();
        let pb2 = pb2.as_pbc(f).unwrap();
        let cc1 = cc1.as_cc(f).unwrap();
        let cc2 = cc2.as_cc(f).unwrap();
        let amo1 = amo1.as_cc(f).unwrap();
        let amo2 = amo2.as_cc(f).unwrap();
        let exo1 = exo1.as_cc(f).unwrap();
        let exo2 = exo2.as_cc(f).unwrap();

        assert_eq!(lits1, pb1.literals);
        assert_eq!(coeffs1, pb1.coefficients);
        assert_eq!(LE, pb1.comparator);
        assert_eq!(2, pb1.rhs);
        assert_eq!(3, pb1.max_weight());

        assert_eq!(lits2, pb2.literals);
        assert_eq!(coeffs2, pb2.coefficients);
        assert_eq!(LE, pb2.comparator);
        assert_eq!(8, pb2.rhs);
        assert_eq!(7, pb2.max_weight());

        assert_eq!(vars1, cc1.variables);
        assert_eq!(LT, cc1.comparator);
        assert_eq!(1, cc1.rhs);
        assert!(!cc1.is_amo());
        assert!(!cc1.is_exo());

        assert_eq!(vars2, cc2.variables);
        assert_eq!(GE, cc2.comparator);
        assert_eq!(2, cc2.rhs);
        assert!(!cc2.is_amo());
        assert!(!cc2.is_exo());

        assert_eq!(vars1, amo1.variables);
        assert_eq!(LE, amo1.comparator);
        assert_eq!(1, amo1.rhs);
        assert!(amo1.is_amo());
        assert!(!amo1.is_exo());

        assert_eq!(vars2, amo2.variables);
        assert_eq!(LE, amo2.comparator);
        assert_eq!(1, amo2.rhs);
        assert!(amo2.is_amo());
        assert!(!amo2.is_exo());

        assert_eq!(vars1, exo1.variables);
        assert_eq!(EQ, exo1.comparator);
        assert_eq!(1, exo1.rhs);
        assert!(!exo1.is_amo());
        assert!(exo1.is_exo());

        assert_eq!(vars2, exo2.variables);
        assert_eq!(EQ, exo2.comparator);
        assert_eq!(1, exo2.rhs);
        assert!(!exo2.is_amo());
        assert!(exo2.is_exo());
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_create_cc_instead_of_pbc() {
        let f = &FormulaFactory::new();
        let lits1: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", true)]);
        let lits2: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false)]);
        let coeffs1: Box<[i64]> = Box::new([1, 1]);
        let coeffs2: Box<[i64]> = Box::new([-1, 1]);

        assert!(f.pbc(LE, 4, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(LT, 4, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(GE, 4, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(GT, 4, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(EQ, 4, lits1.clone(), coeffs1.clone()).is_cc());

        // Corner cases
        assert!(f.pbc(LE, 0, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(LT, 1, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(GE, 0, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(GT, -1, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(f.pbc(EQ, 0, lits1.clone(), coeffs1.clone()).is_cc());

        assert!(!f.pbc(LE, -1, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(LT, 0, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(GE, -1, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(GT, -2, lits1.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(EQ, -1, lits1.clone(), coeffs1.clone()).is_cc());

        assert!(!f.pbc(LE, 4, lits1.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(LT, 4, lits1.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(GE, 4, lits1.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(GT, 4, lits1.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(EQ, 4, lits1, coeffs2.clone()).is_cc());

        assert!(!f.pbc(LE, 4, lits2.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(LT, 4, lits2.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(GE, 4, lits2.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(GT, 4, lits2.clone(), coeffs1.clone()).is_cc());
        assert!(!f.pbc(EQ, 4, lits2.clone(), coeffs1).is_cc());

        assert!(!f.pbc(LE, 4, lits2.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(LT, 4, lits2.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(GE, 4, lits2.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(GT, 4, lits2.clone(), coeffs2.clone()).is_cc());
        assert!(!f.pbc(EQ, 4, lits2, coeffs2).is_cc());
    }

    #[test]
    fn test_is_amo() {
        let f = &FormulaFactory::new();
        let lits1: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", true)]);
        let coeffs1: Box<[i64]> = Box::new([1, 1]);

        assert!(f.pbc(LE, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_amo());
        assert!(f.pbc(LT, 2, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_amo());
        assert!(!f.pbc(LT, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_amo());
        assert!(!f.pbc(GE, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_amo());
        assert!(!f.pbc(GT, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_amo());
        assert!(!f.pbc(EQ, 1, lits1, coeffs1).as_cc(f).unwrap().is_amo());
    }

    #[test]
    fn test_is_exo() {
        let f = &FormulaFactory::new();
        let lits1: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", true)]);
        let coeffs1: Box<[i64]> = Box::new([1, 1]);

        assert!(!f.pbc(LE, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_exo());
        assert!(!f.pbc(LT, 2, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_exo());
        assert!(!f.pbc(LT, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_exo());
        assert!(!f.pbc(GE, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_exo());
        assert!(!f.pbc(GT, 1, lits1.clone(), coeffs1.clone()).as_cc(f).unwrap().is_exo());
        assert!(f.pbc(EQ, 1, lits1, coeffs1).as_cc(f).unwrap().is_exo());
    }

    #[test]
    fn test_number_of_atoms() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert_eq!(1, pb1.number_of_atoms(f));
        assert_eq!(1, pb2.number_of_atoms(f));
        assert_eq!(1, cc1.number_of_atoms(f));
        assert_eq!(1, cc2.number_of_atoms(f));
        assert_eq!(1, amo1.number_of_atoms(f));
        assert_eq!(1, amo2.number_of_atoms(f));
        assert_eq!(1, exo1.number_of_atoms(f));
        assert_eq!(1, exo2.number_of_atoms(f));
    }

    #[test]
    fn test_number_of_nodes() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert_eq!(2, pb1.number_of_nodes(f));
        assert_eq!(4, pb2.number_of_nodes(f));
        assert_eq!(2, cc1.number_of_nodes(f));
        assert_eq!(4, cc2.number_of_nodes(f));
        assert_eq!(2, amo1.number_of_nodes(f));
        assert_eq!(4, amo2.number_of_nodes(f));
        assert_eq!(2, exo1.number_of_nodes(f));
        assert_eq!(4, exo2.number_of_nodes(f));
    }

    #[test]
    fn test_variables() {
        let f = &FormulaFactory::new();
        let vars1 = vec![f.var("a")].into_iter().collect::<BTreeSet<Variable>>();
        let vars2 = vec![f.var("a"), f.var("b"), f.var("c")].into_iter().collect::<BTreeSet<Variable>>();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert_eq!(*pb1.variables(f), vars1);
        assert_eq!(*pb2.variables(f), vars2);
        assert_eq!(*cc1.variables(f), vars1);
        assert_eq!(*cc2.variables(f), vars2);
        assert_eq!(*amo1.variables(f), vars1);
        assert_eq!(*amo2.variables(f), vars2);
        assert_eq!(*exo1.variables(f), vars1);
        assert_eq!(*exo2.variables(f), vars2);
    }

    #[test]
    fn test_literals() {
        let f = &FormulaFactory::new();
        let lits1 = lits("a", f);
        let lits2 = lits("a ~b c", f);
        let lits_cc2 = lits("a b c", f);
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert_eq!(*pb1.literals(f), lits1);
        assert_eq!(*pb2.literals(f), lits2);
        assert_eq!(*cc1.literals(f), lits1);
        assert_eq!(*cc2.literals(f), lits_cc2);
        assert_eq!(*amo1.literals(f), lits1);
        assert_eq!(*amo2.literals(f), lits_cc2);
        assert_eq!(*exo1.literals(f), lits1);
        assert_eq!(*exo2.literals(f), lits_cc2);
    }

    #[test]
    fn test_contains() {
        let f = &FormulaFactory::new();
        let (_, pb2, _, cc2, _, _, _, _) = generate_formulas(f);
        assert!(pb2.contains_var_name("a", f));
        assert!(pb2.contains_var_name("b", f));
        assert!(pb2.contains_var_name("c", f));
        assert!(!pb2.contains_var_name("d", f));
        assert!(!pb2.contains_var_name("x", f));
        assert!(cc2.contains_var_name("a", f));
        assert!(cc2.contains_var_name("b", f));
        assert!(cc2.contains_var_name("c", f));
        assert!(!cc2.contains_var_name("d", f));
        assert!(!cc2.contains_var_name("x", f));
    }

    #[test]
    fn test_contains_subformula() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, _, _, _, _) = generate_formulas(f);
        assert!(pb1.contains_node(f.variable("a"), f));
        assert!(!pb1.contains_node(f.literal("a", false), f));
        assert!(pb2.contains_node(f.literal("b", false), f));
        assert!(pb2.contains_node(f.variable("b"), f));
        assert!(!pb2.contains_node(f.variable("d"), f));
        assert!(pb1.contains_node(pb1, f));
        assert!(pb2.contains_node(pb2, f));
        assert!(cc1.contains_node(f.variable("a"), f));
        assert!(!cc1.contains_node(f.literal("a", false), f));
        assert!(!cc2.contains_node(f.literal("b", false), f));
        assert!(cc2.contains_node(f.variable("b"), f));
        assert!(!cc2.contains_node(f.variable("d"), f));
        assert!(cc1.contains_node(cc1, f));
        assert!(cc2.contains_node(cc2, f));
    }

    #[test]
    fn test_is_nnf() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert!(!pb1.is_nnf(f));
        assert!(!pb2.is_nnf(f));
        assert!(!cc1.is_nnf(f));
        assert!(!cc2.is_nnf(f));
        assert!(!amo1.is_nnf(f));
        assert!(!amo2.is_nnf(f));
        assert!(!exo1.is_nnf(f));
        assert!(!exo2.is_nnf(f));
    }

    #[test]
    fn test_is_dnf() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert!(!pb1.is_dnf(f));
        assert!(!pb2.is_dnf(f));
        assert!(!cc1.is_dnf(f));
        assert!(!cc2.is_dnf(f));
        assert!(!amo1.is_dnf(f));
        assert!(!amo2.is_dnf(f));
        assert!(!exo1.is_dnf(f));
        assert!(!exo2.is_dnf(f));
    }

    #[test]
    fn test_is_cnf() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert!(!pb1.is_cnf(f));
        assert!(!pb2.is_cnf(f));
        assert!(!cc1.is_cnf(f));
        assert!(!cc2.is_cnf(f));
        assert!(!amo1.is_cnf(f));
        assert!(!amo2.is_cnf(f));
        assert!(!exo1.is_cnf(f));
        assert!(!exo2.is_cnf(f));
    }

    #[test]
    fn test_evaluate() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let vars: Box<[Variable]> = lits.iter().map(Literal::variable).collect();
        let coeffs: Box<[i64]> = Box::new([2, -2, 3]);
        let a1 = Assignment::from_variables(&[f.var("a"), f.var("b")], &[f.var("c")]);
        let a2 = Assignment::from_variables(&[f.var("a")], &[f.var("b"), f.var("c")]);
        let pb1 = f.pbc(EQ, 2, lits.clone(), coeffs.clone());
        let pb3 = f.pbc(GE, 1, lits.clone(), coeffs.clone());
        let pb4 = f.pbc(GT, 0, lits.clone(), coeffs.clone());
        let pb5 = f.pbc(LE, 1, lits.clone(), coeffs.clone());
        let pb6 = f.pbc(LT, 2, lits, coeffs);
        assert!(f.evaluate(pb1, &a1));
        assert!(!f.evaluate(pb1, &a2));
        assert!(f.evaluate(pb3, &a1));
        assert!(!f.evaluate(pb3, &a2));
        assert!(f.evaluate(pb4, &a1));
        assert!(!f.evaluate(pb4, &a2));
        assert!(!f.evaluate(pb5, &a1));
        assert!(f.evaluate(pb5, &a2));
        assert!(!f.evaluate(pb6, &a1));
        assert!(f.evaluate(pb6, &a2));

        let cc1 = f.cc(EQ, 2, vars.clone());
        let cc2 = f.cc(GE, 2, vars.clone());
        let cc3 = f.cc(GT, 1, vars.clone());
        let cc4 = f.cc(LE, 1, vars.clone());
        let cc5 = f.cc(LT, 2, vars);
        assert!(f.evaluate(cc1, &a1));
        assert!(!f.evaluate(cc1, &a2));
        assert!(f.evaluate(cc2, &a1));
        assert!(!f.evaluate(cc2, &a2));
        assert!(f.evaluate(cc3, &a1));
        assert!(!f.evaluate(cc3, &a2));
        assert!(!f.evaluate(cc4, &a1));
        assert!(f.evaluate(cc4, &a2));
        assert!(!f.evaluate(cc5, &a1));
        assert!(f.evaluate(cc5, &a2));
    }

    #[test]
    fn test_restrict() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let lits_a1: Box<[Literal]> = Box::new([f.lit("b", false), f.lit("c", true)]);
        let lits_a2: Box<[Literal]> = Box::new([f.lit("c", true)]);
        let coeffs: Box<[i64]> = Box::new([2, -2, 3]);
        let coeffs_a1: Box<[i64]> = Box::new([-2, 3]);
        let coeffs_a2: Box<[i64]> = Box::new([3]);
        let vars: Box<[Variable]> = lits.iter().map(Literal::variable).collect();
        let vars_a1: Box<[Variable]> = lits_a1.iter().map(Literal::variable).collect();
        let vars_a2: Box<[Variable]> = lits_a2.iter().map(Literal::variable).collect();
        let a1 = Assignment::from_variables(&[f.var("a")], &[]);
        let a2 = Assignment::from_variables(&[f.var("a")], &[f.var("b")]);
        let a3 = Assignment::from_variables(&[f.var("a"), f.var("c")], &[f.var("b")]);
        let a4 = Assignment::from_variables(&[f.var("b")], &[f.var("a"), f.var("c")]);
        let pb1 = f.pbc(EQ, 2, lits, coeffs);
        assert_eq!(f.pbc(EQ, 0, lits_a1, coeffs_a1), f.restrict(pb1, &a1));
        assert_eq!(f.pbc(EQ, 2, lits_a2, coeffs_a2), f.restrict(pb1, &a2));
        assert_eq!(f.falsum(), f.restrict(pb1, &a3));
        assert_eq!(f.falsum(), f.restrict(pb1, &a4));

        let cc1 = f.cc(EQ, 2, vars.clone());
        let cc2 = f.cc(GE, 2, vars.clone());
        let cc3 = f.cc(GT, 1, vars.clone());
        let cc4 = f.cc(LE, 1, vars.clone());
        let cc5 = f.cc(LT, 2, vars);
        assert_eq!(f.cc(EQ, 1, vars_a1.clone()), f.restrict(cc1, &a1));
        assert_eq!(f.cc(EQ, 1, vars_a2.clone()), f.restrict(cc1, &a2));
        assert_eq!(f.verum(), f.restrict(cc1, &a3));
        assert_eq!(f.falsum(), f.restrict(cc1, &a4));
        assert_eq!(f.cc(GE, 1, vars_a1.clone()), f.restrict(cc2, &a1));
        assert_eq!(f.cc(GE, 1, vars_a2.clone()), f.restrict(cc2, &a2));
        assert_eq!(f.verum(), f.restrict(cc2, &a3));
        assert_eq!(f.falsum(), f.restrict(cc2, &a4));
        assert_eq!(f.cc(GT, 0, vars_a1.clone()), f.restrict(cc3, &a1));
        assert_eq!(f.cc(GT, 0, vars_a2.clone()), f.restrict(cc3, &a2));
        assert_eq!(f.verum(), f.restrict(cc3, &a3));
        assert_eq!(f.falsum(), f.restrict(cc3, &a4));
        assert_eq!(f.cc(LE, 0, vars_a1.clone()), f.restrict(cc4, &a1));
        assert_eq!(f.cc(LE, 0, vars_a2.clone()), f.restrict(cc4, &a2));
        assert_eq!(f.falsum(), f.restrict(cc4, &a3));
        assert_eq!(f.verum(), f.restrict(cc4, &a4));
        assert_eq!(f.cc(LT, 1, vars_a1), f.restrict(cc5, &a1));
        assert_eq!(f.cc(LT, 1, vars_a2), f.restrict(cc5, &a2));
        assert_eq!(f.falsum(), f.restrict(cc5, &a3));
        assert_eq!(f.verum(), f.restrict(cc5, &a4));
    }

    #[test]
    fn test_restrict_inequality() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> =
            Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true), f.lit("d", true), f.lit("e", true), f.lit("f", false)]);
        let coeffs: Box<[i64]> = Box::new([70, 50, 201, -3, -24, 1]);
        let pb1 = f.pbc(GE, -24, lits.clone(), coeffs.clone());
        let pb2 = f.pbc(LE, 150, lits, coeffs);
        let a1 = Assignment::from_variables(&[f.var("c")], &[f.var("b")]);
        let a2 = Assignment::from_variables(&[f.var("b"), f.var("d"), f.var("e")], &[f.var("a"), f.var("c")]);
        let a3 = Assignment::from_variables(&[], &[f.var("c")]);
        assert_eq!(f.verum(), f.restrict(pb1, &a1));
        assert_eq!(f.falsum(), f.restrict(pb2, &a1));
        assert_eq!(f.falsum(), f.restrict(pb1, &a2));
        assert_eq!(f.verum(), f.restrict(pb2, &a3));
    }

    #[test]
    fn test_negation_pbc() {
        let f = &FormulaFactory::new();
        let lits: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let coeffs: Box<[i64]> = Box::new([2, -2, 3]);
        let pb1 = f.pbc(EQ, 2, lits.clone(), coeffs.clone());
        let pb3 = f.pbc(GE, 1, lits.clone(), coeffs.clone());
        let pb4 = f.pbc(GT, 0, lits.clone(), coeffs.clone());
        let pb5 = f.pbc(LE, 1, lits.clone(), coeffs.clone());
        let pb6 = f.pbc(LT, 2, lits.clone(), coeffs.clone());
        let pb7 = f.pbc(EQ, -2, lits.clone(), coeffs.clone());

        let op11 = f.pbc(LT, 2, lits.clone(), coeffs.clone());
        let op12 = f.pbc(GT, 2, lits.clone(), coeffs.clone());
        assert_eq!(f.or([op11, op12]), f.negate(pb1));
        assert_eq!(f.pbc(LT, 1, lits.clone(), coeffs.clone()), f.negate(pb3));
        assert_eq!(f.pbc(LE, 0, lits.clone(), coeffs.clone()), f.negate(pb4));
        assert_eq!(f.pbc(GT, 1, lits.clone(), coeffs.clone()), f.negate(pb5));
        assert_eq!(f.pbc(GE, 2, lits.clone(), coeffs.clone()), f.negate(pb6));
        let op21 = f.pbc(LT, -2, lits.clone(), coeffs.clone());
        let op22 = f.pbc(GT, -2, lits, coeffs);
        assert_eq!(f.or([op21, op22]), f.negate(pb7));
    }

    #[test]
    fn test_negation_cc() {
        let f = &FormulaFactory::new();
        let vars: Box<[_]> = Box::new([f.var("a"), f.var("b"), f.var("c")]);
        let cc1 = f.cc(EQ, 2, vars.clone());
        let cc3 = f.cc(GE, 1, vars.clone());
        let cc4 = f.cc(GT, 0, vars.clone());
        let cc5 = f.cc(LE, 1, vars.clone());
        let cc6 = f.cc(LT, 2, vars.clone());

        let op11 = f.cc(LT, 2, vars.clone());
        let op12 = f.cc(GT, 2, vars.clone());
        assert_eq!(f.or([op11, op12]), f.negate(cc1));
        assert_eq!(f.cc(LT, 1, vars.clone()), f.negate(cc3));
        assert_eq!(f.cc(LE, 0, vars.clone()), f.negate(cc4));
        assert_eq!(f.cc(GT, 1, vars.clone()), f.negate(cc5));
        assert_eq!(f.cc(GE, 2, vars), f.negate(cc6));
    }

    #[test]
    fn test_nnf() {
        let f = &FormulaFactory::new();
        let (pb1, _, cc1, _, amo1, _, exo1, _) = generate_formulas(f);
        assert_eq!(f.literal("a", false), f.nnf_of(pb1));
        assert_eq!(f.literal("a", false), f.nnf_of(cc1));
        assert_eq!(f.verum(), f.nnf_of(amo1));
        assert_eq!(f.literal("a", true), f.nnf_of(exo1));
    }

    #[test]
    fn test_number_of_operands() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert_eq!(0, pb1.number_of_operands(f));
        assert_eq!(0, pb2.number_of_operands(f));
        assert_eq!(0, cc1.number_of_operands(f));
        assert_eq!(0, cc2.number_of_operands(f));
        assert_eq!(0, amo1.number_of_operands(f));
        assert_eq!(0, amo2.number_of_operands(f));
        assert_eq!(0, exo1.number_of_operands(f));
        assert_eq!(0, exo2.number_of_operands(f));
    }

    #[test]
    fn test_is_constant() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert!(!pb1.is_constant());
        assert!(!pb2.is_constant());
        assert!(!cc1.is_constant());
        assert!(!cc2.is_constant());
        assert!(!amo1.is_constant());
        assert!(!amo2.is_constant());
        assert!(!exo1.is_constant());
        assert!(!exo2.is_constant());
    }

    #[test]
    fn test_is_atomic() {
        let f = &FormulaFactory::new();
        let (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2) = generate_formulas(f);
        assert!(pb1.is_atomic());
        assert!(pb2.is_atomic());
        assert!(cc1.is_atomic());
        assert!(cc2.is_atomic());
        assert!(amo1.is_atomic());
        assert!(amo2.is_atomic());
        assert!(exo1.is_atomic());
        assert!(exo2.is_atomic());
    }

    #[test]
    fn test_trivial_constant() {
        let f = &FormulaFactory::new();
        let empty_lits: Box<[Literal]> = Box::new([]);
        let empty_coeffs: Box<[i64]> = Box::new([]);
        let empty_vars: Box<[Variable]> = Box::new([]);
        assert_eq!(f.verum(), f.pbc(EQ, 0, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(EQ, 1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(EQ, -1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(GT, 0, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(GT, 1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.verum(), f.pbc(GT, -1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.verum(), f.pbc(GE, 0, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(GE, 1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.verum(), f.pbc(GE, -1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(LT, 0, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.verum(), f.pbc(LT, 1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(LT, -1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.verum(), f.pbc(LE, 0, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.verum(), f.pbc(LE, 1, empty_lits.clone(), empty_coeffs.clone()));
        assert_eq!(f.falsum(), f.pbc(LE, -1, empty_lits, empty_coeffs));

        assert_eq!(f.verum(), f.cc(EQ, 0, empty_vars.clone()));
        assert_eq!(f.falsum(), f.cc(EQ, 1, empty_vars.clone()));
        assert_eq!(f.falsum(), f.cc(GT, 0, empty_vars.clone()));
        assert_eq!(f.falsum(), f.cc(GT, 1, empty_vars.clone()));
        assert_eq!(f.verum(), f.cc(GE, 0, empty_vars.clone()));
        assert_eq!(f.falsum(), f.cc(GE, 1, empty_vars.clone()));
        assert_eq!(f.verum(), f.cc(LT, 1, empty_vars.clone()));
        assert_eq!(f.verum(), f.cc(LE, 0, empty_vars.clone()));
        assert_eq!(f.verum(), f.cc(LE, 1, empty_vars));
    }

    #[test]
    fn test_simplified_to_string() {
        let f = &FormulaFactory::new();
        let empty_lits: Box<[Literal]> = Box::new([]);
        let empty_coeffs: Box<[i64]> = Box::new([]);
        let empty_vars: Box<[Variable]> = Box::new([]);
        assert_eq!("$true", f.pbc(EQ, 0, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(EQ, 1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(EQ, -1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(GT, 0, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(GT, 1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$true", f.pbc(GT, -1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$true", f.pbc(GE, 0, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(GE, 1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$true", f.pbc(GE, -1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(LT, 0, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$true", f.pbc(LT, 1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(LT, -1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$true", f.pbc(LE, 0, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$true", f.pbc(LE, 1, empty_lits.clone(), empty_coeffs.clone()).to_string(f));
        assert_eq!("$false", f.pbc(LE, -1, empty_lits, empty_coeffs).to_string(f));

        assert_eq!("$true", f.cc(EQ, 0, empty_vars.clone()).to_string(f));
        assert_eq!("$false", f.cc(EQ, 1, empty_vars.clone()).to_string(f));
        assert_eq!("$false", f.cc(GT, 0, empty_vars.clone()).to_string(f));
        assert_eq!("$false", f.cc(GT, 1, empty_vars.clone()).to_string(f));
        assert_eq!("$true", f.cc(GE, 0, empty_vars.clone()).to_string(f));
        assert_eq!("$false", f.cc(GE, 1, empty_vars.clone()).to_string(f));
        assert_eq!("$true", f.cc(LT, 1, empty_vars.clone()).to_string(f));
        assert_eq!("$true", f.cc(LE, 0, empty_vars.clone()).to_string(f));
        assert_eq!("$true", f.cc(LE, 1, empty_vars).to_string(f));
    }

    fn generate_formulas(
        f: &FormulaFactory,
    ) -> (EncodedFormula, EncodedFormula, EncodedFormula, EncodedFormula, EncodedFormula, EncodedFormula, EncodedFormula, EncodedFormula)
    {
        let vars1: Box<[Variable]> = Box::new([f.var("a")]);
        let lits1: Box<[Literal]> = Box::new([f.lit("a", true)]);
        let vars2: Box<[Variable]> = Box::new([f.var("a"), f.var("b"), f.var("c")]);
        let lits2: Box<[Literal]> = Box::new([f.lit("a", true), f.lit("b", false), f.lit("c", true)]);
        let coeffs1: Box<[i64]> = Box::new([3_i64]);
        let coeffs2: Box<[i64]> = Box::new([3_i64, -2, 7]);
        let pb1 = f.pbc(LE, 2, lits1, coeffs1);
        let pb2 = f.pbc(LE, 8, lits2, coeffs2);
        let cc1 = f.cc(LT, 1, vars1.clone());
        let cc2 = f.cc(GE, 2, vars2.clone());
        let amo1 = f.amo(vars1.clone());
        let amo2 = f.amo(vars2.clone());
        let exo1 = f.exo(vars1);
        let exo2 = f.exo(vars2);
        (pb1, pb2, cc1, cc2, amo1, amo2, exo1, exo2)
    }
}

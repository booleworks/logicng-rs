mod or_test {
    use crate::formulas::EncodedFormula;
    use crate::util::test_util::{hash, lits, string_lits, string_vars, vars, F};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.OR1.is_or());
        assert!(ff.OR1.is_nary_operator());
        assert!(!ff.OR1.is_and());
        assert!(!ff.OR1.is_verum());
        assert!(!ff.OR1.is_falsum());
        assert!(!ff.OR1.is_variable());
        assert!(!ff.OR1.is_literal());
        assert!(!ff.OR1.is_negative_literal());
        assert!(!ff.OR1.is_not());
        assert!(!ff.OR1.is_impl());
        assert!(!ff.OR1.is_equiv());
        assert!(!ff.OR1.is_binary_operator());
    }

    #[test]
    fn test_creator() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.or([] as [EncodedFormula; 0]), ff.FALSE);
        assert_eq!(f.or([ff.TRUE]), ff.TRUE);
        assert_eq!(f.or([ff.FALSE]), ff.FALSE);
        assert_eq!(f.or([ff.TRUE, ff.FALSE]), ff.TRUE);
        assert_eq!(f.or([ff.FALSE, ff.TRUE]), ff.TRUE);
        assert_eq!(f.or([ff.NA]), ff.NA);
        assert_eq!(f.or([ff.X, ff.Y, ff.X, ff.Y, ff.X]), ff.OR1);
        let or1 = f.or([ff.X, ff.Y]);
        let or2 = f.or([ff.X, ff.Y]);
        assert_eq!(f.or([or1, ff.X, or2]), ff.OR1);
        assert_eq!(f.or([ff.FALSE, ff.X, ff.Y, ff.FALSE]), ff.OR1);
        assert_eq!(f.or([ff.NA, ff.NA, ff.NA]), ff.NA);
        assert_eq!(f.or([ff.NA, ff.NA, ff.FALSE, ff.FALSE]), ff.NA);
        assert_eq!(f.or([ff.NA, ff.NA, ff.TRUE, ff.FALSE]), ff.TRUE);
        assert_eq!(f.or([ff.X, ff.Y]), ff.OR1);
        assert_eq!(f.or([ff.A, ff.B, ff.X, ff.TRUE]), ff.TRUE);
        let or1 = f.or([ff.A, ff.B]);
        let or2 = f.or([ff.X, ff.Y]);
        let or3 = f.or([ff.A, ff.B, ff.X, ff.Y]);
        assert_eq!(f.or([or1, or2]), or3);
        let and1 = f.and([ff.A, ff.B]);
        let and2 = f.and([ff.NA, ff.NB]);
        let or1 = f.or([ff.NA, ff.FALSE]);
        let and3 = f.and([and2]);
        let and4 = f.and([or1, ff.NB]);
        let or2 = f.or([and3, and4]);
        assert_eq!(f.or([and1, or2]), ff.OR3);
        assert_eq!(f.or([ff.X, ff.Y, ff.X, ff.Y, ff.X]), ff.OR1);
    }

    #[test]
    fn test_complementary_check() {
        let ff = F::new();
        let f = &ff.f;
        let or1 = f.or([ff.C, ff.X, ff.NB]);
        let or2 = f.or([ff.NX, ff.B, ff.X]);
        let and1 = f.and([ff.NX, ff.B, ff.X]);
        assert_eq!(f.or([ff.A, ff.NA]), ff.TRUE);
        assert_eq!(f.or([ff.A, ff.B, or1]), ff.TRUE);
        assert_eq!(f.or([ff.A, ff.B, or2]), ff.TRUE);
        assert_eq!(f.or([ff.X, ff.Y, and1]), ff.OR1);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.OR2.variables(f), vars("x y", f));
        assert_eq!(ff.OR2.string_variables(f), string_vars("x y"));

        let or = f.or([ff.A, ff.A, ff.B, ff.IMP3]);
        assert_eq!(*or.variables(f), vars("a b x y", f));
        assert_eq!(or.string_variables(f), string_vars("a b x y"));
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.OR2.literals(f), lits("~x ~y", f));
        assert_eq!(ff.OR2.string_literals(f), string_lits("~x ~y"));

        let impl1 = f.implication(ff.NB, ff.NA);
        let or = f.or([ff.A, ff.A, ff.B, impl1]);
        assert_eq!(*or.literals(f), lits("a b ~a ~b", f));
        assert_eq!(or.string_literals(f), string_lits("a b ~a ~b"));
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.OR1.to_string(f), "x | y");
        assert_eq!(ff.OR2.to_string(f), "~x | ~y");
        assert_eq!(ff.OR3.to_string(f), "a & b | ~a & ~b");
        assert_eq!(f.or([ff.A, ff.B, ff.NX, ff.NY]).to_string(f), "a | b | ~x | ~y");
        assert_eq!(f.or([ff.IMP1, ff.IMP2]).to_string(f), "(a => b) | (~a => ~b)");
        assert_eq!(f.or([ff.EQ1, ff.EQ2]).to_string(f), "(a <=> b) | (~a <=> ~b)");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.or([ff.X, ff.Y]), ff.OR1);
        assert_eq!(f.or([ff.AND1, ff.AND2]), ff.OR3);
        assert_eq!(ff.OR2, ff.OR2);
        assert_eq!(f.or([ff.NX, ff.A, ff.NB, ff.AND1]), f.or([ff.A, ff.NB, ff.AND1, ff.NX]));
        assert_ne!(ff.OR2, ff.OR1);
        assert_ne!(f.or([ff.A, ff.B, ff.C]), ff.OR1);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        let or = f.or([ff.AND1, ff.AND2]);
        assert_eq!(hash(or), hash(ff.OR3));
        assert_eq!(hash(f.or([ff.NX, ff.NY])), hash(ff.OR2));
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.OR1.number_of_atoms(f), 2);
        assert_eq!(ff.OR2.number_of_atoms(f), 2);
        assert_eq!(ff.OR3.number_of_atoms(f), 4);
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.OR1.number_of_nodes(f), 3);
        assert_eq!(ff.OR2.number_of_nodes(f), 3);
        assert_eq!(ff.OR3.number_of_nodes(f), 7);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        let or = f.parse("a & (b | c) => (d <=> (b | c))").unwrap();
        assert_eq!(ff.OR3.number_of_internal_nodes(f), 7);
        assert_eq!(or.number_of_internal_nodes(f), 8);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.OR1.number_of_operands(f), 2);
        assert_eq!(ff.OR3.number_of_operands(f), 2);
        assert_eq!(f.or([ff.A, ff.NX, ff.EQ1]).number_of_operands(f), 3);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(!ff.OR1.is_constant());
        assert!(!ff.OR2.is_constant());
        assert!(!ff.OR3.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(!ff.OR1.is_atomic());
        assert!(!ff.OR2.is_atomic());
        assert!(!ff.OR3.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(ff.OR1.contains_var_name("x", f));
        assert!(!ff.OR1.contains_var_name("a", f));
        let cont_and = f.parse("a | b | (c & (d | e))").unwrap();
        assert!(cont_and.contains_node(f.parse("d | e").unwrap(), f));
    }
}

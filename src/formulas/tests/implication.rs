mod implication_test {
    use crate::util::test_util::{hash, lits, string_lits, string_vars, vars, F};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.IMP1.is_impl());
        assert!(ff.IMP1.is_binary_operator());
        assert!(!ff.IMP1.is_or());
        assert!(!ff.IMP1.is_nary_operator());
        assert!(!ff.IMP1.is_and());
        assert!(!ff.IMP1.is_verum());
        assert!(!ff.IMP1.is_falsum());
        assert!(!ff.IMP1.is_variable());
        assert!(!ff.IMP1.is_literal());
        assert!(!ff.IMP1.is_negative_literal());
        assert!(!ff.IMP1.is_not());
        assert!(!ff.IMP1.is_equiv());
    }

    #[test]
    fn test_creator() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.implication(ff.FALSE, ff.A), ff.TRUE);
        assert_eq!(f.implication(ff.A, ff.TRUE), ff.TRUE);
        assert_eq!(f.implication(ff.TRUE, ff.A), ff.A);
        assert_eq!(f.implication(ff.A, ff.FALSE), ff.NA);
        assert_eq!(f.implication(ff.A, ff.A), ff.TRUE);
        assert_eq!(f.implication(ff.A, ff.NA), ff.NA);
        assert_eq!(f.implication(ff.NA, ff.A), ff.A);
        assert_eq!(f.implication(ff.IMP4, f.negate(ff.IMP4)), f.negate(ff.IMP4));
        assert_eq!(f.implication(f.negate(ff.IMP4), ff.IMP4), ff.IMP4);
        assert_eq!(f.implication(ff.AND1, ff.OR1), ff.IMP3);
    }

    #[test]
    fn test_getters() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.IMP2.left(f).unwrap(), ff.NA);
        assert_eq!(ff.IMP2.right(f).unwrap(), ff.NB);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.IMP3.variables(f), vars("a b x y", f));
        assert_eq!(ff.IMP3.string_variables(f), string_vars("a b x y"));

        let imp = f.implication(ff.AND1, ff.AND2);
        assert_eq!(*imp.variables(f), vars("a b", f));
        assert_eq!(imp.string_variables(f), string_vars("a b"));
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.IMP3.literals(f), lits("a b x y", f));
        assert_eq!(ff.IMP3.string_literals(f), string_lits("a b x y"));

        let imp = f.implication(ff.AND1, ff.AND2);
        assert_eq!(*imp.literals(f), lits("a b ~a ~b", f));
        assert_eq!(imp.string_literals(f), string_lits("a b ~a ~b"));

        let imp = f.implication(ff.AND1, ff.A);
        assert_eq!(*imp.literals(f), lits("a b", f));
        assert_eq!(imp.string_literals(f), string_lits("a b"));
    }

    #[test]
    fn test_negation() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.negate(ff.IMP1), f.not(ff.IMP1));
        assert_eq!(f.negate(ff.IMP2), f.not(ff.IMP2));
        assert_eq!(f.negate(ff.IMP3), f.not(ff.IMP3));
        assert_eq!(f.negate(ff.IMP4), f.not(ff.IMP4));
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.IMP1.to_string(f), "a => b");
        assert_eq!(ff.IMP2.to_string(f), "~a => ~b");
        assert_eq!(ff.IMP3.to_string(f), "a & b => x | y");
        assert_eq!(ff.IMP4.to_string(f), "(a <=> b) => (~x <=> ~y)");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.implication(ff.A, ff.B), ff.IMP1);
        assert_eq!(f.implication(ff.AND1, ff.OR1), ff.IMP3);
        assert_eq!(ff.IMP2, ff.IMP2);
        assert_ne!(ff.IMP2, ff.IMP1);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        let imp = f.implication(ff.NA, ff.NB);
        assert_eq!(hash(imp), hash(ff.IMP2));
        assert_eq!(hash(f.implication(ff.AND1, ff.OR1)), hash(ff.IMP3));
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.IMP1.number_of_atoms(f), 2);
        assert_eq!(ff.IMP3.number_of_atoms(f), 4);
        assert_eq!(ff.IMP3.number_of_atoms(f), 4);
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.IMP1.number_of_nodes(f), 3);
        assert_eq!(ff.IMP4.number_of_nodes(f), 7);
        assert_eq!(ff.IMP4.number_of_nodes(f), 7);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        let imp = f.parse("a & (b | c) => (d <=> (b | c))").unwrap();
        assert_eq!(ff.IMP4.number_of_internal_nodes(f), 7);
        assert_eq!(imp.number_of_internal_nodes(f), 8);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.IMP1.number_of_operands(f), 2);
        assert_eq!(ff.IMP2.number_of_operands(f), 2);
        assert_eq!(ff.IMP3.number_of_operands(f), 2);
        assert_eq!(ff.IMP4.number_of_operands(f), 2);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(!ff.IMP1.is_constant());
        assert!(!ff.IMP2.is_constant());
        assert!(!ff.IMP3.is_constant());
        assert!(!ff.IMP4.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(!ff.IMP1.is_atomic());
        assert!(!ff.IMP4.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(ff.IMP4.contains_var_name("a", f));
        assert!(!ff.IMP4.contains_var_name("c", f));
        assert!(ff.IMP4.contains_node(ff.EQ1, f));
        assert!(!ff.IMP4.contains_node(ff.NOT1, f));
    }
}

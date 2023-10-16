mod not_test {
    use crate::util::test_util::{hash, lits, string_lits, string_vars, vars, F};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.NOT1.is_not());
        assert!(!ff.NOT1.is_or());
        assert!(!ff.NOT1.is_nary_operator());
        assert!(!ff.NOT1.is_and());
        assert!(!ff.NOT1.is_verum());
        assert!(!ff.NOT1.is_falsum());
        assert!(!ff.NOT1.is_variable());
        assert!(!ff.NOT1.is_literal());
        assert!(!ff.NOT1.is_negative_literal());
        assert!(!ff.NOT1.is_impl());
        assert!(!ff.NOT1.is_binary_operator());
        assert!(!ff.NOT1.is_equiv());
    }

    #[test]
    fn test_creator() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.not(ff.FALSE), ff.TRUE);
        assert_eq!(f.not(ff.TRUE), ff.FALSE);
        assert_eq!(f.not(ff.NA), ff.A);
        assert_eq!(f.not(ff.A), ff.NA);
        let not = f.not(ff.IMP3);
        assert_eq!(f.not(not), ff.IMP3);
        assert_eq!(f.not(ff.AND1), ff.NOT1);
    }

    #[test]
    fn test_getters() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.NOT1.not_operand(f).unwrap(), ff.AND1);
        assert_eq!(ff.NOT2.not_operand(f).unwrap(), ff.OR1);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.NOT1.variables(f), vars("a b", f));
        assert_eq!(*ff.NOT2.variables(f), vars("x y", f));
        assert_eq!(ff.NOT1.string_variables(f), string_vars("a b"));
        assert_eq!(ff.NOT2.string_variables(f), string_vars("x y"));
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.NOT1.literals(f), lits("a b", f));
        assert_eq!(ff.NOT1.string_literals(f), string_lits("a b"));

        let imp = f.implication(ff.B, ff.NA);
        let and = f.and([ff.A, ff.NB, imp]);
        let not = f.not(and);
        assert_eq!(*not.literals(f), lits("a b ~a ~b", f));
        assert_eq!(not.string_literals(f), string_lits("a b ~a ~b"));
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.NOT1.to_string(f), "~(a & b)");
        assert_eq!(ff.NOT2.to_string(f), "~(x | y)");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.not(ff.AND1), ff.NOT1);
        assert_eq!(f.not(ff.OR1), ff.NOT2);
        assert_eq!(ff.NOT1, ff.NOT1);
        assert_ne!(ff.NOT2, ff.NOT1);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        let not = f.not(ff.AND1);
        assert_eq!(hash(not), hash(ff.NOT1));
        assert_eq!(hash(f.not(ff.OR1)), hash(ff.NOT2));
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.NOT1.number_of_atoms(f), 2);
        assert_eq!(ff.NOT2.number_of_atoms(f), 2);
        assert_eq!(ff.OR1.number_of_atoms(f), 2);
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.NOT1.number_of_nodes(f), 4);
        assert_eq!(ff.NOT2.number_of_nodes(f), 4);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        let eq = f.parse("a & (b | c) <=> ~(d => (b | c))").unwrap();
        assert_eq!(ff.NOT1.number_of_internal_nodes(f), 4);
        assert_eq!(eq.number_of_internal_nodes(f), 9);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.NOT1.number_of_operands(f), 1);
        assert_eq!(f.not(ff.EQ1).number_of_operands(f), 1);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(!ff.NOT1.is_constant());
        assert!(!ff.NOT2.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(!ff.NOT1.is_atomic());
        assert!(!ff.NOT2.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(ff.NOT1.contains_var_name("a", f));
        assert!(!ff.NOT1.contains_var_name("x", f));
        assert!(ff.NOT1.contains_node(ff.AND1, f));
        assert!(!ff.NOT1.contains_node(ff.AND2, f));
    }
}

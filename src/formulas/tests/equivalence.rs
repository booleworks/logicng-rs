mod implication_test {
    use crate::util::test_util::{F, hash, lits, string_lits, string_vars, vars};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.EQ1.is_equiv());
        assert!(ff.EQ1.is_binary_operator());
        assert!(!ff.EQ1.is_or());
        assert!(!ff.EQ1.is_nary_operator());
        assert!(!ff.EQ1.is_and());
        assert!(!ff.EQ1.is_verum());
        assert!(!ff.EQ1.is_falsum());
        assert!(!ff.EQ1.is_variable());
        assert!(!ff.EQ1.is_literal());
        assert!(!ff.EQ1.is_negative_literal());
        assert!(!ff.EQ1.is_not());
        assert!(!ff.EQ1.is_impl());
    }

    #[test]
    fn test_creator() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.equivalence(ff.TRUE, ff.AND1), ff.AND1);
        assert_eq!(f.equivalence(ff.AND1, ff.TRUE), ff.AND1);
        assert_eq!(f.equivalence(ff.FALSE, ff.AND1), ff.NOT1);
        assert_eq!(f.equivalence(ff.AND1, ff.FALSE), ff.NOT1);
        assert_eq!(f.equivalence(ff.OR1, ff.OR1), ff.TRUE);
        assert_eq!(f.equivalence(ff.NOT1, ff.AND1), ff.FALSE);
        assert_eq!(f.equivalence(ff.AND1, ff.NOT1), ff.FALSE);
        assert_eq!(f.equivalence(ff.OR1, ff.NOT2), ff.FALSE);
        assert_eq!(f.equivalence(ff.NOT2, ff.OR1), ff.FALSE);
        assert_eq!(f.equivalence(ff.AND1, ff.OR1), ff.EQ3);
    }

    #[test]
    fn test_getters() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.EQ2.left(f).unwrap(), ff.NA);
        assert_eq!(ff.EQ2.right(f).unwrap(), ff.NB);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.IMP3.variables(f), vars("a b x y", f));
        assert_eq!(ff.IMP3.string_variables(f), string_vars("a b x y"));

        let equiv = f.equivalence(ff.AND1, ff.AND2);
        assert_eq!(*equiv.variables(f), vars("a b", f));
        assert_eq!(equiv.string_variables(f), string_vars("a b"));
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.IMP3.literals(f), lits("a b x y", f));
        assert_eq!(ff.IMP3.string_literals(f), string_lits("a b x y"));

        let equiv = f.equivalence(ff.AND1, ff.AND2);
        assert_eq!(*equiv.literals(f), lits("a b ~a ~b", f));
        assert_eq!(equiv.string_literals(f), string_lits("a b ~a ~b"));

        let equiv = f.equivalence(ff.AND1, ff.A);
        assert_eq!(*equiv.literals(f), lits("a b", f));
        assert_eq!(equiv.string_literals(f), string_lits("a b"));
    }

    #[test]
    fn test_negation() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.negate(ff.EQ1), f.not(ff.EQ1));
        assert_eq!(f.negate(ff.EQ2), f.not(ff.EQ2));
        assert_eq!(f.negate(ff.EQ3), f.not(ff.EQ3));
        assert_eq!(f.negate(ff.EQ4), f.not(ff.EQ4));
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.EQ1.to_string(f), "a <=> b");
        assert_eq!(ff.EQ2.to_string(f), "~a <=> ~b");
        assert_eq!(ff.EQ3.to_string(f), "a & b <=> x | y");
        assert_eq!(ff.EQ4.to_string(f), "a => b <=> ~a => ~b");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.equivalence(ff.A, ff.B), ff.EQ1);
        assert_eq!(f.equivalence(ff.B, ff.A), ff.EQ1);
        assert_eq!(f.equivalence(ff.AND1, ff.OR1), ff.EQ3);
        assert_eq!(ff.EQ4, ff.EQ4);
        assert_ne!(ff.EQ2, ff.EQ1);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        let eq = f.equivalence(ff.IMP1, ff.IMP2);
        assert_eq!(hash(eq), hash(ff.EQ4));
        assert_eq!(hash(eq), hash(ff.EQ4));
        assert_eq!(hash(f.equivalence(ff.AND1, ff.OR1)), hash(ff.EQ3));
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.EQ1.number_of_atoms(f), 2);
        assert_eq!(ff.EQ4.number_of_atoms(f), 4);
        assert_eq!(ff.EQ4.number_of_atoms(f), 4);
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.EQ1.number_of_nodes(f), 3);
        assert_eq!(ff.EQ4.number_of_nodes(f), 7);
        assert_eq!(ff.EQ4.number_of_nodes(f), 7);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        let eq = f.parse("a & (b | c) <=> (d => (b | c))").unwrap();
        assert_eq!(ff.EQ4.number_of_internal_nodes(f), 7);
        assert_eq!(eq.number_of_internal_nodes(f), 8);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.EQ1.number_of_operands(f), 2);
        assert_eq!(ff.EQ2.number_of_operands(f), 2);
        assert_eq!(ff.EQ3.number_of_operands(f), 2);
        assert_eq!(ff.EQ4.number_of_operands(f), 2);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(!ff.EQ1.is_constant());
        assert!(!ff.EQ2.is_constant());
        assert!(!ff.EQ3.is_constant());
        assert!(!ff.EQ4.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(!ff.EQ1.is_atomic());
        assert!(!ff.EQ4.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(ff.EQ4.contains_var_name("a", f));
        assert!(!ff.EQ4.contains_var_name("x", f));
        assert!(ff.EQ4.contains_node(ff.IMP1, f));
        assert!(!ff.EQ4.contains_node(ff.IMP4, f));
    }
}

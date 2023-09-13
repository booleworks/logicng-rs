mod literals_test {
    use std::borrow::Cow;

    use crate::util::test_util::{hash, lits, string_lits, string_vars, vars, F};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.A.is_variable());
        assert!(ff.A.is_literal());
        assert!(!ff.A.is_negative_literal());
        assert!(!ff.A.is_or());
        assert!(!ff.A.is_nary_operator());
        assert!(!ff.A.is_and());
        assert!(!ff.A.is_verum());
        assert!(!ff.A.is_falsum());
        assert!(!ff.A.is_not());
        assert!(!ff.A.is_equiv());
        assert!(!ff.A.is_impl());
        assert!(!ff.A.is_binary_operator());
        assert!(ff.NA.is_negative_literal());
        assert!(ff.NA.is_literal());
        assert!(!ff.NA.is_variable());
        assert!(!ff.NA.is_or());
        assert!(!ff.NA.is_nary_operator());
        assert!(!ff.NA.is_and());
        assert!(!ff.NA.is_verum());
        assert!(!ff.NA.is_falsum());
        assert!(!ff.NA.is_not());
        assert!(!ff.NA.is_equiv());
        assert!(!ff.NA.is_impl());
        assert!(!ff.NA.is_binary_operator());
    }

    #[test]
    fn test_creation() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.variable("a"), f.literal("a", true));
        assert_eq!(f.variable("b"), ff.B);
    }

    #[test]
    fn test_negation() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.negate(ff.A), ff.NA);
        assert_eq!(f.negate(ff.NA), ff.A);
    }

    #[test]
    fn test_getters() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.A.as_literal().map(|l| l.name(f)), Some(Cow::from("a")));
        assert_eq!(ff.NA.as_literal().map(|l| l.name(f)), Some(Cow::from("a")));
        assert_eq!(ff.A.as_literal().map(|l| l.phase()), Some(true));
        assert_eq!(ff.NA.as_literal().map(|l| l.phase()), Some(false));
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.A.variables(f), vars("a", f));
        assert_eq!(*ff.NA.variables(f), vars("a", f));
        assert_eq!(ff.A.string_variables(f), string_vars("a"));
        assert_eq!(ff.NA.string_variables(f), string_vars("a"));
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.A.literals(f), lits("a", f));
        assert_eq!(*ff.NA.literals(f), lits("~a", f));
        assert_eq!(ff.A.string_literals(f), string_lits("a"));
        assert_eq!(ff.NA.string_literals(f), string_lits("~a"));
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.A.to_string(f), "a");
        assert_eq!(ff.NA.to_string(f), "~a");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.literal("a", true), ff.A);
        assert_eq!(f.literal("a", false), ff.NA);
        assert_eq!(ff.A, ff.A);
        assert_ne!(ff.B, ff.A);
        assert_ne!(ff.NA, ff.A);
        assert_ne!(f.falsum(), ff.A);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(hash(f.literal("a", true)), hash(ff.A));
        assert_eq!(hash(f.literal("a", false)), hash(ff.NA));
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.A.number_of_atoms(f), 1);
        assert_eq!(ff.NA.number_of_atoms(f), 1);
        assert_eq!(ff.NA.number_of_atoms(f), 1);
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.A.number_of_nodes(f), 1);
        assert_eq!(ff.NA.number_of_nodes(f), 1);
        assert_eq!(ff.NA.number_of_nodes(f), 1);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.A.number_of_internal_nodes(f), 1);
        assert_eq!(ff.NA.number_of_internal_nodes(f), 1);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.A.number_of_operands(f), 0);
        assert_eq!(ff.NA.number_of_operands(f), 0);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(!ff.A.is_constant());
        assert!(!ff.NA.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(ff.A.is_atomic());
        assert!(ff.NA.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(!ff.A.contains_var_name("b", f));
        assert!(ff.A.contains_var_name("a", f));
        assert!(!ff.NA.contains_var_name("b", f));
        assert!(ff.NA.contains_var_name("a", f));
        assert!(ff.A.contains_node(ff.A, f));
        assert!(!ff.A.contains_node(ff.NA, f));
        assert!(!ff.A.contains_node(ff.AND1, f));
        assert!(ff.NA.contains_node(ff.NA, f));
        assert!(!ff.NA.contains_node(ff.A, f));
        assert!(!ff.NA.contains_node(ff.AND1, f));
    }
}

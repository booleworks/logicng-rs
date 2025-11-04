mod false_test {
    use crate::util::test_util::{F, hash};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.FALSE.is_falsum());
        assert!(!ff.FALSE.is_verum());
        assert!(!ff.FALSE.is_variable());
        assert!(!ff.FALSE.is_literal());
        assert!(!ff.FALSE.is_negative_literal());
        assert!(!ff.FALSE.is_or());
        assert!(!ff.FALSE.is_nary_operator());
        assert!(!ff.FALSE.is_and());
        assert!(!ff.FALSE.is_not());
        assert!(!ff.FALSE.is_equiv());
        assert!(!ff.FALSE.is_impl());
        assert!(!ff.FALSE.is_binary_operator());
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.number_of_atoms(f), 1);
    }

    #[test]
    fn test_negation() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.negate(ff.FALSE), ff.TRUE);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.variables(f).len(), 0);
        assert_eq!(ff.FALSE.string_variables(f).len(), 0);
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.literals(f).len(), 0);
        assert_eq!(ff.FALSE.string_literals(f).len(), 0);
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.to_string(f), "$false");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.falsum(), ff.FALSE);
        assert_ne!(f.verum(), ff.FALSE);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(hash(ff.FALSE), hash(f.falsum()));
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.number_of_nodes(f), 1);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.number_of_internal_nodes(f), 1);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.FALSE.number_of_operands(f), 0);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(ff.FALSE.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(ff.FALSE.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(!ff.FALSE.contains_var_name("a", f));
        assert!(ff.FALSE.contains_node(ff.FALSE, f));
        assert!(!ff.FALSE.contains_node(ff.TRUE, f));
        assert!(!ff.FALSE.contains_node(ff.A, f));
    }
}

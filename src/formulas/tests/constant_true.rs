mod true_test {
    use crate::util::test_util::{hash, F};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.TRUE.is_verum());
        assert!(!ff.TRUE.is_falsum());
        assert!(!ff.TRUE.is_variable());
        assert!(!ff.TRUE.is_literal());
        assert!(!ff.TRUE.is_negative_literal());
        assert!(!ff.TRUE.is_or());
        assert!(!ff.TRUE.is_nary_operator());
        assert!(!ff.TRUE.is_and());
        assert!(!ff.TRUE.is_not());
        assert!(!ff.TRUE.is_equiv());
        assert!(!ff.TRUE.is_impl());
        assert!(!ff.TRUE.is_binary_operator());
    }

    #[test]
    fn test_number_of_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.number_of_atoms(f), 1);
        assert_eq!(ff.TRUE.number_of_atoms(f), 1);
    }

    #[test]
    fn test_negation() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.negate(ff.TRUE), ff.FALSE);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.variables(f).len(), 0);
        assert_eq!(ff.TRUE.string_variables(f).len(), 0);
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.literals(f).len(), 0);
        assert_eq!(ff.TRUE.string_literals(f).len(), 0);
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.to_string(f), "$true");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.verum(), ff.TRUE);
        assert_ne!(f.falsum(), ff.TRUE);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(hash(ff.TRUE), hash(f.verum()));
    }

    #[test]
    fn test_number_of_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.number_of_nodes(f), 1);
    }

    #[test]
    fn test_number_of_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.number_of_internal_nodes(f), 1);
    }

    #[test]
    fn test_number_of_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.TRUE.number_of_operands(f), 0);
    }

    #[test]
    fn test_is_constant_formula() {
        let ff = F::new();
        assert!(ff.TRUE.is_constant());
    }

    #[test]
    fn test_atomic_formula() {
        let ff = F::new();
        assert!(ff.TRUE.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(!ff.TRUE.contains_var_name("a", f));
        assert!(!ff.TRUE.contains_node(ff.A, f));
        assert!(ff.TRUE.contains_node(ff.TRUE, f));
        assert!(!ff.TRUE.contains_node(ff.FALSE, f));
    }
}

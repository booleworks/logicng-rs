mod and_test {
    use crate::formulas::{EncodedFormula, FormulaFactory};
    use crate::util::test_util::{F, hash, lits, string_lits, string_vars, vars};

    #[test]
    fn test_type() {
        let ff = F::new();
        assert!(ff.AND1.is_and());
        assert!(ff.AND1.is_nary_operator());
        assert!(!ff.AND1.is_or());
        assert!(!ff.AND1.is_verum());
        assert!(!ff.AND1.is_falsum());
        assert!(!ff.AND1.is_variable());
        assert!(!ff.AND1.is_literal());
        assert!(!ff.AND1.is_negative_literal());
        assert!(!ff.AND1.is_not());
        assert!(!ff.AND1.is_impl());
        assert!(!ff.AND1.is_equiv());
        assert!(!ff.AND1.is_binary_operator());
    }

    #[test]
    fn test_creation() {
        let ff = F::new();
        let f = &FormulaFactory::new();
        let _nx = f.literal("x", false);
        let _ny = f.literal("y", false);
        assert_eq!(f.and([] as [EncodedFormula; 0]), ff.TRUE);
        assert_eq!(f.and([ff.TRUE]), ff.TRUE);
        assert_eq!(f.and([ff.FALSE]), ff.FALSE);
        assert_eq!(f.and([ff.TRUE, ff.FALSE]), ff.FALSE);
        assert_eq!(f.and([ff.FALSE, ff.TRUE]), ff.FALSE);
        assert_eq!(f.and([ff.NA]), ff.NA);
        assert_eq!(f.and([ff.A, ff.B, ff.A, ff.B, ff.A]), f.and([ff.A, ff.B]));
        let op1 = f.and([ff.A, ff.B]);
        let op2 = f.and([ff.B, ff.A]);
        assert_eq!(f.and([op1, ff.A, op2]), f.and([ff.A, ff.B]));
        assert_eq!(f.and([ff.TRUE, ff.A, ff.B, ff.TRUE]), f.and([ff.A, ff.B]));
        assert_eq!(f.and([ff.NA, ff.NA, ff.NA]), ff.NA);
        assert_eq!(f.and([ff.NA, ff.NA, ff.TRUE, ff.TRUE]), ff.NA);
        assert_eq!(f.and([ff.NA, ff.NA, ff.FALSE, ff.TRUE]), ff.FALSE);
        assert_eq!(f.and([ff.A, ff.B, ff.X, ff.FALSE]), ff.FALSE);
        let op1 = f.and([ff.A, ff.B]);
        let op2 = f.and([ff.X, ff.Y]);
        assert_eq!(f.and([op1, op2]), f.and([ff.A, ff.B, ff.X, ff.Y]));
        assert_eq!(f.and([ff.A, ff.B, ff.A, ff.B, ff.A]), ff.AND1);
    }

    #[test]
    fn test_complementary_check() {
        let ff = F::new();
        let f = &FormulaFactory::new();
        let op1 = f.and([ff.C, ff.X, ff.NB]);
        let op2 = f.and([ff.NX, ff.B, ff.X]);
        assert_eq!(f.and([ff.A, ff.NA]), ff.FALSE);
        assert_eq!(f.and([ff.A, ff.B, op1]), ff.FALSE);
        assert_eq!(f.and([ff.A, ff.B, op2]), ff.FALSE);
    }

    #[test]
    fn test_variables() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.AND1.variables(f), vars("a b", f));
        assert_eq!(*f.and([ff.A, ff.A, ff.B, ff.IMP3]).variables(f), vars("a b x y", f));
        assert_eq!(ff.AND1.string_variables(f), string_vars("a b"));
        assert_eq!(f.and([ff.A, ff.A, ff.B, ff.IMP3]).string_variables(f), string_vars("a b x y"));
    }

    #[test]
    fn test_literals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(*ff.AND1.literals(f), lits("a b", f));
        assert_eq!(*f.and([ff.A, ff.A, ff.B, ff.IMP2]).literals(f), lits("a b ~a ~b", f));
        assert_eq!(ff.AND1.string_literals(f), string_lits("a b"));
        assert_eq!(f.and([ff.A, ff.A, ff.B, ff.IMP2]).string_literals(f), string_lits("a b ~a ~b"));
    }

    #[test]
    fn test_to_string() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.AND1.to_string(f), "a & b");
        assert_eq!(ff.AND2.to_string(f), "~a & ~b");
        assert_eq!(ff.AND3.to_string(f), "(x | y) & (~x | ~y)");
        assert_eq!(f.and([ff.A, ff.B, ff.NX, ff.NY]).to_string(f), "a & b & ~x & ~y");
        assert_eq!(f.and([ff.IMP1, ff.IMP2]).to_string(f), "(a => b) & (~a => ~b)");
        assert_eq!(f.and([ff.EQ1, ff.EQ2]).to_string(f), "(a <=> b) & (~a <=> ~b)");
    }

    #[test]
    fn test_equals() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(f.and([ff.A, ff.B]), ff.AND1);
        assert_eq!(f.and([ff.OR1, ff.OR2]), ff.AND3);
        assert_eq!(ff.AND2, ff.AND2);
        let ny = f.literal("y", false);
        let x = f.variable("x");
        let a = f.variable("a");
        let b = f.variable("b");
        let or1 = f.or([ny, x]);
        let or2 = f.or([b, a]);
        let or3 = f.or([a, b]);
        let or4 = f.or([x, ny]);
        assert_eq!(f.and([or1, or2]), f.and([or3, or4]));
        assert_eq!(f.and([ff.NX, ff.A, ff.NB, ff.OR1]), f.and([ff.A, ff.NB, ff.OR1, ff.NX]));
        assert_ne!(ff.AND2, ff.AND1);
        assert_ne!(f.and([ff.A, ff.B, ff.C]), ff.AND1);
    }

    #[test]
    fn test_hash() {
        let ff = F::new();
        let f = &ff.f;
        let and = f.and([ff.OR1, ff.OR2]);
        assert_eq!(hash(and), hash(ff.AND3));
        assert_eq!(hash(f.and([ff.NA, ff.NB])), hash(ff.AND2));
    }

    #[test]
    fn test_num_atoms() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.AND1.number_of_atoms(f), 2);
        assert_eq!(ff.AND2.number_of_atoms(f), 2);
        assert_eq!(ff.AND3.number_of_atoms(f), 4);
    }

    #[test]
    fn test_num_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.AND1.number_of_nodes(f), 3);
        assert_eq!(ff.AND2.number_of_nodes(f), 3);
        assert_eq!(ff.AND3.number_of_nodes(f), 7);
        let and = f.parse("a & (b | c) => (d <=> (b | c))").unwrap();
        assert_eq!(and.number_of_nodes(f), 11);
    }

    #[test]
    fn test_num_internal_nodes() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.AND1.number_of_internal_nodes(f), 3);
        assert_eq!(ff.AND2.number_of_internal_nodes(f), 3);
        assert_eq!(ff.AND3.number_of_internal_nodes(f), 7);
        let and = f.parse("a & (b | c) => (d <=> (b | c))").unwrap();
        assert_eq!(and.number_of_internal_nodes(f), 8);
    }

    #[test]
    fn test_num_operands() {
        let ff = F::new();
        let f = &ff.f;
        assert_eq!(ff.AND1.number_of_operands(f), 2);
        assert_eq!(ff.AND2.number_of_operands(f), 2);
        assert_eq!(ff.AND3.number_of_operands(f), 2);
        assert_eq!(f.and([ff.A, ff.NX, ff.EQ1]).number_of_operands(f), 3);
    }

    #[test]
    fn test_is_constant() {
        let ff = F::new();
        assert!(!ff.AND1.is_constant());
        assert!(!ff.AND2.is_constant());
        assert!(!ff.AND3.is_constant());
    }

    #[test]
    fn test_is_atomic() {
        let ff = F::new();
        assert!(!ff.AND1.is_atomic());
        assert!(!ff.AND2.is_atomic());
        assert!(!ff.AND3.is_atomic());
    }

    #[test]
    fn test_contains() {
        let ff = F::new();
        let f = &ff.f;
        assert!(ff.AND3.contains_var_name("x", f));
        assert!(!ff.AND3.contains_var_name("a", f));
        assert!(f.parse("a & b & (c | (d & e))").unwrap().contains_node(f.parse("d & e").unwrap(), f));
        assert!(f.parse("a & b & (c | (d & ~e))").unwrap().contains_node(f.parse("b").unwrap(), f));
        assert!(f.parse("a & b & (c | (d & ~e))").unwrap().contains_node(f.parse("~e").unwrap(), f));
        assert!(!f.parse("a & b & (c | (d & e))").unwrap().contains_node(f.parse("d & f").unwrap(), f));
        assert!(!f.parse("a & b & (c | (d & ~e))").unwrap().contains_node(f.parse("e").unwrap(), f));
    }
}

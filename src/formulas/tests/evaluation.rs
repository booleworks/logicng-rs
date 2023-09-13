mod evaluation_tests {
    use crate::datastructures::Assignment;
    use crate::formulas::ToFormula;
    use crate::util::test_util::F;

    fn ass(ff: &F) -> Assignment {
        Assignment::from_variables(
            &[ff.A.as_variable().unwrap(), ff.B.as_variable().unwrap(), ff.C.as_variable().unwrap()],
            &[ff.X.as_variable().unwrap(), ff.Y.as_variable().unwrap()],
        )
    }

    #[test]
    fn test_constant_eval() {
        let ff = F::new();
        assert!(ff.f.evaluate(ff.TRUE, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.FALSE, &ass(&ff)));
    }

    #[test]
    fn test_literal_eval() {
        let ff = F::new();
        assert!(ff.f.evaluate(ff.A, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.NA, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.X, &ass(&ff)));
        assert!(ff.f.evaluate(ff.NX, &ass(&ff)));
    }

    #[test]
    fn test_not_eval() {
        let ff = F::new();
        assert!(!ff.f.evaluate(ff.NOT1, &ass(&ff)));
        assert!(ff.f.evaluate(ff.NOT2, &ass(&ff)));
    }

    #[test]
    fn test_binary_eval() {
        let ff = F::new();
        assert!(ff.f.evaluate(ff.IMP1, &ass(&ff)));
        assert!(ff.f.evaluate(ff.IMP2, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.IMP3, &ass(&ff)));
        assert!(ff.f.evaluate(ff.IMP4, &ass(&ff)));

        assert!(ff.f.evaluate(ff.EQ1, &ass(&ff)));
        println!("{}", ff.EQ2.to_string(&ff.f));
        assert!(ff.f.evaluate(ff.EQ2, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.EQ3, &ass(&ff)));
        assert!(ff.f.evaluate(ff.EQ4, &ass(&ff)));
    }

    #[test]
    fn test_nary_eval() {
        let ff = F::new();
        let formula1 = "~a | ~b | ~c | x | y".to_formula(&ff.f);
        let formula2 = "~a | ~b | ~c | x | ~y".to_formula(&ff.f);
        let formula3 = "a & b & c & ~x & ~y".to_formula(&ff.f);
        let formula4 = "a & b & c & ~x & y".to_formula(&ff.f);

        assert!(!ff.f.evaluate(ff.OR1, &ass(&ff)));
        assert!(ff.f.evaluate(ff.OR2, &ass(&ff)));
        assert!(ff.f.evaluate(ff.OR3, &ass(&ff)));
        assert!(!ff.f.evaluate(formula1, &ass(&ff)));
        assert!(ff.f.evaluate(formula2, &ass(&ff)));

        assert!(ff.f.evaluate(ff.AND1, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.AND2, &ass(&ff)));
        assert!(!ff.f.evaluate(ff.AND3, &ass(&ff)));
        assert!(ff.f.evaluate(formula3, &ass(&ff)));
        assert!(!ff.f.evaluate(formula4, &ass(&ff)));
    }
}
